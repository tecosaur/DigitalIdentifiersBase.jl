# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Why have pretty code when you can have efficient code? 😜

"""
    @defid name pattern [kwarg=value...]

Define a new identifier type `name` with a parsing and printing `pattern`.

The `pattern` is a S-expression that describes the structure of the identifier.
The following constructs are available:

- `seq(arg1, arg2, ...)`: A sequence of patterns that must match in order.
  This is the implicit default, so you may just write `(arg1, arg2, ...)`.
- `optional(arg1, arg2, ...)`: An optional pattern that may or may not be present.
- `skip([print=str0], str1, str2, ...)`: A sequence of literal strings that should be skipped if present.
- `choice([is=opt0], opt1, opt2, ...)`: A choice between several literal string options.
- `literal(str)`: A literal string that must be present.
- `digits([n | min:max], [base=10, min=0, max=base^digits-1, pad=0])`:
- `alphnum([length], [min=length, max=length])`: A sequence of alphanumeric characters.

You may also use `:field(pattern)` to capture the value of a sub-pattern as a
property of the identifier. The captured value will be available as a property
with the same name as the field.

# Examples

```julia-repl
julia> @defid MyId ("i",
                    skip("-"),
                    :id(digits(6, pad=6)),
                    optional(".v", :version(digits(max=255)),
                             optional(".p", :participants(digits(max=2^16-1)))))

julia> parse(MyId, "i-000473.v2.p10")
MyId:i000473.v2.p10

julia> id = parse(MyId, "i5162.v1")
MyId:i005162.v1

julia> (id.id, id.version, id.participants)
(5162, 1, nothing)
```
"""
macro defid(name, pattern, args...)
    casefold_val = true
    prefix_val = nothing
    for arg in args
        Meta.isexpr(arg, :(=), 2) || throw(ArgumentError("Expected keyword arguments of the form key=value, got $arg"))
        kwname, kwval = arg.args
        kwname ∈ ALL_KNOWN_KEYS ||
            throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments are: $(join(ALL_KNOWN_KEYS, ", "))"))
        kwname === :casefold && (casefold_val = kwval)
        kwname === :purlprefix && (prefix_val = kwval)
    end
    root = ParseBranch(1, nothing, nothing, 0, 0, 0, 0, 0)
    state = DefIdState(name, __module__, 0, casefold_val, prefix_val, ParseBranch[root], String[])
    nctx = NodeCtx(:current_branch, root)
    exprs = IdExprs(([], [], [], []))
    # Strip PURL prefix before the main pattern
    if !isnothing(prefix_val)
        defid_dispatch!(exprs, state, nctx, Expr(:call, :skip, lowercase(prefix_val)))
    end
    defid_dispatch!(exprs, state, nctx, :__first_nonskip)
    defid_dispatch!(exprs, state, nctx, pattern)
    defid_make(exprs, state, name)
end

@static if VERSION < v"1.13-"
    takestring!(io::IO) = String(take!(io))
end

# -----------------------------------------------------------
# Types, constants, and helpers
# -----------------------------------------------------------

const ExprVarLine = Union{Expr, Symbol, LineNumberNode}
const NodeCtx = Base.ImmutableDict{Symbol, Any}
# Unified segment: each value-carrying pattern node pushes one of these
const IdValueSegment = @NamedTuple{
    nbits::Int,                            # bits consumed in packed representation
    kind::Symbol,                          # :digits, :choice, :letters, :alphnum, :literal, :skip
    label::Symbol,                         # attr_fieldname (inside field) or gensym (anonymous)
    desc::String,                          # human-readable description
    argtype::Any,                          # :Integer, :Symbol, :AbstractString, or nothing (non-parameterisable)
    argvar::Symbol,                        # gensym used as parameter placeholder in impart
    extract::Vector{ExprVarLine},          # bits → typed value (last expr is the value)
    impart::Vector{Any},                   # argvar → packed bits (validate + encode + orshift)
    condition::Union{Nothing, Symbol},     # optional scope gensym, nothing if required
}
const IdExprs = @NamedTuple{
    parse::Vector{ExprVarLine},
    print::Vector{ExprVarLine},
    segments::Vector{IdValueSegment},
    properties::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}},
}

"""Per-branch byte counters for tracking parse/print bounds through optional nesting."""
mutable struct ParseBranch
    const id::Int                              # 1-based index into branches registry
    const parent::Union{Nothing, ParseBranch}  # nothing for root
    const scope::Union{Nothing, Symbol}        # optional gensym (the boolean flag)
    const start_min::Int                       # parsed_min at branch creation
    parsed_min::Int                            # cumulative min input bytes consumed
    parsed_max::Int                            # cumulative max input bytes consumed
    print_min::Int                             # cumulative min output bytes produced
    print_max::Int                             # cumulative max output bytes produced
end

"""Global mutable state for @defid macro expansion, separating from scoped NodeCtx."""
mutable struct DefIdState
    const name::Symbol
    const mod::Module
    bits::Int
    const casefold::Bool
    const purlprefix::Union{Nothing, String}
    const branches::Vector{ParseBranch}
    const errconsts::Vector{String}
end

inc_parsed!(nctx::NodeCtx, dmin, dmax) =
    let b = nctx[:current_branch]; b.parsed_min += dmin; b.parsed_max += dmax end
inc_print!(nctx::NodeCtx, dmin, dmax) =
    let b = nctx[:current_branch]; b.print_min += dmin; b.print_max += dmax end

"""Resolve `__branch_check(Bool, id)`: `true` when zero-content or parent subsumes, else runtime check."""
function resolve_branch_check(b::ParseBranch)
    local_min = b.parsed_min - b.start_min
    local_min <= 0 || (!isnothing(b.parent) && b.parent.parsed_min >= b.parsed_min) ?
        true : :(nbytes - pos + 1 >= $local_min)
end

"""Non-value segment (literal, skip, zero-bit choice): no extract/impart/argtype."""
nullsegment(; nbits::Int, kind::Symbol, label::Symbol, desc::String,
              condition::Union{Nothing, Symbol}) =
    IdValueSegment((nbits, kind, label, desc, nothing, :_, ExprVarLine[], Any[], condition))

"""Filter nothings and LineNumberNodes from a quote block's args."""
clean_quote_args(block::Expr) =
    filter(e -> !isnothing(e) && !(e isa LineNumberNode), block.args)

"""Wrap impart body in `if !isnothing(argvar) ... end` for optional segments."""
wrap_optional_impart(argvar::Symbol, body) =
    Expr(:if, :(!isnothing($argvar)), Expr(:block, body...))

"""Strip `attr_` prefix from a fieldvar to get the segment label."""
seg_label(fieldvar::Symbol) = Symbol(chopprefix(String(fieldvar), "attr_"))

"""Generate the zero-initialized `parsed` expression for the packed identifier."""
zero_parsed_expr(state::DefIdState) =
    if state.bits <= 8
        :(Core.bitcast($(esc(state.name)), 0x00))
    else
        :(Core.Intrinsics.zext_int($(esc(state.name)), 0x0))
    end

"""
Map properties to `(name, segment_indices)` pairs, resolving Symbol refs to segments.
Returns a vector of `(property_name, [segment_index, ...])` pairs.
"""
function resolve_property_segments(properties, segs::Vector{IdValueSegment})
    result = Pair{Symbol, Vector{Int}}[]
    for (pname, val) in properties
        if val isa Symbol
            idx = findfirst(s -> s.label == val, segs)
            isnothing(idx) && continue
            push!(result, pname => [idx])
        else
            idxs = [i for (i, s) in enumerate(segs)
                     if !isnothing(s.argtype) && s.label == pname]
            push!(result, pname => idxs)
        end
    end
    result
end

const KNOWN_KEYS = (
    choice = (:casefold, :is),
    digits = (:base, :min, :max, :pad),
    letters = (:upper, :lower, :casefold),
    alphnum = (:upper, :lower, :casefold),
    skip = (:casefold, :print),
    _global = (:purlprefix,)
)

const ALL_KNOWN_KEYS = Tuple(unique(collect(Iterators.flatten(values(KNOWN_KEYS)))))

function segments end

nbits(::Type{T}) where {T<:AbstractIdentifier} = 8 * sizeof(T)

"""
    cardbits(n::Integer) -> Int

The number of bits required to store `n` distinct values.
"""
cardbits(n::Integer) = 8 * sizeof(n) - leading_zeros(n)

Base.@assume_effects :foldable function cardtype(minbits::Int)
    iszero(minbits) && return Nothing
    logtypesize = 1 + 8 * sizeof(minbits) - leading_zeros(cld(minbits, 8) - 1)
    logtypesize > 5 && throw(ArgumentError("Cannot allocate more than 128 bits for an identifier field, but $minbits bits were requested"))
    (UInt8, UInt16, UInt32, UInt64, UInt128)[logtypesize]
end

"""The smallest unsigned integer type that can hold `nd` bytes."""
swar_type(nd::Int) = nd <= 1 ? UInt8 : nd <= 2 ? UInt16 : nd <= 4 ? UInt32 : UInt64

"""Register a compile-time error message and return its 1-based index for use as an error code."""
function defid_errmsg(state::DefIdState, msg::String)
    push!(state.errconsts, msg)
    length(state.errconsts)
end

# -----------------------------------------------------------
# Pattern dispatch
# -----------------------------------------------------------

function defid_dispatch!(exprs::IdExprs,
                         state::DefIdState, nctx::NodeCtx,
                         node::Any, args::Vector{Any})
    if node isa QuoteNode
        defid_field!(exprs, state, nctx, node, args)
    elseif node === :seq
        for arg in args
            defid_dispatch!(exprs, state, nctx, arg)
        end
    elseif node === :optional
        defid_optional!(exprs, state, nctx, args)
    elseif node === :skip
        defid_skip!(exprs, state, nctx, args)
    elseif node === :choice
        defid_choice!(exprs, state, nctx, args)
    elseif node === :literal
        length(args) == 1 || throw(ArgumentError("Expected exactly one argument for literal, got $(length(args))"))
        lit = args[1]
        lit isa String || throw(ArgumentError("Expected a string literal for literal, got $lit"))
        defid_literal!(exprs, state, nctx, lit)
    elseif node === :digits
        defid_digits!(exprs, state, nctx, args)
    elseif node === :letters
        defid_charseq!(exprs, state, nctx, args, :letters)
    elseif node === :alphnum
        defid_charseq!(exprs, state, nctx, args, :alphnum)
    else
        throw(ArgumentError("Unknown pattern node $node"))
    end
end

function defid_dispatch!(exprs::IdExprs,
                         state::DefIdState, nctx::NodeCtx,
                         thing::Any)
    if Meta.isexpr(thing, :tuple)
        args = Any[]
        for arg in thing.args
            if Meta.isexpr(arg, :(=), 2)
                kwname, kwval = arg.args
                kwname ∈ ALL_KNOWN_KEYS ||
                    throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments are: $(join(ALL_KNOWN_KEYS, ", "))"))
                nctx = NodeCtx(nctx, kwname, kwval)
            else
                push!(args, arg)
            end
        end
        defid_dispatch!(exprs, state, nctx, :seq, args)
    elseif Meta.isexpr(thing, :call)
        name = first(thing.args)
        args = Any[]
        nkeys = if name isa Symbol && haskey(KNOWN_KEYS, name)
            KNOWN_KEYS[name]
        else
            ALL_KNOWN_KEYS
        end
        for arg in thing.args[2:end]
            if Meta.isexpr(arg, :kw, 2)
                kwname, kwval = arg.args
                kwname ∈ nkeys ||
                    throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments for $name are: $(join(nkeys, ", "))"))
                nctx = NodeCtx(nctx, kwname, kwval)
            else
                push!(args, arg)
            end
        end
        defid_dispatch!(exprs, state, nctx, name, args)
    elseif thing isa String
        defid_literal!(exprs, state, nctx, thing)
    elseif thing === :__first_nonskip
        root = nctx[:current_branch]
        root.parsed_min = 0
        root.parsed_max = 0
        push!(exprs.parse, Expr(:call, :__branch_check, root.id, nothing))
    end
end

# -----------------------------------------------------------
# Pattern handlers: field, optional, skip
# -----------------------------------------------------------

function defid_field!(exprs::IdExprs,
                      state::DefIdState, nctx::NodeCtx,
                      node::QuoteNode,
                      args::Vector{Any})
    isnothing(get(nctx, :fieldvar, nothing)) || throw(ArgumentError("Fields may not be nested"))
    nctx = NodeCtx(nctx, :fieldvar, Symbol("attr_$(node.value)"))
    initial_segs = length(exprs.segments)
    initialprints = length(exprs.print)
    for arg in args
        defid_dispatch!(exprs, state, nctx, arg)
    end
    # Count new value-carrying segments (those with argtype !== nothing)
    new_value_segs = filter(s -> !isnothing(s.argtype), @view exprs.segments[initial_segs+1:end])
    isempty(new_value_segs) && throw(ArgumentError("Field $(node.value) does not capture any value"))
    if length(new_value_segs) == 1
        # Single value segment: property references the segment's extract directly
        push!(exprs.properties, node.value => new_value_segs[1].label)
    else
        # Multi-node field: property assembles via IOBuffer from print expressions
        propprints = map(strip_segsets! ∘ copy, exprs.print[initialprints+1:end])
        filter!(e -> !Meta.isexpr(e, :(=), 2) || first(e.args) !== :__segment_printed, propprints)
        push!(exprs.properties, node.value => ExprVarLine[(
            quote
                io = IOBuffer()
                $(propprints...)
                takestring!(io)
            end).args...])
    end
end

function defid_optional!(exprs::IdExprs,
                         state::DefIdState, nctx::NodeCtx,
                         args::Vector{Any})
    popt = get(nctx, :optional, nothing)
    nctx = NodeCtx(nctx, :optional, gensym("optional"))
    nctx = NodeCtx(nctx, :oprint_detect, ExprVarLine[])
    # Fork a child branch for this optional scope
    parent = nctx[:current_branch]
    child = ParseBranch(length(state.branches) + 1, parent, nctx[:optional],
                        parent.parsed_min, parent.parsed_min, parent.parsed_max,
                        parent.print_min, parent.print_max)
    push!(state.branches, child)
    nctx = NodeCtx(nctx, :current_branch, child)
    oexprs = (; parse = ExprVarLine[], print = ExprVarLine[], segments = exprs.segments, properties = exprs.properties)
    if all(a -> a isa String, args)
        defid_choice!(oexprs, state, nctx, push!(Any[join(Vector{String}(args))], ""))
    else
        for arg in args
            defid_dispatch!(oexprs, state, nctx, arg)
        end
    end
    # Merge max back to parent; min stays unchanged (optional content doesn't raise the guarantee)
    parent.parsed_max = Base.max(parent.parsed_max, child.parsed_max)
    parent.print_max = Base.max(parent.print_max, child.print_max)
    optvar = nctx[:optional]
    # Rewind pos when the optional has multiple nodes: an early node may advance
    # pos before a later node fails and sets option=false. Not needed when the
    # all-strings path converted to a choice (single-node handling).
    needs_rewind = length(args) > 1 && !all(a -> a isa String, args)
    savedpos = needs_rewind ? gensym("savedpos") : nothing
    needs_rewind && push!(exprs.parse, :($savedpos = pos))
    # Branch check as condition: when resolved, guarantees local_min bytes
    # are available, allowing sentinels within the branch to fold safely.
    branch_check = Expr(:call, :__branch_check, Bool, child.id)
    guard = isnothing(popt) ? branch_check : :($popt && $branch_check)
    push!(exprs.parse, :($optvar = $guard))
    push!(exprs.parse, :(if $optvar; $(oexprs.parse...) end))
    needs_rewind && push!(exprs.parse, :($optvar || (pos = $savedpos)))
    append!(exprs.print, nctx[:oprint_detect])
    push!(exprs.print, :(if $(nctx[:optional]); $(oexprs.print...) end))
    nothing
end

function defid_skip!(exprs::IdExprs,
                     state::DefIdState, nctx::NodeCtx,
                     args::Vector{Any})
    all(a -> a isa String, args) || throw(ArgumentError("Expected all arguments to be strings for skip"))
    pval = get(nctx, :print, nothing)
    sargs = Vector{String}(args)
    !isnothing(pval) && pval ∉ sargs && push!(sargs, pval)
    casefold = get(nctx, :casefold, state.casefold) === true
    if casefold
        all(isascii, sargs) || throw(ArgumentError("Expected all arguments to be ASCII strings for skip with casefolding"))
    end
    push!(exprs.parse, gen_static_lchop(casefold ? map(lowercase, sargs) : sargs, casefold=casefold))
    inc_parsed!(nctx, 0, maximum(ncodeunits, sargs))
    if !isnothing(pval)
        push!(exprs.segments, nullsegment(nbits=0, kind=:skip, label=:skip,
              desc="Skipped literal string \"$(join(sargs, ", "))\"",
              condition=get(nctx, :optional, nothing)))
        push!(exprs.print, :(print(io, $pval)), :(__segment_printed = $(length(exprs.segments))))
        inc_print!(nctx, ncodeunits(pval), ncodeunits(pval))
    end
    nothing
end

# -----------------------------------------------------------
# Choice: perfect hashing and verification
# -----------------------------------------------------------

"""
    find_perfect_hash(options::Vector{String}, casefold::Bool)

Search for a perfect hash function over `options` using word-sized windows
and multiple hash families. Returns `nothing` or a named tuple with:
- `pos`: byte position of the window
- `iT`: unsigned integer type for the window load
- `foldmask`: OR mask for case folding
- `hashexpr`: function `value_expr -> index_expr` producing a 1-based index
- `perm`: permutation of options matching hash output order
- `kind`: `:direct` (consecutive hash values) or `:table` (lookup table)
- `injective`: whether the hash function is injective (identity family)
- `table`: lookup table (only for `:table` kind)
- `tablelen`: length of table (only for `:table` kind)
"""
function find_perfect_hash(options::Vector{String}, casefold::Bool)
    nopts = length(options)
    nopts <= 1 && return nothing
    minlen = minimum(ncodeunits, options)
    # Collect discriminating window candidates
    candidates = @NamedTuple{pos::Int, iT::DataType, values::Vector{UInt64}, foldmask::UInt64}[]
    for iT in INTS_UP_TO_WORD
        bwidth = sizeof(iT)
        bwidth > minlen && break
        for pos in 1:minlen - bwidth + 1
            values = map(options) do opt
                v = zero(UInt64)
                for j in 0:bwidth-1
                    b = codeunit(opt, pos + j)
                    v |= UInt64(casefold ? (b | 0x20) : b) << (8j)
                end
                v
            end
            length(unique(values)) == nopts || continue
            foldmask = zero(UInt64)
            if casefold
                for j in 0:bwidth-1
                    foldmask |= UInt64(0x20) << (8j)
                end
            end
            push!(candidates, (; pos, iT, values, foldmask))
        end
    end
    isempty(candidates) && return nothing
    best = nothing
    best_tier = 4  # lower is better
    for (; pos, iT, values, foldmask) in candidates
        best_tier <= 1 && break
        for hashfam in hash_families(iT, nopts)
            hvals = map(hashfam.fn, values)
            any(h -> h < 1, hvals) && continue
            length(unique(hvals)) == nopts || continue
            result = classify_hash(hvals, nopts, options,
                                    pos, iT, foldmask % iT, hashfam.expr)
            if result.tier < best_tier
                best = merge(result.ph, (; injective = hashfam.injective))
                best_tier = result.tier
                best_tier <= 1 && break
            end
        end
    end
    best
end

function hash_families(iT::DataType, nopts::Int)
    families = @NamedTuple{fn::Function, expr::Function, injective::Bool}[]
    # v (identity — simplest possible hash, produces v - offset when consecutive)
    push!(families, (fn = v -> v, expr = v -> v, injective = true))
    for m in nopts:2*nopts
        # v % m + 1
        push!(families, (fn = v -> v % m + 1,
                         expr = v -> :($v % $m + 1), injective = false))
        # (v >> k) % m + 1
        for k in 1:min(8 * sizeof(iT) - 1, 16)
            push!(families, (fn = v -> (v >> k) % m + 1,
                             expr = v -> :(($v >> $k) % $m + 1), injective = false))
        end
        # (v * c) >> k % m + 1
        for c in (0x9e3779b97f4a7c15, 0x517cc1b727220a95, 0x6c62272e07bb0142)
            for k in max(1, 8 * sizeof(iT) - 8):8 * sizeof(iT) - 1
                push!(families, (fn = v -> (v * c) >> k % m + 1,
                                 expr = v -> :((($v * $(c % iT)) >> $k) % $m + 1), injective = false))
            end
        end
    end
    families
end

function classify_hash(hvals::Vector{UInt64}, nopts::Int, options::Vector{String},
                        pos::Int, iT::DataType, foldmask, hashexpr_fn)
    sorted_indices = sortperm(hvals)
    sorted_hvals = hvals[sorted_indices]
    lo, hi = Int(sorted_hvals[1]), Int(sorted_hvals[end])
    # Tier 1: consecutive values — hashexpr(v) ± offset maps to 1:n
    if hi - lo + 1 == nopts
        if lo == 1
            ph = (; pos, iT, foldmask, hashexpr = hashexpr_fn,
                   perm = sorted_indices, kind = :direct,
                   table = (), tablelen = 0)
        else
            offset = iT(lo - 1)
            ph = (; pos, iT, foldmask,
                   hashexpr = v -> :($(hashexpr_fn(v)) - $offset),
                   perm = sorted_indices, kind = :direct,
                   table = (), tablelen = 0)
        end
        return (; tier = 1, ph)
    end
    # Tier 3: table lookup (original order, no permutation needed)
    maxval = Int(maximum(hvals))
    table = zeros(Int, maxval)
    for (i, h) in enumerate(hvals)
        table[Int(h)] = i
    end
    ph = (; pos, iT, foldmask, hashexpr = hashexpr_fn,
           perm = collect(1:nopts), kind = :table,
           table = Tuple(table), tablelen = maxval)
    (; tier = 3, ph)
end

"""
    gen_verify_table(options::Vector{String}, casefold::Bool; skip, nbytes)

Build word-sized comparison data for verifying a perfect-hash match.

Uses `load & mask == expected` convention: per-byte mask is `0xFF` (exact),
`0xDF` (case-insensitive), or `0x00` (overflow/ignore).

When `nbytes > minimum(ncodeunits, options)`, the no-skip chunks are widened,
with overflow bytes masked to `0x00`.

Returns `(; verify_table, masks, chunks)`.
"""
function gen_verify_table(options::Vector{String}, casefold::Bool;
                          skip::Union{Nothing, Tuple{Int, Int}} = nothing,
                          nbytes::Int = minimum(ncodeunits, options))
    minlen = minimum(ncodeunits, options)
    chunks = if isnothing(skip)
        word_chunks(nbytes)
    else
        # Split into chunks covering [0, gap) and [gap+width, total),
        # with right-side offsets adjusted to original string positions.
        # Widening is not applied when skip is active.
        gap_offset, gap_width = skip
        left = word_chunks(gap_offset)
        right = word_chunks(minlen - gap_offset - gap_width)
        right_base = gap_offset + gap_width
        for i in eachindex(right)
            right[i] = (; right[i]..., offset = right[i].offset + right_base)
        end
        vcat(left, right)
    end
    masks = Tuple(
        build_chunk_mask(c.iT, c.width,
            j -> c.offset + j < minlen,
            j -> casefold && any(opt -> codeunit(opt, c.offset + j + 1) in UInt8('a'):UInt8('z'), options))
        for c in chunks)
    verify_table = Tuple(
        Tuple(pack_bytes(opt, c.offset, min(c.width, max(0, minlen - c.offset)), c.iT) & m
              for (c, m) in zip(chunks, masks))
        for opt in options)
    (; verify_table, masks, chunks)
end

"""
    gen_verify_exprs(vt, prefix::Symbol; pos_offset=0) -> (destructure, checks)

Generate AST for destructured comparison of word-sized chunks.

Uses `load & mask == expected` convention. Assumes `idbytes` is in scope.
Returns:
- `destructure`: assignments that extract per-option expected values from the verify table
- `checks`: a boolean expression that is `true` when all chunks match
"""
function gen_verify_exprs(vt, prefix::Symbol; pos_offset::Int = 0)
    nchunks = length(vt.chunks)
    cvars = [Symbol(prefix, "_expect", ci) for ci in 1:nchunks]
    mvars = [Symbol(prefix, "_mask", ci) for ci in 1:nchunks]
    destructure = [
        Expr(:(=), Expr(:tuple, cvars...), :($(vt.verify_table)[i])),
        Expr(:(=), Expr(:tuple, mvars...), vt.masks)]
    checks = foldr(1:nchunks, init = :(true)) do ci, rest
        baseoff = vt.chunks[ci].offset + pos_offset
        posexpr = iszero(baseoff) ? :pos : :(pos + $baseoff)
        check = masked_load_check(vt.chunks[ci].iT, vt.masks[ci], cvars[ci], posexpr)
        rest == :(true) ? check : :($check && $rest)
    end
    (; destructure, checks)
end

"""
    gen_tail_verify(options, minoptlen, casefold, prefix) -> Expr

Generate verification for the tail bytes (beyond `minoptlen`) of variable-length
options. When all tails are the same length, uses word-sized comparisons via a
lookup table. Otherwise falls back to a `codeunit` loop over pre-chopped tail strings.
"""
function gen_tail_verify(options::Vector{String}, minoptlen::Int, casefold::Bool, prefix::Symbol)
    tails = [opt[minoptlen+1:end] for opt in options]
    taillens = ncodeunits.(tails)
    has_empty = any(iszero, taillens)
    distinct_taillens = unique(filter(!iszero, taillens))
    body = if length(distinct_taillens) == 1
        # Single tail length: word-sized comparison via gen_verify_exprs
        taillen = only(distinct_taillens)
        chunks = word_chunks(taillen)
        nonempty_tails = filter(!isempty, tails)
        masks = Tuple(
            build_chunk_mask(c.iT, c.width,
                _ -> true,
                j -> casefold && any(t -> codeunit(t, c.offset + j + 1) in UInt8('a'):UInt8('z'), nonempty_tails))
            for c in chunks)
        zerotup = Tuple(zero(c.iT) for c in chunks)
        verify_table = Tuple(
            if isempty(tails[oi])
                zerotup
            else
                Tuple(pack_bytes(tails[oi], c.offset, c.width, c.iT) & m
                      for (c, m) in zip(chunks, masks))
            end
            for oi in eachindex(options))
        vt = (; verify_table, masks, chunks)
        tve = gen_verify_exprs(vt, Symbol(prefix, "_tail"); pos_offset = minoptlen)
        ExprVarLine[tve.destructure..., :(found = $(tve.checks))]
    else
        # Multiple tail lengths: codeunit loop over tail bytes
        tailtable = Tuple(Tuple(codeunits(t)) for t in tails)
        taillenst = Tuple(taillens)
        loadbyte = if casefold
            :(@inbounds idbytes[pos + $minoptlen + j - 1] | 0x20)
        else
            :(@inbounds idbytes[pos + $minoptlen + j - 1])
        end
        ExprVarLine[:(tailbytes = $tailtable[i]),
                     :(for j in 1:$taillenst[i]
                           if $loadbyte != @inbounds tailbytes[j]
                               found = false
                               break
                           end
                       end)]
    end
    cond = if has_empty
        :(found && optlen > $minoptlen)
    else
        :found
    end
    :(if $cond
          $(body...)
      end)
end

function defid_choice!(exprs::IdExprs,
                       state::DefIdState, nctx::NodeCtx,
                       options::Vector{Any})
    all(o -> o isa String, options) || throw(ArgumentError("Expected all options to be strings for choice"))
    soptions = Vector{String}(options)
    allowempty = any(isempty, soptions)
    allowempty && filter!(!isempty, soptions)
    casefold = get(nctx, :casefold, state.casefold)
    target = get(nctx, :is, nothing)::Union{Nothing, String}
    fieldvar = get(nctx, :fieldvar, gensym("prefix"))
    option = get(nctx, :optional, nothing)
    choicebits = cardbits(length(soptions) + !isnothing(option))
    choiceint = if isnothing(target)
        cardtype(choicebits)
    else
        Bool
    end
    if !isnothing(target)
        push!(soptions, target)
    end
    if casefold
        all(isascii, soptions) || throw(ArgumentError("Expected all options to be ASCII strings for casefolding"))
    end
    matchoptions = casefold ? map(lowercase, soptions) : soptions
    ph = find_perfect_hash(matchoptions, casefold)
    foundaction = if isnothing(target)
        :($fieldvar = i % $choiceint)
    else
        :($fieldvar = one($fieldvar))
    end
    matcher = if !isnothing(ph)
        # Reorder options to match hash output order
        matchoptions = matchoptions[ph.perm]
        soptions = soptions[ph.perm]
        # Build common verification data
        optlens = Tuple(ncodeunits.(matchoptions))
        phoff = ph.pos - 1
        phposexpr = iszero(phoff) ? :pos : :(pos + $phoff)
        load = load_word(ph.iT, phposexpr)
        foldedload = if !iszero(ph.foldmask); :($load | $(ph.foldmask)) else load end
        hashval = ph.hashexpr(foldedload)
        minoptlen = minimum(ncodeunits, matchoptions)
        variable_len = minoptlen != maximum(ncodeunits, matchoptions)
        # For injective hashes, skip bytes already validated by the hash window
        hash_skip = if ph.injective
            find_best_hash_skip(minoptlen, phoff, sizeof(ph.iT))
        else
            nothing
        end
        vt = gen_verify_table(matchoptions, casefold; skip = hash_skip)
        # Try widening the verify table when it reduces chunk count
        wide_minlen = min(nextpow(2, minoptlen), sizeof(UInt) * cld(minoptlen, sizeof(UInt)))
        use_wide_vt = isnothing(hash_skip) && wide_minlen > minoptlen &&
            length(word_chunks(wide_minlen)) < length(vt.chunks)
        vt_wide = if use_wide_vt
            gen_verify_table(matchoptions, casefold; nbytes = wide_minlen)
        else
            nothing
        end
        tailcheck = if variable_len
            gen_tail_verify(matchoptions, minoptlen, casefold, fieldvar)
        else
            nothing
        end
        # Index resolution depends on hash kind
        resolve_i = if ph.kind === :direct
            ExprVarLine[:(i = $hashval),
                        :(found = 1 <= i <= $(length(matchoptions)))]
        else
            ExprVarLine[:(hi = $hashval),
                        :(i = if 1 <= hi <= $(ph.tablelen)
                              $(ph.table)[hi]
                          else
                              0
                          end),
                        :(found = !iszero(i))]
        end
        # Collect matcher expressions: resolve_i then a single guarded block
        parts = ExprVarLine[resolve_i...]
        verify_body = ExprVarLine[]
        if variable_len
            optlencheck = defid_lengthcheck(state, nctx, :optlen, minoptlen, maximum(ncodeunits, matchoptions))
            append!(verify_body,
                    ExprVarLine[:(optlen = $(optlens)[i]),
                                :(found = $optlencheck)])
        end
        if !isempty(vt.chunks)
            ve = gen_verify_exprs(vt, fieldvar)
            verify_stmts = if use_wide_vt
                ve_wide = gen_verify_exprs(vt_wide, fieldvar)
                wide_block = Expr(:block, ve_wide.destructure..., :(found = $(ve_wide.checks)))
                verify_block = Expr(:block, ve.destructure..., :(found = $(ve.checks)))
                ExprVarLine[Expr(:if, defid_static_lengthcheck(state, nctx, wide_minlen),
                                 wide_block, verify_block)]
            else
                ExprVarLine[ve.destructure..., :(found = $(ve.checks))]
            end
            # Wrap in found guard only when there are prior stages that may have cleared it
            if !isempty(verify_body)
                push!(verify_body, :(if found; $(verify_stmts...) end))
            else
                append!(verify_body, verify_stmts)
            end
        end
        if variable_len
            push!(verify_body, tailcheck)
        end
        push!(verify_body,
              :(if found
                    pos += $(if variable_len; :optlen else minoptlen end)
                    $foundaction
                end))
        push!(parts, :(if found; $(verify_body...) end))
        parts
    else # Linear scan fallback
        opts = casefold ? matchoptions : soptions
        optlens = Tuple(ncodeunits.(opts))
        optcus = Tuple(Tuple(codeunits(s)) for s in opts)
        loadbyte = casefold ? :(@inbounds idbytes[pos + j - 1] | 0x20) : :(@inbounds idbytes[pos + j - 1])
        ExprVarLine[:(for (i, (prefixlen, prefixbytes)) in enumerate(zip($optlens, $optcus))
              nbytes - pos + 1 >= prefixlen || continue
              found = true
              for j in 1:prefixlen
                  $loadbyte != prefixbytes[j] || continue
                  found = false
                  break
              end
              if found
                  $foundaction
                  pos += prefixlen
                  break
              end
          end)]
    end
    notfound = if isnothing(option)
        errsym = defid_errmsg(state, "Expected one of $(join(soptions, ", "))")
        :(return ($errsym, pos))
    else
        :($option = false)
    end
    minoptbytes = minimum(ncodeunits, soptions)
    lencheck = defid_lengthcheck(state, nctx, minoptbytes)
    checkedmatch = if allowempty
        :(if $lencheck
              $(matcher...)
              if $fieldvar == zero($choiceint)
                  $notfound
              end
          end)
    else
        :(if !$lencheck
              $notfound
          else
              $(matcher...)
              if $fieldvar == zero($choiceint)
                  $notfound
              end
          end)
    end
    if isnothing(target)
        nbits = (state.bits += choicebits)
        inc_print!(nctx, minimum(ncodeunits, soptions), maximum(ncodeunits, soptions))
        inc_parsed!(nctx, minimum(ncodeunits, soptions), maximum(ncodeunits, soptions))
        push!(exprs.parse,
              :($fieldvar = zero($choiceint)),
              checkedmatch,
              defid_orshift(state, choiceint, fieldvar, nbits))
        fextract = :($fieldvar = $(defid_fextract(state, nbits, choicebits)))
        if isnothing(option)
            push!(exprs.print, fextract)
        else
            push!(nctx[:oprint_detect], fextract, :($option = !iszero($fieldvar)))
        end
        # Build extract and impart for the segment
        symoptions = Tuple(Symbol.(soptions))
        seg_extract = if isnothing(option)
            ExprVarLine[fextract, :(@inbounds $(symoptions)[$fieldvar])]
        else
            ExprVarLine[fextract, :(if !iszero($fieldvar) @inbounds $(symoptions)[$fieldvar] end)]
        end
        # Constructor impart: validate Symbol -> 1-based index -> pack
        argvar = gensym("arg_choice")
        seg_impart = Any[]
        impart_core = Any[
            :($fieldvar = let idx = findfirst(==(Symbol($argvar)), $symoptions)
                  isnothing(idx) && throw(ArgumentError(
                      string("Invalid option :", $argvar, "; expected one of: ", $(join(soptions, ", ")))))
                  idx % $choiceint
              end),
            defid_orshift(state, choiceint, fieldvar, nbits)]
        if isnothing(option)
            append!(seg_impart, impart_core)
            seg_argtype = :Symbol
        else
            push!(seg_impart, wrap_optional_impart(argvar, impart_core))
            seg_argtype = :(Union{Symbol, Nothing})
        end
        push!(exprs.segments, (; nbits=choicebits, kind=:choice,
              label=seg_label(fieldvar),
              desc=join(soptions, " | "), argtype=seg_argtype, argvar,
              extract=seg_extract, impart=seg_impart, condition=option))
        push!(exprs.print,
              :(print(io, @inbounds $(Tuple(soptions))[$fieldvar])),
              :(__segment_printed = $(length(exprs.segments))))
    else
        if any(isempty, soptions)
            push!(exprs.parse, matcher)
        else
            push!(exprs.parse,
                  :($fieldvar = zero($choiceint)),
                  checkedmatch)
        end
        inc_print!(nctx, ncodeunits(target), ncodeunits(target))
        inc_parsed!(nctx, minimum(ncodeunits, soptions), maximum(ncodeunits, soptions))
        push!(exprs.segments, nullsegment(nbits=0, kind=:choice,
              label=seg_label(fieldvar),
              desc="Choice of literal string \"$(target)\" vs $(join(soptions, ", "))",
              condition=option))
        push!(exprs.print, :(print(io, $target)), :(__segment_printed = $(length(exprs.segments))))
    end
    nothing
end


# -----------------------------------------------------------
# Word-sized operations and string comparison
# -----------------------------------------------------------

"""Generate an expression to load a value of type `iT` from `idbytes` at `posexpr`."""
function load_word(iT::DataType, posexpr::Union{Symbol, Expr})
    if iT === UInt8
        :(@inbounds idbytes[$posexpr])
    else
        :(Base.unsafe_load(Ptr{$iT}(pointer(idbytes, $posexpr))))
    end
end

"""
    word_chunks(nbytes::Int) -> Vector{@NamedTuple{offset::Int, width::Int, iT::DataType}}

Decompose `nbytes` into a sequence of word-sized chunks (UInt64, UInt32, UInt16,
UInt8) covering the byte range. Each chunk has an `offset` from the start, a
byte `width`, and an integer type `iT`.
"""
function word_chunks(nbytes::Int)
    chunks = @NamedTuple{offset::Int, width::Int, iT::DataType}[]
    off, nb = 0, nbytes
    while nb > 0
        isize = min(length(INTS_UP_TO_WORD), 8 * sizeof(Int) - leading_zeros(nb))
        bw = 1 << (isize - 1)
        push!(chunks, (; offset = off, width = bw, iT = INTS_UP_TO_WORD[isize]))
        off += bw
        nb -= bw
    end
    chunks
end

"""Build a per-byte OR-mask for a word-sized chunk: `0xFF` (exact), `0xDF` (casefold alpha), or `0x00` (invalid)."""
function build_chunk_mask(iT::DataType, width::Int, is_valid, is_casefold_alpha)
    reduce(|, (begin
        byte_mask = if is_valid(j)
            is_casefold_alpha(j) ? iT(0xDF) : iT(0xFF)
        else
            zero(iT)
        end
        byte_mask << (8j)
    end for j in 0:width-1), init=zero(iT))
end

"""Build the AST for `load_word(iT, posexpr) & mask == expected`, eliding the mask when all-ones."""
function masked_load_check(iT::DataType, mask, expected, posexpr)
    load = load_word(iT, posexpr)
    mask == typemax(iT) ? :($load == $expected) : :($load & $mask == $expected)
end

"""
    find_best_hash_skip(optlen, hash_offset, hash_width)

Find the largest byte removal within the hash window `[hash_offset, hash_offset+hash_width)`
that minimises the total number of word-sized loads needed to verify the remaining bytes.
Returns `(gap_offset, gap_width)` or `nothing` if no removal reduces the load count.
"""
function find_best_hash_skip(optlen::Int, hash_offset::Int, hash_width::Int)
    nloads(n) = n ÷ sizeof(Int) + count_ones(n % sizeof(Int))
    baseline = nloads(optlen)
    baseline == 0 && return (hash_offset, hash_width)
    best_cost, best_start, best_width = baseline, 0, 0
    for start in hash_offset:hash_offset + hash_width - 1
        for w in 1:hash_offset + hash_width - start
            cost = nloads(start) + nloads(optlen - start - w)
            if cost < best_cost
                best_cost = cost
                best_start = start
                best_width = w
            end
        end
    end
    best_cost < baseline ? (best_start, best_width) : nothing
end

"""Pack bytes from `str` at positions `offset+1 : offset+width` into a value of type `iT`."""
function pack_bytes(str::String, offset::Int, width::Int, iT::DataType)
    v = zero(iT)
    for j in 0:width-1
        v |= iT(codeunit(str, offset + j + 1)) << (8j)
    end
    v
end

"""
    gen_static_stringcomp(str::String, casefold::Bool, nbytes::Int=ncodeunits(str)) -> Vector{Expr}

Generate word-sized match checks for `str` against `idbytes` at `pos`.
Each expression evaluates to `true` on match.

Uses `load & mask == expected` convention: per-byte mask is `0xFF` (exact),
`0xDF` (case-insensitive), or `0x00` (overflow/ignore).

When `nbytes > ncodeunits(str)`, chunks are computed for `nbytes` and overflow
bytes are masked to `0x00`. This enables widened loads (e.g. a single UInt64
for a 7-byte string) when subsequent pattern nodes guarantee that extra bytes
exist in the input.
"""
function gen_static_stringcomp(str::String, casefold::Bool, nbytes::Int = ncodeunits(str))
    strlen = ncodeunits(str)
    map(word_chunks(nbytes)) do (; offset, width, iT)
        valid = min(width, strlen - offset)
        mask = build_chunk_mask(iT, width,
            j -> j < valid,
            j -> casefold && codeunit(str, offset + j + 1) in UInt8('a'):UInt8('z'))
        value = pack_bytes(str, offset, valid, iT) & mask
        posexpr = iszero(offset) ? :pos : :(pos + $offset)
        masked_load_check(iT, mask, value, posexpr)
    end
end

"""
    gen_static_lchop(prefixes::Vector{String}; casefold::Bool) -> Expr

Generate an if/elseif chain that strips the first matching prefix by advancing
`pos`. Uses word-sized comparisons. Prefixes are grouped by length (longest
first), with same-length alternatives as nested if/elseif. Assumes `casefold`
prefixes are already lowercased. Expects `idbytes`, `pos`, `nbytes` in scope.
"""
function gen_static_lchop(prefixes::Vector{String}; casefold::Bool)
    groups = Dict{Int, Vector{String}}()
    for p in prefixes
        push!(get!(Vector{String}, groups, ncodeunits(p)), p)
    end
    lengths = sort!(collect(keys(groups)), rev=true)
    matchcond(str) = let checks = gen_static_stringcomp(str, casefold)
        foldl((a, b) -> :($a && $b), checks)
    end
    branches = map(lengths) do nb
        grp = groups[nb]
        lencheck = :(nbytes - pos + 1 >= $nb)
        if length(grp) == 1
            :(if $lencheck && $(matchcond(only(grp))); pos += $nb end)
        else
            inner = :(if $(matchcond(last(grp))); pos += $nb end)
            for i in length(grp)-1:-1:1
                alt = matchcond(grp[i])
                inner = Expr(:elseif, alt, :(pos += $nb), inner)
            end
            :(if $lencheck; $inner end)
        end
    end
    result = branches[end]
    for i in length(branches)-1:-1:1
        br = branches[i]
        result = Expr(:if, br.args[1], br.args[2], result)
    end
    result
end

# -----------------------------------------------------------
# Pattern handlers: literal, digits, letters/alphnum
# -----------------------------------------------------------

function defid_literal!(exprs::IdExprs,
                        state::DefIdState, nctx::NodeCtx,
                        lit::String)
    option = get(nctx, :optional, nothing)
    notfound = if isnothing(option)
        errsym = defid_errmsg(state, "Expected literal '$(lit)'")
        :(return ($errsym, pos))
    else
        :($option = false)
    end
    casefold = get(nctx, :casefold, state.casefold) === true
    if casefold
        all(isascii, lit) || throw(ArgumentError("Expected ASCII string for literal with casefolding"))
    end
    litref = casefold ? lowercase(lit) : lit
    litlen = ncodeunits(litref)
    # When widening to fewer loads is possible, emit both paths gated by
    # __static_length_check; fold_static_branches! picks the winner.
    wide_n = min(nextpow(2, litlen), sizeof(UInt) * cld(litlen, sizeof(UInt)))
    use_wide = wide_n > litlen && length(word_chunks(wide_n)) < length(word_chunks(litlen))
    mismatch = if use_wide
        wide_checks = gen_static_stringcomp(litref, casefold, wide_n)
        wide_mm = :(!($(foldl((a, b) -> :($a && $b), wide_checks))))
        narrow_checks = gen_static_stringcomp(litref, casefold)
        narrow_mm = :(!($(foldl((a, b) -> :($a && $b), narrow_checks))))
        Expr(:if, defid_static_lengthcheck(state, nctx, wide_n), wide_mm, narrow_mm)
    else
        checks = gen_static_stringcomp(litref, casefold)
        :(!($(foldl((a, b) -> :($a && $b), checks))))
    end
    lencheck = defid_lengthcheck(state, nctx, litlen)
    if isnothing(option)
        push!(exprs.parse,
              :(if !$lencheck
                    $notfound
                elseif $mismatch
                    $notfound
                end),
              :(pos += $litlen))
    else
        litvar = gensym("literal")
        append!(exprs.parse,
                (quote
                     $litvar = true
                     if !$lencheck
                         $litvar = false
                         $notfound
                     elseif $mismatch
                         $litvar = false
                         $notfound
                     end
                     if $litvar
                         pos += $litlen
                     end
                 end).args)
    end
    push!(exprs.segments, nullsegment(nbits=0, kind=:literal, label=:literal,
          desc=sprint(show, lit), condition=option))
    push!(exprs.print, :(print(io, $lit)), :(__segment_printed = $(length(exprs.segments))))
    inc_print!(nctx, litlen, litlen)
    inc_parsed!(nctx, litlen, litlen)
    nothing
end

# -----------------------------------------------------------
# SWAR digit parsing
# -----------------------------------------------------------

"""
    swarparse_consts(::Type{T}, base::Int, ndigits::Int)

Compute constants for SWAR (SIMD Within A Register) parallel ASCII-to-integer
conversion of `ndigits` digit bytes high-aligned in unsigned type `T`.

The caller should load `sizeof(T)` bytes ending at the last digit, so that the
`ndigits` digit bytes occupy the high byte positions and the low
`sizeof(T) - ndigits` bytes are garbage. The `ascii_mask` simultaneously strips
ASCII encoding and zeros the garbage bytes.

Returns `(; ascii_mask, alpha_mask, steps)`. Each step has `(; multiplier, shift)`
and optionally `mask` (omitted on the final step). The multiply-shift reduction
combines adjacent digit groups in O(log n) steps:

    # intermediate step:  word = ((word * multiplier) >> shift) & mask
    # final step:         word = (word * multiplier) >> shift

The multiplier `Cₖ = base^g * 2^(g*8) + 1` encodes both the scale factor and the
group combination into a single multiply: for each pair of `g`-byte groups
`[even, odd]` in the word, `(even + odd * 2^(g*8)) * Cₖ` places `even * base^g + odd`
at bit offset `g*8` within each `2g`-byte lane. The right shift then extracts it.

For base > 10, an alpha correction converts hex letter bytes to values 10-15
between the ASCII mask and the first reduction step.
"""
function swarparse_consts(::Type{T}, base::Int, nd::Int) where {T <: Unsigned}
    nbytes = sizeof(T)
    1 <= nd <= nbytes || throw(ArgumentError(
        "ndigits=$nd must be between 1 and $nbytes for $T"))
    2 <= base <= 16 || throw(ArgumentError(
        "base=$base must be between 2 and 16"))
    hex = base > 10
    padding = nbytes - nd
    # Digit bytes sit in the high positions (byte indices padding:nbytes-1).
    # ASCII mask: 0x0F (or 0x4F for hex) per digit byte, 0x00 per garbage byte.
    byteval = hex ? T(0x4F) : T(0x0F)
    ascii_mask = reduce(|, (byteval << (8 * (padding + i)) for i in 0:nd-1); init=zero(T))
    alpha_mask = if hex
        reduce(|, (T(0x40) << (8 * (padding + i)) for i in 0:nd-1); init=zero(T))
    else
        zero(T)
    end
    # Reduction steps: combine adjacent digit groups in a binary tree using
    # multiply-shift. At each level, groups of `g` bytes are paired. The multiplier
    # Cₖ = base^g * 2^(g*8) + 1 computes `even * base^g + odd` for each pair via a
    # single multiply, and the right shift extracts the combined value. An AND mask
    # between steps cleans up inter-lane overflow; the final step omits it since the
    # result is extracted by truncation or a single shift.
    nsteps = nd <= 1 ? 0 : 8 * sizeof(nd) - leading_zeros(nd - 1)
    steps = map(1:nsteps) do step
        g = 1 << (step - 1)      # current group size in bytes
        shift = g * 8
        scale = T(base) ^ g
        multiplier = scale * (one(T) << shift) + one(T)
        if step < nsteps
            # Cleanup mask: g bytes of 0xFF alternating with g bytes of 0x00,
            # shifted up by g bytes (the result sits in the high half of each pair)
            group_mask = (one(T) << shift) - one(T)
            mask = reduce(|, (group_mask << (2g * 8 * i) for i in 0:(nbytes ÷ (2g))); init=zero(T))
            (; multiplier, shift, mask)
        else
            (; multiplier, shift)
        end
    end
    (; ascii_mask, alpha_mask, steps = Tuple(steps))
end

"""
    swar_digitconsts(::Type{T}, base::Int)

Compute constants for SWAR digit detection in type `T` for the given `base`.
Returns a named tuple used by `gen_swar_digitcheck` and `gen_swar_digitcount`.

For base ≤ 10, uses the nibble-check approach:
    diff = (val & (val + addmask) & 0xF0F0...) ⊻ 0x3030...
where `diff` is zero per-byte for valid digits.

For base 11-16 (hex), uses addition-based range checks after casefolding:
    nondigit = (is_decimal | is_alpha) ⊻ 0x8080...
where `nondigit` has bit 7 set per-byte for non-digits. Cross-byte carry
from invalid bytes cannot produce false positives because we scan/check
from the lowest byte, so corruption is always beyond the first failure.
"""
function swar_digitconsts(::Type{T}, base::Int) where {T <: Unsigned}
    rep = T(0x01) * typemax(T) ÷ typemax(UInt8)  # 0x0101... repeating byte
    if base <= 10
        addmask = T(0x10 - base) * rep
        nibmask = T(0xF0) * rep
        expected = T(0x30) * rep
        (; kind = :nibble, addmask, nibmask, expected)
    else
        foldmask = T(0x20) * rep
        hibits = T(0x80) * rep
        # Decimal range 0x30-0x39
        dec_lo = T(0x80 - 0x30) * rep   # 0x50
        dec_hi = T(0x80 - 0x3A) * rep   # 0x46
        # Alpha range 0x61-(0x60+base-10) (after casefold), i.e. a-f for base 16
        alp_end = 0x61 + base - 10  # one past last valid alpha digit
        alp_lo = T(0x80 - 0x61) * rep
        alp_hi = T(0x80 - alp_end) * rep
        (; kind = :hex, foldmask, hibits, dec_lo, dec_hi, alp_lo, alp_hi)
    end
end

"""
    gen_swar_nondigits(::Type{T}, var::Symbol, result::Symbol, base::Int) -> Expr

Generate an expression that computes a non-digit indicator from `var::T` into
`result::T`. For base ≤ 10, each byte of `result` is zero for valid digits and
nonzero otherwise. For base > 10, bit 7 of each byte in `result` is set for
non-digits, clear for digits.
"""
function gen_swar_nondigits(::Type{T}, var::Symbol, result::Symbol, base::Int) where {T <: Unsigned}
    c = swar_digitconsts(T, base)
    if c.kind === :nibble
        :($(result) = ($var & ($var + $(c.addmask)) & $(c.nibmask)) ⊻ $(c.expected))
    else
        dec_ok = gensym("dec")
        alp_ok = gensym("alp")
        folded = gensym("folded")
        # Decimal check uses the original value (0-9 are unaffected by casefold,
        # and casefolding would turn control chars like 0x10 into 0x30).
        # Alpha check uses the casefolded value (A-F → a-f).
        quote
            $folded = $var | $(c.foldmask)
            $dec_ok = ($var + $(c.dec_lo)) & ~($var + $(c.dec_hi)) & $(c.hibits)
            $alp_ok = ($folded + $(c.alp_lo)) & ~($folded + $(c.alp_hi)) & $(c.hibits)
            $result = ($dec_ok | $alp_ok) ⊻ $(c.hibits)
        end
    end
end

"""
    gen_swar_digitcheck(::Type{T}, var::Symbol, base::Int, nd::Int, on_fail) -> Vector{ExprVarLine}

Generate expressions that check all `nd` high-aligned digit bytes in `var::T`
are valid base-`base` digits. If the check fails, evaluates `on_fail`.
"""
function gen_swar_digitcheck(::Type{T}, var::Symbol, base::Int, nd::Int, on_fail) where {T <: Unsigned}
    nondig = gensym("nondig")
    check_expr = gen_swar_nondigits(T, var, nondig, base)
    padding = sizeof(T) - nd
    checkmask = if base <= 10
        # Nibble check: diff is zero for digit bytes, nonzero otherwise.
        # Mask to only check the nd high-aligned digit bytes.
        padding == 0 ? nothing : typemax(T) - ((one(T) << (8 * padding)) - one(T))
    else
        # Hex check: bit 7 set per non-digit byte.
        # Mask high bits of the nd digit bytes only.
        rep = T(0x80) * (T(0x01) * typemax(T) ÷ typemax(UInt8))
        padding == 0 ? nothing : rep & (typemax(T) - ((one(T) << (8 * padding)) - one(T)))
    end
    # When nd == sizeof(T), the mask covers all bytes — omit the redundant AND
    failcond = isnothing(checkmask) ? :(!iszero($nondig)) : :(!iszero($nondig & $checkmask))
    ExprVarLine[check_expr, :(if $failcond; $on_fail end)]
end

"""
    gen_swar_digitcount(::Type{T}, var::Symbol, countvar::Symbol, base::Int, maxdigits::Int) -> Vector{ExprVarLine}

Generate expressions that count consecutive base-`base` digit bytes from the
LSB of `var::T`, storing the count in `countvar`. Counts at most `maxdigits`.
Digits are in the low byte positions (not high-aligned).
"""
function gen_swar_digitcount(::Type{T}, var::Symbol, countvar::Symbol, base::Int, maxdigits::Int) where {T <: Unsigned}
    nondig = gensym("nondig")
    check_expr = gen_swar_nondigits(T, var, nondig, base)
    # Set sentinel bits beyond maxdigits to ensure we stop counting
    sentinel_expr = if maxdigits < sizeof(T)
        sentinel = ~((one(T) << (8 * maxdigits)) - one(T))
        if base <= 10
            # For nibble check, any nonzero byte stops the count.
            # Set all bits beyond maxdigits.
            :($nondig |= $sentinel)
        else
            # For hex check, only bit 7 matters. Set bit 7 beyond maxdigits.
            hibits = T(0x80) * (T(0x01) * typemax(T) ÷ typemax(UInt8))
            :($nondig |= $(sentinel & hibits))
        end
    else
        nothing
    end
    count_assign = if base <= 10
        # Nibble check: each non-digit byte is nonzero, digit byte is zero.
        # haszero: sets bit 7 for each ZERO byte (i.e. digit byte), invert to find first non-digit.
        rep01 = T(0x01) * typemax(T) ÷ typemax(UInt8)
        rep80 = T(0x80) * rep01
        :($countvar = trailing_zeros(
            (($nondig - $rep01) & ~$nondig & $rep80) ⊻ $rep80) >> 3)
    else
        # Hex check: bit 7 set for non-digits. First set bit 7 = first non-digit.
        :($countvar = trailing_zeros($nondig) >> 3)
    end
    result = ExprVarLine[check_expr]
    isnothing(sentinel_expr) || push!(result, sentinel_expr)
    push!(result, count_assign)
    result
end

"""
    gen_swarparse(::Type{T}, var::Symbol, base::Int, nd::Int) -> Vector{ExprVarLine}

Generate expressions that SWAR-parse `nd` fixed-width ASCII digit bytes
(base ≤ 16) from `var::T`, storing the result back in `var`.

The caller is responsible for loading `sizeof(T)` bytes ending at the last
digit into `var` before this expression runs. The `ascii_mask` zeros any
garbage bytes in the low positions.

Uses the multiply-shift reduction: each step applies `var = ((var * Cₖ) >> shift) & mask`,
where `Cₖ = base^g * 2^(g*8) + 1`. The final step omits the mask (result extracted
by the shift alone). This is 2-3 ops per step vs the 5-op mask-multiply-shift-add-mask
of the textbook SWAR approach.
"""
function gen_swarparse(::Type{T}, var::Symbol, base::Int, nd::Int) where {T <: Unsigned}
    c = swarparse_consts(T, base, nd)
    exprs = ExprVarLine[:($var &= $(c.ascii_mask))]
    if !iszero(c.alpha_mask)
        alpha = gensym("alpha")
        push!(exprs,
              :($alpha = $var & $(c.alpha_mask)),
              :($var = ($alpha >> 6) * $(T(9)) + ($var ⊻ $alpha)))
    end
    for s in c.steps
        if hasproperty(s, :mask)
            push!(exprs,
                  :($var = (($var * $(s.multiplier)) >> $(s.shift)) & $(s.mask)))
        else
            push!(exprs,
                  :($var = ($var * $(s.multiplier)) >> $(s.shift)))
        end
    end
    exprs
end

"""
    gen_swar_load(::Type{T}, var::Symbol, nd::Int; backward::Bool) -> Expr

Generate an expression that loads `nd` digit bytes from `idbytes` at `pos` into
`var::T`, high-aligned (digit bytes in the most significant positions, low bytes
zeroed).

When `backward=true` and `nd < sizeof(T)`, loads `sizeof(T)` bytes ending at the
last digit byte (`pos + nd - 1`), relying on preceding parsed bytes as padding.
This is a single load — the cheapest path.

When `backward=false` and `nd == sizeof(T)`, loads `sizeof(T)` bytes starting at `pos`
(no padding needed, digits already fill the entire register).

When `backward=false` and `nd < sizeof(T)`, performs an **exact load**: decomposes `nd`
into power-of-2 sub-loads (e.g., 3 = 2+1, 5 = 4+1, 7 = 4+2+1), each shifted to its
high-aligned position and ORed together. This reads exactly `nd` bytes, avoiding any
out-of-bounds access and eliminating the need for forward-safety length checks.

Uses `htol` for endianness portability on multi-byte loads.
"""
function gen_swar_load(::Type{T}, var::Symbol, nd::Int; backward::Bool) where {T}
    if nd == sizeof(T)
        # Full-width load — no padding, no alignment needed
        if T === UInt8
            return :($var = @inbounds idbytes[pos])
        end
        return :($var = htol(Base.unsafe_load(Ptr{$T}(pointer(idbytes, pos)))))
    end
    # nd < sizeof(T): need high-alignment
    if backward
        # Single load reading sizeof(T) bytes ending at the last digit byte
        padding = sizeof(T) - nd
        return :($var = htol(Base.unsafe_load(Ptr{$T}(pointer(idbytes, pos - $padding)))))
    end
    # Exact load: decompose nd into power-of-2 chunks, then shift each to its
    # correct byte position and OR together. On little-endian, a chunk loaded at
    # string offset `off` should occupy byte positions `padding+off` through
    # `padding+off+chunk-1` in the register (byte 0 = LSB), so the bit shift
    # is `8 * (padding + off)`.
    padding = sizeof(T) - nd
    chunks = Tuple{Int,Int}[]  # (chunk_size_bytes, string_offset_from_pos)
    remaining = nd
    offset = 0
    while remaining > 0
        chunk = 1 << (8 * sizeof(remaining) - 1 - leading_zeros(remaining))
        push!(chunks, (chunk, offset))
        offset += chunk
        remaining -= chunk
    end
    parts = Expr[]
    for (chunk, off) in chunks
        bit_shift = 8 * (padding + off)
        cT = swar_type(chunk)
        load = if cT === UInt8
            :($T(@inbounds idbytes[pos + $off]))
        else
            :(htol(Base.unsafe_load(Ptr{$cT}(pointer(idbytes, pos + $off)))) % $T)
        end
        push!(parts, bit_shift == 0 ? load : :($load << $bit_shift))
    end
    rhs = parts[1]
    for i in 2:length(parts)
        rhs = :($rhs | $(parts[i]))
    end
    :($var = $rhs)
end

"""
    gen_swar_varload(::Type{sT}, var, countvar, availvar, base, maxdigits) -> Vector{ExprVarLine}

Generate a cascading variable-width load for SWAR digit parsing. Decomposes
`maxdigits` into descending power-of-2 chunks and generates a flat sequence of
conditional load-check-accumulate blocks.

After execution, `var::sT` holds the digit bytes low-aligned (first digit at
LSB) and `countvar` holds the number of consecutive digit bytes found (0 to
maxdigits). The caller must left-shift to high-align before running `gen_swarparse`.

The generated code references `idbytes`, `pos` (from the enclosing parse
context), and `availvar` (max bytes available, set by the caller via
`defid_lengthbound`).

Each chunk reads exactly `chunk` bytes, so no oversized loads occur and no
`__length_check` for `sizeof(sT)` is needed — eliminating the `parseint` fallback.
"""
function gen_swar_varload(::Type{sT}, var::Symbol, countvar::Symbol,
                          availvar::Symbol, base::Int, maxdigits::Int) where {sT <: Unsigned}
    @assert sizeof(sT) >= maxdigits "gen_swar_varload requires sizeof(sT) >= maxdigits"
    # Enumerate all power-of-2 chunk sizes from prevpow2(maxdigits) down to 1.
    # Each chunk is tried at the current offset: if all its bytes are digits it
    # advances the count, otherwise we fall through to the next smaller chunk.
    # This covers all possible digit counts 0..maxdigits.
    chunks = Int[]
    c = 1 << (8 * sizeof(maxdigits) - 1 - leading_zeros(maxdigits))
    while c >= 1
        push!(chunks, c)
        c >>= 1
    end
    gen_varload_chunks(sT, var, countvar, availvar, base, maxdigits, chunks)
end

"""Generate the cascading load-check-accumulate blocks for the given chunk sequence."""
function gen_varload_chunks(::Type{sT}, var::Symbol, countvar::Symbol,
                            availvar::Symbol, base::Int, maxdigits::Int,
                            chunks::AbstractVector{Int}) where {sT <: Unsigned}
    isempty(chunks) && return ExprVarLine[]
    chunk = first(chunks)
    rest = @view chunks[2:end]
    cT = swar_type(chunk)
    chunk_var = gensym("chunk$(chunk)")
    nondig_var = gensym("nondig$(chunk)")
    load_expr = if cT === UInt8
        :($chunk_var = @inbounds idbytes[pos + $countvar])
    else
        :($chunk_var = htol(Base.unsafe_load(Ptr{$cT}(pointer(idbytes, pos + $countvar)))))
    end
    nondig_raw = gen_swar_nondigits(cT, chunk_var, nondig_var, base)
    nondig_stmts = if Meta.isexpr(nondig_raw, :block)
        filter(e -> !(e isa LineNumberNode), nondig_raw.args)
    else
        ExprVarLine[nondig_raw]
    end
    accum = :($var |= ($chunk_var % $sT) << ($countvar << 3))
    advance = :($countvar += $chunk)
    # When this chunk fills the register, a successful load-and-check accounts
    # for all maxdigits bytes. Remaining smaller chunks only run on failure,
    # nested under else branches to skip redundant checks.
    rest_exprs = gen_varload_chunks(sT, var, countvar, availvar, base, maxdigits, rest)
    if chunk == sizeof(sT)
        # Full-register chunk: success means done, smaller chunks under else.
        # Both the bounds failure and the digit-check failure fall through to
        # the same smaller-chunk cascade since countvar hasn't advanced.
        ExprVarLine[:(if $countvar + $chunk <= $availvar
                          $load_expr
                          $(nondig_stmts...)
                          if iszero($nondig_var)
                              $accum
                              $advance
                          else
                              $(rest_exprs...)
                          end
                      else
                          $(rest_exprs...)
                      end)]
    else
        # Sub-register chunk: independent check, then continue to next chunk
        ExprVarLine[:(if $countvar + $chunk <= $availvar
                          $load_expr
                          $(nondig_stmts...)
                          if iszero($nondig_var)
                              $accum
                              $advance
                          end
                      end),
                    rest_exprs...]
    end
end

"""
    compute_digit_vocab(fieldvar, option, dspec, ctx) -> NamedTuple

Compute the shared vocabulary needed by all digit-parse strategies and wrapping
helpers. Bundles symbols, encoding expressions, range checks, and error messages.
"""
function compute_digit_vocab(fieldvar::Symbol, option,
                             dspec::NamedTuple,
                             state::DefIdState)
    (; base, mindigits, maxdigits, min, max, pad, dI, dT) = dspec
    fixedwidth = mindigits == maxdigits
    fnum = Symbol("$(fieldvar)_num")
    # numexpr: transform raw fnum into the stored representation
    directval = cardbits(max - min + 1 + !isnothing(option)) ==
                cardbits(max) && (min > 0 || isnothing(option))
    numexpr = if directval
        if dI != dT; :($fnum % $dT) else fnum end
    elseif iszero(min) && !isnothing(option)
        :($fnum + $(one(dT)))
    elseif min - !isnothing(option) > 0
        :(($fnum - $(dT(min - !isnothing(option)))) % $dT)
    else
        if dI != dT; :($fnum % $dT) else fnum end
    end
    directvar = numexpr === fnum
    parsevar = ifelse(directvar, fnum, fieldvar)
    rangecheck = if min == 0 && max == base^maxdigits - 1
        :()
    else
        maxerr = defid_errmsg(state, "Expected at most a value of $(string(max; base, pad))")
        minerr = defid_errmsg(state, "Expected at least a value of $(string(min; base, pad))")
        maxcheck = :($fnum <= $max || return ($maxerr, pos))
        mincheck = :($fnum >= $min || return ($minerr, pos))
        if min == 0; maxcheck
        elseif max == base^maxdigits - 1; mincheck
        else :($mincheck; $maxcheck) end
    end
    errmsg = defid_errmsg(state, if fixedwidth && maxdigits > 1
        "exactly $maxdigits digits in base $base"
    elseif mindigits > 1
        "$mindigits to $maxdigits digits in base $base"
    else
        "up to $maxdigits digits in base $base"
    end)
    fail_expr = :(return ($errmsg, pos))
    (; fnum, fieldvar, parsevar, directvar, numexpr, rangecheck,
       fail_expr, option, dT, errmsg)
end

"""
    digit_required(vocab, fnum_setters...) -> Vector{ExprVarLine}

Wrap fnum-producing expressions with range checking and encoding for required fields.
"""
function digit_required(vocab, fnum_setters...)
    (; rangecheck, directvar, fieldvar, numexpr) = vocab
    exprs = ExprVarLine[]
    for s in fnum_setters
        s isa Vector ? append!(exprs, s) : push!(exprs, s)
    end
    rangecheck != :() && push!(exprs, rangecheck)
    directvar || push!(exprs, :($fieldvar = $numexpr))
    exprs
end

"""
    digit_optional(vocab, valid_cond, fnum_setters) -> Vector{ExprVarLine}

Wrap fnum-producing expressions with range checking and encoding for optional fields.
Returns a single-element vector containing the if/else parsevar assignment.
"""
function digit_optional(vocab, valid_cond, fnum_setters)
    (; parsevar, rangecheck, numexpr, option, dT) = vocab
    ExprVarLine[:($parsevar = if $valid_cond
                      $(fnum_setters...)
                      $rangecheck; $numexpr
                  else
                      $option = false; zero($dT)
                  end)]
end

"""
    digit_absent(vocab) -> Vector{ExprVarLine}

Emit the `option = false; parsevar = zero(dT)` pair for an absent optional field.
"""
function digit_absent(vocab)
    (; option, parsevar, dT) = vocab
    ExprVarLine[:($option = false), :($parsevar = zero($dT))]
end

"""
    gen_swar_chunk(cT, var, nd, base, on_fail) -> (check, parse)

Generate digit-checking and value-parsing expressions for a single SWAR chunk.
Handles 1-digit decimal, 1-digit hex, and multi-digit SWAR cases.
"""
function gen_swar_chunk(cT, var::Symbol, nd::Int, base::Int, on_fail)
    check = if nd == 1 && base <= 10
        ExprVarLine[:($var = ($var - $(UInt8('0'))) % $cT),
             :(if $var >= $(cT(base)); $on_fail end)]
    elseif nd == 1  # hex single byte
        folded = gensym("folded")
        ExprVarLine[:($folded = ($var | 0x20) % $cT),
             :($var = $folded - $(cT(0x30))),
             :(if $var > $(cT(9))
                   $var = $folded - $(cT(0x61 - 10))
                   if $var < $(cT(10)) || $var >= $(cT(base))
                       $on_fail
                   end
               end)]
    else
        gen_swar_digitcheck(cT, var, base, nd, on_fail)
    end
    parse = nd == 1 ? ExprVarLine[] : gen_swarparse(cT, var, base, nd)
    (check, parse)
end

"""
    gen_digit_parseint(vocab, dspec, ctx) -> Vector{ExprVarLine}

Scalar `parseint` fallback for digit fields where SWAR isn't applicable.
"""
function gen_digit_parseint(vocab, dspec::NamedTuple,
                            state::DefIdState, nctx::NodeCtx)
    (; fnum, fail_expr, option) = vocab
    (; base, mindigits, maxdigits) = dspec
    fixedwidth = mindigits == maxdigits
    bitsconsumed = Symbol("$(vocab.fieldvar)_bitsconsumed")
    scanlimit = defid_lengthbound(state, nctx, maxdigits)
    matchcond = if fixedwidth
        :($bitsconsumed == $maxdigits)
    elseif mindigits > 1
        :($bitsconsumed >= $mindigits)
    else
        :(!iszero($bitsconsumed))
    end
    fnum_set = :(($bitsconsumed, $fnum) = parseint($(dspec.dI), idbytes, pos, $base, $scanlimit))
    if isnothing(option)
        digit_required(vocab, fnum_set, :($matchcond || $fail_expr))
    else
        # parseint must run before matchcond is checked
        ExprVarLine[fnum_set, digit_optional(vocab, matchcond, ExprVarLine[])...]
    end
end

"""
    gen_digit_fixed_guarded(vocab, ctx, nd, load_exprs, check_fn, parse_and_encode)

Shared skeleton for fixed-width digit strategies. Handles the length guard and
required/optional branching that every fixed-width path needs.

`check_fn(on_fail) -> Vector{ExprVarLine}` produces check expressions that
evaluate `on_fail` when the digit check fails.
"""
function gen_digit_fixed_guarded(vocab, state::DefIdState, nctx::NodeCtx,
                                 nd::Int,
                                 load_exprs::Vector{ExprVarLine},
                                 check_fn,
                                 parse_and_encode::Vector{ExprVarLine})
    (; fail_expr, option, errmsg) = vocab
    b = nctx[:current_branch]
    if isnothing(option)
        nd_guard = :(if !($(Expr(:call, :__length_check, b.id, b.parsed_max, nd, nd, nd)))
                         return ($errmsg, pos)
                     end)
        ExprVarLine[nd_guard, load_exprs..., check_fn(fail_expr)...,
                    parse_and_encode..., digit_required(vocab)...]
    else
        valid = gensym("valid")
        opt_check = Expr(:call, :__length_check, b.id, b.parsed_max, nd, nd, nd)
        check = check_fn(:($valid = false))
        swar_block = ExprVarLine[:($valid = true), check...,
                                 digit_optional(vocab, :($valid), parse_and_encode)...]
        ExprVarLine[:(if $opt_check
                          $(load_exprs...)
                          $(swar_block...)
                      else
                          $(digit_absent(vocab)...)
                      end)]
    end
end

"""
    gen_digit_swar_fixed(vocab, dspec, ctx) -> Vector{ExprVarLine}

Fixed-width single-chunk SWAR for 1-8 digit fields. Uses `gen_swar_chunk` for
the digit check (which has a sub+cmp fast path for nd==1) and delegates the
required/optional wrapping to `gen_digit_fixed_guarded`.

Load strategy (best to worst):
1. Backward — preceding bytes provide padding for a single sizeof(sT) load
2. Forward overread — trailing content guarantees sizeof(sT) bytes at pos;
   single full-width load + left-shift discards overflow (via `__static_length_check`)
3. Exact — decompose maxdigits into power-of-2 sub-loads, shift and OR
"""
function gen_digit_swar_fixed(vocab, dspec::NamedTuple,
                              state::DefIdState, nctx::NodeCtx)
    (; fnum) = vocab
    (; base, maxdigits, dI) = dspec
    sT = swar_type(maxdigits)
    swar_var = Symbol("$(vocab.fieldvar)_swar")
    # Backward load when enough preceding bytes provide padding
    b = nctx[:current_branch]
    backward = b.parsed_min >= sizeof(sT) - maxdigits
    # Forward overread: when maxdigits < sizeof(sT) and backward isn't available,
    # a full-width forward load + left-shift is cheaper than exact sub-loads.
    # Gated by __static_length_check so it only activates when trailing content
    # guarantees sizeof(sT) bytes exist from pos onward.
    use_forward_overread = !backward && maxdigits < sizeof(sT)
    load = if use_forward_overread
        shift = 8 * (sizeof(sT) - maxdigits)
        wide_load = :($swar_var = htol(Base.unsafe_load(Ptr{$sT}(pointer(idbytes, pos)))) << $shift)
        narrow_load = gen_swar_load(sT, swar_var, maxdigits; backward=false)
        Expr(:if, defid_static_lengthcheck(state, nctx, sizeof(sT)), wide_load, narrow_load)
    else
        gen_swar_load(sT, swar_var, maxdigits; backward)
    end
    check_fn = on_fail -> gen_swar_chunk(sT, swar_var, maxdigits, base, on_fail)[1]
    # gen_swarparse is a no-op for nd==1 (just `&= 0x0F`), skip it
    parse_expr = maxdigits == 1 ? ExprVarLine[] : gen_swarparse(sT, swar_var, base, maxdigits)
    swar_cast = sT == dI ? :($fnum = $swar_var) : :($fnum = $swar_var % $dI)
    gen_digit_fixed_guarded(vocab, state, nctx, maxdigits,
                            ExprVarLine[load], check_fn,
                            ExprVarLine[parse_expr..., swar_cast])
end

"""
    gen_digit_twochunk(vocab, dspec, ctx) -> Vector{ExprVarLine}

Two-chunk SWAR for fixed-width fields with 9-16 digits: split into an 8-digit
upper chunk and a (maxdigits-8)-digit lower chunk.
"""
function gen_digit_twochunk(vocab, dspec::NamedTuple,
                            state::DefIdState, nctx::NodeCtx)
    (; fnum, fieldvar) = vocab
    (; base, maxdigits, dI) = dspec
    upper_nd = sizeof(UInt)  # 8
    lower_nd = maxdigits - upper_nd
    upper_sT = UInt64
    lower_sT = swar_type(lower_nd)
    # Upper chunk: full UInt64 at pos
    upper_var = Symbol("$(fieldvar)_upper")
    upper_load = gen_swar_load(upper_sT, upper_var, upper_nd; backward=false)
    # Lower chunk: at pos+upper_nd (upper bytes provide backward padding)
    lower_var = Symbol("$(fieldvar)_lower")
    lower_backward = sizeof(lower_sT) > lower_nd
    lower_pos_advance = :(pos += $upper_nd)
    lower_pos_restore = :(pos -= $upper_nd)
    lower_load = gen_swar_load(lower_sT, lower_var, lower_nd; backward=lower_backward)
    load_exprs = ExprVarLine[upper_load, lower_pos_advance, lower_load, lower_pos_restore]
    # Check both chunks; parse and combine: fnum = upper * base^lower_nd + lower
    check_fn = on_fail -> begin
        uc, _ = gen_swar_chunk(upper_sT, upper_var, upper_nd, base, on_fail)
        lc, _ = gen_swar_chunk(lower_sT, lower_var, lower_nd, base, on_fail)
        ExprVarLine[uc..., lc...]
    end
    _, upper_parse = gen_swar_chunk(upper_sT, upper_var, upper_nd, base, nothing)
    _, lower_parse = gen_swar_chunk(lower_sT, lower_var, lower_nd, base, nothing)
    scale = UInt64(base) ^ lower_nd
    combine = :($fnum = ($(upper_var) * $scale + $(lower_var) % UInt64) % $dI)
    gen_digit_fixed_guarded(vocab, state, nctx, maxdigits, load_exprs, check_fn,
                            ExprVarLine[upper_parse..., lower_parse..., combine])
end

"""
    gen_digit_swar_variable(vocab, dspec, ctx) -> Vector{ExprVarLine}

Variable-width SWAR for 2-8 digit fields.

Load strategy (best to worst):
1. Backward — preceding bytes provide padding for a single sizeof(sT) backward load
   with runtime-variable position. Digit counting from LSB after right-shift low-alignment.
2. Forward overread — trailing content guarantees sizeof(sT) bytes at pos; single
   full-width forward load, digit counting from LSB (digits naturally at LSB on LE),
   left-shift to high-align. Via `__static_length_check`.
3. Cascading exact-loads — decompose maxdigits into power-of-2 sub-loads (`gen_swar_varload`)

When `avail` or shifts resolve to compile-time constants, LLVM eliminates
the runtime-dependent operations entirely.
"""
function gen_digit_swar_variable(vocab, dspec::NamedTuple,
                                 state::DefIdState, nctx::NodeCtx)
    (; fnum, fail_expr, option, fieldvar) = vocab
    (; base, mindigits, maxdigits, dI) = dspec
    sT = swar_type(Base.min(maxdigits, sizeof(UInt)))
    swar_var = Symbol("$(fieldvar)_swar")
    bitsconsumed = Symbol("$(fieldvar)_bitsconsumed")
    parse_expr = gen_swarparse(sT, swar_var, base, maxdigits)
    countvar = Symbol("$(fieldvar)_count")
    countcheck = mindigits > 1 ? :($countvar >= $mindigits) : :(!iszero($countvar))
    swar_cast_var = sT == dI ? swar_var : :($swar_var % $dI)
    varparse = ExprVarLine[
        :($swar_var <<= ($(sizeof(sT)) - $countvar) << 3),
        parse_expr...,
        :($fnum = $swar_cast_var)]
    # Backward-load: single load with runtime-variable position, branchless digit count.
    # Requires sizeof(sT) - 1 preceding bytes (worst case: avail=1, load reaches back
    # sizeof(sT) - 1 bytes). Most identifiers with a literal prefix qualify.
    b = nctx[:current_branch]
    backward = b.parsed_min >= sizeof(sT) - 1
    availvar = Symbol("$(fieldvar)_avail")
    avail_bound = defid_lengthbound(state, nctx, maxdigits)
    load_and_count = if backward
        # Load sizeof(sT) bytes ending at pos + avail - 1, then right-shift to
        # low-align the digit window. gen_swar_digitcount counts from the LSB.
        backload = ExprVarLine[
            :($swar_var = htol(Base.unsafe_load(
                Ptr{$sT}(pointer(idbytes, pos + $availvar - $(sizeof(sT))))))),
            :($swar_var >>>= ($(sizeof(sT)) - $availvar) << 3),
            gen_swar_digitcount(sT, swar_var, countvar, base, maxdigits)...]
        # Guard avail >= mindigits (required) or avail >= 1 (optional) via
        # __length_check, giving resolve_length_checks! a chance to fold it away.
        guard_n = Base.max(mindigits, 1)
        guard_check = Expr(:call, :__length_check, b.id, b.parsed_max, guard_n, guard_n, guard_n)
        if isnothing(option)
            ExprVarLine[:($availvar = $avail_bound),
                        :(if !($guard_check); return ($(vocab.errmsg), pos) end),
                        backload...]
        else
            ExprVarLine[:($availvar = $avail_bound),
                        :(if $guard_check
                              $(backload...)
                          else
                              $countvar = 0; $swar_var = zero($sT)
                          end)]
        end
    else
        # Forward overread: single full-width forward load at pos. Digits land at LSB
        # (on LE with htol), so gen_swar_digitcount counts from LSB directly.
        # The sentinel-capped maxdigits in digitcount handles overflow bytes from
        # trailing content. Gated by __static_length_check for trailing safety.
        fwdload = ExprVarLine[
            :($swar_var = htol(Base.unsafe_load(Ptr{$sT}(pointer(idbytes, pos))))),
            gen_swar_digitcount(sT, swar_var, countvar, base, maxdigits)...]
        guard_n = Base.max(mindigits, 1)
        guard_check = Expr(:call, :__length_check, b.id, b.parsed_max, guard_n, guard_n, guard_n)
        fwd_guarded = if isnothing(option)
            ExprVarLine[:(if !($guard_check); return ($(vocab.errmsg), pos) end),
                        fwdload...]
        else
            ExprVarLine[:(if $guard_check
                              $(fwdload...)
                          else
                              $countvar = 0; $swar_var = zero($sT)
                          end)]
        end
        # Cascading power-of-2 exact-loads fallback (no backward or forward safety)
        varload = gen_swar_varload(sT, swar_var, countvar, availvar, base, maxdigits)
        cascade = ExprVarLine[:($countvar = 0), :($swar_var = zero($sT)),
                              :($availvar = $avail_bound), varload...]
        # Emit both paths; __static_length_check + fold_static_branches! picks the winner
        wide = Expr(:block, fwd_guarded...)
        narrow = Expr(:block, cascade...)
        ExprVarLine[Expr(:if, defid_static_lengthcheck(state, nctx, sizeof(sT)), wide, narrow)]
    end
    if isnothing(option)
        swar_core = ExprVarLine[load_and_count...,
                                :($countcheck || $fail_expr),
                                varparse...,
                                :($bitsconsumed = $countvar)]
        append!(swar_core, digit_required(vocab))
        swar_core
    else
        ExprVarLine[load_and_count...,
                    :($bitsconsumed = $countvar),
                    digit_optional(vocab, countcheck, varparse)...]
    end
end

"""
    gen_digit_parse(ctx, fieldvar, option, dspec) -> (; exprs, parsevar, directvar)

Generate parse expressions for a digit field, using SWAR when applicable.

Returns the expressions to append to the parse vector, plus `parsevar` (the
symbol holding the encoded value for `defid_orshift`) and `directvar` (whether
`parsevar === fnum`, controlling print/property extraction).

`dspec` is a NamedTuple with: `base`, `mindigits`, `maxdigits`, `min`, `max`,
`pad`, `dI` (value integer type), `dT` (stored/encoded type).
"""
function gen_digit_parse(state::DefIdState, nctx::NodeCtx,
                         fieldvar::Symbol, option,
                         dspec::NamedTuple)
    vocab = compute_digit_vocab(fieldvar, option, dspec, state)
    (; mindigits, maxdigits, base) = dspec
    fixedwidth = mindigits == maxdigits
    swar_limit = fixedwidth ? 2 * sizeof(UInt) : sizeof(UInt)
    use_swar = base <= 16 && maxdigits <= swar_limit
    exprs = if !use_swar
        gen_digit_parseint(vocab, dspec, state, nctx)
    elseif !fixedwidth
        gen_digit_swar_variable(vocab, dspec, state, nctx)
    elseif maxdigits > sizeof(UInt)
        gen_digit_twochunk(vocab, dspec, state, nctx)
    else
        gen_digit_swar_fixed(vocab, dspec, state, nctx)
    end
    (; exprs, vocab.parsevar, vocab.directvar)
end

function defid_digits!(exprs::IdExprs,
                       state::DefIdState, nctx::NodeCtx,
                       args::Vector{Any})
    length(args) ∈ (0, 1) || throw(ArgumentError("Expected at most one positional argument for digits, got $(length(args))"))
    base = get(nctx, :base, 10)::Int
    min = get(nctx, :min, 0)::Int
    max = get(nctx, :max, nothing)
    if max isa Expr
        max = Core.eval(state.mod, max)::Int
    end
    pad = get(nctx, :pad, 0)::Int
    # Positional arg: integer n → digits(1:n), range lo:hi → digits(lo:hi)
    mindigits, maxdigits = if !isempty(args) && Meta.isexpr(first(args), :call, 3) && first(first(args).args) == :(:)
        lo, hi = first(args).args[2], first(args).args[3]
        (lo isa Integer && hi isa Integer) ||
            throw(ArgumentError("Range bounds for digits must be integer literals"))
        lo <= hi || throw(ArgumentError("digits range min must be <= max"))
        (lo, hi)
    elseif !isempty(args) && first(args) isa Integer
        (1, first(args))
    elseif !isnothing(max)
        (1, ndigits(max, base=base))
    else
        throw(ArgumentError("Must specify either a digits argument or a max argument for digits"))
    end
    fixedwidth = mindigits == maxdigits
    if isnothing(max)
        max = (base^maxdigits) - 1
    end
    option = get(nctx, :optional, nothing)
    range = max - min + 1 + !isnothing(option)
    # Store raw values when it fits in the same bits as offset encoding
    directval = cardbits(range) == cardbits(max) && (min > 0 || isnothing(option))
    dbits = sizeof(typeof(range)) * 8 - leading_zeros(range)
    dI = cardtype(8 * sizeof(typeof(max)) - leading_zeros(max))
    dT = cardtype(dbits)
    fieldvar = get(nctx, :fieldvar, gensym("digits"))
    nbits = (state.bits += dbits)
    fixedpad = ifelse(fixedwidth, maxdigits, 0)
    printmin = Base.max(ndigits(Base.max(min, 1); base), pad, fixedpad)
    printmax = Base.max(ndigits(max; base), pad, fixedpad)
    # gen_digit_parse reads parsed_min for SWAR safety, so call before updating
    dspec = (; base, mindigits, maxdigits, min, max, pad, dI, dT)
    parsed = gen_digit_parse(state, nctx, fieldvar, option, dspec)
    inc_print!(nctx, printmin, printmax)
    inc_parsed!(nctx, mindigits, maxdigits)
    fnum = Symbol("$(fieldvar)_num")
    bitsconsumed = Symbol("$(fieldvar)_bitsconsumed")
    (; parsevar, directvar) = parsed
    append!(exprs.parse, parsed.exprs)
    posadv = ifelse(fixedwidth, maxdigits, bitsconsumed)
    posexpr = if isnothing(option)
        :(pos += $posadv)
    else
        :(if $option; pos += $posadv end)
    end
    push!(exprs.parse, defid_orshift(state, dT, parsevar, nbits), posexpr)
    # --- Extract and print ---
    fextract = :($fnum = $(defid_fextract(state, nbits, dbits)))
    fcast = dI == dT ? fnum : :($fnum % $dI)
    fvalue = if iszero(min) && !isnothing(option)
        :($fcast - $(one(dI)))
    elseif !directval && min - !isnothing(option) > 0
        :(($fcast + $(dI(min - !isnothing(option)))) % $dI)
    else
        fcast
    end
    printvar = ifelse(directvar, fnum, fieldvar)
    printpad = if fixedwidth && maxdigits > 1; maxdigits
    elseif pad > 0; pad
    else 0 end
    printex = if printpad > 0
        :(print(io, string($printvar, base=$base, pad=$printpad)))
    elseif base == 10
        :(print(io, $printvar))
    else
        :(print(io, string($printvar, base=$base)))
    end
    seg_desc = string(fixedwidth ? "$maxdigits" : "$mindigits-$maxdigits",
                      isone(maxdigits) ? " digit" : " digits",
                      base != 10 ? " in base $base" : "",
                      if min > 0 && max < base^maxdigits - 1
                          " between $(string(min; base, pad)) and $(string(max; base, pad))"
                      elseif min > 0
                          ", at least $(string(min; base, pad))"
                      elseif max < base^maxdigits - 1
                          ", at most $(string(max; base, pad))"
                      else "" end)
    if isnothing(option)
        push!(exprs.print, fextract)
    else
        push!(nctx[:oprint_detect], fextract, :($option = !iszero($fnum)))
    end
    directvar || push!(exprs.print, :($fieldvar = $fvalue))
    # Build extract for property access
    propvalue = if max < typemax(dI) ÷ 2
        sI = signed(dI)
        :($fvalue % $sI)
    else
        fvalue
    end
    # Build impart for constructor encoding
    argvar = gensym("arg_digit")
    directval = cardbits(max - min + 1 + !isnothing(option)) ==
                cardbits(max) && (min > 0 || isnothing(option))
    # Compute encode_expr: maps fnum → parsevar with appropriate offset
    offset = min - !isnothing(option)
    encode_expr = if directval
        dI != dT ? :($parsevar = $fnum % $dT) : :($parsevar = $fnum)
    elseif offset > 0
        :($parsevar = (($fnum - $(dT(offset))) % $dT))
    elseif offset < 0  # optional with min==0: +1 to reserve zero for "absent"
        :($parsevar = ($fnum + $(one(dT))) % $dT)
    else
        dI != dT ? :($parsevar = $fnum % $dT) : :($parsevar = $fnum)
    end
    # Assemble validation + encoding
    body = Any[]
    push!(body, :($argvar >= $min || throw(ArgumentError(
        string("Value ", $argvar, " is below minimum ", $min)))))
    push!(body, :($argvar <= $max || throw(ArgumentError(
        string("Value ", $argvar, " is above maximum ", $max)))))
    push!(body, :($fnum = $argvar % $dI))
    directvar || push!(body, encode_expr)
    push!(body, defid_orshift(state, dT, parsevar, nbits))
    seg_extract = if isnothing(option)
        ExprVarLine[fextract, propvalue]
    else
        ExprVarLine[fextract, :(if !iszero($fnum); $propvalue end)]
    end
    seg_impart = Any[]
    if isnothing(option)
        append!(seg_impart, body)
        seg_argtype = :Integer
    else
        push!(seg_impart, wrap_optional_impart(argvar, body))
        seg_argtype = :(Union{Integer, Nothing})
    end
    push!(exprs.segments, (; nbits=dbits, kind=:digits,
          label=seg_label(fieldvar),
          desc=seg_desc, argtype=seg_argtype, argvar,
          extract=seg_extract, impart=seg_impart, condition=option))
    push!(exprs.print, printex, :(__segment_printed = $(length(exprs.segments))))
    nothing
end

function defid_charseq!(exprs::IdExprs,
                        state::DefIdState, nctx::NodeCtx,
                        args::Vector{Any},
                        kind::Symbol)
    length(args) == 1 || throw(ArgumentError("Expected exactly one positional argument for $kind"))
    arg = first(args)
    minlen, maxlen = if arg isa Integer
        (arg, arg)
    elseif Meta.isexpr(arg, :call, 3) && first(arg.args) == :(:)
        lo, hi = arg.args[2], arg.args[3]
        (lo isa Integer && hi isa Integer) ||
            throw(ArgumentError("Range bounds for $kind must be integer literals"))
        lo <= hi || throw(ArgumentError("$kind range min must be <= max"))
        (lo, hi)
    else
        throw(ArgumentError("Expected integer or range for $kind, got $arg"))
    end
    function charseq_ranges(nctx, kind)
        upper = get(nctx, :upper, false)::Bool
        lower = get(nctx, :lower, false)::Bool
        casefold = get(nctx, :casefold, false)::Bool
        upper && lower && throw(ArgumentError("Cannot specify both upper=true and lower=true for $kind"))
        AZ = UInt8('A'):UInt8('Z')
        az = UInt8('a'):UInt8('z')
        d09 = UInt8('0'):UInt8('9')
        singlecase = upper || lower || casefold
        letters = if lower && !upper; (az,) elseif singlecase; (AZ,) else (AZ, az) end
        print_ranges = kind === :letters ? letters : (d09, letters...)
        (; print_ranges, casefold)
    end
    cfg = charseq_ranges(nctx, kind)
    variable = minlen != maxlen
    option = get(nctx, :optional, nothing)
    nvals = sum(length, cfg.print_ranges)
    bpc = cardbits(nvals)
    # When oneindexed, indices start at 1 so zero packed value means absent
    oneindexed = !isnothing(option) && !variable && cardbits(nvals + 1) == bpc
    if oneindexed
        bpc = cardbits(nvals + 1)
    end
    charbits = maxlen * bpc
    # Store length directly when it fits in the same bits as the range offset
    optoffset = !isnothing(option) && variable && minlen > 0
    directlen = variable && cardbits(maxlen + 1) == cardbits(maxlen - minlen + 1 + optoffset)
    lenrange = if !variable
        0
    elseif directlen
        maxlen + 1
    else
        maxlen - minlen + 1 + optoffset
    end
    lenbits = if variable; cardbits(lenrange) else 0 end
    presbits = if !isnothing(option) && !variable && !oneindexed; 1 else 0 end
    totalbits = charbits + lenbits + presbits
    fieldvar = get(nctx, :fieldvar, gensym(string(kind)))
    charvar = Symbol("$(fieldvar)_chars")
    lenvar = Symbol("$(fieldvar)_len")
    cT = cardtype(charbits)
    lT = if variable; cardtype(lenbits) else Nothing end
    ranges = cfg.print_ranges
    cfold = cfg.casefold
    nbits_pos = (state.bits += totalbits)
    scanlimit = defid_lengthbound(state, nctx, maxlen)
    inc_print!(nctx, minlen, maxlen)
    inc_parsed!(nctx, minlen, maxlen)
    # --- Parse ---
    push!(exprs.parse,
          :(($lenvar, $charvar) = parsechars($cT, idbytes, pos, $scanlimit, $ranges, $cfold, $oneindexed)))
    errmsg = defid_errmsg(state, if variable
        "Expected $minlen to $maxlen $kind characters"
    else
        "Expected $maxlen $kind characters"
    end)
    notfound = if isnothing(option)
        [:(return ($errmsg, pos))]
    else
        [:($option = false), :($charvar = zero($cT)), :($lenvar = 0)]
    end
    if !isnothing(option) && variable && minlen == 0
        push!(exprs.parse, :($lenvar > 0 || ($option = false)))
    else
        push!(exprs.parse,
              :(if $(if variable; :($lenvar < $minlen) else :($lenvar != $maxlen) end)
                    $(notfound...)
                end))
    end
    lenoffset = Symbol("$(fieldvar)_lenoff")
    lenbase = if directlen
        0
    elseif optoffset
        minlen - 1
    else
        minlen
    end
    push!(exprs.parse,
          defid_orshift(state, cT, charvar, nbits_pos - lenbits - presbits),
          :(pos += $lenvar))
    if variable
        lenpack = if lenbase == 0
            :($lenoffset = $lenvar % $lT)
        else
            :($lenoffset = ($lenvar - $lenbase) % $lT)
        end
        push!(exprs.parse, lenpack,
              defid_orshift(state, lT, lenoffset, nbits_pos))
    elseif presbits > 0
        push!(exprs.parse,
              defid_orshift(state, Bool, option, nbits_pos))
    end
    # --- Print / extract ---
    fextract_chars = :($charvar = $(defid_fextract(state, nbits_pos - lenbits - presbits, charbits)))
    extracts = ExprVarLine[fextract_chars]
    if variable
        fextract_len = if lenbase == 0
            :($lenvar = $(defid_fextract(state, nbits_pos, lenbits)))
        else
            :($lenvar = $(defid_fextract(state, nbits_pos, lenbits)) + $lenbase)
        end
        push!(extracts, fextract_len)
    end
    printex = if variable
        :(printchars(io, $charvar, Int($lenvar), $ranges))
    else
        :(printchars(io, $charvar, $maxlen, $ranges, $oneindexed))
    end
    tostringex = if variable
        :(chars2string($charvar, Int($lenvar), $ranges))
    else
        :(chars2string($charvar, $maxlen, $ranges, $oneindexed))
    end
    present = if variable
        if minlen == 0; :($lenvar > 0) else :(!iszero($lenvar)) end
    elseif oneindexed
        :(!iszero($charvar))
    else
        :(!iszero($(defid_fextract(state, nbits_pos, presbits))))
    end
    if !isnothing(option)
        push!(nctx[:oprint_detect], extracts..., :($option = $present))
    else
        append!(exprs.print, extracts)
    end
    push!(exprs.print, printex)
    # Build impart for constructor encoding
    argvar = gensym("arg_charseq")
    encode_chars = quote
        ($lenvar, $charvar) = parsechars($cT, String($argvar), $maxlen, $ranges, $cfold, $oneindexed)
        $lenvar == ncodeunits(String($argvar)) || throw(ArgumentError(
            string("Invalid characters in \"", $argvar, "\" for ", $(String(kind)))))
        $(if variable
              quote
                  $lenvar < $minlen && throw(ArgumentError(
                      string("String \"", $argvar, "\" is too short (minimum ", $minlen, " characters)")))
                  $lenvar > $maxlen && throw(ArgumentError(
                      string("String \"", $argvar, "\" is too long (maximum ", $maxlen, " characters)")))
              end
          else
              :($lenvar != $maxlen && throw(ArgumentError(
                  string("String \"", $argvar, "\" must be exactly ", $maxlen, " characters"))))
          end)
        $(defid_orshift(state, cT, charvar, nbits_pos - lenbits - presbits))
        $(if variable
              lenpack_expr = if lenbase == 0
                  :($lenoffset = $lenvar % $lT)
              else
                  :($lenoffset = ($lenvar - $lenbase) % $lT)
              end
              quote
                  $lenpack_expr
                  $(defid_orshift(state, lT, lenoffset, nbits_pos))
              end
          elseif presbits > 0
              defid_orshift(state, Bool, true, nbits_pos)
          else
              nothing
          end)
    end
    charseq_body = clean_quote_args(encode_chars)
    # Build extract for property access
    seg_extract = if isnothing(option)
        ExprVarLine[extracts..., tostringex]
    else
        ExprVarLine[extracts..., :(if $present; $tostringex end)]
    end
    seg_impart = Any[]
    if isnothing(option)
        append!(seg_impart, charseq_body)
        seg_argtype = :AbstractString
    else
        push!(seg_impart, wrap_optional_impart(argvar, charseq_body))
        seg_argtype = :(Union{AbstractString, Nothing})
    end
    push!(exprs.segments, (; nbits=totalbits, kind,
          label=seg_label(fieldvar),
          desc=string(variable ? "$minlen-$maxlen" : "$maxlen",
                      " ", kind, maxlen > 1 ? " characters" : " character"),
          argtype=seg_argtype, argvar, extract=seg_extract, impart=seg_impart,
          condition=option))
    push!(exprs.print, :(__segment_printed = $(length(exprs.segments))))
    nothing
end

# -----------------------------------------------------------
# Bit packing and sentinel resolution
# -----------------------------------------------------------

function defid_orshift(state::DefIdState, type::Type, value::Union{Symbol, Expr}, shift::Int)
    valcast = Expr(:call, :__cast_to_id, type, value)
    :(parsed = Core.Intrinsics.or_int(parsed, Core.Intrinsics.shl_int($valcast, (8 * sizeof($(esc(state.name))) - $shift))))
end

function defid_fextract(state::DefIdState, position::Int, width::Int)
    fT = cardtype(width)
    fval = :(Core.Intrinsics.lshr_int(id, 8 * sizeof($(esc(state.name))) - $position))
    ival = Expr(:call, :__cast_from_id, fT, fval)
    if width == sizeof(fT) * 8
        ival
    else
        fTmask = ~(typemax(fT) << width)
        :($ival & $fTmask)
    end
end

"""Emit a `__length_check` sentinel resolved by `resolve_length_checks!`."""
function defid_lengthcheck(state::DefIdState, nctx::NodeCtx, n_expr, n_min::Int=n_expr, n_max::Int=n_min)
    b = nctx[:current_branch]
    Expr(:call, :__length_check, b.id, b.parsed_max, n_min, n_max, n_expr)
end

"""Emit a `__static_length_check` sentinel resolving to `true`/`false` (never runtime)."""
defid_static_lengthcheck(state::DefIdState, nctx::NodeCtx, n::Int) =
    let b = nctx[:current_branch]; Expr(:call, :__static_length_check, b.id, b.parsed_max, n) end

"""Emit a `__length_bound` sentinel, resolving to `n` or `min(n, nbytes-pos+1)` at runtime."""
function defid_lengthbound(state::DefIdState, nctx::NodeCtx, n::Int)
    b = nctx[:current_branch]
    Expr(:call, :__length_bound, b.id, b.parsed_max, n)
end

"""
    resolve_length_checks!(exprs, branches)

Walk the AST and resolve length sentinels to their static or runtime values.
`__length_check` becomes `true` or `nbytes - pos + 1 >= n`;
`__static_length_check` becomes a `Bool`; `__length_bound` becomes `n` or
`min(n, nbytes - pos + 1)`; `__branch_check(Bool, id)` becomes `true` or a
runtime guard. Static booleans left in `if`/`elseif` conditions are folded
by the subsequent `fold_static_branches!` pass.
"""
function resolve_length_checks!(exprlikes::Vector{<:ExprVarLine}, branches::Vector{ParseBranch})
    splice_indices = Int[]
    for (idx, expr) in enumerate(exprlikes)
        expr isa Expr || continue
        if Meta.isexpr(expr, :call) && first(expr.args) === :__branch_check
            if expr.args[2] === Bool
                exprlikes[idx] = resolve_branch_check(branches[expr.args[3]])
            end
            # Root branch check (args[2] is Int): leave for defid_parsebytes
            continue
        end
        result = resolve_length_check_expr!(expr, branches)
        if result === :remove
            push!(splice_indices, idx)
        elseif !isnothing(result)
            exprlikes[idx] = result
        end
    end
    deleteat!(exprlikes, splice_indices)
    exprlikes
end

# Resolve __length_check to true or a runtime `nbytes - pos + 1 >= n` expression.
# Uses the sentinel's branch parsed_min as the guarantee: for the root branch this
# is the global minimum; for optional branches, the __branch_check guard ensures
# the branch minimum holds when the code executes. The branch-local emission_max
# avoids the old system's problem where optionals inflated the global max.
function resolve_length_check_value(expr::Expr, branches::Vector{ParseBranch})
    branch_id, emission_max, _, n_max, n_expr = expr.args[2:end]
    branches[branch_id].parsed_min - emission_max >= n_max ? true : :(nbytes - pos + 1 >= $n_expr)
end

# Walk and resolve sentinels. Returns :remove or nothing (modified in-place).
function resolve_length_check_expr!(expr::Expr, branches::Vector{ParseBranch})
    splice_indices = Int[]
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        if Meta.isexpr(arg, :call) && first(arg.args) === :__length_check
            val = resolve_length_check_value(arg, branches)
            if val isa Expr
                arg.head, arg.args = val.head, val.args
            else
                expr.args[i] = val
            end
        elseif Meta.isexpr(arg, :call) && first(arg.args) === :__length_bound
            branch_id, emission_max, n = arg.args[2:end]
            if branches[branch_id].parsed_min - emission_max >= n
                expr.args[i] = n
            else
                replacement = :(min($n, nbytes - pos + 1))
                arg.head, arg.args = replacement.head, replacement.args
            end
        elseif Meta.isexpr(arg, :call) && first(arg.args) === :__static_length_check
            branch_id, emission_max, n = arg.args[2:end]
            expr.args[i] = branches[branch_id].parsed_min - emission_max >= n
        elseif Meta.isexpr(arg, :call) && first(arg.args) === :__branch_check
            if arg.args[2] === Bool
                val = resolve_branch_check(branches[arg.args[3]])
                if val isa Expr
                    arg.head, arg.args = val.head, val.args
                else
                    expr.args[i] = val
                end
            end
            # Root branch check: leave for defid_parsebytes
        else
            result = resolve_length_check_expr!(arg, branches)
            if result === :remove
                push!(splice_indices, i)
            elseif !isnothing(result)
                expr.args[i] = result
            end
        end
    end
    deleteat!(expr.args, splice_indices)
    nothing
end

"""
    fold_static_branches!(exprlikes)

Resolve `if true`/`if false` and `if !true`/`if !false` statically: splice the taken
branch, discard the dead one. Handles `if`/`elseif`/`else` chains. Recurses until fixpoint.
"""
function fold_static_branches!(items::Vector{<:ExprVarLine})
    while _fold_static_vec!(items) end
    items
end

function _fold_static_vec!(items::AbstractVector)
    splices = Tuple{Int, Vector{Any}}[]
    changed = false
    for (i, item) in enumerate(items)
        item isa Expr || continue
        if item.head in (:if, :elseif) && item.args[1] isa Bool
            push!(splices, (i, _take_branch(item)))
            changed = true
        elseif item.head in (:if, :elseif) &&
               Meta.isexpr(item.args[1], :call, 2) &&
               item.args[1].args[1] === :! && item.args[1].args[2] isa Bool
            # Resolve negated boolean: !true → false, !false → true
            item.args[1] = !item.args[1].args[2]
            push!(splices, (i, _take_branch(item)))
            changed = true
        else
            changed |= _fold_static_vec!(item.args)
        end
    end
    for (i, replacement) in reverse(splices)
        splice!(items, i, replacement)
    end
    changed
end

function _take_branch(expr::Expr)
    if expr.args[1]::Bool
        body = expr.args[2]
    elseif length(expr.args) >= 3
        body = expr.args[3]
        body isa Expr && body.head === :elseif && (body.head = :if)
    else
        return Any[]
    end
    body isa Expr && body.head === :block ?
        filter(e -> !(e isa LineNumberNode), body.args) : Any[body]
end

function implement_casting!(expr::Expr, name::Symbol, finalsize::Int)
    if Meta.isexpr(expr, :call, 3) && first(expr.args) ∈ (:__cast_to_id, :__cast_from_id)
        casttype, valtype, value = expr.args
        targettype, targetsize, valsize = if casttype == :__cast_to_id
            esc(name), finalsize, sizeof(valtype)
        else
            valtype, sizeof(valtype), finalsize
        end
        expr.args[1:3] = if valsize == targetsize
            :(Core.bitcast($targettype, $value)).args
        elseif valsize < targetsize
            :(Core.Intrinsics.zext_int($targettype, $value)).args
        else
            :(Core.Intrinsics.trunc_int($targettype, $value)).args
        end
    else
        for arg in expr.args
            arg isa Expr && implement_casting!(arg, name, finalsize)
        end
    end
    expr
end

function implement_casting!(state::DefIdState, exprlikes::Vector{<:ExprVarLine})
    finalsize = cld(state.bits, 8)
    for expr in exprlikes
        expr isa Expr && implement_casting!(expr, state.name, finalsize)
    end
    exprlikes
end

# -----------------------------------------------------------
# Codegen assembly
# -----------------------------------------------------------

function defid_parsebytes(pexprs::Vector{ExprVarLine}, state::DefIdState, name::Symbol)
    parsed_min = state.branches[1].parsed_min  # root branch's cumulative min
    resolved = resolve_length_checks!(implement_casting!(state, pexprs), state.branches)
    fold_static_branches!(resolved)
    # Replace the root __branch_check sentinel with the upfront minimum-length check
    errmsg = defid_errmsg(state, string("Expected at least ", parsed_min, " bytes"))
    split_idx = findfirst(e -> Meta.isexpr(e, :call) && first(e.args) === :__branch_check &&
                                e.args[2] == 1, resolved)
    if !isnothing(split_idx) && parsed_min > 0
        check = if split_idx > 1
            :(nbytes - pos >= $(parsed_min - 1) || return ($errmsg, 1))
        else
            :(nbytes >= $parsed_min || return ($errmsg, 1))
        end
        resolved[split_idx] = check
    else
        !isnothing(split_idx) && deleteat!(resolved, split_idx)
    end
    :(Base.@assume_effects :foldable :nothrow function $(GlobalRef(@__MODULE__, :parsebytes))(::Type{$(esc(name))}, idbytes::AbstractVector{UInt8})
          parsed = $(zero_parsed_expr(state))
          pos = 1
          nbytes = length(idbytes)
          $(resolved...)
          (parsed, pos)
      end)
end

function defid_parse(state::DefIdState, name::Symbol)
    errmsgs = Tuple(state.errconsts)
    ename = esc(name)
    (:(function $(GlobalRef(Base, :parse))(::Type{$ename}, id::AbstractString)
           result, pos = parsebytes($ename, codeunits(id))
           if result isa $ename
               pos > ncodeunits(id) || throw(MalformedIdentifier{$ename}(id, "Unparsed trailing content"))
               result
           else
               throw(MalformedIdentifier{$ename}(id, @inbounds $errmsgs[result]))
           end
       end),
     :(function $(GlobalRef(Base, :tryparse))(::Type{$ename}, id::AbstractString)
           result, pos = parsebytes($ename, codeunits(id))
           if result isa $ename && pos > ncodeunits(id)
               result
           end
       end))
end

function defid_bufprint!(pexprs::Union{Vector{<:ExprVarLine}, Vector{Any}})
    # Collect (index, replacement_exprs) for splicing, applied in reverse
    splices = Tuple{Int, Vector{Any}}[]
    for (i, expr) in enumerate(pexprs)
        if Meta.isexpr(expr, :call) && length(expr.args) >= 3 && expr.args[2] == :io
            fname, _, args... = expr.args
            replacement = if fname == :print
                if length(args) == 1
                    if Meta.isexpr(first(args), :call) && first(first(args).args) == :string
                        # Unwrap print(io, string(var, kw...)) → bufprint(buf, pos, var, kw...)
                        sargs = first(args).args[2:end]
                        positional = Any[]
                        base, pad = 10, 0
                        for sa in sargs
                            if Meta.isexpr(sa, :kw, 2) && sa.args[1] == :base
                                base = sa.args[2]
                            elseif Meta.isexpr(sa, :kw, 2) && sa.args[1] == :pad
                                pad = sa.args[2]
                            else
                                push!(positional, sa)
                            end
                        end
                        Any[:(pos = bufprint(buf, pos, $(positional...), $base, $pad))]
                    elseif first(args) isa String
                        Any[bufprint_static(first(args))...]
                    else
                        Any[:(pos = bufprint(buf, pos, $(first(args))))]
                    end
                else
                    Any[:(pos = bufprint(buf, pos, $arg)) for arg in args]
                end
            elseif fname == :printchars
                Any[:(pos = bufprintchars(buf, pos, $(args...)))]
            end
            push!(splices, (i, replacement))
        elseif expr isa Expr
            for arg in expr.args
                arg isa Expr && defid_bufprint!(arg.args)
            end
        end
    end
    for (i, replacement) in reverse(splices)
        splice!(pexprs, i, replacement)
    end
end

const INTS_UP_TO_WORD = let ints = DataType[UInt8]
    while ints[end] != UInt
        push!(ints, widen(ints[end]))
    end
    Tuple(ints)
end

function bufprint_static(str::String)
    reduce(word_chunks(ncodeunits(str)), init = Expr[]) do exprs, (; offset, width, iT)
        value = pack_bytes(str, offset, width, iT)
        if iT === UInt8
            push!(exprs, :(buf[pos += 1] = $value))
        else
            push!(exprs,
                  :(Base.unsafe_store!(Ptr{$iT}(pointer(buf, pos + 1)), $value)),
                  :(pos += $width))
        end
    end
end

function bufprint(buf::Memory{UInt8}, pos::Int, str::String)
    n = ncodeunits(str)
    Base.unsafe_copyto!(pointer(buf, pos + 1), pointer(str), n)
    pos + n
end

function bufprintchars(buf::Memory{UInt8}, pos::Int, packed::P, nchars::Int,
                       ranges::NTuple{N, UnitRange{UInt8}},
                       oneindexed::Bool = false) where {P <: Unsigned, N}
    nvals = sum(length, ranges)
    bpc = cardbits(nvals + oneindexed)
    topshift = 8 * sizeof(P) - bpc
    packed <<= 8 * sizeof(P) - nchars * bpc
    offset = UInt8(oneindexed)
    @inbounds for _ in 1:nchars
        idx = UInt8(packed >> topshift) - offset
        for r in ranges
            rlen = length(r) % UInt8
            if idx < rlen
                buf[pos += 1] = first(r) + idx
                break
            end
            idx -= rlen
        end
        packed <<= bpc
    end
    pos
end

Base.@constprop :aggressive function bufprint(buf::Memory{UInt8}, pos::Int, num::Integer, base::Int = 10, pad::Int = 0)
    @inline int2byte(d) = if d < 10
        UInt8('0') + d % UInt8
    elseif base <= 36
        UInt8('a') - 0x0a + d % UInt8
    else
        db = d % UInt8
        ifelse(db < 36, UInt8('a') - 0x0a + db, UInt8('a') - 0x24 + db)
    end
    nd = ndigits(num; base)
    width = Base.max(nd, pad)
    endpos = pos + width
    i = endpos
    @inbounds while num != 0
        num, d = divrem(num, base)
        buf[i] = int2byte(d)
        i -= 1
    end
    @inbounds while i > pos
        buf[i] = UInt8('0')
        i -= 1
    end
    endpos
end

function strip_segsets!(expr::ExprVarLine)
    expr isa Expr || return expr
    delat = Int[]
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        if Meta.isexpr(arg, :(=), 2) && first(arg.args) === :__segment_printed
            push!(delat, i)
        else
            strip_segsets!(arg)
        end
    end
    isempty(delat) || deleteat!(expr.args, delat)
    expr
end

function defid_shortcode(pexprs::Vector{ExprVarLine}, state::DefIdState, name::Symbol)
    root = state.branches[1]
    maxbytes = root.print_max
    minbytes = root.print_min
    fixedlen = minbytes == maxbytes
    # Build buffer-based expressions from the print expressions,
    # stripping __segment_printed assignments used only by segments()
    bufexprs = map(strip_segsets! ∘ copy, pexprs)
    filter!(e -> !Meta.isexpr(e, :(=), 2) || first(e.args) !== :__segment_printed, bufexprs)
    defid_bufprint!(bufexprs)
    tobytes_def = :(function $(GlobalRef(@__MODULE__, :tobytes))(id::$(esc(name)))
          buf = $(fixedlen ? :(Base.StringMemory($maxbytes)) : :(Memory{UInt8}(undef, $maxbytes)))
          pos = 0
          $(bufexprs...)
          buf, pos
      end)
    shortcode_io_def = :(function $(GlobalRef(@__MODULE__, :shortcode))(io::IO, id::$(esc(name)))
          buf, len = tobytes(id)
          unsafe_write(io, pointer(buf), len)
          nothing
      end)
    shortcode_def = if fixedlen
        :(function $(GlobalRef(@__MODULE__, :shortcode))(id::$(esc(name)))
              buf, _ = tobytes(id)
              Base.unsafe_takestring(buf)
          end)
    else
        :(function $(GlobalRef(@__MODULE__, :shortcode))(id::$(esc(name)))
              buf, len = tobytes(id)
              str = Base.StringMemory(len)
              Base.unsafe_copyto!(pointer(str), pointer(buf), len)
              Base.unsafe_takestring(str)
          end)
    end
    Expr(:block, tobytes_def, shortcode_io_def, shortcode_def)
end

function defid_properties(properties::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}},
                          segs::Vector{IdValueSegment},
                          state::DefIdState, name::Symbol)
    isempty(properties) && return :()
    resolved = resolve_property_segments(properties, segs)
    fallback = :(throw(FieldError($(esc(name)), prop)))
    clauses = foldr(enumerate(properties), init = fallback) do (i, (prop, val)), rest
        prop_exprs = if val isa Symbol
            idx = only(resolved[i].second)
            copy(segs[idx].extract)
        else
            copy(val)
        end
        qprop = QuoteNode(prop)
        body = Expr(:block, implement_casting!(state, prop_exprs)...)
        Expr(ifelse(i == 1, :if, :elseif), :(prop === $qprop), body, rest)
    end
    :(function $(GlobalRef(Base, :getproperty))(id::$(esc(name)), prop::Symbol)
          $clauses
      end)
end

function defid_segments_type(segs::Vector{IdValueSegment}, name::Symbol)
    isempty(segs) && return :()
    :(function $(GlobalRef(@__MODULE__, :segments))(::Type{$(esc(name))})
          $(Expr(:tuple, [(; nbits=s.nbits, kind=s.kind, label=s.label, desc=s.desc)
                          for s in segs if s.nbits > 0]...))
      end)
end

function defid_segments_value(segs::Vector{IdValueSegment}, pexprs::Vector{ExprVarLine}, name::Symbol)
    function print_segsets!(segvars::Vector{Tuple{Int, Symbol}}, expr::ExprVarLine)
        expr isa Expr || return expr
        if Meta.isexpr(expr, :(=)) && first(expr.args) === :__segment_printed
            _, i = expr.args
            # We should never see i+1 before i
            if i > length(segvars)
                anon = segs[i].nbits == 0
                precount = sum((s.nbits > 0 for s in segs[1:i-1]), init = 0)
                push!(segvars, (ifelse(anon, 0, precount + 1), Symbol("seg$i")))
            end
            var = last(segvars[i])
            expr.args[1:2] = :($var = takestring!(io)).args
        else
            for arg in expr.args
                arg isa Expr && print_segsets!(segvars, arg)
            end
        end
        expr
    end
    isempty(segs) && return :()
    svars = Tuple{Int, Symbol}[]
    pexprs2 = map(copy, pexprs)
    for expr in pexprs2
        print_segsets!(svars, expr)
    end
    :(function $(GlobalRef(@__MODULE__, :segments))(id::$(esc(name)))
          io = IOBuffer()
          $(Expr(:(=), Expr(:tuple, (s for (_, s) in svars)...), Expr(:tuple, ("" for _ in svars)...)))
          $(pexprs2...)
          $(Expr(:tuple, (Expr(:tuple, i, s) for (i, s) in svars)...))
      end)
end

function defid_constructor(segs::Vector{IdValueSegment},
                          properties::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}},
                          state::DefIdState, name::Symbol)
    resolved = resolve_property_segments(properties, segs)
    isempty(resolved) && return :()
    # Build (argname, seg_index) pairs: single-node uses property name, multi-node
    # gets numbered sub-names
    args = Tuple{Symbol, Int}[]
    for (pname, idxs) in resolved
        if length(idxs) == 1
            push!(args, (pname, only(idxs)))
        else
            for (j, si) in enumerate(idxs)
                push!(args, (Symbol(pname, "_", j), si))
            end
        end
    end
    isempty(args) && return :()
    # Build parameter list and arg→segvar bindings
    params = [let seg = segs[si]
                  isnothing(seg.argtype) ? :($aname) : :($aname::$(seg.argtype))
              end for (aname, si) in args]
    argbindings = [:($(segs[si].argvar) = $aname) for (aname, si) in args]
    # Validate optional scope nesting — derive scope_parents from branch registry
    scope_parents = Dict{Symbol, Union{Nothing, Symbol}}()
    for b in state.branches
        isnothing(b.scope) && continue
        scope_parents[b.scope] = isnothing(b.parent) ? nothing : b.parent.scope
    end
    scope_args = Dict{Symbol, Vector{Int}}()
    for (idx, (_, si)) in enumerate(args)
        scope = segs[si].condition
        isnothing(scope) && continue
        push!(get!(Vector{Int}, scope_args, scope), idx)
    end
    scope_checks = [:(if isnothing($(args[first(pidxs)][1])) && !isnothing($(args[first(cidxs)][1]))
                          throw(ArgumentError(
                              string("Cannot specify ", $(QuoteNode(args[first(cidxs)][1])),
                                     " when ", $(QuoteNode(args[first(pidxs)][1])), " is nothing")))
                      end)
                    for (scope, cidxs) in scope_args
                    for pidxs in (get(scope_args, get(scope_parents, scope, nothing), nothing),)
                    if !isnothing(pidxs)]
    # Build encode expressions from segment impart
    encode_exprs = reduce(vcat, (segs[si].impart for (_, si) in args); init=Any[])
    finalsize = cld(state.bits, 8)
    for expr in encode_exprs
        expr isa Expr && implement_casting!(expr, name, finalsize)
    end
    :(function $(esc(name))($(params...))
          parsed = $(zero_parsed_expr(state))
          $(argbindings...)
          $(scope_checks...)
          $(encode_exprs...)
          parsed
      end)
end

"""Generate `Base.show(io::IO, id::T)` displaying constructor form, e.g. `T(42, :A)`."""
function defid_show(segs::Vector{IdValueSegment},
                    properties::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}},
                    state::DefIdState, name::Symbol)
    resolved = resolve_property_segments(properties, segs)
    isempty(resolved) && return :()
    # Build show body: each constructor arg separated by commas
    show_parts = ExprVarLine[]
    for (pname, idxs) in resolved
        isempty(show_parts) || push!(show_parts, :(print(io, ", ")))
        if length(idxs) == 1
            push!(show_parts, :(show(io, getproperty(id, $(QuoteNode(pname))))))
        else
            for (j, si) in enumerate(idxs)
                j > 1 && push!(show_parts, :(print(io, ", ")))
                extract_copy = map(copy, segs[si].extract)
                implement_casting!(state, extract_copy)
                push!(show_parts, Expr(:block, extract_copy[1:end-1]...,
                                       :(show(io, $(extract_copy[end])))))
            end
        end
    end
    :(function $(GlobalRef(Base, :show))(io::IO, id::$(esc(name)))
          if get(io, :limit, false) === true
              if get(io, :typeinfo, Nothing) != $(esc(name))
                  print(io, $(QuoteNode(name)), ':')
              end
              print(io, shortcode(id))
          else
              show(io, $(esc(name)))
              print(io, '(')
              $(show_parts...)
              print(io, ')')
          end
      end)
end

function defid_make(exprs::IdExprs, state::DefIdState, name::Symbol)
    block = Expr(:toplevel)
    numbits = 8 * cld(state.bits, 8)
    implement_casting!(state, exprs.print)
    push!(block.args,
          :(Base.@__doc__(primitive type $(esc(name)) <: $AbstractIdentifier $numbits end)),
          :($(GlobalRef(@__MODULE__, :nbits))(::Type{$(esc(name))}) = $(state.bits)),
          defid_parsebytes(exprs.parse, state, name),
          defid_parse(state, name)...,
          defid_shortcode(exprs.print, state, name),
          :($(GlobalRef(Base, :propertynames))(::$(esc(name))) = $(Tuple(map(first, exprs.properties)))),
          defid_properties(exprs.properties, exprs.segments, state, name),
          defid_segments_type(exprs.segments, name),
          defid_segments_value(exprs.segments, exprs.print, name),
          defid_constructor(exprs.segments, exprs.properties, state, name),
          defid_show(exprs.segments, exprs.properties, state, name),
          :($(GlobalRef(Base, :isless))(a::$(esc(name)), b::$(esc(name))) =
                Core.Intrinsics.ult_int(a, b)))
    if !isnothing(state.purlprefix)
        push!(block.args,
              :($(GlobalRef(@__MODULE__, :purlprefix))(::Type{$(esc(name))}) = $(state.purlprefix)))
    end
    push!(block.args, esc(name))
    block
end
