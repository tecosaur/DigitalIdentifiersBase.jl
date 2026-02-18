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
    ctx = Base.ImmutableDict{Symbol, Any}(:name, name)
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :bits, Ref(0))
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :segments, IdSegment[])
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :print_bytes_min, Ref(0))
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :print_bytes_max, Ref(0))
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :parsed_bytes_min, Ref(0))
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :parsed_bytes_max, Ref(0))
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :casefold, true)
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :__module__, __module__)
    for arg in args
        Meta.isexpr(arg, :(=), 2) || throw(ArgumentError("Expected keyword arguments of the form key=value, got $arg"))
        kwname, kwval = arg.args
        kwname ∈ ALL_KNOWN_KEYS ||
            throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments are: $(join(ALL_KNOWN_KEYS, ", "))"))
        ctx = Base.ImmutableDict{Symbol, Any}(ctx, kwname, kwval)
    end
    exprs = IdExprs(([], [], []))
    # Strip leading prefixes (stripname/purlprefix) before the main pattern
    prefix = get(ctx, :purlprefix, nothing)
    stripname = get(ctx, :stripname, true)::Bool
    skipprefixes = String[]
    !isnothing(prefix) && push!(skipprefixes, lowercase(prefix))
    stripname && push!(skipprefixes, lowercase(string(name)) * ":")
    if !isempty(skipprefixes)
        defid_dispatch!(exprs, ctx, Expr(:call, :skip, skipprefixes...))
    end
    defid_dispatch!(exprs, ctx, :__first_nonskip)
    defid_dispatch!(exprs, ctx, pattern)
    defid_make(exprs, ctx, name)
end

@static if VERSION < v"1.13-"
    takestring!(io::IO) = String(take!(io))
end

const ExprVarLine = Union{Expr, Symbol, LineNumberNode}
const IdExprs = @NamedTuple{parse::Vector{ExprVarLine},
                            print::Vector{ExprVarLine},
                            properties::Vector{Pair{Symbol, Vector{ExprVarLine}}}}

const IdSegment = @NamedTuple{nbits::Int, kind::Symbol, label::Symbol, desc::String}

const KNOWN_KEYS = (
    choice = (:casefold, :is),
    digits = (:base, :min, :max, :pad),
    letters = (:upper, :lower, :casefold),
    alphnum = (:upper, :lower, :casefold),
    skip = (:casefold, :print),
    _global = (:purlprefix, :stripname)
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

function defid_dispatch!(exprs::IdExprs,
                         ctx::Base.ImmutableDict{Symbol, Any},
                         node::Any, args::Vector{Any})
    if node isa QuoteNode
        defid_field!(exprs, ctx, node, args)
    elseif node === :seq
        for arg in args
            defid_dispatch!(exprs, ctx, arg)
        end
    elseif node === :optional
        defid_optional!(exprs, ctx, args)
    elseif node === :skip
        defid_skip!(exprs, ctx, args)
    elseif node === :choice
        defid_choice!(exprs, ctx, args)
    elseif node === :literal
        length(args) == 1 || throw(ArgumentError("Expected exactly one argument for literal, got $(length(args))"))
        lit = args[1]
        lit isa String || throw(ArgumentError("Expected a string literal for literal, got $lit"))
        defid_literal!(exprs, ctx, lit)
    elseif node === :digits
        defid_digits!(exprs, ctx, args)
    elseif node === :letters
        defid_charseq!(exprs, ctx, args, :letters)
    elseif node === :alphnum
        defid_charseq!(exprs, ctx, args, :alphnum)
    else
        throw(ArgumentError("Unknown pattern node $node"))
    end
end

function defid_dispatch!(exprs::IdExprs,
                         ctx::Base.ImmutableDict{Symbol, Any},
                         thing::Any)
    if Meta.isexpr(thing, :tuple)
        args = Any[]
        for arg in thing.args
            if Meta.isexpr(arg, :(=), 2)
                kwname, kwval = arg.args
                kwname ∈ ALL_KNOWN_KEYS ||
                    throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments are: $(join(ALL_KNOWN_KEYS, ", "))"))
                ctx = Base.ImmutableDict{Symbol, Any}(ctx, kwname, kwval)
            else
                push!(args, arg)
            end
        end
        defid_dispatch!(exprs, ctx, :seq, args)
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
                ctx = Base.ImmutableDict{Symbol, Any}(ctx, kwname, kwval)
            else
                push!(args, arg)
            end
        end
        defid_dispatch!(exprs, ctx, name, args)
    elseif thing isa String
        defid_literal!(exprs, ctx, thing)
    elseif thing === :__first_nonskip
        ctx[:parsed_bytes_min][] = 0
        ctx[:parsed_bytes_max][] = 0
        push!(exprs.parse, Expr(:call, :__upfront_lengthcheck))
    end
end

function defid_field!(exprs::IdExprs,
                      ctx::Base.ImmutableDict{Symbol, Any},
                      node::QuoteNode,
                      args::Vector{Any})
    isnothing(get(ctx, :fieldvar, nothing)) || throw(ArgumentError("Fields may not be nested"))
    fieldvals = Any[]
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :fieldvar, Symbol("attr_$(node.value)"))
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :fieldvals, fieldvals)
    initialprints = length(exprs.print)
    for arg in args
        defid_dispatch!(exprs, ctx, arg)
    end
    if length(fieldvals) == 0
        throw(ArgumentError("Field $(node.value) does not capture any value"))
    elseif length(fieldvals) == 1
        fv = first(fieldvals)
        push!(exprs.properties, node.value => if fv isa Expr; fv.args else [fv] end)
    else
        propprints = map(strip_segsets! ∘ copy, exprs.print[initialprints+1:end])
        filter!(e -> !Meta.isexpr(e, :(=), 2) || first(e.args) !== :__segment_printed, propprints)
        push!(exprs.properties, node.value => (
            quote
                io = IOBuffer()
                $(propprints...)
                takestring!(io)
            end).args)
    end
end

function defid_optional!(exprs::IdExprs,
                         ctx::Base.ImmutableDict{Symbol, Any},
                         args::Vector{Any})
    popt = get(ctx, :optional, nothing)
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :optional, gensym("optional"))
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :oprint_detect, ExprVarLine[])
    oexprs = (; parse = ExprVarLine[], print = ExprVarLine[], properties = exprs.properties)
    saved_print_min = ctx[:print_bytes_min][]
    saved_parse_min = ctx[:parsed_bytes_min][]
    if all(a -> a isa String, args)
        defid_choice!(oexprs, ctx, push!(Any[join(Vector{String}(args))], ""))
    else
        for arg in args
            defid_dispatch!(oexprs, ctx, arg)
        end
    end
    ctx[:print_bytes_min][] = saved_print_min
    ctx[:parsed_bytes_min][] = saved_parse_min
    if isnothing(popt)
        append!(exprs.parse, oexprs.parse)
    else
        push!(exprs.parse,
              :(if $popt
                    $(oexprs.parse...)
                end))
    end
    append!(exprs.print, ctx[:oprint_detect])
    push!(exprs.print, :(if $(ctx[:optional]); $(oexprs.print...) end))
    nothing
end

function defid_skip!(exprs::IdExprs,
                     ctx::Base.ImmutableDict{Symbol, Any},
                     args::Vector{Any})
    all(a -> a isa String, args) || throw(ArgumentError("Expected all arguments to be strings for skip"))
    pval = get(ctx, :print, nothing)
    sargs = Vector{String}(args)
    !isnothing(pval) && pval ∉ sargs && push!(sargs, pval)
    casefold = get(ctx, :casefold, true) === true
    if casefold
        all(isascii, sargs) || throw(ArgumentError("Expected all arguments to be ASCII strings for skip with casefolding"))
    end
    push!(exprs.parse, gen_static_lchop(casefold ? map(lowercase, sargs) : sargs, casefold=casefold))
    ctx[:parsed_bytes_max][] += maximum(ncodeunits, sargs)
    if !isnothing(pval)
        push!(ctx[:segments], (0, :skip, :skip, "Skipped literal string \"$(join(sargs, ", "))\""))
        push!(exprs.print, :(print(io, $pval)), :(__segment_printed = $(length(ctx[:segments]))))
        ctx[:print_bytes_min][] += ncodeunits(pval)
        ctx[:print_bytes_max][] += ncodeunits(pval)
    end
    nothing
end

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
    gen_verify_table(options::Vector{String}, casefold::Bool)

Build word-sized comparison data for verifying a perfect-hash match.

Decomposes the common prefix (minimum option length) into word-sized chunks,
returning `(; verify_table, foldmasks, chunks)` where:
- `verify_table`: `NTuple{N, NTuple{C, UInt}}` — per-option expected values for each chunk
- `foldmasks`: `NTuple{C, UInt}` — casefold OR masks for each chunk
- `chunks`: `Vector{@NamedTuple{offset, width, iT}}` — position, byte width, and integer type for each chunk load
"""
function gen_verify_table(options::Vector{String}, casefold::Bool;
                          skip::Union{Nothing, Tuple{Int, Int}} = nothing)
    minlen = minimum(ncodeunits, options)
    chunks = if isnothing(skip)
        word_chunks(minlen)
    else
        # Split into chunks covering [0, gap) and [gap+width, total),
        # with right-side offsets adjusted to original string positions
        gap_offset, gap_width = skip
        left = word_chunks(gap_offset)
        right = word_chunks(minlen - gap_offset - gap_width)
        right_base = gap_offset + gap_width
        for i in eachindex(right)
            right[i] = (; right[i]..., offset = right[i].offset + right_base)
        end
        vcat(left, right)
    end
    verify_table = Tuple(Tuple(pack_bytes(opt, c.offset, c.width, c.iT) for c in chunks) for opt in options)
    foldmasks = Tuple(
        if casefold
            reduce(|, (c.iT(ifelse(any(opt -> codeunit(opt, c.offset + j + 1) in UInt8('a'):UInt8('z'), options), 0x20, 0x00)) << (8j) for j in 0:c.width-1), init=zero(c.iT))
        else
            zero(c.iT)
        end
        for c in chunks)
    (; verify_table, foldmasks, chunks)
end

"""
    gen_verify_exprs(vt, prefix::Symbol) -> (destructure, checks)

Generate AST for destructured comparison of word-sized chunks.

Assumes `idbytes` is in scope. Returns:
- `destructure`: assignments that extract per-option expected values from the verify table
- `checks`: a boolean expression that is `true` when all chunks match
"""
function gen_verify_exprs(vt, prefix::Symbol)
    nchunks = length(vt.chunks)
    cvars = [Symbol(prefix, "_expect", ci) for ci in 1:nchunks]
    fmvars = [Symbol(prefix, "_fmask", ci) for ci in 1:nchunks]
    destructure = [
        Expr(:(=), Expr(:tuple, cvars...), :($(vt.verify_table)[i])),
        Expr(:(=), Expr(:tuple, fmvars...), vt.foldmasks)]
    checks = foldr(1:nchunks, init = :(true)) do ci, rest
        (; offset, iT) = vt.chunks[ci]
        posexpr = iszero(offset) ? :pos : :(pos + $offset)
        load = load_word(iT, posexpr)
        check = :($load | $(fmvars[ci]) == $(cvars[ci]))
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
        # Single tail length: word-sized comparison
        taillen = only(distinct_taillens)
        chunks = word_chunks(taillen)
        nonempty_tails = filter(!isempty, tails)
        zerotup = Tuple(zero(c.iT) for c in chunks)
        tailtable = Tuple(
            if isempty(tails[oi])
                zerotup
            else
                Tuple(pack_bytes(tails[oi], c.offset, c.width, c.iT) for c in chunks)
            end
            for oi in eachindex(options))
        foldmasks = Tuple(
            if casefold
                reduce(|, (c.iT(ifelse(any(t -> codeunit(t, c.offset + j + 1) in UInt8('a'):UInt8('z'), nonempty_tails), 0x20, 0x00)) << (8j) for j in 0:c.width-1), init=zero(c.iT))
            else
                zero(c.iT)
            end
            for c in chunks)
        tvars = [Symbol(prefix, "_tail", ci) for ci in 1:length(chunks)]
        tmvars = [Symbol(prefix, "_tmask", ci) for ci in 1:length(chunks)]
        destructure = [
            Expr(:(=), Expr(:tuple, tvars...), :($tailtable[i])),
            Expr(:(=), Expr(:tuple, tmvars...), foldmasks)]
        checks = foldr(1:length(chunks), init = :(true)) do ci, rest
            (; offset, iT) = chunks[ci]
            posexpr = :(pos + $(minoptlen + offset))
            load = load_word(iT, posexpr)
            check = :($load | $(tmvars[ci]) == $(tvars[ci]))
            rest == :(true) ? check : :($check && $rest)
        end
        ExprVarLine[destructure..., :(found = $checks)]
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
                       ctx::Base.ImmutableDict{Symbol, Any},
                       options::Vector{Any})
    all(o -> o isa String, options) || throw(ArgumentError("Expected all options to be strings for choice"))
    soptions = Vector{String}(options)
    allowempty = any(isempty, soptions)
    allowempty && filter!(!isempty, soptions)
    casefold = get(ctx, :casefold, true)
    target = get(ctx, :is, nothing)::Union{Nothing, String}
    fieldvar = get(ctx, :fieldvar, gensym("prefix"))
    option = get(ctx, :optional, nothing)
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
        # Collect matcher expressions, skipping absent optional parts
        parts = ExprVarLine[resolve_i...]
        if variable_len
            optlencheck = defid_lengthcheck(ctx, :optlen, minoptlen, maximum(ncodeunits, matchoptions))
            push!(parts,
                  :(if found
                        optlen = $(optlens)[i]
                        found = $optlencheck
                    end))
        end
        if !isempty(vt.chunks)
            ve = gen_verify_exprs(vt, fieldvar)
            push!(parts,
                  :(if found
                        $(ve.destructure...)
                        found = $(ve.checks)
                    end))
        end
        if variable_len
            push!(parts, tailcheck)
        end
        push!(parts,
              :(if found
                    pos += $(if variable_len; :optlen else minoptlen end)
                    $foundaction
                end))
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
        :(return ($"Expected one of $(join(soptions, ", "))", pos))
    else
        :($option = false)
    end
    minoptbytes = minimum(ncodeunits, soptions)
    lencheck = defid_lengthcheck(ctx, minoptbytes)
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
        nbits = (ctx[:bits][] += choicebits)
        ctx[:print_bytes_min][] += minimum(ncodeunits, soptions)
        ctx[:print_bytes_max][] += maximum(ncodeunits, soptions)
        ctx[:parsed_bytes_min][] += minimum(ncodeunits, soptions)
        ctx[:parsed_bytes_max][] += maximum(ncodeunits, soptions)
        push!(exprs.parse,
              :($fieldvar = zero($choiceint)),
              checkedmatch,
              defid_orshift(ctx, choiceint, fieldvar, nbits))
        fextract = :($fieldvar = $(defid_fextract(ctx, nbits, choicebits)))
        push!(ctx[:segments], (choicebits, :choice, Symbol(chopprefix(String(fieldvar), "attr_")),
                               join(soptions, " | ")))
        if isnothing(option)
            push!(exprs.print, fextract)
        else
            push!(ctx[:oprint_detect], fextract, :($option = !iszero($fieldvar)))
        end
        push!(exprs.print,
              :(print(io, @inbounds $(Tuple(soptions))[$fieldvar])),
              :(__segment_printed = $(length(ctx[:segments]))))
        if haskey(ctx, :fieldvals)
            symoptions = Tuple(Symbol.(soptions))
            push!(ctx[:fieldvals],
                if isnothing(option)
                    :($fextract; @inbounds $(symoptions)[$fieldvar])
                else
                    :($fextract; if !iszero($fieldvar) @inbounds $(symoptions)[$fieldvar] end)
                end)
        end
    else
        if any(isempty, soptions)
            push!(exprs.parse, matcher)
        else
            push!(exprs.parse,
                  :($fieldvar = zero($choiceint)),
                  checkedmatch)
        end
        ctx[:print_bytes_min][] += ncodeunits(target)
        ctx[:print_bytes_max][] += ncodeunits(target)
        ctx[:parsed_bytes_min][] += minimum(ncodeunits, soptions)
        ctx[:parsed_bytes_max][] += maximum(ncodeunits, soptions)
        push!(ctx[:segments], (0, :choice, Symbol(chopprefix(String(fieldvar), "attr_")),
                               "Choice of literal string \"$(target)\" vs $(join(soptions, ", "))"))
        push!(exprs.print, :(print(io, $target)), :(__segment_printed = $(length(ctx[:segments]))))
    end
    nothing
end


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
    gen_static_stringcomp(str::String, casefold::Bool) -> Vector{Expr}

Generate word-sized match checks for `str` against `idbytes` at `pos`.
Each expression evaluates to `true` on match. When `casefold` is true,
alphabetic bytes are OR-masked with `0x20` before comparison.
"""
function gen_static_stringcomp(str::String, casefold::Bool)
    map(word_chunks(ncodeunits(str))) do (; offset, width, iT)
        value = pack_bytes(str, offset, width, iT)
        foldmask = if casefold
            reduce(|, (iT(ifelse(codeunit(str, offset + j + 1) in UInt8('a'):UInt8('z'), 0x20, 0x00)) << (8j) for j in 0:width-1), init=zero(iT))
        else
            zero(iT)
        end
        posexpr = iszero(offset) ? :pos : :(pos + $offset)
        load = load_word(iT, posexpr)
        if !iszero(foldmask)
            :($load | $foldmask == $value)
        else
            :($load == $value)
        end
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

function defid_literal!(exprs::IdExprs,
                        ctx::Base.ImmutableDict{Symbol, Any},
                        lit::String)
    option = get(ctx, :optional, nothing)
    notfound = if isnothing(option)
        :(return ($"Expected literal '$(lit)'", pos))
    else
        :($option = false)
    end
    casefold = get(ctx, :casefold, true) === true
    if casefold
        all(isascii, lit) || throw(ArgumentError("Expected ASCII string for literal with casefolding"))
    end
    litref = casefold ? lowercase(lit) : lit
    checks = gen_static_stringcomp(litref, casefold)
    mismatch = :(!($(foldl((a, b) -> :($a && $b), checks))))
    litlen = ncodeunits(litref)
    lencheck = defid_lengthcheck(ctx, litlen)
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
    push!(ctx[:segments], (0, :literal, :literal, sprint(show, lit)))
    push!(exprs.print, :(print(io, $lit)), :(__segment_printed = $(length(ctx[:segments]))))
    ctx[:print_bytes_min][] += litlen
    ctx[:print_bytes_max][] += litlen
    ctx[:parsed_bytes_min][] += litlen
    ctx[:parsed_bytes_max][] += litlen
    if haskey(ctx, :fieldvals)
        push!(ctx[:fieldvals],
              if isnothing(option)
                  lit
              else
                  :(if $option; $lit end)
              end)
    end
    nothing
end

function defid_digits!(exprs::IdExprs,
                       ctx::Base.ImmutableDict{Symbol, Any},
                       args::Vector{Any})
    length(args) ∈ (0, 1) || throw(ArgumentError("Expected at most one positional argument for digits, got $(length(args))"))
    base = get(ctx, :base, 10)::Int
    min = get(ctx, :min, 0)::Int
    max = get(ctx, :max, nothing)
    if max isa Expr
        max = Core.eval(ctx[:__module__], max)::Int
    end
    pad = get(ctx, :pad, 0)::Int
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
    option = get(ctx, :optional, nothing)
    range = max - min + 1 + !isnothing(option)
    # Store raw values when it fits in the same bits as offset encoding
    directval = cardbits(range) == cardbits(max) && (min > 0 || isnothing(option))
    dbits = sizeof(typeof(range)) * 8 - leading_zeros(range)
    dI = cardtype(8 * sizeof(typeof(max)) - leading_zeros(max))
    fieldvar = get(ctx, :fieldvar, gensym("digits"))
    bitsconsumed = Symbol("$(fieldvar)_bitsconsumed")
    matchcond = if fixedwidth
        :($bitsconsumed == $maxdigits)
    elseif mindigits > 1
        :($bitsconsumed >= $mindigits)
    else
        :(!iszero($bitsconsumed))
    end
    nbits = (ctx[:bits][] += dbits)
    fixedpad = ifelse(fixedwidth, maxdigits, 0)
    printmin = Base.max(ndigits(Base.max(min, 1); base), pad, fixedpad)
    printmax = Base.max(ndigits(max; base), pad, fixedpad)
    scanlimit = defid_lengthbound(ctx, maxdigits)
    ctx[:print_bytes_min][] += printmin
    ctx[:print_bytes_max][] += printmax
    ctx[:parsed_bytes_min][] += mindigits
    ctx[:parsed_bytes_max][] += maxdigits
    fnum = Symbol("$(fieldvar)_num")
    dT = cardtype(dbits)
    numexpr = if directval
        if dI != dT; :($fnum % $dT) else fnum end
    elseif iszero(min) && !isnothing(option)
        :($fnum + $(one(dT)))
    elseif min - !isnothing(option) > 0
        :(($fnum - $(dT(min - !isnothing(option)))) % $dT)
    else
        if dI != dT; :($fnum % $dT) else fnum end
    end
    rangecheck = if min == 0 && max == base^maxdigits - 1
        :()
    else
        maxcheck = :($fnum <= $max || return ($"Expected at most a value of $(string(max; base, pad))", pos))
        mincheck = :($fnum >= $min || return ($"Expected at least a value of $(string(min; base, pad))", pos))
        if min == 0; maxcheck
        elseif max == base^maxdigits - 1; mincheck
        else :($mincheck; $maxcheck) end
    end
    errmsg = if fixedwidth && maxdigits > 1
        "exactly $maxdigits digits in base $base"
    elseif mindigits > 1
        "$mindigits to $maxdigits digits in base $base"
    else
        "up to $maxdigits digits in base $base"
    end
    directvar = numexpr === fnum
    parsevar = ifelse(directvar, fnum, fieldvar)
    push!(exprs.parse,
          :(($bitsconsumed, $fnum) = parseint($dI, idbytes, pos, $base, $scanlimit)))
    if isnothing(option)
        push!(exprs.parse, :($matchcond || return ($errmsg, pos)))
        rangecheck != :() && push!(exprs.parse, rangecheck)
        directvar || push!(exprs.parse, :($fieldvar = $numexpr))
    else
        push!(exprs.parse,
              :($parsevar = if $matchcond
                    $option = true
                    $rangecheck
                    $numexpr
                else
                    $option = false
                    zero($dT)
                end))
    end
    push!(exprs.parse,
          defid_orshift(ctx, dT, parsevar, nbits),
          :(pos += $(fixedwidth ? maxdigits : bitsconsumed)))
    # --- Extract and print ---
    fextract = :($fnum = $(defid_fextract(ctx, nbits, dbits)))
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
    push!(ctx[:segments], (dbits, :digits, Symbol(chopprefix(String(fieldvar), "attr_")),
                           string(fixedwidth ? "$maxdigits" : "$mindigits-$maxdigits",
                                  isone(maxdigits) ? " digit" : " digits",
                                  base != 10 ? " in base $base" : "",
                                  if min > 0 && max < base^maxdigits - 1
                                      " between $(string(min; base, pad)) and $(string(max; base, pad))"
                                  elseif min > 0
                                      ", at least $(string(min; base, pad))"
                                  elseif max < base^maxdigits - 1
                                      ", at most $(string(max; base, pad))"
                                  else "" end)))
    segsym = :(__segment_printed = $(length(ctx[:segments])))
    if isnothing(option)
        push!(exprs.print, fextract)
    else
        push!(ctx[:oprint_detect], fextract, :($option = !iszero($fnum)))
    end
    directvar || push!(exprs.print, :($fieldvar = $fvalue))
    push!(exprs.print, printex, segsym)
    if haskey(ctx, :fieldvals)
        propvalue = if max < typemax(dI) ÷ 2
            sI = signed(dI)
            :($fvalue % $sI)
        else
            fvalue
        end
        push!(ctx[:fieldvals],
              if isnothing(option)
                  :($fextract; $propvalue)
              else
                  :($fextract; if !iszero($fnum); $propvalue end)
              end)
    end
    nothing
end

function defid_charseq!(exprs::IdExprs,
                        ctx::Base.ImmutableDict{Symbol, Any},
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
    function charseq_ranges(ctx, kind)
        upper = get(ctx, :upper, false)::Bool
        lower = get(ctx, :lower, false)::Bool
        casefold = get(ctx, :casefold, false)::Bool
        upper && lower && throw(ArgumentError("Cannot specify both upper=true and lower=true for $kind"))
        AZ = UInt8('A'):UInt8('Z')
        az = UInt8('a'):UInt8('z')
        d09 = UInt8('0'):UInt8('9')
        singlecase = upper || lower || casefold
        letters = if lower && !upper; (az,) elseif singlecase; (AZ,) else (AZ, az) end
        print_ranges = kind === :letters ? letters : (d09, letters...)
        (; print_ranges, casefold)
    end
    cfg = charseq_ranges(ctx, kind)
    variable = minlen != maxlen
    option = get(ctx, :optional, nothing)
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
    fieldvar = get(ctx, :fieldvar, gensym(string(kind)))
    charvar = Symbol("$(fieldvar)_chars")
    lenvar = Symbol("$(fieldvar)_len")
    cT = cardtype(charbits)
    lT = if variable; cardtype(lenbits) else Nothing end
    ranges = cfg.print_ranges
    cfold = cfg.casefold
    nbits_pos = (ctx[:bits][] += totalbits)
    scanlimit = defid_lengthbound(ctx, maxlen)
    ctx[:print_bytes_min][] += minlen
    ctx[:print_bytes_max][] += maxlen
    ctx[:parsed_bytes_min][] += minlen
    ctx[:parsed_bytes_max][] += maxlen
    # --- Parse ---
    push!(exprs.parse,
          :(($lenvar, $charvar) = parsechars($cT, idbytes, pos, $scanlimit, $ranges, $cfold, $oneindexed)))
    errmsg = if variable
        "Expected $minlen to $maxlen $kind characters"
    else
        "Expected $maxlen $kind characters"
    end
    notfound = if isnothing(option)
        [:(return ($errmsg, pos))]
    else
        [:($option = false), :($charvar = zero($cT)), :($lenvar = 0)]
    end
    if !isnothing(option) && variable && minlen == 0
        push!(exprs.parse,
              :(if $lenvar > 0
                    $option = true
                elseif !@isdefined($option)
                    $option = false
                end))
    else
        if !isnothing(option)
            push!(exprs.parse, :($option = true))
        end
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
          defid_orshift(ctx, cT, charvar, nbits_pos - lenbits - presbits),
          :(pos += $lenvar))
    if variable
        lenpack = if lenbase == 0
            :($lenoffset = $lenvar % $lT)
        else
            :($lenoffset = ($lenvar - $lenbase) % $lT)
        end
        push!(exprs.parse, lenpack,
              defid_orshift(ctx, lT, lenoffset, nbits_pos))
    elseif presbits > 0
        push!(exprs.parse,
              defid_orshift(ctx, Bool, option, nbits_pos))
    end
    # --- Print / extract ---
    fextract_chars = :($charvar = $(defid_fextract(ctx, nbits_pos - lenbits - presbits, charbits)))
    extracts = ExprVarLine[fextract_chars]
    if variable
        fextract_len = if lenbase == 0
            :($lenvar = $(defid_fextract(ctx, nbits_pos, lenbits)))
        else
            :($lenvar = $(defid_fextract(ctx, nbits_pos, lenbits)) + $lenbase)
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
        :(!iszero($(defid_fextract(ctx, nbits_pos, presbits))))
    end
    if !isnothing(option)
        push!(ctx[:oprint_detect], extracts..., :($option = $present))
    else
        append!(exprs.print, extracts)
    end
    push!(exprs.print, printex)
    push!(ctx[:segments],
          (totalbits, kind, Symbol(chopprefix(String(fieldvar), "attr_")),
           string(variable ? "$minlen-$maxlen" : "$maxlen",
                  " ", kind, maxlen > 1 ? " characters" : " character")))
    push!(exprs.print, :(__segment_printed = $(length(ctx[:segments]))))
    # --- Field value ---
    if haskey(ctx, :fieldvals)
        push!(ctx[:fieldvals],
              if isnothing(option)
                  :($(extracts...); $tostringex)
              else
                  :($(extracts...); if $present; $tostringex end)
              end)
    end
    nothing
end

function defid_orshift(ctx::Base.ImmutableDict{Symbol, Any}, type::Type, value::Union{Symbol, Expr}, shift::Int)
    valcast = Expr(:call, :__cast_to_id, type, value)
    :(parsed = Core.Intrinsics.or_int(parsed, Core.Intrinsics.shl_int($valcast, (8 * sizeof($(esc(ctx[:name]))) - $shift))))
end

function defid_fextract(ctx::Base.ImmutableDict{Symbol, Any}, position::Int, width::Int)
    fT = cardtype(width)
    fval = :(Core.Intrinsics.lshr_int(id, 8 * sizeof($(esc(ctx[:name]))) - $position))
    ival = Expr(:call, :__cast_from_id, fT, fval)
    if width == sizeof(fT) * 8
        ival
    else
        fTmask = ~(typemax(fT) << width)
        :($ival & $fTmask)
    end
end

"""
    defid_lengthcheck(ctx, n_expr, [n_min, n_max])

Emit a `__length_check(n_expr, n_min, n_max, parsed_min, parsed_max)` sentinel resolved by
`resolve_length_checks!` once the final parse byte minimum is known.
"""
function defid_lengthcheck(ctx::Base.ImmutableDict{Symbol, Any}, n_expr, n_min::Int=n_expr, n_max::Int=n_min)
    Expr(:call, :__length_check, n_expr, n_min, n_max, ctx[:parsed_bytes_min][], ctx[:parsed_bytes_max][])
end

"""
    defid_lengthbound(ctx, n)

Emit a `__length_bound(n, parsed_min, parsed_max)` sentinel that resolves to
`n` when enough bytes are guaranteed, or `min(n, nbytes - pos + 1)` at runtime.
"""
function defid_lengthbound(ctx::Base.ImmutableDict{Symbol, Any}, n::Int)
    Expr(:call, :__length_bound, n, ctx[:parsed_bytes_min][], ctx[:parsed_bytes_max][])
end

"""
    resolve_length_checks!(exprs, total_parsed_min)

Walk the AST and resolve `__length_check` sentinels. When the total minimum
guarantees enough bytes remain (`total_parsed_min - parsed_max >= n_max`),
the check is statically true; if/elseif branches are simplified accordingly.
Otherwise, the sentinel is replaced with a runtime `nbytes - pos + 1 >= n_expr`.
"""
function resolve_length_checks!(exprlikes::Vector{<:ExprVarLine}, total_parsed_min::Int)
    elided = false
    splice_indices = Int[]
    for (idx, expr) in enumerate(exprlikes)
        expr isa Expr || continue
        result, elided = resolve_length_check_expr!(expr, total_parsed_min, elided)
        if result === :remove
            push!(splice_indices, idx)
        elseif !isnothing(result)
            exprlikes[idx] = result
        end
    end
    deleteat!(exprlikes, splice_indices)
    exprlikes, elided
end

# Resolve __length_check to true or a runtime `nbytes - pos + 1 >= n` expression
function resolve_length_check_value(expr::Expr, total_parsed_min::Int)
    n_expr, n_min, n_max, parsed_min, parsed_max = expr.args[2:end]
    total_parsed_min - parsed_max >= n_max ? true : :(nbytes - pos + 1 >= $n_expr)
end

# Walk and resolve. Returns (replacement, elided) where replacement is
# :remove, a value to splice in (Expr or literal), or nothing (modified in-place).
function resolve_length_check_expr!(expr::Expr, total::Int, elided::Bool)
    # if/elseif with __length_check or !__length_check condition — special
    # handling to fold away the entire branch when statically known
    if expr.head in (:if, :elseif)
        cond = expr.args[1]
        check, negated = if Meta.isexpr(cond, :call) && first(cond.args) === :__length_check
            (cond, false)
        elseif Meta.isexpr(cond, :call, 2) && cond.args[1] === :! &&
               Meta.isexpr(cond.args[2], :call) && first(cond.args[2].args) === :__length_check
            (cond.args[2], true)
        else
            (nothing, false)
        end
        if !isnothing(check)
            val = resolve_length_check_value(check, total)
            if val isa Bool
                # Statically known — keep the taken branch, discard the other
                elided = true
                taken = xor(val, negated)
                promoted = if taken
                    expr.args[2]
                elseif length(expr.args) >= 3
                    elsebranch = expr.args[3]
                    if elsebranch isa Expr && elsebranch.head === :elseif
                        elsebranch.head = :if
                    end
                    elsebranch
                else
                    nothing
                end
                isnothing(promoted) && return :remove, elided
                # Recurse into the promoted branch to resolve any nested sentinels
                if promoted isa Expr
                    result, elided = resolve_length_check_expr!(promoted, total, elided)
                    !isnothing(result) && (promoted = result)
                end
                return promoted, elided
            end
            # Runtime — replace sentinel with actual comparison
            expr.args[1] = negated ? :(nbytes - pos + 1 < $(check.args[2])) : val
        end
    end
    # Recurse into all children, resolving sentinels wherever they appear
    splice_indices = Int[]
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        if Meta.isexpr(arg, :call) && first(arg.args) === :__length_check
            val = resolve_length_check_value(arg, total)
            elided |= val isa Bool
            if val isa Expr
                arg.head, arg.args = val.head, val.args
            else
                expr.args[i] = val
            end
        elseif Meta.isexpr(arg, :call) && first(arg.args) === :__length_bound
            n, parsed_min, parsed_max = arg.args[2:end]
            if total - parsed_max >= n
                elided = true
                expr.args[i] = n
            else
                replacement = :(min($n, nbytes - pos + 1))
                arg.head, arg.args = replacement.head, replacement.args
            end
        else
            result, elided = resolve_length_check_expr!(arg, total, elided)
            if result === :remove
                push!(splice_indices, i)
            elseif !isnothing(result)
                expr.args[i] = result
            end
        end
    end
    deleteat!(expr.args, splice_indices)
    nothing, elided
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

function implement_casting!(ctx::Base.ImmutableDict{Symbol, Any}, exprlikes::Vector{<:ExprVarLine})
    finalsize = cld(ctx[:bits][], 8)
    name = ctx[:name]
    for expr in exprlikes
        expr isa Expr && implement_casting!(expr, name, finalsize)
    end
    exprlikes
end

function defid_parsebytes(pexprs::Vector{ExprVarLine}, ctx::Base.ImmutableDict{Symbol, Any}, name::Symbol)
    parsed_min = ctx[:parsed_bytes_min][]
    resolved, elided = resolve_length_checks!(implement_casting!(ctx, pexprs), parsed_min)
    # Split at __upfront_lengthcheck sentinel, replacing it with the actual check
    errmsg = string("Expected at least ", parsed_min, " bytes")
    split_idx = findfirst(e -> Meta.isexpr(e, :call) && first(e.args) === :__upfront_lengthcheck, resolved)
    if !isnothing(split_idx) && elided
        check = if split_idx > 1
            :(nbytes - pos >= $(parsed_min - 1) || return ($errmsg, 1))
        else
            :(nbytes >= $parsed_min || return ($errmsg, 1))
        end
        resolved[split_idx] = check
    else
        # No leading skips or no elision — remove the sentinel
        !isnothing(split_idx) && deleteat!(resolved, split_idx)
        if elided
            pushfirst!(resolved, :(nbytes >= $parsed_min || return ($errmsg, 1)))
        end
    end
    :(Base.@assume_effects :foldable :nothrow function $(GlobalRef(@__MODULE__, :parsebytes))(::Type{$(esc(name))}, idbytes::AbstractVector{UInt8})
          parsed = $(if ctx[:bits][] <= 8
                         :(Core.bitcast($(esc(ctx[:name])), 0x00))
                     else
                         :(Core.Intrinsics.zext_int($(esc(ctx[:name])), 0x0))
                     end)
          pos = 1
          nbytes = length(idbytes)
          $(resolved...)
          (parsed, pos)
      end)
end

function defid_parseid(ctx::Base.ImmutableDict{Symbol, Any}, name::Symbol)
    :(function $(GlobalRef(@__MODULE__, :parseid))(::Type{$(esc(name))}, id::SubString)
          result, pos = parsebytes($(esc(name)), codeunits(id))
          if result isa $(esc(name))
              pos > ncodeunits(id) || return MalformedIdentifier{$(esc(name))}(id, "Unparsed trailing content")
              return result
          end
          MalformedIdentifier{$(esc(name))}(id, result)
      end)
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

function defid_shortcode(pexprs::Vector{ExprVarLine}, ctx::Base.ImmutableDict{Symbol, Any}, name::Symbol)
    maxbytes = ctx[:print_bytes_max][]
    minbytes = ctx[:print_bytes_min][]
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

function defid_properties(pexprs::Vector{Pair{Symbol, Vector{ExprVarLine}}}, ctx::Base.ImmutableDict{Symbol, Any}, name::Symbol)
    isempty(pexprs) && return :()
    # Build the if/elseif chain from the bottom up: innermost elseif first, outermost if last
    fallback = :(throw(FieldError($(esc(name)), prop)))
    clauses = foldr(enumerate(pexprs), init = fallback) do (i, (prop, exprs)), rest
        qprop = QuoteNode(prop)
        body = Expr(:block, implement_casting!(ctx, exprs)...)
        Expr(ifelse(i == 1, :if, :elseif), :(prop === $qprop), body, rest)
    end
    :(function $(GlobalRef(Base, :getproperty))(id::$(esc(name)), prop::Symbol)
          $clauses
      end)
end

function defid_segments_type(ctx::Base.ImmutableDict{Symbol, Any}, name::Symbol)
    segments = ctx[:segments]
    isempty(segments) && return :()
    :(function $(GlobalRef(@__MODULE__, :segments))(::Type{$(esc(name))})
          $(Expr(:tuple, [(; nbits, kind, label, desc) for (; nbits, kind, label, desc) in segments if nbits > 0]...))
      end)
end

function defid_segments_value(ctx::Base.ImmutableDict{Symbol, Any}, pexprs::Vector{ExprVarLine}, name::Symbol)
    function print_segsets!(segvars::Vector{Tuple{Int, Symbol}}, expr::ExprVarLine)
        expr isa Expr || return expr
        if Meta.isexpr(expr, :(=)) && first(expr.args) === :__segment_printed
            _, i = expr.args
            # We should never see i+1 before i
            if i > length(segvars)
                anon = ctx[:segments][i].nbits == 0
                precount = sum((s.nbits > 0 for s in ctx[:segments][1:i-1]), init = 0)
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
    segments = ctx[:segments]
    isempty(segments) && return :()
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

function defid_make(exprs::IdExprs, ctx::Base.ImmutableDict{Symbol, Any}, name::Symbol)
    block = Expr(:toplevel)
    numbits = 8 * cld(ctx[:bits][], 8)
    prefix = get(ctx, :purlprefix, nothing)
    implement_casting!(ctx, exprs.print)
    push!(block.args,
          :(Base.@__doc__(primitive type $(esc(name)) <: $AbstractIdentifier $numbits end)),
          :($(GlobalRef(@__MODULE__, :nbits))(::Type{$(esc(name))}) = $(ctx[:bits][])),
          defid_parsebytes(exprs.parse, ctx, name),
          defid_parseid(ctx, name),
          defid_shortcode(exprs.print, ctx, name),
          :($(GlobalRef(Base, :propertynames))(::$(esc(name))) = $(Tuple(map(first, exprs.properties)))),
          defid_properties(exprs.properties, ctx, name),
          defid_segments_type(ctx, name),
          defid_segments_value(ctx, exprs.print, name),
          :($(GlobalRef(Base, :isless))(a::$(esc(name)), b::$(esc(name))) =
                Core.Intrinsics.ult_int(a, b)))
    if !isnothing(prefix)
        push!(block.args,
              :($(GlobalRef(@__MODULE__, :purlprefix))(::Type{$(esc(name))}) = $prefix))
    end
    push!(block.args, esc(name))
    block
end
