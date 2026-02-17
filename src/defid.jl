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
    defid_dispatch!(exprs, ctx, pattern)
    defid_make(exprs, ctx, name)
end

@static if VERSION < v"1.13-"
    takestring(io::IO) = String(take!(io))
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

const ALL_KNOWN_KEYS = Tuple(collect(Iterators.flatten(values(KNOWN_KEYS))))

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
    end
end

function defid_field!(exprs::IdExprs,
                      ctx::Base.ImmutableDict{Symbol, Any},
                      node::QuoteNode,
                      args::Vector{Any})
    isnothing(get(ctx, :fieldvar, nothing)) || throw(ArgumentError("Fields may not be nested"))
    fieldvals = Expr[]
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :fieldvar, Symbol("attr_$(node.value)"))
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :fieldvals, fieldvals)
    initialprints = length(exprs.print)
    for arg in args
        defid_dispatch!(exprs, ctx, arg)
    end
    if length(fieldvals) == 0
        throw(ArgumentError("Field $(node.value) does not capture any value"))
    elseif length(fieldvals) == 1
        push!(exprs.properties, node.value => fieldvals[1].args)
    else
        push!(exprs.properties, node.value => (
            quote
                io = IOBuffer()
                $(exprs.print[initialprints+1:end]...)
                :(takestring!(io))
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
    saved_min = ctx[:print_bytes_min][]
    if all(a -> a isa String, args)
        defid_choice!(oexprs, ctx, push!(Any[join(Vector{String}(args))], ""))
    else
        for arg in args
            defid_dispatch!(oexprs, ctx, arg)
        end
    end
    ctx[:print_bytes_min][] = saved_min
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
- `order`: permutation of options matching hash output order
- `kind`: `:direct` (no table), `:offset` (subtract constant), or `:table`
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
                best = result.ph
                best_tier = result.tier
                best_tier <= 1 && break
            end
        end
    end
    best
end

function hash_families(iT::DataType, nopts::Int)
    families = @NamedTuple{fn::Function, expr::Function}[]
    # v (identity — simplest possible hash, produces v - offset when consecutive)
    push!(families, (fn = v -> v, expr = v -> v))
    for m in nopts:2*nopts
        # v % m + 1
        push!(families, (fn = v -> v % m + 1,
                         expr = v -> :($v % $m + 1)))
        # (v >> k) % m + 1
        for k in 1:min(8 * sizeof(iT) - 1, 16)
            push!(families, (fn = v -> (v >> k) % m + 1,
                             expr = v -> :(($v >> $k) % $m + 1)))
        end
        # (v * c) >> k % m + 1
        for c in (0x9e3779b97f4a7c15, 0x517cc1b727220a95, 0x6c62272e07bb0142)
            for k in max(1, 8 * sizeof(iT) - 8):8 * sizeof(iT) - 1
                push!(families, (fn = v -> (v * c) >> k % m + 1,
                                 expr = v -> :((($v * $(c % iT)) >> $k) % $m + 1)))
            end
        end
    end
    families
end

function classify_hash(hvals::Vector{UInt64}, nopts::Int, options::Vector{String},
                        pos::Int, iT::DataType, foldmask, hashexpr_fn)
    sorted_indices = sortperm(hvals)
    sorted_hvals = hvals[sorted_indices]
    order = options[sorted_indices]
    lo, hi = Int(sorted_hvals[1]), Int(sorted_hvals[end])
    # Tier 1: consecutive values — hashexpr(v) ± offset maps to 1:n
    if hi - lo + 1 == nopts
        if lo == 1
            # Already 1:n, no offset needed
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
    # Tier 1b: consecutive descending
    rsorted_indices = sortperm(hvals, rev=true)
    rsorted_hvals = hvals[rsorted_indices]
    if Int(rsorted_hvals[1]) - Int(rsorted_hvals[end]) + 1 == nopts
        top = iT(rsorted_hvals[1] + 1)
        ph = (; pos, iT, foldmask,
               hashexpr = v -> :($top - $(hashexpr_fn(v))),
               perm = rsorted_indices, kind = :direct,
               table = (), tablelen = 0)
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
returning `(; verify_table, foldmasks, chunk_types, chunk_positions)` where:
- `verify_table`: `NTuple{N, NTuple{C, UInt}}` — per-option expected values for each chunk
- `foldmasks`: `NTuple{C, UInt}` — casefold OR masks for each chunk
- `chunk_types`: `Vector{DataType}` — integer type for each chunk load
- `chunk_positions`: `Vector{Int}` — byte position for each chunk load
"""
function gen_verify_table(options::Vector{String}, casefold::Bool)
    chunks = word_chunks(minimum(ncodeunits, options))
    verify_table = Tuple(Tuple(pack_bytes(opt, c.offset, c.width, c.iT) for c in chunks) for opt in options)
    foldmasks = Tuple(
        if casefold
            reduce(|, (c.iT(ifelse(any(opt -> codeunit(opt, c.offset + j + 1) in 0x61:0x7a, options), 0x20, 0x00)) << (8j) for j in 0:c.width-1), init=zero(c.iT))
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
                reduce(|, (c.iT(ifelse(any(t -> codeunit(t, c.offset + j + 1) in 0x61:0x7a, nonempty_tails), 0x20, 0x00)) << (8j) for j in 0:c.width-1), init=zero(c.iT))
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
            :(idbytes[pos + $minoptlen + j - 1] | 0x20)
        else
            :(idbytes[pos + $minoptlen + j - 1])
        end
        ExprVarLine[:(tailbytes = $tailtable[i]),
                     :(for j in 1:$taillenst[i]
                           if $loadbyte != tailbytes[j]
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
        vt = gen_verify_table(matchoptions, casefold)
        ve = gen_verify_exprs(vt, fieldvar)
        minoptlen = minimum(ncodeunits, matchoptions)
        variable_len = minoptlen != maximum(ncodeunits, matchoptions)
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
            push!(parts,
                  :(if found
                        optlen = $(optlens)[i]
                        found = nbytes - pos + 1 >= optlen
                    end))
        end
        push!(parts,
              :(if found
                    $(ve.destructure...)
                    found = $(ve.checks)
                end))
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
        loadbyte = casefold ? :(idbytes[pos + j - 1] | 0x20) : :(idbytes[pos + j - 1])
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
    checkedmatch = if allowempty
        :(if nbytes - pos + 1 >= $(minimum(ncodeunits, soptions))
              $(matcher...)
              if $fieldvar == zero($choiceint)
                  $notfound
              end
          end)
    else
        :(if nbytes - pos + 1 < $(minimum(ncodeunits, soptions))
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
        push!(exprs.parse,
              :($fieldvar = zero($choiceint)),
              checkedmatch,
              defid_orshift(ctx, choiceint, fieldvar, nbits))
        fextract = :($fieldvar = $(defid_fextract(ctx, nbits, choicebits)))
        push!(ctx[:segments], (choicebits, :choice, Symbol(chopprefix(String(fieldvar), "attr_")),
                               join(soptions, " | ")))
        if isnothing(option)
            push!(exprs.print,
                  fextract,
                  :(print(io, @inbounds $(Tuple(soptions))[$fieldvar])),
                  :(__segment_printed = $(length(ctx[:segments]))))
        else
            push!(ctx[:oprint_detect],
                fextract,
                :($option = !iszero($fieldvar)))
            push!(exprs.print,
                  :(print(io, @inbounds $(Tuple(soptions))[$fieldvar])),
                  :(__segment_printed = $(length(ctx[:segments]))))
        end
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
        push!(ctx[:segments], (0, :choice, Symbol(chopprefix(String(fieldvar), "attr_")),
                               "Choice of literal string \"$(target)\" vs $(join(soptions, ", "))"))
        push!(exprs.print, :(print(io, $target)), :(__segment_printed = $(length(ctx[:segments]))))
    end
    nothing
end


"""Generate an expression to load a value of type `iT` from `idbytes` at `posexpr`."""
function load_word(iT::DataType, posexpr::Union{Symbol, Expr})
    if iT === UInt8
        :(idbytes[$posexpr])
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

Generate word-sized mismatch checks for `str` against `idbytes` at `pos`.
Each expression evaluates to `true` on mismatch. When `casefold` is true,
alphabetic bytes are OR-masked with `0x20` before comparison.
"""
function gen_static_stringcomp(str::String, casefold::Bool)
    map(word_chunks(ncodeunits(str))) do (; offset, width, iT)
        value = pack_bytes(str, offset, width, iT)
        foldmask = if casefold
            reduce(|, (iT(ifelse(codeunit(str, offset + j + 1) in 0x61:0x7a, 0x20, 0x00)) << (8j) for j in 0:width-1), init=zero(iT))
        else
            zero(iT)
        end
        posexpr = iszero(offset) ? :pos : :(pos + $offset)
        load = load_word(iT, posexpr)
        if !iszero(foldmask)
            :($load | $foldmask != $value)
        else
            :($load != $value)
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
    # Group by length, longest first
    groups = Dict{Int, Vector{String}}()
    for p in prefixes
        push!(get!(Vector{String}, groups, ncodeunits(p)), p)
    end
    lengths = sort!(collect(keys(groups)), rev=true)
    # Build one branch per length group
    branches = map(lengths) do nb
        grp = groups[nb]
        # Inner if/elseif for same-length alternatives
        inner = gen_lchop_match(last(grp), nb, casefold)
        for i in length(grp)-1:-1:1
            alt = gen_lchop_match(grp[i], nb, casefold)
            inner = Expr(:elseif, alt.args[1], alt.args[2], inner)
        end
        :(if nbytes - pos + 1 >= $nb
              $inner
          end)
    end
    # Chain length groups into if/elseif
    result = branches[end]
    for i in length(branches)-1:-1:1
        br = branches[i]
        result = Expr(:if, br.args[1], br.args[2], result)
    end
    result
end

function gen_lchop_match(prefix::String, nb::Int, casefold::Bool)
    checks = gen_static_stringcomp(prefix, casefold)
    mismatch = foldl((a, b) -> :($a || $b), checks)
    :(if !($mismatch)
          pos += $nb
      end)
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
    mismatch = foldl((a, b) -> :($a || $b), checks)
    litlen = ncodeunits(litref)
    if isnothing(option)
        push!(exprs.parse,
              :(if nbytes - pos + 1 < $litlen
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
                     if nbytes - pos + 1 < $litlen
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
    ctx[:print_bytes_min][] += ncodeunits(lit)
    ctx[:print_bytes_max][] += ncodeunits(lit)
    if haskey(ctx, :fieldvals)
        push!(ctx[:fieldvals],
              if isnothing(option)
                  :($lit)
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
    ctx[:print_bytes_min][] += printmin
    ctx[:print_bytes_max][] += printmax
    fnum = Symbol("$(fieldvar)_num")
    dT = cardtype(dbits)
    numexpr = if iszero(min) && !isnothing(option)
        :($fnum + $(one(dT)))
    elseif min - !isnothing(option) > 0
        offset = dT(min - !isnothing(option))
        :(($fnum - $offset) % $dT)
    else
        fnum
    end
    if dI != dT
        numexpr = :($numexpr % $dT)
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
    push!(exprs.parse,
          :(($bitsconsumed, $fnum) = parseint($dI, idbytes, pos, $base, min($maxdigits, nbytes - pos + 1))))
    if isnothing(option)
        push!(exprs.parse, :($matchcond || return ($errmsg, pos)))
        rangecheck != :() && push!(exprs.parse, rangecheck)
        push!(exprs.parse, :($fieldvar = $numexpr))
    else
        push!(exprs.parse,
              :($fieldvar = if $matchcond
                    $option = true
                    $rangecheck
                    $numexpr
                else
                    $option = false
                    zero($dT)
                end))
    end
    push!(exprs.parse,
          defid_orshift(ctx, dT, fieldvar, nbits),
          :(pos += $(fixedwidth ? maxdigits : bitsconsumed)))
    # --- Extract and print ---
    fextract = :($fnum = $(defid_fextract(ctx, nbits, dbits)))
    fvalue = if dI == dT; fnum else :($fnum % $dI) end
    if iszero(min) && !isnothing(option)
        fvalue = :($fvalue - $(one(dI)))
    elseif min - !isnothing(option) > 0
        fvalue = :(($fvalue + $(dI(min - !isnothing(option)))) % $dI)
    end
    printpad = if fixedwidth && maxdigits > 1; maxdigits
    elseif pad > 0; pad
    else 0 end
    printex = if printpad > 0
        :(print(io, string($fieldvar, base=$base, pad=$printpad)))
    elseif base == 10
        :(print(io, $fieldvar))
    else
        :(print(io, string($fieldvar, base=$base)))
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
    if isnothing(option)
        push!(exprs.print,
              fextract, :($fieldvar = $fvalue), printex,
              :(__segment_printed = $(length(ctx[:segments]))))
    else
        push!(ctx[:oprint_detect],
              fextract, :($option = !iszero($fnum)))
        push!(exprs.print,
              :(if $option
                    $fieldvar = $fvalue
                    $printex
                    __segment_printed = $(length(ctx[:segments]))
                end))
    end
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

function charseq_config(ctx::Base.ImmutableDict{Symbol, Any}, kind::Symbol)
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
    nvals = sum(length, print_ranges)
    (; print_ranges, casefold, nvals)
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
    cfg = charseq_config(ctx, kind)
    variable = minlen != maxlen
    bpc = cardbits(cfg.nvals)
    charbits = maxlen * bpc
    lenbits = variable ? cardbits(maxlen - minlen + 1) : 0
    totalbits = charbits + lenbits
    option = get(ctx, :optional, nothing)
    if !isnothing(option) && !variable
        totalbits += 1
    end
    fieldvar = get(ctx, :fieldvar, gensym(string(kind)))
    charvar = Symbol("$(fieldvar)_chars")
    lenvar = Symbol("$(fieldvar)_len")
    cT = cardtype(charbits)
    lT = variable ? cardtype(lenbits) : Nothing
    ranges = cfg.print_ranges
    cfold = cfg.casefold
    nbits_pos = (ctx[:bits][] += totalbits)
    ctx[:print_bytes_min][] += minlen
    ctx[:print_bytes_max][] += maxlen
    # --- Parse ---
    push!(exprs.parse,
          :(($lenvar, $charvar) = parsechars($cT, idbytes, pos, min($maxlen, nbytes - pos + 1), $ranges, $cfold)))
    notfound = if isnothing(option)
        :(return ($"Expected $(variable ? "$minlen to $maxlen" : "$maxlen") $kind characters", pos))
    else
        :($option = false)
    end
    push!(exprs.parse,
          :(if $lenvar < $minlen; $notfound end))
    if !variable
        push!(exprs.parse,
              :(if $lenvar != $maxlen; $notfound end))
    end
    push!(exprs.parse,
          defid_orshift(ctx, cT, charvar, nbits_pos - lenbits),
          :(pos += $lenvar))
    if variable
        lenoffset = Symbol("$(fieldvar)_lenoff")
        push!(exprs.parse,
              :($lenoffset = ($lenvar - $minlen) % $lT),
              defid_orshift(ctx, lT, lenoffset, nbits_pos))
    end
    # --- Print ---
    fextract_chars = :($charvar = $(defid_fextract(ctx, nbits_pos - lenbits, charbits)))
    if variable
        fextract_len = :($lenvar = $(defid_fextract(ctx, nbits_pos, lenbits)) + $minlen)
        push!(exprs.print,
              fextract_chars, fextract_len,
              :(printchars(io, $charvar, Int($lenvar), $ranges)))
    else
        push!(exprs.print,
              fextract_chars,
              :(printchars(io, $charvar, $maxlen, $ranges)))
    end
    push!(ctx[:segments],
          (totalbits, kind, Symbol(chopprefix(String(fieldvar), "attr_")),
           string(variable ? "$minlen-$maxlen" : "$maxlen",
                  " ", kind, maxlen > 1 ? " characters" : " character")))
    push!(exprs.print, :(__segment_printed = $(length(ctx[:segments]))))
    # --- Field value ---
    if haskey(ctx, :fieldvals)
        fvblock = if variable
            :($fextract_chars; $fextract_len; chars2string($charvar, Int($lenvar), $ranges))
        else
            :($fextract_chars; chars2string($charvar, $maxlen, $ranges))
        end
        push!(ctx[:fieldvals], fvblock)
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
    :(function $(GlobalRef(@__MODULE__, :parsebytes))(::Type{$(esc(name))}, idbytes::AbstractVector{UInt8})
          parsed = $(if ctx[:bits][] <= 8
                         :(Core.bitcast($(esc(ctx[:name])), 0x00))
                     else
                         :(Core.Intrinsics.zext_int($(esc(ctx[:name])), 0x0))
                     end)
          pos = 1
          nbytes = length(idbytes)
          $(implement_casting!(ctx, pexprs)...)
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
                       ranges::NTuple{N, UnitRange{UInt8}}) where {P <: Unsigned, N}
    nvals = sum(length, ranges)
    bpc = cardbits(nvals)
    topshift = 8 * sizeof(P) - bpc
    packed <<= 8 * sizeof(P) - nchars * bpc
    @inbounds for _ in 1:nchars
        idx = UInt8(packed >> topshift)
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
        0x30 + d % UInt8
    elseif base <= 36
        0x57 + d % UInt8  # 'a' - 10
    else
        db = d % UInt8
        ifelse(db < 36, 0x57 + db, 0x3d + db)  # 'a' - 10 / 'A' - 36
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
        buf[i] = 0x30
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
    implement_casting!(ctx, bufexprs)
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
    clauses = nothing
    currentif = nothing
    for (prop, exprs) in pexprs
        qprop = QuoteNode(prop)
        if isnothing(currentif)
            clauses = Expr(:if, :(prop === $qprop), Expr(:block, implement_casting!(ctx, exprs)...))
            currentif = clauses
        else
            nextif = Expr(:elseif,:(prop === $qprop), Expr(:block, implement_casting!(ctx, exprs)...))
            push!(currentif.args, nextif)
            currentif = nextif
        end
    end
    push!(currentif.args, :(throw(FieldError($(esc(name)), prop))))
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
    block = Expr(:block) # :toplevel
    numbits = 8 * cld(ctx[:bits][], 8)
    prefix = get(ctx, :purlprefix, nothing)
    stripname = get(ctx, :stripname, true)::Bool
    skipprefixes = String[]
    !isnothing(prefix) && push!(skipprefixes, lowercase(prefix))
    stripname && push!(skipprefixes, lowercase(string(name)) * ":")
    if !isempty(skipprefixes)
        pushfirst!(exprs.parse, gen_static_lchop(skipprefixes, casefold=true))
    end
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
