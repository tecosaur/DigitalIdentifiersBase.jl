# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

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
- `digits([digits], [base=10, min=0, max=base^digits-1, zfill=false, pad=0])`:
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
    ctx = Base.ImmutableDict{Symbol, Any}(ctx, :print_byte_estimate, Ref(0))
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

const ExprVarLine = Union{Expr, Symbol, LineNumberNode}
const IdExprs = @NamedTuple{parse::Vector{ExprVarLine},
                            print::Vector{ExprVarLine},
                            properties::Vector{Pair{Symbol, Vector{ExprVarLine}}}}

const IdSegment = @NamedTuple{nbits::Int, kind::Symbol, label::Symbol, desc::String}

const KNOWN_KEYS = (
    choice = (:casefold, :is),
    digits = (:base, :min, :max, :pad, :zfill),
    skip = (:casefold, :print),
    _global = (:prefix,)
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
    elseif node === :alphnum
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
                $(if VERSION >= v"1.13"
                      :(takestring!(io))
                  else
                      :(String(take!(io)))
                  end)
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
    if all(a -> a isa String, args)
        defid_choice!(oexprs, ctx, push!(Any[join(Vector{String}(args))], ""))
    else
        for arg in args
            defid_dispatch!(oexprs, ctx, arg)
        end
    end
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
    sargs = Vector{String}(args)
    if get(ctx, :casefold, true) === true
        all(isascii, sargs) || throw(ArgumentError("Expected all arguments to be ASCII strings for skip with casefolding"))
        push!(exprs.parse, :((_, id) = lchopfolded(id, $(Tuple(map(lowercase, sargs))))))
    else
        push!(exprs.parse, :(for prefix in $(Tuple(sargs))
                                 id = chopprefix(id, prefix)
                             end))
    end
    pval = get(ctx, :print, nothing)
    if !isnothing(pval)
        push!(ctx[:segments], (0, :skip, :skip, "Skipped literal string \"$(join(sargs, ", "))\""))
        push!(exprs.print, :(print(io, $pval)), :(__segment_printed = $(length(ctx[:segments]))))
        ctx[:print_byte_estimate][] += ncodeunits(pval)
    end
    nothing
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
    diffbytes = Int[]
    for p in 1:minimum(ncodeunits, soptions)
        push!(diffbytes, length(unique(codeunit(s, p) for s in soptions)))
    end
    mostdiscriminatingbyte = argmax(diffbytes)
    fieldvar = get(ctx, :fieldvar, gensym("prefix"))
    option = get(ctx, :optional, nothing)
    choicebits = cardbits(length(soptions) + !isnothing(option))
    choiceint = if isnothing(target)
        cardtype(choicebits)
    else
        Bool
    end
    foundaction = if isnothing(target)
        :($fieldvar = i % $choiceint)
    else
        push!(soptions, target)
        :($fieldvar = one($fieldvar))
    end
    matcher = if casefold
        all(isascii, soptions) || throw(ArgumentError("Expected all options to be ASCII strings for casefolding"))
        :(@inbounds for (i, prefix) in enumerate($(map(lowercase, soptions)))
              codeunit(id, $mostdiscriminatingbyte) | 0x20 == codeunit(prefix, $mostdiscriminatingbyte) || continue
              found, id = lchopfolded(id, prefix)
              if found
                  $foundaction
                  break
              end
          end)
    else
        :(@inbounds for (i, prefix) in enumerate($(soptions))
              codeunit(id, $mostdiscriminatingbyte) == codeunit(prefix, $mostdiscriminatingbyte) || continue
              found = true
              for j in 1:ncodeunits(prefix)
                  if codeunit(id, j) != codeunit(prefix, j)
                      found = false
                      break
                  end
              end
              if found
                  $foundaction
                  id = unsafe_substr(id, ncodeunits(prefix))
                  break
              end
          end)
    end
    notfound = if isnothing(option)
        :(return MalformedIdentifier{$(esc(ctx[:name]))}(id, $"Expected one of $(join(soptions, ", "))"))
    else
        :($option = false)
    end
    checkedmatch = if allowempty
        :(if ncodeunits(id) >= $(minimum(ncodeunits, soptions))
              $matcher
              if $fieldvar == zero($choiceint)
                  $notfound
              end
          end)
    else
        :(if ncodeunits(id) < $(minimum(ncodeunits, soptions))
              $notfound
          else
              $matcher
              if $fieldvar == zero($choiceint)
                  $notfound
              end
          end)
    end
    if isnothing(target)
        nbits = (ctx[:bits][] += choicebits)
        ctx[:print_byte_estimate][] += maximum(ncodeunits, soptions)
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
            push!(ctx[:fieldvals],
                if isnothing(option)
                    :($fextract; @inbounds $(Tuple(soptions))[$fieldvar])
                else
                    :($fextract; if !iszero($fieldvar) @inbounds $(Tuple(soptions))[$fieldvar] end)
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
        ctx[:print_byte_estimate][] += ncodeunits(target)
        push!(ctx[:segments], (0, :choice, Symbol(chopprefix(String(fieldvar), "attr_")),
                               "Choice of literal string \"$(target)\" vs $(join(soptions, ", "))"))
        push!(exprs.print, :(print(io, $target)), :(__segment_printed = $(length(ctx[:segments]))))
    end
    nothing
end

function defid_literal!(exprs::IdExprs,
                        ctx::Base.ImmutableDict{Symbol, Any},
                        lit::String)
    option = get(ctx, :optional, nothing)
    notfound = if isnothing(option)
        :(return MalformedIdentifier{$(esc(ctx[:name]))}(id, $"Expected literal '$(lit)'"))
    else
        :($option = false)
    end
    # TODO: implement optimised single-character literal parsing
    checkchar, litref = if get(ctx, :casefold, true) === true
        all(isascii, lit) || throw(ArgumentError("Expected ASCII string for literal with casefolding"))
        :(codeunit(id, i) | 0x20 == c), lowercase(lit)
    else
        :(codeunit(id, i) == c), lit
    end
    if isnothing(option)
        push!(exprs.parse,
              :(if ncodeunits(id) < $(ncodeunits(litref))
                    $notfound
                else
                    @inbounds(for (i, c) in enumerate($(Tuple(codeunits(litref))))
                                  if !($checkchar)
                                      $notfound
                                  end
                              end)
                end),
              :(id = unsafe_substr(id, $(ncodeunits(litref)))))
    else
        litvar = gensym("literal")
        append!(exprs.parse,
                (quote
                     $litvar = true
                     if ncodeunits(id) < $(ncodeunits(litref))
                         $litvar = false
                         $notfound
                     else
                         @inbounds(for (i, c) in enumerate($(Tuple(codeunits(litref))))
                                       if !($checkchar)
                                           $litvar = false
                                           $notfound
                                           break
                                       end
                                   end)
                     end
                     if $litvar
                         id = unsafe_substr(id, $(ncodeunits(litref)))
                     end
                 end).args)
    end
    push!(ctx[:segments], (0, :literal, :literal, sprint(show, lit)))
    push!(exprs.print, :(print(io, $lit)), :(__segment_printed = $(length(ctx[:segments]))))
    ctx[:print_byte_estimate][] += ncodeunits(lit)
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
    length(args) ∈ (0, 1) ||throw(ArgumentError("Expected at most one positional argument for digits, got $(length(args))"))
    base = get(ctx, :base, 10)::Int
    min = get(ctx, :min, 0)::Int
    max = get(ctx, :max, nothing)
    if max isa Expr
        max = Core.eval(ctx[:__module__], max)::Int
    end
    pad = get(ctx, :pad, 0)::Int
    zfill = get(ctx, :zfill, false)::Bool
    digits = if isempty(args) && isnothing(max)
        throw(ArgumentError("Must specify either a digits argument or a max argument for digits to know how many bits of information should be allocated"))
    elseif !isnothing(max)
        ndigits(max, base=base)
    elseif first(args) isa Integer
        first(args)
    else
        throw(ArgumentError("Expected a single numerical argument for digits specifying the number of digits, got $(first(args))"))
    end
    if isnothing(max)
        max = (base^digits) - 1
    end
    option = get(ctx, :optional, nothing)
    range = max - min + 1 + !isnothing(option)
    dbits = sizeof(typeof(range)) * 8 - leading_zeros(range)
    dI = cardtype(8 * sizeof(typeof(max)) - leading_zeros(max))
    fieldvar = get(ctx, :fieldvar, gensym("digits"))
    bitsconsumed = Symbol("$(fieldvar)_bitsconsumed")
    matchcond = if zfill
        :($bitsconsumed == $digits)
    else
        :(!iszero($bitsconsumed))
    end
    nbits = (ctx[:bits][] += dbits)
    ctx[:print_byte_estimate][] += ndigits(max; base)
    fnum = Symbol("$(fieldvar)_num")
    numexpr = if iszero(min) && !isnothing(option)
        :($fnum + 0x1)
    elseif min - !isnothing(option) > 0
        :($fnum - $(min - !isnothing(option)))
    else
        fnum
    end
    if dI != cardtype(dbits)
        numexpr = :($numexpr % $(cardtype(dbits)))
    end
    rangecheck = if min == 0 && max == base^digits - 1
        :()
    else
        maxcheck = :($fnum <= $max ||return MalformedIdentifier{$(esc(ctx[:name]))}(id, $"Expected at most a value of $(string(max; base, pad))"))
        mincheck = :($fnum >= $min ||return MalformedIdentifier{$(esc(ctx[:name]))}(id, $"Expected at least a value of $(string(min; base, pad))"))
        if min == 0
            maxcheck
        elseif max == base^digits - 1
            mincheck
        else
            :($mincheck; $maxcheck)
        end
    end
    push!(exprs.parse,
          :(($bitsconsumed, $fnum) = parseint($dI, id, $base, min($digits, ncodeunits(id)))),
          if isnothing(option)
              :($matchcond || return MalformedIdentifier{$(esc(ctx[:name]))}(
                  id, $"Expected $(if zfill "$digits digits with leading zeros" else "up to $digits digits" end) in base $base");
                $rangecheck;
                $fieldvar = $numexpr)
          else
              :($fieldvar = if $matchcond
                    $option = true
                    $rangecheck
                    $numexpr
                else
                    $option = false
                    zero($(cardtype(dbits)))
                end)
          end,
          defid_orshift(ctx, cardtype(dbits), fieldvar, nbits),
          :(id = unsafe_substr(id, $(if zfill digits else bitsconsumed end))))
    fextract = :($fnum = $(defid_fextract(ctx, nbits, dbits)))
    fvalue = if dI == cardtype(dbits)
        fnum
    else
        :($fnum % $dI)
    end
    if iszero(min) && !isnothing(option)
        fvalue = :($fvalue - 0x1)
    elseif min - !isnothing(option) > 0
        fvalue = :($fvalue + $(min - !isnothing(option)))
    end
    printex = if pad > 0 || zfill
        :(print(io, string($fieldvar, base=$base, pad=$(if zfill digits else pad end))))
    elseif base == 10
        :(print(io, $fieldvar))
    else
        :(print(io, string($fieldvar, base=$base)))
    end
    push!(ctx[:segments], (dbits, :digits, Symbol(chopprefix(String(fieldvar), "attr_")),
                           string(if zfill
                                      "up to $digits"
                                  else
                                      string(digits)
                                  end,
                                  if isone(digits)
                                      " digit"
                                  else
                                      " digits"
                                  end,
                                  if base != 10
                                      " in base $base"
                                  else
                                      ""
                                  end,
                                  if min > 0 && max < base^digits - 1
                                      " between $(string(min; base, pad)) and $(string(max; base, pad))"
                                  elseif min > 0
                                      ", at least $(string(min; base, pad))"
                                  elseif max < base^digits - 1
                                      ", at most $(string(max; base, pad))"
                                  else
                                      ""
                                  end)))
    if isnothing(option)
        push!(exprs.print,
              fextract,
              :($fieldvar = $fvalue),
              printex,
              :(__segment_printed = $(length(ctx[:segments]))))
    else
        push!(ctx[:oprint_detect],
              fextract,
              :($option = !iszero($fnum)))
        push!(exprs.print,
              :(if $option
                    $fieldvar = $fvalue
                    $printex
                    __segment_printed = $(length(ctx[:segments]))
                end))
    end
    if haskey(ctx, :fieldvals)
        push!(ctx[:fieldvals],
              if isnothing(option)
                  :($fextract; $fvalue)
              else
                  :($fextract; if !iszero($fnum); $fvalue end)
              end)
    end
    nothing
end

function defid_alphnum!(exprs::IdExprs,
                        ctx::Base.ImmutableDict{Symbol, Any},
                        arg = nothing)
    # TODO
end

function defid_orshift(ctx::Base.ImmutableDict{Symbol, Any}, type::Type, value::Union{Symbol, Expr}, shift::Int)
    valcast = Expr(:call, :__cast_to_id, type, value)
    # valcast = :(if sizeof($(esc(ctx[:name]))) == sizeof($value)
    #                 Core.bitcast($(esc(ctx[:name])), $value)
    #             elseif sizeof($(esc(ctx[:name]))) < sizeof($value)
    #                 # @info "We're producing a $(typeof($value)) = $($value) which is bigger than the final identifier??"
    #                 Core.Intrinsics.trunc_int($(esc(ctx[:name])), $value)
    #             else
    #                 Core.Intrinsics.zext_int($(esc(ctx[:name])), $value)
    #             end)
    :(parsed = Core.Intrinsics.or_int(parsed, Core.Intrinsics.shl_int($valcast, (8 * sizeof($(esc(ctx[:name]))) - $shift))))
end

function defid_fextract(ctx::Base.ImmutableDict{Symbol, Any}, position::Int, width::Int)
    fT = cardtype(width)
    fval = :(Core.Intrinsics.lshr_int(id, 8 * sizeof($(esc(ctx[:name]))) - $position))
    ival = Expr(:call, :__cast_from_id, fT, fval)
    # ival = :(if sizeof($(esc(ctx[:name]))) == sizeof($fT)
    #             Core.bitcast($fT, $fval)
    #          elseif sizeof($(esc(ctx[:name]))) > sizeof($fT)
    #              Core.Intrinsics.trunc_int($fT, $fval)
    #          else
    #              Core.Intrinsics.zext_int($fT, $fval)
    #          end)
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

function defid_parser(pexprs::Vector{ExprVarLine}, ctx::Base.ImmutableDict{Symbol, Any}, name::Symbol)
    :(function $(GlobalRef(@__MODULE__, :parseid))(::Type{$(esc(name))}, id::SubString)
          parsed = $(if ctx[:bits][] <= 8
                         :(Core.bitcast($(esc(ctx[:name])), 0x00))
                     else
                         :(Core.Intrinsics.zext_int($(esc(ctx[:name])), 0x0))
                     end)
          $(implement_casting!(ctx, pexprs)...)
          isempty(id) || return MalformedIdentifier{$(esc(name))}(id, "Unparsed trailing content")
          parsed
      end)
end

function defid_shortcode(pexprs::Vector{ExprVarLine}, ctx::Base.ImmutableDict{Symbol, Any}, name::Symbol)
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
    :(function $(GlobalRef(@__MODULE__, :shortcode))(io::IO, id::$(esc(name)))
          $(implement_casting!(ctx, map(strip_segsets! ∘ copy, pexprs))...)
          nothing
      end)
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
          $((:($s = "") for (_, s) in svars)...)
          $(pexprs2...)
          $(Expr(:tuple, (Expr(:tuple, i, s) for (i, s) in svars)...))
      end)
end

function defid_make(exprs::IdExprs, ctx::Base.ImmutableDict{Symbol, Any}, name::Symbol)
    block = Expr(:block) # :toplevel
    numbits = 8 * cld(ctx[:bits][], 8)
    push!(block.args,
          :(Base.@__doc__(primitive type $(esc(name)) <: $AbstractIdentifier $numbits end)),
          :($(GlobalRef(@__MODULE__, :nbits))(::Type{$(esc(name))}) = $(ctx[:bits][])),
          defid_parser(exprs.parse, ctx, name),
          defid_shortcode(exprs.print, ctx, name),
          :($(GlobalRef(Base, :propertynames))(::$(esc(name))) = $(Tuple(map(first, exprs.properties)))),
          defid_properties(exprs.properties, ctx, name),
          defid_segments_type(ctx, name),
          defid_segments_value(ctx, exprs.print, name),
          esc(name))
    block
end
