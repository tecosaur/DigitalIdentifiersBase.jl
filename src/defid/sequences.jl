# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Pattern handlers for value-carrying sequences: digits, character sequences
# (letters, alphnum), and embedded identifier types. These emit parse/print
# expressions, bit-packing, and constructor impart code.

## Digits

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
    mindigits, maxdigits = parse_digit_range(args, max, base)
    fixedwidth = mindigits == maxdigits
    if isnothing(max)
        max = (base^maxdigits) - 1
    end
    option = get(nctx, :optional, nothing)
    range = max - min + 1 + !isnothing(option)
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
    push!(exprs.parse, defid_emit_pack(state, dT, parsevar, nbits), posexpr)
    # Extract and print
    fextract = :($fnum = $(defid_emit_extract(state, nbits, dbits)))
    fcast = if dI == dT; fnum else :($fnum % $dI) end
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
    seg_desc = string(if fixedwidth; "$maxdigits" else "$mindigits-$maxdigits" end,
                      if isone(maxdigits); " digit" else " digits" end,
                      base != 10 ? " in base $base" : "",
                      if min > 0 && max < base^maxdigits - 1
                          " between $(string(min; base, pad)) and $(string(max; base, pad))"
                      elseif min > 0
                          ", at least $(string(min; base, pad))"
                      elseif max < base^maxdigits - 1
                          ", at most $(string(max; base, pad))"
                      else "" end)
    emit_print_detect!(exprs, nctx, option, ExprVarLine[fextract], :(!iszero($fnum)))
    directvar || push!(exprs.print, :($fieldvar = $fvalue))
    push!(exprs.print, printex)
    # Property extract value
    propvalue = if max < typemax(dI) ÷ 2
        sI = signed(dI)
        :($fvalue % $sI)
    else
        fvalue
    end
    # Constructor impart
    argvar = gensym("arg_digit")
    directval = cardbits(max - min + 1 + !isnothing(option)) ==
                cardbits(max) && (min > 0 || isnothing(option))
    offset = min - !isnothing(option)
    encode_expr = if directval
        if dI != dT; :($parsevar = $fnum % $dT) else :($parsevar = $fnum) end
    elseif offset > 0
        :($parsevar = (($fnum - $(dT(offset))) % $dT))
    elseif offset < 0  # optional with min==0: +1 to reserve zero for "absent"
        :($parsevar = ($fnum + $(one(dT))) % $dT)
    else
        if dI != dT; :($parsevar = $fnum % $dT) else :($parsevar = $fnum) end
    end
    body = Any[]
    push!(body, :($argvar >= $min || throw(ArgumentError(
        string("Value ", $argvar, " is below minimum ", $min)))))
    push!(body, :($argvar <= $max || throw(ArgumentError(
        string("Value ", $argvar, " is above maximum ", $max)))))
    push!(body, :($fnum = $argvar % $dI))
    directvar || push!(body, encode_expr)
    push!(body, defid_emit_pack(state, dT, parsevar, nbits))
    push_value_segment!(exprs;
        nbits=dbits, kind=:digits, fieldvar, desc=seg_desc,
        argvar, base_argtype=:Integer, option,
        extract_setup=ExprVarLine[fextract], extract_value=propvalue,
        present_check=:(!iszero($fnum)), impart_body=body)
end

function parse_digit_range(args, max, base)
    if !isempty(args) && Meta.isexpr(first(args), :call, 3) && first(first(args).args) == :(:)
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
end

## Character sequences (letters, alphnum)

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
    ranges, cfold = charseq_config(nctx, kind)
    variable = minlen != maxlen
    option = get(nctx, :optional, nothing)
    nvals = sum(length, ranges)
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
    nbits_pos = (state.bits += totalbits)
    scanlimit = defid_lengthbound(state, nctx, maxlen)
    inc_print!(nctx, minlen, maxlen)
    inc_parsed!(nctx, minlen, maxlen)
    # Parse
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
          defid_emit_pack(state, cT, charvar, nbits_pos - lenbits - presbits),
          :(pos += $lenvar))
    if variable
        lenpack = if lenbase == 0
            :($lenoffset = $lenvar % $lT)
        else
            :($lenoffset = ($lenvar - $lenbase) % $lT)
        end
        push!(exprs.parse, lenpack,
              defid_emit_pack(state, lT, lenoffset, nbits_pos))
    elseif presbits > 0
        push!(exprs.parse,
              defid_emit_pack(state, Bool, option, nbits_pos))
    end
    # Print / extract
    fextract_chars = :($charvar = $(defid_emit_extract(state, nbits_pos - lenbits - presbits, charbits)))
    extracts = ExprVarLine[fextract_chars]
    if variable
        fextract_len = if lenbase == 0
            :($lenvar = $(defid_emit_extract(state, nbits_pos, lenbits)))
        else
            :($lenvar = $(defid_emit_extract(state, nbits_pos, lenbits)) + $lenbase)
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
        :(!iszero($(defid_emit_extract(state, nbits_pos, presbits))))
    end
    emit_print_detect!(exprs, nctx, option, extracts, present)
    push!(exprs.print, printex)
    # Constructor impart
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
        $(defid_emit_pack(state, cT, charvar, nbits_pos - lenbits - presbits))
        $(if variable
              lenpack_expr = if lenbase == 0
                  :($lenoffset = $lenvar % $lT)
              else
                  :($lenoffset = ($lenvar - $lenbase) % $lT)
              end
              quote
                  $lenpack_expr
                  $(defid_emit_pack(state, lT, lenoffset, nbits_pos))
              end
          elseif presbits > 0
              defid_emit_pack(state, Bool, true, nbits_pos)
          else
              nothing
          end)
    end
    charseq_body = filter(e -> !isnothing(e) && !(e isa LineNumberNode), encode_chars.args)
    push_value_segment!(exprs;
        nbits=totalbits, kind, fieldvar,
        desc=string(if variable; "$minlen-$maxlen" else "$maxlen" end,
                    " ", kind, if maxlen > 1; " characters" else " character" end),
        argvar, base_argtype=:AbstractString, option,
        extract_setup=extracts, extract_value=tostringex,
        present_check=present, impart_body=charseq_body)
end

function charseq_config(nctx, kind)
    upper = get(nctx, :upper, false)::Bool
    lower = get(nctx, :lower, false)::Bool
    casefold = get(nctx, :casefold, false)::Bool
    upper && lower && throw(ArgumentError("Cannot specify both upper=true and lower=true for $kind"))
    AZ = UInt8('A'):UInt8('Z')
    az = UInt8('a'):UInt8('z')
    d09 = UInt8('0'):UInt8('9')
    singlecase = upper || lower || casefold
    letters = if lower && !upper; (az,) elseif singlecase; (AZ,) else (AZ, az) end
    ranges = if kind === :letters; letters else (d09, letters...) end
    (ranges, casefold)
end

## Embedded identifier types

function defid_embed!(exprs::IdExprs,
                      state::DefIdState, nctx::NodeCtx,
                      args::Vector{Any})
    length(args) == 1 || throw(ArgumentError("embed takes exactly one argument (the identifier type)"))
    T = Core.eval(state.mod, args[1])
    T isa DataType && T <: AbstractIdentifier && isprimitivetype(T) ||
        throw(ArgumentError("embed type must be a primitive AbstractIdentifier subtype, got $T"))
    ebits = nbits(T)
    epad = 8 * sizeof(T) - ebits  # MSB padding bits in the embedded type
    option = get(nctx, :optional, nothing)
    presbits = isnothing(option) ? 0 : 1
    fieldvar = get(nctx, :fieldvar, gensym("embed"))
    nbits_pos = (state.bits += ebits + presbits)
    inc_parsed!(nctx, parsebounds(T)...)
    inc_print!(nctx, printbounds(T)...)
    # @defid types pack from the MSB, so embedded values must be shifted
    # right by epad before packing (MSB→LSB) and left after extracting (LSB→MSB)
    to_lsb(val) = :(Core.Intrinsics.lshr_int($val, $epad))
    to_msb(val) = :(Core.Intrinsics.shl_int($val, $epad))
    # Parse: delegate to inner parsebytes
    eresult = Symbol("$(fieldvar)_result")
    epos = Symbol("$(fieldvar)_epos")
    errmsg = defid_errmsg(state, "Invalid embedded $(T)")
    notfound = if isnothing(option)
        [:(return ($errmsg, pos))]
    else
        [:($option = false)]
    end
    eshifted = Symbol("$(fieldvar)_shifted")
    pack = defid_emit_pack(state, T, eshifted, nbits_pos - presbits)
    push!(exprs.parse,
          :(($eresult, $epos) = parsebytes($T, @view idbytes[pos:end])),
          :(if !($eresult isa $T); $(notfound...) end),
          :($eshifted = $(to_lsb(eresult))))
    if isnothing(option)
        push!(exprs.parse, pack, :(pos += $epos - 1))
    else
        push!(exprs.parse,
              :(if $option; $pack; $(defid_emit_pack(state, Bool, option, nbits_pos)); pos += $epos - 1 end))
    end
    # Extract + print
    fextract = :($fieldvar = $(to_msb(defid_emit_extract(state, nbits_pos - presbits, ebits, T))))
    present = if presbits > 0
        :(!iszero($(defid_emit_extract(state, nbits_pos, presbits))))
    else
        true
    end
    emit_print_detect!(exprs, nctx, option, ExprVarLine[fextract], present)
    push!(exprs.print, :(shortcode(io, $fieldvar)))
    # Constructor impart
    argvar = gensym("arg_embed")
    argshifted = gensym("arg_embed_shifted")
    body = Any[:($argshifted = $(to_lsb(argvar))),
               defid_emit_pack(state, T, argshifted, nbits_pos - presbits)]
    if presbits > 0
        push!(body, defid_emit_pack(state, Bool, true, nbits_pos))
    end
    push_value_segment!(exprs;
        nbits=ebits + presbits, kind=:embed, fieldvar,
        desc="embedded $(T)",
        argvar, base_argtype=T, option,
        extract_setup=ExprVarLine[fextract], extract_value=fieldvar,
        present_check=present, impart_body=body)
end
