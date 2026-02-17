# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

"""
    parsefor(::Type{T}, ::Type{I}, num::Union{<:AbstractString, <:AbstractChar}; base::Integer=10)

Attempt to parse the `num` string as an integer of type `I`, for use in a `T` identifier.

If the string cannot be parsed as an integer, a `MalformedIdentifier{T}` exception is returned.

# Example

```julia
function FastIdentifiers.parseid(::Type{MyID}, input::SubString)
    num = parsefor(MyID, UInt16, input)
    num isa UInt16 || return num  # Forward parse error
    MyID(num)
end
```
"""
function parsefor(::Type{T}, ::Type{I}, num::Union{<:AbstractString,<:AbstractChar}; base::Integer=10) where {T<:AbstractIdentifier, I<:Integer}
    int = if base <= 36 && I <: Unsigned
        fastparse(I, num, base)
    else
        tryparse(I, num, base)
    end
    if isnothing(int)
        (@noinline function(iT, iI, inum, ibase)
             isdigit(c, b) = c ∈ '0':('0' + min(9, b-1)) || (b > 10 && c ∈ 'a':('a' + min(25, b-11)) || c ∈ 'A':('A' + min(25, b-11)))
             nonint = if inum isa AbstractChar inum else filter(c -> !isdigit(c, ibase), inum) end
             if isempty(nonint)
                 MalformedIdentifier{T}(inum, "is not a valid base $base $iI")
             else
                 MalformedIdentifier{T}(inum, "includes invalid base $base digit$(ifelse(length(nonint)==1, "", "s")) '$(nonint)'")
             end
         end)(T, I, num, base)
    else
        int
    end
end

"""
    byte2int(b::UInt8, base::Integer) -> UInt8

Convert a byte `b` to an integer in the specified `base` (2-62).

If `b` is not a valid digit in the specified base, `0xff` is returned.
"""
function byte2int(b::UInt8, base::Integer)
    if b ∈ UInt8('0'):(UInt8('0') - 0x1 + min(base, 10) % UInt8)
        b - UInt8('0')
    elseif 10 < base <= 36 && (b | 0x20) ∈ UInt8('a'):(UInt8('a') - 0x1 + (base - 10) % UInt8)
        (b | 0x20) - (UInt8('a') - UInt8(10))
    elseif base > 36 && b ∈ UInt8('A'):(UInt8('z') - UInt8(62) + base % UInt)
        b - (UInt8('A') - UInt8(10)) - ifelse(b >= UInt8('a'), 0x06, 0x00)
    else
        0xff
    end
end

"""
    parsechars(::Type{P}, str::AbstractString, maxlen::Int, ranges::NTuple{N, UnitRange{UInt8}}, casefold::Bool) -> (Int, P)

Parse up to `maxlen` characters from `str`, mapping each byte to a 0-based
index via the given byte `ranges`. Each range maps contiguously: the first
range covers indices 0:length(r1)-1, the second continues from there, etc.
The total number of distinct values determines bits per character, packed MSB-first
into an unsigned integer of type `P`.

When `casefold` is true, both the input byte and range endpoints are
lowercased (`| 0x20`) before comparison, enabling case-insensitive matching.

Returns `(chars_consumed, packed_value)`. Stops at the first non-matching byte.
"""
function parsechars(::Type{P}, bytes::AbstractVector{UInt8}, pos::Int, maxlen::Int,
                    ranges::NTuple{N, UnitRange{UInt8}},
                    casefold::Bool) where {P <: Unsigned, N}
    nvals = sum(length, ranges)
    bpc = cardbits(nvals)
    packed = zero(P)
    endpos = min(pos + maxlen, length(bytes) + 1)
    pos > length(bytes) && return 0, packed
    nread = 0
    @inbounds while pos < endpos
        b = bytes[pos]
        casefold && (b |= 0x20)
        idx = 0xff % UInt8
        offset = zero(UInt8)
        for r in ranges
            lo = casefold ? (first(r) | 0x20) : first(r)
            d = b - lo
            if d < length(r) % UInt8
                idx = offset + d
                break
            end
            offset += length(r) % UInt8
        end
        idx == 0xff && break
        packed = (packed << bpc) | P(idx)
        nread += 1
        pos += 1
    end
    nread, packed
end

function parsechars(::Type{P}, str::AbstractString, maxlen::Int,
                    ranges::NTuple{N, UnitRange{UInt8}},
                    casefold::Bool) where {P <: Unsigned, N}
    parsechars(P, codeunits(str), 1, maxlen, ranges, casefold)
end

"""
    printchars(io::IO, packed::Unsigned, nchars::Int, ranges::NTuple{N, UnitRange{UInt8}})

Unpack `nchars` characters from `packed` (MSB-first, same encoding as
[`parsechars`](@ref)) and write them to `io` using the given byte `ranges`.
"""
function printchars(io::IO, packed::P, nchars::Int,
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
                write(io, first(r) + idx)
                break
            end
            idx -= rlen
        end
        packed <<= bpc
    end
end

"""
    chars2string(packed::Unsigned, nchars::Int, ranges::NTuple{N, UnitRange{UInt8}}) -> String

Unpack `nchars` characters from `packed` into a `String`, using the same
encoding as [`parsechars`](@ref).
"""
function chars2string(packed::P, nchars::Int,
                      ranges::NTuple{N, UnitRange{UInt8}}) where {P <: Unsigned, N}
    nvals = sum(length, ranges)
    bpc = cardbits(nvals)
    topshift = 8 * sizeof(P) - bpc
    packed <<= 8 * sizeof(P) - nchars * bpc
    buf = Vector{UInt8}(undef, nchars)
    @inbounds for ci in 1:nchars
        idx = UInt8(packed >> topshift)
        for r in ranges
            rlen = length(r) % UInt8
            if idx < rlen
                buf[ci] = first(r) + idx
                break
            end
            idx -= rlen
        end
        packed <<= bpc
    end
    String(buf)
end

"""
    fastparse(::Type{I<:Integer}, number::Union{Char, <:AbstractString}, base::Integer) -> Union{I, Nothing}

Attempt to parse the `number` as an integer of type `I` in the specified `base`.

Should the `number` not be a valid representation, `nothing` is returned instead.
"""
function fastparse end

function fastparse(::Type{I}, c::Char, base::Integer) where {I <: Integer}
    n = byte2int(c % UInt8, base)
    n == 0xff && return
    n
end

function fastparse(::Type{I}, str::AbstractString, base::Integer) where {I <: Unsigned}
    n, num = parseint(I, str, base, ncodeunits(str))
    n == ncodeunits(str) || return
    num
end

function parseint(::Type{I}, bytes::AbstractVector{UInt8}, pos::Int, base::Integer, maxlen::Integer) where {I <: Unsigned}
    num = zero(I)
    nread = 0
    endpos = min(pos + maxlen, length(bytes) + 1)
    pos > length(bytes) && return 0, zero(I)
    # NOTE: Don't ask me why, but it turns out that `while` is
    # considerably faster than `for` here (~7ns vs ~4ns).
    @inbounds while true
        digit = byte2int(bytes[pos], base)
        digit == 0xff && return nread, num # Invalid byte
        numnext = muladd(widen(num), base % I, digit)
        iszero(numnext & ~widen(typemax(I))) || return 0, zero(I) # Overflow check
        num = numnext % I
        nread += 1
        pos += 1
        pos < endpos || break
    end
    nread, num
end

function parseint(::Type{I}, str::AbstractString, base::Integer, maxlen::Integer) where {I <: Unsigned}
    parseint(I, codeunits(str), 1, base, maxlen)
end

"""
    chopprefixfolded(str::SubString, prefix::AbstractString) -> Tuple{Bool, SubString}

Remove an ASCII `prefix` from the start of `str`, ignoring case.

The `prefix` argument must be lowercase.
"""
function chopprefixfolded(s::SubString, prefix::AbstractString)
    k = firstindex(s)
    i, j = iterate(s), iterate(prefix)
    @inbounds while true
        isnothing(j) && isnothing(i) && return true, SubString(s, 1, 0)
        isnothing(j) && return true, SubString(s, k)
        isnothing(i) && return false, s
        ui, uj = UInt32(first(i)), UInt32(first(j))
        if ui ∈ 0x41:0x5a
            ui |= 0x20
        end
        ui == uj || return false, s
        k = last(i)
        i, j = iterate(s, k), iterate(prefix, last(j))
    end
end

function chopprefixfolded(s::SubString{String}, prefix::String)
    cs, cp = codeunits(s), codeunits(prefix)
    length(cs) >= length(cp) || return false, s
    i = firstindex(cp)
    while i < lastindex(cp)
        c, p = @inbounds cs[i], cp[i]
        c != p && !(c | 0x20 == p && c ∈ 0x41:0x5a) && return false, s
        i += 1
    end
    true, @inbounds SubString(s.string, 1+s.offset+ncodeunits(prefix))
end

"""
    lchopfolded(str::SubString, prefixes::AbstractString...) -> Tuple{Bool, SubString}

Remove any of the specified `prefixes` from the start of `str`, ignoring case.

This function will return `true` if any of the prefixes were successfully removed,
and `false` otherwise. The remaining string is returned as a `SubString`.

The `prefixes` arguments must all be lowercase.
"""
function lchopfolded(s::SubString, prefixes::NTuple{N, String}) where {N}
    chopped = false
    for prefix in prefixes
        did, s = @inline chopprefixfolded(s, prefix)
        chopped |= did
    end
    chopped, s
end

function lchopfolded(s::SubString{String}, prefixes::NTuple{N, String}) where {N}
    prefbytes = map(codeunits, prefixes)
    offset = s.offset
    nbytes = s.ncodeunits
    sbytes = codeunits(s.string)
    chopped = false
    for pbytes in prefbytes
        nb = length(pbytes)
        length(sbytes) - offset >= nb || continue
        match = true
        @inbounds for i in eachindex(pbytes)
            if sbytes[i + offset] | 0x20 != pbytes[i]
                match = false
                break
            end
        end
        if match
            offset += nb
            nbytes -= nb
            chopped = true
        end
    end
    chopped, if chopped
        unsafe_substr(s.string, offset, nbytes)
    else
        s
    end
end

lchopfolded(s::SubString, prefixes::String...) = lchopfolded(s, tuple(prefixes...))

"""
    unsafe_substr(s::AbstractString, off::Int, ncu::Int) -> SubString{String}

Return a `SubString` of `s` starting at `off` with length `ncu`.

This function is unsafe because it does not check that the substring is within bounds.
It is intended for use in performance-critical code where you know the bounds are valid.
"""
@generated function unsafe_substr(s::S, offset::Int, ncodeunits::Int) where {S <: AbstractString}
    Expr(:new, SubString{S}, :s, :offset, :ncodeunits)
end

unsafe_substr(s::AbstractString, off::Integer = 0) = unsafe_substr(s, Int(off), ncodeunits(s) - off)
unsafe_substr(s::SubString, off::Int, ncu::Int) = unsafe_substr(s.string, s.offset+off, ncu)
unsafe_substr(s::SubString, off::Integer, ncu::Integer) = unsafe_substr(s, Int(off), Int(ncu))
