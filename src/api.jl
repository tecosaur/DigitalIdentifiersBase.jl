# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

"""
    AbstractIdentifier

An abstract type for structured (and validated) digital identifiers.

It is expected that all identifiers have a plain text canonical form, and
optionally a PURL (Persistent Uniform Resource Locator) that can be used to link
to the resource. These may be one and the same.

All subtypes of `AbstractIdentifier` must implement `parse` and `tryparse` methods.
You can either implement [`parseid`](@ref) (recommended) or override the methods directly
(see the extended help for a guide to implementing a new identifier type).

See also: [`shortcode`](@ref), [`purl`](@ref).

# Extended help

Digital identifiers like DOIs, ORCIDs, and ISBNs share common patterns but have
different validation rules and URL schemes. This framework provides a consistent
interface for all of them.

## Terminology

- **Shortcode**: The minimal representation without prefixes (e.g., "123")
- **Canonical**: The standard formatted representation (e.g., "MyID:123")
- **PURL**: Persistent URL for web access (e.g., "https://example.com/123")

## Implementation Guide

All identifier types must implement `parse` and `tryparse` for converting
strings to identifier objects. This can be conveniently done by just
implementing [`parseid`](@ref).

### Optional Methods

You may also implement:
- [`shortcode`](@ref) for a minimally formatted representation
- [`idcode`](@ref) for providing the number within a numeric identifier
- [`idchecksum`](@ref) when the identifier includes/uses a checksum
- [`purlprefix`](@ref) (or [`purl`](@ref)) for generating persistent URLs (PURLs)

All methods but `idchecksum` and `purlprefix` have generic implementations.

### Example identifier implementation

Let's implement a simple numeric identifier called "MyId" that accepts the format
`MyId:<number>` where `<number>` is between 0 and 65535. We want to support:
- Parsing forms like `123`, `MyId:123` (case insensitive), and `https://example.com/123`
- Providing permanent URLs
- Automatic display formatting

#### Basic implementation

```julia
struct MyIdentifier <: AbstractIdentifier
    id::UInt16
end

FastIdentifiers.purlprefix(::Type{MyIdentifier}) = "https://example.com/"

function FastIdentifiers.parseid(::Type{MyIdentifier}, input::SubString)
    _, cleaned = lchopfolded(input, "myid:", "https://example.com/")
    num = parsefor(MyIdentifier, UInt16, cleaned)
    num isa UInt16 || return num  # Forward parse error
    MyIdentifier(num)
end
```

This minimal implementation uses the generic `idcode` and `shortcode` methods
(returning `123` and `"123"` respectively), PURL generation
("https://example.com/123"), and parsing support for multiple formats.

#### Adding checksum validation

Types that implement [`idchecksum`](@ref) automatically receive a `Type(id, checksum)`
constructor that validates the computed checksum matches the provided value.

```julia
FastIdentifiers.idchecksum(id::MyIdentifier) =
    sum(digits(id.id) .* (2 .^ (1:ndigits(id.id)) .- 1)) % 0xf

# Defining `idchecksum` supports a generic `MyIdentifier(id, checksum)` constructor

FastIdentifiers.shortcode(id::MyIdentifier) =
    string(id.id) * string(idchecksum(id), base=16)

function FastIdentifiers.parseid(::Type{MyIdentifier}, input::SubString)
    _, cleaned = lchopfolded(input, "myid:", "https://example.com/")
    digits_str, check_char = cleaned[1:end-1], cleaned[end]
    num = parsefor(MyIdentifier, UInt16, digits_str)
    num isa UInt16 || return num
    check = parsefor(MyIdentifier, UInt8, check_char, base=16)
    check isa UInt8 || return check
    try MyIdentifier(num, check) catch e; e end
end
```

This extended version performs checksum calculation, automatic validation via
the `MyIdentifier(id, checksum)` constructor, and uses specific errors for
malformed input and checksum violations.

### Validation and errors

`parseid(::Type{T}, input::SubString)` is a convenience function used by the generic
`parse` and `tryparse` implementations. The function should accept multiple formats
and return either a valid identifier or an exception object ([`MalformedIdentifier`](@ref)
or [`ChecksumViolation`](@ref)).

When parsing fails, your implementation should:
- Return [`MalformedIdentifier`](@ref) for invalid formats
- Return [`ChecksumViolation`](@ref) for checksum mismatches
- Use [`parsefor`](@ref) helper for safe integer parsing

### Method details

**`parseid`** is the recommended way to implement parsing - the generic `parse`/`tryparse`
methods will use it automatically.

**`shortcode`** has a fallback implementation that uses [`idcode`](@ref) if available,
or attempts to extract from single-field structs. For multi-field structs without
`idcode`, you must implement this method to get meaningful output.

**Numeric Identifiers**: If your identifier has a numeric component, consider implementing:
- [`idcode`](@ref) enables automatic `shortcode` generation and comparison
- [`idchecksum`](@ref) affects `idcode` behavior and enables checksum validation

**URL Generation**: For identifiers with standard web URLs, implement either:
- [`purlprefix`](@ref) when URL follows `prefix * shortcode` pattern
- [`purl`](@ref) for custom URL schemes

## Invariants

All identifiers should ensure round-trip consistency:
- `parse(T, shortcode(x)) == x`
- `parse(T, string(x)) == x`
- `parse(T, purl(x)) == x` (when applicable)

# See Also

- [`MalformedIdentifier`](@ref), [`ChecksumViolation`](@ref): Exception types
- [`parsefor`](@ref), [`lchopfolded`](@ref): Parsing utilities
- [`@reexport`](@ref): Convenience macro for exporting the public-facing API
"""
abstract type AbstractIdentifier end

"""
    parseid(::Type{T}, input::SubString) -> Union{T, Exception}

Parse the `input` string as an identifier of type `T`.

This function is used by the generic `parse` and `tryparse` functions and provides
a convenient way to implement parsing. It should accept multiple input formats
(shortcode, canonical, PURL) and return either a valid identifier or an exception object.

Alternatively, you can implement `parse` and `tryparse` methods directly.

# Example

```julia
function FastIdentifiers.parseid(::Type{MyID}, input::SubString)
    _, cleaned = lchopfolded(input, "myid:", "https://example.com/")
    num = parsefor(MyID, UInt16, cleaned)
    num isa UInt16 || return num  # Return MalformedIdentifier on parse failure
    MyID(num)
end
```

See also:
- [`parsefor`](@ref): Safe integer parsing helper
- [`lchopfolded`](@ref): Case-insensitive prefix removal
"""
function parseid end

function Base.parse(::Type{T}, input::AbstractString) where {T<:AbstractIdentifier}
    id = @inline parseid(T, unsafe_substr(input))
    id isa T || throw(id)
    id
end

function Base.tryparse(::Type{T}, input::AbstractString) where {T<:AbstractIdentifier}
    id = @inline parseid(T, unsafe_substr(input))
    if id isa T id end
end

"""
    MalformedIdentifier{T}(input, problem::String)

Exception indicating that `input` is not a valid form of identifier type `T`.

The `problem` string should describe what specifically makes the input invalid.
This exception is typically returned by [`parseid`](@ref) implementations rather
than thrown directly.

# Example

```julia
function FastIdentifiers.parseid(::Type{MyID}, input::SubString)
    if length(input) > 10
        return MalformedIdentifier{MyID}(input, "must be 10 characters or fewer")
    end
    # ... continue parsing
end
```
"""
struct MalformedIdentifier{T <: AbstractIdentifier, I} <: Exception
    input::I
    problem::String
end

MalformedIdentifier{T}(input::I, problem::String) where {T, I} =
    MalformedIdentifier{T,I}(input, problem)

"""
    ChecksumViolation{T}(id, expected::Integer, provided::Integer)

The `provided` checksum for the `T` identifier `id` is incorrect;
the correct checksum is `expected`.

# Example

```julia
function MyID(value::Integer, checksum::Integer)
    id = MyID(value) # Create without checksum validation
    expected = idchecksum(id)
    expected == checksum || throw(ChecksumViolation{MyID}(value, expected, checksum))
    id
end
```
"""
struct ChecksumViolation{T <: AbstractIdentifier, I} <: Exception
    id::I
    expected::Int
    provided::Int
end

ChecksumViolation{T}(id::I, expected::Integer, provided::Integer) where {T, I} =
    ChecksumViolation{T, I}(id, Int(expected), Int(provided))

"""
    idcode(id::AbstractIdentifier) -> Union{Integer, Nothing}

Return the numeric identifier component, if applicable.

The default implementation automatically extracts the first field if the
identifier type has exactly one integer field and no checksum. Should the first
field be another identifier, `idcode` is called on that identifier. Specialised
methods should be implemented for identifiers that need more sophisticated
handling.

Returns `nothing` if the identifier has multiple fields or uses a checksum.

See also: [`idchecksum`](@ref), [`shortcode`](@ref).
"""
function idcode(id::AbstractIdentifier)
    if fieldcount(typeof(id)) == 1
        if fieldtype(typeof(id), 1) <: Integer && isnothing(idchecksum(id))
            getfield(id, 1)
        elseif fieldtype(typeof(id), 1) <: AbstractIdentifier
            idcode(getfield(id, 1))
        end
    end
end

"""
    idchecksum(id::AbstractIdentifier) -> Union{Integer, Nothing}

Return the checksum/check digit component, if applicable.

The default implementation returns `nothing`. Identifiers that include or
support checksum should implement specialised methods. When `idchecksum` is defined,
a generic `MyIdentifier(id, checksum)` constructor is automatically provided that:
- Constructs the identifier using `MyIdentifier(id)`
- Validates the computed checksum matches the provided checksum
- Throws `ChecksumViolation` if the checksums don't match

Returns `nothing` if the identifier has no checksum component.

See also: [`idcode`](@ref), [`ChecksumViolation`](@ref).
"""
function idchecksum(::AbstractIdentifier) end

function (T::Type{<:AbstractIdentifier})(id, checksum)
    if hasmethod(T, Tuple{typeof(id)})
        tid = T(id)
        expected = idchecksum(tid)
        if !isnothing(expected)
            checksum == expected || throw(ChecksumViolation{T}(id, expected, checksum))
            return tid
        end
    end
    throw(MethodError(T, (id, checksum)))
end

"""
    shortcode(io::IO, id::AbstractIdentifier) -> Nothing
    shortcode(id::AbstractIdentifier) -> String

Return the minimal string representation of an identifier.

This is the most compact unambiguous form, without prefixes or decorative formatting.
The shortcode should contain only the essential identifying information.

If [`idcode`](@ref) is defined, the default implementation prints the numeric value.
Otherwise, you must implement this method explicitly.

See also: [`idcode`](@ref), [`purl`](@ref).
"""
function shortcode(io::IO, id::AbstractIdentifier)
    icode = idcode(id)
    if !isnothing(icode)
        print(io, icode)
    elseif fieldcount(typeof(id)) == 1
        val = getfield(id, 1)
        if val isa AbstractIdentifier
            shortcode(io, val)
        end
    end
end

shortcode(id::AbstractIdentifier) = sprint(shortcode, id)

"""
    purlprefix(::Type{<:AbstractIdentifier}) -> Union{String, Nothing}

Return the standard prefix of a PURL for an `AbstractIdentifier`, if applicable.

If defined, this implies that a PURL can be constructed by appending the `shortcode`
representation of the identifier to this prefix. As such, you should take care to
include any necessary trailing slashes or other separators in this prefix.
"""
function purlprefix(::Type{T}) where {T <: AbstractIdentifier} end

purlprefix(::T) where {T <: AbstractIdentifier} = purlprefix(T)

"""
    purl(id::AbstractIdentifier) -> Union{String, Nothing}

If applicable, return the PURL of an `AbstractIdentifier`.

PURLs provide permanent web links to resources. The generic implementation
constructs URLs using [`purlprefix`](@ref), if defined, together with the
[`shortcode`](@ref) of the identifier.

Returns `nothing` if no web URL is available for this identifier type.

See also: [`purlprefix`](@ref), [`shortcode`](@ref).
"""
function purl(id::AbstractIdentifier)
    prefix = purlprefix(id)
    if !isnothing(prefix)
        prefix * shortcode(id)
    end
end

function Base.print(io::IO, id::AbstractIdentifier)
    if get(io, :limit, false) === true
        get(io, :compact, false) === true ||
            print(io, typeof(id), ':')
        shortcode(io, id)
    else
        url = purl(id)
        if !isnothing(url)
            print(io, url)
        else
            shortcode(io, id)
        end
    end
end

function Base.show(io::IO, id::AbstractIdentifier)
    if get(io, :limit, false) === true
        if get(io, :typeinfo, Nothing) != typeof(id)
            print(io, nameof(typeof(id)), ':')
        end
        print(io, shortcode(id))
    elseif isnothing(idchecksum(id)) &&
           fieldcount(typeof(id)) == 1 &&
           idcode(id) == getfield(id, 1)
        show(io, typeof(id))
        print(io, '(', idcode(id), ')')
    else
        show(io, parse)
        show(io, (typeof(id), shortcode(id)))
    end
end

function Base.isless(a::T, b::T) where {T <: AbstractIdentifier}
    ca = idcode(a)
    cb = idcode(b)
    (isnothing(ca) || isnothing(cb)) && return isless(shortcode(a), shortcode(b))
    ca < cb
end
