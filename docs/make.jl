# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

using Documenter
using FastIdentifiers

Core.eval(FastIdentifiers,
    quote
        """
            parse(::Type{T<:AbstractIdentifier}, representation::String) -> T

        Parse a string `representation` of a `T` identifier.

        All unambiguous identifiers should be parseable, for example:
        - `abc123` (minimal form/shortcode)
        - `example:abc123` (canonical form)
        - `https://example.com/abc123` (full URL)

        Throws [`MalformedIdentifier`](@ref) for invalid formats or [`ChecksumViolation`](@ref)
        for checksum validation failures.

        This function uses the [`parseid`](@ref) implementation defined by each identifier type.
        """
        Base.parse(::Type{<:AbstractIdentifier}, ::String) = nothing

        """
            tryparse(::Type{T<:AbstractIdentifier}, representation::String) -> Union{T, Nothing}

        Attempt to parse a string `representation` of a `T` identifier.

        See [`parse`](@ref Base.parse(::Type{<:AbstractIdentifier}, ::String)) for more details.
        """
        Base.tryparse(::Type{<:AbstractIdentifier}, ::String) = nothing

        """
            print(io::IO, id::AbstractIdentifier)

        Print an identifier `id` to the given `io` stream.

        The identifier should be printed in the most "standard" form.
        By default, this prints the PURL if available, otherwise the shortcode. In
        limited contexts, only the shortcode is printed, prefixed by the identifier type name
        (unless the context is also compact). This behaviour is a heuristic to pick
        the most appropriate form to print based on the context.
        """
        Base.print(::IO, ::AbstractIdentifier) = nothing
    end)

makedocs(;
    modules=[FastIdentifiers],
    pages=[
        "Index" => "index.md",
    ],
    format=Documenter.HTML(assets=["assets/favicon.ico"]),
    sitename="FastIdentifiers.jl",
    authors="tecosaur",
    warnonly=[:missing_docs],
)

deploydocs(repo="github.com/tecosaur/FastIdentifiers.jl")
