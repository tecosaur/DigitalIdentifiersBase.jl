# FastIdentifiers.jl

A tiny framework for structured and validated identifier types.

## Types

```@docs
AbstractIdentifier
MalformedIdentifier
ChecksumViolation
```

## Interface

```@docs
Base.parse(::Type{<:AbstractIdentifier}, ::String)
Base.tryparse(::Type{<:AbstractIdentifier}, ::String)
Base.print(::IO, ::AbstractIdentifier)
FastIdentifiers.idcode
FastIdentifiers.idchecksum
FastIdentifiers.shortcode
FastIdentifiers.purl
FastIdentifiers.purlprefix
```

## Helper functions

```@docs
FastIdentifiers.@reexport
FastIdentifiers.parseid
FastIdentifiers.parsefor
FastIdentifiers.lchopfolded
```
