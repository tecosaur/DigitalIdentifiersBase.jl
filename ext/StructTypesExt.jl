# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module StructTypesExt

using FastIdentifiers: AbstractIdentifier
using StructTypes

StructTypes.StructType(::Type{<:AbstractIdentifier}) = StructTypes.StringType()
StructTypes.construct(::Type{T}, id::String; _kw...) where {T<:AbstractIdentifier} = parse(T, id)

end
