# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module StructUtilsExt

using FastIdentifiers: AbstractIdentifier
using StructUtils

StructUtils.structlike(::Type{<:AbstractIdentifier}) = false
StructUtils.lower(id::AbstractIdentifier) = string(id)
StructUtils.lift(::Type{T}, id::String) where {T<:AbstractIdentifier} = parse(T, id)

end
