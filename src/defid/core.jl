# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Core types, constants, and state-mutation helpers for @defid codegen.
#
# Defines the data structures threaded through pattern walking
# (IdExprs, NodeCtx, DefIdState, ParseBranch) and the small helpers
# that every pattern handler calls to track bits, bytes, errors,
# and segments.

## Type aliases

const ExprVarLine = Union{Expr, Symbol, LineNumberNode}
const NodeCtx = Base.ImmutableDict{Symbol, Any}

# Schema for a single value-carrying pattern node in the packed representation.
const IdValueSegment = @NamedTuple{
    nbits::Int,                            # bits consumed in packed representation
    kind::Symbol,                          # :digits, :choice, :letters, :alphnum, :literal, :skip
    label::Symbol,                         # attr_fieldname (inside field) or gensym (anonymous)
    desc::String,                          # human-readable description
    argtype::Any,                          # :Integer, :Symbol, :AbstractString, or nothing (non-parameterisable)
    argvar::Symbol,                        # gensym used as parameter placeholder in impart
    extract::Vector{ExprVarLine},          # bits → typed value (last expr is the value)
    impart::Vector{Any},                   # argvar → packed bits (validate + encode + orshift)
    condition::Union{Nothing, Symbol},     # optional scope gensym, nothing if required
}

# Accumulator for the expression vectors built during pattern walking.
const IdExprs = @NamedTuple{
    parse::Vector{ExprVarLine},
    print::Vector{ExprVarLine},
    segments::Vector{IdValueSegment},
    properties::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}},
}

## Structs

"""
    ParseBranch

Per-branch byte counters for tracking parse/print bounds through optional nesting.

The root branch covers the required pattern; each `optional(...)` forks a child.
`parsed_min`/`parsed_max` track cumulative input bytes consumed;
`print_min`/`print_max` track cumulative output bytes produced.
Length-check sentinels reference these counters so that `resolve_length_checks!`
can fold static guarantees and emit minimal runtime checks.
"""
mutable struct ParseBranch
    const id::Int
    const parent::Union{Nothing, ParseBranch}
    const scope::Union{Nothing, Symbol}
    const start_min::Int
    parsed_min::Int
    parsed_max::Int
    print_min::Int
    print_max::Int
end

# Global mutable state for @defid macro expansion (bit width, branches, errors).
mutable struct DefIdState
    const name::Symbol
    const mod::Module
    bits::Int
    const casefold::Bool
    const purlprefix::Union{Nothing, String}
    const branches::Vector{ParseBranch}
    const errconsts::Vector{String}
end

## Constants

const KNOWN_KEYS = (
    choice = (:casefold, :is),
    digits = (:base, :min, :max, :pad),
    letters = (:upper, :lower, :casefold),
    alphnum = (:upper, :lower, :casefold),
    skip = (:casefold, :print),
    _global = (:purlprefix,),
)

const ALL_KNOWN_KEYS = Tuple(unique(collect(Iterators.flatten(values(KNOWN_KEYS)))))

## Bit-sizing

"""
    cardbits(n::Integer) -> Int

Return the number of bits needed to represent `n` distinct values (i.e. `ceil(log2(n))`
computed via leading zeros).
"""
cardbits(n::Integer) = 8 * sizeof(n) - leading_zeros(n)

"""
    cardtype(minbits::Int) -> DataType

Return the smallest unsigned integer type that can hold `minbits` bits.

Returns `Nothing` for zero bits. Supports up to 128 bits (`UInt128`).
"""
Base.@assume_effects :foldable function cardtype(minbits::Int)
    iszero(minbits) && return Nothing
    logtypesize = 1 + 8 * sizeof(minbits) - leading_zeros(cld(minbits, 8) - 1)
    if logtypesize > 5
        throw(ArgumentError(
            "Cannot allocate more than 128 bits for an identifier field, but $minbits bits were requested"))
    end
    (UInt8, UInt16, UInt32, UInt64, UInt128)[logtypesize]
end

## State mutation helpers

function inc_parsed!(nctx::NodeCtx, dmin, dmax)
    b = nctx[:current_branch]
    b.parsed_min += dmin
    b.parsed_max += dmax
end
function inc_print!(nctx::NodeCtx, dmin, dmax)
    b = nctx[:current_branch]
    b.print_min += dmin
    b.print_max += dmax
end

"""
    defid_errmsg(state::DefIdState, msg::String) -> Int

Register a compile-time error message and return its 1-based index.

The index is used as an error code in the generated `parsebytes` function,
mapped back to the message string at `parse` time.
"""
function defid_errmsg(state::DefIdState, msg::String)
    idx = findfirst(==(msg), state.errconsts)
    isnothing(idx) || return idx
    push!(state.errconsts, msg)
    length(state.errconsts)
end

## Segment and property assembly

"""
    push_value_segment!(exprs::IdExprs; nbits, kind, fieldvar, desc,
                        argvar, base_argtype, option,
                        extract_setup, extract_value,
                        present_check, impart_body)

Push a value-carrying segment with the standard required/optional split.

For required fields, `extract` is the setup expressions followed by the
value expression. For optional fields, the value expression is wrapped
in a presence check, and `impart` is wrapped in an `isnothing` guard.
Also appends a `__segment_printed` marker to `exprs.print` for later
use by `segments(id)`.
"""
function push_value_segment!(exprs::IdExprs;
        nbits::Int, kind::Symbol, fieldvar::Symbol, desc::String,
        argvar::Symbol, base_argtype::Any, option::Union{Nothing, Symbol},
        extract_setup::Vector{ExprVarLine}, extract_value::Any,
        present_check::Any, impart_body::Vector{Any})
    seg_extract = if isnothing(option)
        ExprVarLine[extract_setup..., extract_value]
    else
        ExprVarLine[extract_setup..., :(if $present_check; $extract_value end)]
    end
    seg_impart, seg_argtype = if isnothing(option)
        copy(impart_body), base_argtype
    else
        wrapped = Expr(:if, :(!isnothing($argvar)), Expr(:block, impart_body...))
        Any[wrapped], :(Union{$base_argtype, Nothing})
    end
    label = Symbol(chopprefix(String(fieldvar), "attr_"))
    push!(exprs.segments, IdValueSegment((
        nbits, kind, label, desc,
        seg_argtype, argvar, seg_extract, seg_impart, option)))
    push!(exprs.print, :(__segment_printed = $(length(exprs.segments))))
end

"""
    emit_print_detect!(exprs::IdExprs, nctx::NodeCtx, option, extracts, present_check)

Route extract expressions and optional presence detection to the right target.

For optional fields (non-nothing `option`), appends to `nctx[:oprint_detect]`
so the enclosing `defid_optional!` can emit them before the conditional print
block. For required fields, appends directly to `exprs.print`.
"""
function emit_print_detect!(exprs::IdExprs, nctx::NodeCtx,
                            option, extracts::Vector{ExprVarLine}, present_check)
    if !isnothing(option)
        push!(nctx[:oprint_detect], extracts..., :($option = $present_check))
    else
        append!(exprs.print, extracts)
    end
end

## Bit packing

zero_parsed_expr(state::DefIdState) =
    if state.bits <= 8
        :(Core.bitcast($(esc(state.name)), 0x00))
    else
        :(Core.Intrinsics.zext_int($(esc(state.name)), 0x0))
    end

function defid_emit_pack(state::DefIdState, type::Type, value::Union{Symbol, Expr}, shift::Int)
    valcast = Expr(:call, :__cast_to_id, type, value)
    :(parsed = Core.Intrinsics.or_int(parsed, Core.Intrinsics.shl_int($valcast, (8 * sizeof($(esc(state.name))) - $shift))))
end

function defid_emit_extract(state::DefIdState, position::Int, width::Int)
    fT = cardtype(width)
    fval = :(Core.Intrinsics.lshr_int(id, 8 * sizeof($(esc(state.name))) - $position))
    ival = Expr(:call, :__cast_from_id, fT, fval)
    if width == sizeof(fT) * 8
        ival
    else
        fTmask = ~(typemax(fT) << width)
        :($ival & $fTmask)
    end
end
