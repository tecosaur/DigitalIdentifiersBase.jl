# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Placeholder sentinel emission, resolution, and AST post-processing.
#
# During pattern walking, length checks and type casts are emitted as
# placeholder sentinel calls (e.g. `__length_check`, `__cast_to_id`)
# since the final byte counts and type sizes aren't known yet. After
# the full pattern has been walked, `resolve_length_checks!`,
# `fold_static_branches!`, and `implement_casting!` replace these
# sentinels with concrete expressions or compile-time constants.

## Sentinel emission

function defid_lengthcheck(state::DefIdState, nctx::NodeCtx, n_expr, n_min::Int=n_expr, n_max::Int=n_min)
    b = nctx[:current_branch]
    Expr(:call, :__length_check, b.id, b.parsed_max, n_min, n_max, n_expr)
end

function defid_static_lengthcheck(state::DefIdState, nctx::NodeCtx, n::Int)
    b = nctx[:current_branch]
    Expr(:call, :__static_length_check, b.id, b.parsed_max, n)
end

function defid_lengthbound(state::DefIdState, nctx::NodeCtx, n::Int)
    b = nctx[:current_branch]
    Expr(:call, :__length_bound, b.id, b.parsed_max, n)
end

## Sentinel resolution

"""
    resolve_length_checks!(exprlikes, branches) -> exprlikes

Walk the AST and replace all length-related sentinels with concrete expressions.

Each sentinel type uses the emitting branch's `parsed_min` as the static guarantee:
- `__length_check` → `true` or runtime `nbytes - pos + 1 >= n`
- `__static_length_check` → compile-time `Bool` (never runtime)
- `__length_bound` → `n` or `min(n, nbytes - pos + 1)`
- `__branch_check(Bool, id)` → resolved via `resolve_branch_check`
- `__branch_check(Int, id)` → left for `defid_parsebytes` (root upfront check)
"""
function resolve_length_checks!(exprlikes::Vector{<:ExprVarLine}, branches::Vector{ParseBranch})
    remove = Int[]
    for (idx, expr) in enumerate(exprlikes)
        expr isa Expr || continue
        if Meta.isexpr(expr, :call) && first(expr.args) === :__branch_check
            if expr.args[2] === Bool
                exprlikes[idx] = resolve_branch_check(branches[expr.args[3]])
            end
            continue
        end
        result = resolve_sentinels!(expr, branches)
        if result === :remove
            push!(remove, idx)
        elseif !isnothing(result)
            exprlikes[idx] = result
        end
    end
    deleteat!(exprlikes, remove)
end

function resolve_branch_check(b::ParseBranch)
    local_min = b.parsed_min - b.start_min
    if local_min <= 0 || (!isnothing(b.parent) && b.parent.parsed_min >= b.parsed_min)
        true
    else
        :(nbytes - pos + 1 >= $local_min)
    end
end

# Recursive AST walker that resolves sentinel calls in-place.
# Branch-local `parsed_min` is the guarantee, so optionals don't inflate
# the max seen by sentinels in other branches.
function resolve_sentinels!(expr::Expr, branches::Vector{ParseBranch})
    remove = Int[]
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        sentinel = if Meta.isexpr(arg, :call)
            first(arg.args)
        end
        if sentinel === :__length_check
            resolved = resolve_length_check(arg, branches)
            if resolved isa Expr
                arg.head, arg.args = resolved.head, resolved.args
            else
                expr.args[i] = resolved
            end
        elseif sentinel === :__length_bound
            branch_id, emission_max, n = arg.args[2:end]
            if branches[branch_id].parsed_min - emission_max >= n
                expr.args[i] = n
            else
                r = :(min($n, nbytes - pos + 1))
                arg.head, arg.args = r.head, r.args
            end
        elseif sentinel === :__static_length_check
            branch_id, emission_max, n = arg.args[2:end]
            expr.args[i] = branches[branch_id].parsed_min - emission_max >= n
        elseif sentinel === :__branch_check
            if arg.args[2] === Bool
                resolved = resolve_branch_check(branches[arg.args[3]])
                if resolved isa Expr
                    arg.head, arg.args = resolved.head, resolved.args
                else
                    expr.args[i] = resolved
                end
            end
        else
            result = resolve_sentinels!(arg, branches)
            if result === :remove
                push!(remove, i)
            elseif !isnothing(result)
                expr.args[i] = result
            end
        end
    end
    deleteat!(expr.args, remove)
    nothing
end

function resolve_length_check(expr::Expr, branches::Vector{ParseBranch})
    branch_id, emission_max, _, n_max, n_expr = expr.args[2:end]
    if branches[branch_id].parsed_min - emission_max >= n_max
        true
    else
        :(nbytes - pos + 1 >= $n_expr)
    end
end

## Static branch folding

"""
    fold_static_branches!(items::Vector{<:ExprVarLine}) -> items

Resolve `if true`/`if false` and their negations statically, splicing the
taken branch in place. Recurses into nested expressions and repeats until
fixpoint.
"""
function fold_static_branches!(items::Vector{<:ExprVarLine})
    while fold_branches!(items) end
    items
end

function fold_branches!(items::AbstractVector)
    splices = Tuple{Int, Vector{Any}}[]
    changed = false
    for (i, item) in enumerate(items)
        item isa Expr || continue
        if item.head in (:if, :elseif) && item.args[1] isa Bool
            push!(splices, (i, take_branch(item)))
            changed = true
        elseif item.head in (:if, :elseif) &&
               Meta.isexpr(item.args[1], :call, 2) &&
               item.args[1].args[1] === :! && item.args[1].args[2] isa Bool
            item.args[1] = !item.args[1].args[2]
            push!(splices, (i, take_branch(item)))
            changed = true
        elseif item.head === :|| && item.args[1] isa Bool
            push!(splices, (i, if item.args[1] Any[] else Any[item.args[2]] end))
            changed = true
        elseif item.head === :&& && item.args[1] isa Bool
            push!(splices, (i, if item.args[1] Any[item.args[2]] else Any[] end))
            changed = true
        else
            changed |= fold_branches!(item.args)
        end
    end
    for (i, replacement) in reverse(splices)
        splice!(items, i, replacement)
    end
    changed
end

function take_branch(expr::Expr)
    if expr.args[1]::Bool
        body = expr.args[2]
    elseif length(expr.args) >= 3
        body = expr.args[3]
        if body isa Expr && body.head === :elseif
            body.head = :if
        end
    else
        return Any[]
    end
    if body isa Expr && body.head === :block
        filter(e -> !(e isa LineNumberNode), body.args)
    else
        Any[body]
    end
end

## Casting resolution

"""
    implement_casting!(state, exprlikes) -> exprlikes

Replace `__cast_to_id` / `__cast_from_id` sentinels with the appropriate
`Core.bitcast`, `zext_int`, or `trunc_int` call, now that the final type
size is known.

Compares physical type sizes (`sizeof`) for intrinsic selection, since
`zext_int`/`trunc_int` operate on physical widths — not logical bit counts.
This matters for embedded `@defid` types whose `nbits` may be less than
`8*sizeof`.
"""
function implement_casting!(state::DefIdState, exprlikes::Vector{<:ExprVarLine})
    targetsize = cld(state.bits, 8)
    for expr in exprlikes
        if expr isa Expr
            implement_casting!(expr, state.name, targetsize)
        end
    end
    exprlikes
end

function implement_casting!(expr::Expr, name::Symbol, targetsize::Int)
    if Meta.isexpr(expr, :call, 3) && first(expr.args) in (:__cast_to_id, :__cast_from_id)
        casttype, valtype, value = expr.args
        targettype, targetbits, valbits = if casttype == :__cast_to_id
            esc(name), targetsize, sizeof(valtype)
        else
            valtype, sizeof(valtype), targetsize
        end
        expr.args[1:3] = if valbits == targetbits
            :(Core.bitcast($targettype, $value)).args
        elseif valbits < targetbits
            :(Core.Intrinsics.zext_int($targettype, $value)).args
        else
            :(Core.Intrinsics.trunc_int($targettype, $value)).args
        end
    else
        for arg in expr.args
            if arg isa Expr
                implement_casting!(arg, name, targetsize)
            end
        end
    end
    expr
end
