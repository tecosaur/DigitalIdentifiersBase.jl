# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Pattern dispatch and structural handlers (field capture, optional branching).

## Pattern dispatch

function defid_dispatch!(exprs::IdExprs,
                         state::DefIdState, nctx::NodeCtx,
                         node::Any, args::Vector{Any})
    if node isa QuoteNode
        defid_field!(exprs, state, nctx, node, args)
    elseif node === :seq
        for arg in args
            defid_dispatch!(exprs, state, nctx, arg)
        end
    elseif node === :optional
        defid_optional!(exprs, state, nctx, args)
    elseif node === :skip
        defid_skip!(exprs, state, nctx, args)
    elseif node === :choice
        defid_choice!(exprs, state, nctx, args)
    elseif node === :literal
        length(args) == 1 || throw(ArgumentError("Expected exactly one argument for literal, got $(length(args))"))
        lit = args[1]
        lit isa String || throw(ArgumentError("Expected a string literal for literal, got $lit"))
        defid_literal!(exprs, state, nctx, lit)
    elseif node === :digits
        defid_digits!(exprs, state, nctx, args)
    elseif node === :letters
        defid_charseq!(exprs, state, nctx, args, :letters)
    elseif node === :alphnum
        defid_charseq!(exprs, state, nctx, args, :alphnum)
    elseif node === :embed
        defid_embed!(exprs, state, nctx, args)
    else
        throw(ArgumentError("Unknown pattern node $node"))
    end
end

function defid_dispatch!(exprs::IdExprs,
                         state::DefIdState, nctx::NodeCtx,
                         thing::Any)
    if Meta.isexpr(thing, :tuple)
        args = Any[]
        for arg in thing.args
            if Meta.isexpr(arg, :(=), 2)
                kwname, kwval = arg.args
                kwname ∈ ALL_KNOWN_KEYS ||
                    throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments are: $(join(ALL_KNOWN_KEYS, ", "))"))
                nctx = NodeCtx(nctx, kwname, kwval)
            else
                push!(args, arg)
            end
        end
        defid_dispatch!(exprs, state, nctx, :seq, args)
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
                nctx = NodeCtx(nctx, kwname, kwval)
            else
                push!(args, arg)
            end
        end
        defid_dispatch!(exprs, state, nctx, name, args)
    elseif thing isa String
        defid_literal!(exprs, state, nctx, thing)
    elseif thing === :__first_nonskip
        root = nctx[:current_branch]
        root.parsed_min = 0
        root.parsed_max = 0
        push!(exprs.parse, Expr(:call, :__branch_check, root.id, nothing))
    end
end

## Field capture

function defid_field!(exprs::IdExprs,
                      state::DefIdState, nctx::NodeCtx,
                      node::QuoteNode,
                      args::Vector{Any})
    isnothing(get(nctx, :fieldvar, nothing)) || throw(ArgumentError("Fields may not be nested"))
    nctx = NodeCtx(nctx, :fieldvar, Symbol("attr_$(node.value)"))
    initial_segs = length(exprs.segments)
    initialprints = length(exprs.print)
    for arg in args
        defid_dispatch!(exprs, state, nctx, arg)
    end
    new_value_segs = filter(s -> !isnothing(s.argtype), @view exprs.segments[initial_segs+1:end])
    isempty(new_value_segs) && throw(ArgumentError("Field $(node.value) does not capture any value"))
    if length(new_value_segs) == 1
        push!(exprs.properties, node.value => new_value_segs[1].label)
    else
        # Multi-node field: property assembles via IOBuffer from print expressions
        propprints = map(strip_segsets! ∘ copy, exprs.print[initialprints+1:end])
        filter!(e -> !Meta.isexpr(e, :(=), 2) || first(e.args) !== :__segment_printed, propprints)
        push!(exprs.properties, node.value => ExprVarLine[(
            quote
                io = IOBuffer()
                $(propprints...)
                takestring!(io)
            end).args...])
    end
end

## Optional branching

function defid_optional!(exprs::IdExprs,
                         state::DefIdState, nctx::NodeCtx,
                         args::Vector{Any})
    popt = get(nctx, :optional, nothing)
    nctx = NodeCtx(nctx, :optional, gensym("optional"))
    nctx = NodeCtx(nctx, :oprint_detect, ExprVarLine[])
    # Fork a child branch for this optional scope
    parent = nctx[:current_branch]
    child = ParseBranch(length(state.branches) + 1, parent, nctx[:optional],
                        parent.parsed_min, parent.parsed_min, parent.parsed_max,
                        parent.print_min, parent.print_max)
    push!(state.branches, child)
    nctx = NodeCtx(nctx, :current_branch, child)
    oexprs = (; parse = ExprVarLine[], print = ExprVarLine[], segments = exprs.segments, properties = exprs.properties)
    if all(a -> a isa String, args)
        defid_choice!(oexprs, state, nctx, push!(Any[join(Vector{String}(args))], ""))
    else
        for arg in args
            defid_dispatch!(oexprs, state, nctx, arg)
        end
    end
    # Merge max back to parent; min stays unchanged (optional content doesn't raise the guarantee)
    parent.parsed_max = Base.max(parent.parsed_max, child.parsed_max)
    parent.print_max = Base.max(parent.print_max, child.print_max)
    optvar = nctx[:optional]
    # Rewind pos when the optional has multiple nodes: an early node may advance
    # pos before a later node fails and sets option=false
    needs_rewind = length(args) > 1 && !all(a -> a isa String, args)
    savedpos = if needs_rewind
        gensym("savedpos")
    end
    needs_rewind && push!(exprs.parse, :($savedpos = pos))
    branch_check = Expr(:call, :__branch_check, Bool, child.id)
    guard = if isnothing(popt)
        branch_check
    else
        :($popt && $branch_check)
    end
    push!(exprs.parse, :($optvar = $guard))
    push!(exprs.parse, :(if $optvar; $(oexprs.parse...) end))
    needs_rewind && push!(exprs.parse, :($optvar || (pos = $savedpos)))
    append!(exprs.print, nctx[:oprint_detect])
    push!(exprs.print, :(if $(nctx[:optional]); $(oexprs.print...) end))
end
