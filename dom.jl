function dfs!(code, label, order, n, pred, succ)
    rpc = label == 0 ? 1 : code.label_pc[label]
    order[label+1] == typemax(Int) || return n
    pc = rpc+1
    body = code.body
    @show code
    N = length(body)
    n += 1
    order[label+1] = n
    while pc <= N
        e = body[pc]
        @show e
        o = pc-rpc
        if isa(e, GotoNode)
            l = (e::GotoNode).label+1
            push!(pred[l], (label,o))
            push!(succ[label+1], (l,o))
            n = dfs!(code, l, order, n, pred, succ)
            break
        elseif isa(e,Expr) && (e::Expr).head === :gotoifnot
            l = (e::Expr).args[2]::Int + 1
            push!(pred[l], (label,o))
            push!(succ[label+1], (l,o))
            n = dfs!(code, l, order, n, pred, succ)
        elseif isa(e,LabelNode)
            l = (e::LabelNode).label+1
            push!(pred[l], (label,o))
            push!(succ[label+1], (l,o))
            n = dfs!(code, l, order, n, pred, succ)
            break
        elseif isa(e, Expr) && (e::Expr).head === :return
            break
        end
        pc += 1
    end
    n
end

function build_dfs(code)
    N = length(code.label_pc)
    order = fill(typemax(Int), N+1)
    pred = [Array(Tuple{Int,Int},0) for _ = 1:N]
    succ = [Array(Tuple{Int,Int},0) for _ = 1:N+1]
    dfs!(code, 0, order, 0, pred, succ)
    order, pred, succ
end

function inter_idom(i, j, order, idom)
    while i[1] != j[1]
        i[1] == -1 && return j
        j[1] == -1 && return i
        if order[i[1]+1] > order[j[1]+1]
            i = idom[i[1]]
        else
            j = idom[j[1]]
        end
    end
    return (i[1], min(i[2],j[2]))
end

type DomTree
    idom :: Vector{Tuple{Int,Int}} # label => immediate dominator
    pred :: Vector{Vector{Tuple{Int,Int}}} # label => (pred label, offset), ...
    succ :: Vector{Vector{Tuple{Int,Int}}} # label+1 => (succ label, offset) ...
    order :: Vector{Int} # label+1 => rev po index
    order_perm :: Vector{Int} # reverse perm
    front :: Vector{Dict{Int,Tuple{Int,Int}}} # label => dom frontier
end

function build_dom_tree(code)
    order, pred, succ = build_dfs(code)
    changed = true
    order_perm = sortperm(order)
    N = length(code.label_pc)
    idom = fill((-1,0), N)
    @assert order_perm[1] == 1
    while changed
        changed = false
        for i=2:N+1
            ni = order_perm[i]-1
            
            new_idom = (-1,0)
            for p in pred[ni]
                new_idom = inter_idom(new_idom, p, order, idom)
            end
            if new_idom != idom[ni]
                changed = true
            end
            idom[ni] = new_idom
        end
    end
    #@assert count(x->x[1] < 0, idom) == 0
    front = dom_front(idom, pred)
    DomTree(idom, pred, succ, order, order_perm, front)
end

function update_front!(d, k, v)
    if haskey(d,k)
        ov = d[k]
        @assert ov[1] == v[1]
        d[k] = (v[1],max(v[2],ov[2]))
    else
        d[k] = v
    end
end

function dom_front(idom, pred)
    N = length(idom)
    domfront = [Dict{Int,Tuple{Int,Int}}() for i=1:N+1]
    for i=1:N
        length(pred[i]) <= 1 && continue
        iid,iio = idom[i]
        for (p,o) in pred[i]
            runner,ro = p,o
            while runner != iid && runner != 0
                d = domfront[runner+1]
                update_front!(d, i, (0, ro))
                runner,ro = idom[runner]
            end
            @assert runner == iid
            ro > iio && update_front!(domfront[runner+1],i,(iio,ro))
        end
    end
    domfront
end

function find_label(code, pc)
    lpc = code.label_pc
    lbl = 0
    for i=1:length(lpc)
        if lpc[i] < pc
            if lbl == 0 || lpc[lbl] < lpc[i]
                lbl = i
            end
        end
    end
    lbl
end

# right before pc
function df!(code, dtree, pc, df)
    lbl = find_label(code, pc)
    lbl > 0 || return
    off = pc - code.label_pc[lbl]
    for (k,(lb,ub)) in dtree.front[lbl+1]
        (lb < off <= ub) && push!(df, k)
    end
end

function iterated_domfront(code, dtree, pc)
    idf = Set{Int}()
    todo = Set{Int}()
    df!(code, dtree, pc, todo)
    while !isempty(todo)
        lb = pop!(todo)
        push!(idf, lb)
        df!(code, dtree, code.label_pc[lb]+1, todo)
        setdiff!(todo, idf)
    end
    idf
end
type DefStore
    defs :: Dict{Int,Vector{Int}} # TODO optimize for single def
    ndefs :: Int
end
DefStore() = DefStore(Dict{Int,Vector{Int}}(), 0)
function add_def!(code, dtree::DomTree, d::DefStore, pc::Int)
    l = find_label(code, pc)
    def_delta = 0
    defs = d.defs
    if !haskey(defs, l)
        defs[l] = Int[pc]
        def_delta += 1
    else
        ldef = defs[l]
        if !(pc in ldef)
            push!(ldef, pc)
            def_delta += 1
            sort!(ldef) # TODO ugh
        end
    end
    for l in iterated_domfront(code, dtree, pc)
        lpc = code.label_pc[l]+1
        if !haskey(defs, l)
            defs[l] = Int[lpc]
            def_delta += 1
        else
            ldef = defs[l]
            if ldef[1] != lpc
                unshift!(ldef, lpc)
                @assert issorted(ldef)
                def_delta += 1
            end
        end
    end
    d.ndefs += def_delta
end
function find_def_fast(code, dtree, ds, pc)
    l = find_label(code, pc)
    defs = ds.defs
    if haskey(defs, l)
        local_defs = defs[l]
        for i = 1:length(local_defs)
            ld = local_defs[end - i + 1]
            if ld <= pc
                return (l,ld)
            end
        end
    end
    @assert(l != 0, "use not dominated by a def")
    id,off = dtree.idom[l]
    pc = (id == 0 ? 1 : code.label_pc[id]) + off
    return find_def_fast(code, dtree, ds, pc)
end
export DefStore,DomTree,find_label,add_def!,find_def_fast
