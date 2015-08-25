function dfs!(code, label, order, n, pred, succ)
    rpc = label == 0 ? 1 : code.label_pc[label]
    if rpc <= 0
        order[label+1] = -2
    end
    order[label+1] == 0 || return n
    order[label+1] = -1
    pc = rpc+1
    body = code.body
    N = length(body)
    while pc <= N
        e = body[pc]
        o = pc-rpc
        if isa(e, GotoNode)
            l = (e::GotoNode).label+1
            push!(pred[l], (label,pc))
            push!(succ[label+1], (l,pc))
            n = dfs!(code, l, order, n, pred, succ)
            break
        elseif isa(e,Expr) && (e::Expr).head === :gotoifnot
            l = (e::Expr).args[2]::Int + 1
            push!(pred[l], (label,pc))
            push!(succ[label+1], (l,pc))
            n = dfs!(code, l, order, n, pred, succ)
        elseif isa(e,LabelNode)
            l = (e::LabelNode).label+1
            pc -= 1
            push!(pred[l], (label,pc))
            push!(succ[label+1], (l,pc))
            n = dfs!(code, l, order, n, pred, succ)
            break
        elseif isa(e, Expr) && (e::Expr).head === :return
            break
        end
        pc += 1
    end
    n += 1
    order[label+1] = n
    n
end

function build_dfs(code)
    N = length(code.label_pc)
    order = zeros(Int, N+1)
    pred = Vector{Tuple{Int,Int}}[Array(Tuple{Int,Int},0) for _ = 1:N]
    succ = Vector{Tuple{Int,Int}}[Array(Tuple{Int,Int},0) for _ = 1:N+1]
    n = dfs!(code, 0, order, 0, pred, succ)
    order[find(order)] += length(order) - n # ensure root is the first component
    n = 0
    while true
        i = findfirst(order, 0)
        i == 0 && break        
        n = dfs!(code, i-1, order, n, pred, succ) 
    end
    #@assert isperm(filter(i->i>=1,order))
    m = maximum(order)
    @assert m > 0
    order = (1+m) .- order # reverse post order
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
    depth :: Vector{Int} # label => dominator depth
    pred :: Vector{Vector{Tuple{Int,Int}}} # label => (pred label, pc), ...
    succ :: Vector{Vector{Tuple{Int,Int}}} # label+1 => (succ label, pc) ...
    order :: Vector{Int} # label+1 => rev po index
    order_perm :: Vector{Int} # reverse perm
    front :: Vector{Dict{Int,Tuple{Int,Int}}} # label => dom frontier : [ front_label => front range ]
end

function inter_idom(code, dtree::DomTree, pc1::Int, pc2::Int)
    l1 = find_label(code, pc1)
    l2 = find_label(code, pc2)
    inter_idom((l1,pc1),(l2,pc2), dtree.order, dtree.idom)[2]
end

dom_depth(dtree, label) = label == 0 ? 0 : dtree.depth[label]

function compute_depth!(idom, depth, i)
    i != 0 || return 0
    depth[i] == -1 || return depth[i]
    id = idom[i][1]
    if id == -1
        return -1
    end
    d = compute_depth!(idom, depth, id)+1
    depth[i] = d
    d
end

function build_dom_tree(code, order, pred, succ, idom)
    any_changed = true
    order_perm = sortperm(order)
    N = length(code.label_pc)
    @assert order_perm[1] == 1

    while any_changed
        any_changed = false
        for i=2:N+1
            ni = order_perm[i]-1
            
            new_idom = (-1,0)
            no_pred_idom = true
            for p in pred[ni]
                if p[1] == 0 || idom[p[1]][1] != -1
                    no_pred_idom = false
                end
                new_idom = inter_idom(new_idom, p, order, idom)
            end
            if no_pred_idom
            elseif new_idom != idom[ni]
                any_changed = true
                idom[ni] = new_idom
            end
        end
    end

    depth = fill(-1, N)
    for i=1:N
        compute_depth!(idom, depth, i)
    end
    
    front = dom_front(idom, pred)
    DomTree(idom, depth, pred, succ, order, order_perm, front)
end

function build_dom_tree(code)
    order, pred, succ = build_dfs(code)
    N = length(pred)
    build_dom_tree(code, order, pred, succ, fill((-1,0), N))
end

# one day :
# - make this a proper incremental dominator tree update
#   i.e. find a convincing paper
# - add a symmetric del_edge! and use it to implement temporal sparsity
function add_edge!(code, dtree::DomTree, from::Int, dest::Int)
    from_lb = find_label(code, from)
    ((from_lb,from) in dtree.pred[dest]) && return dtree
    push!(dtree.pred[dest], (from_lb, from))
    push!(dtree.succ[from_lb+1], (dest, from))
    order,pred,succ = dtree.order,dtree.pred,dtree.succ
    #@show dtree.idom
    #dtinc = build_dom_tree(code, order, pred, succ, dest, dtree.idom)
    dtfull = build_dom_tree(code, order, pred, succ, fill((-1,0),length(pred)))
    #println("Add edge $from $dest")
    #@show pred
    #@show dtinc.idom
    #@show dtfull.idom
    #=if dtinc.idom != dtfull.idom
        error("incremental error")
    end=#
    dtfull
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
                runner == -1 && break
            end
            runner == -1 && continue
            #@assert runner == iid
            ro > iio && update_front!(domfront[runner+1],i,(iio,ro))
        end
    end
    domfront
end

function find_label(code, pc)
    lpc = code.label_pc
    lbl = 0
    for i=1:length(lpc)
        if lpc[i] >= 0 && lpc[i] <= pc
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
    for (k,(lb,ub)) in dtree.front[lbl+1]
        (lb < pc <= ub) && push!(df, k)
    end
end

function iterated_domfront(code, dtree, pc)
    idf = Array(Int,0)
    todo = Set{Int}()
    df!(code, dtree, pc, todo)
    order = dtree.order
    while !isempty(todo)
        lb = pop!(todo)
        (order[lb+1] in idf) && continue
        heappush!(idf, order[lb+1])
        df!(code, dtree, code.label_pc[lb], todo)
    end
    idf
end
type DefStore{T}
    defs :: Dict{Int,Vector{Int}} # label => pcs
    phis :: Dict{Int,Vector{Int}} # label => incoming defs
    phi_edges :: Dict{Int,Vector{Int}} # label => incoming pred pc
    ndefs :: Int
end
function Base.show(io::IO, ds::DefStore)
    println(io, "DefStore:")
    for (i,vi) in ds.defs
        print(io, "\t- $i ")
        for k in vi
            print(io, k, " ")
        end
        println(io)
    end
    for (i,vi) in ds.phis
        print(io, "\t- $i = phi( ")
        for k in vi
            print(io, k, " ")
        end
        print(io, ")")
        println(io)
    end
end
DefStore{T}(::Type{T}) = DefStore{T}(Dict{Int,Vector{Int}}(), Dict{Int,Vector{Int}}(), Dict{Int,Vector{Int}}(), 0)

function add_def!(code, dtree::DomTree, d::DefStore, pc::Int)
    l = find_label(code, pc)
    def_delta = 0
    defs = d.defs
    phis = d.phis
    phi_edges = d.phi_edges
    chgd = false
    if !haskey(defs, l)
        defs[l] = Int[pc]
        def_delta += 1
        chgd = true
    else
        ldef = defs[l]
        if !(pc in ldef)
            push!(ldef, pc)
            def_delta += 1
            sort!(ldef) # TODO ugh
            chgd = true
        end
    end
    chgd || return false

    operm = dtree.order_perm
    idf = iterated_domfront(code, dtree, pc)
    todos = Dict{Int,Vector{Int}}()
    for l in idf
        l = operm[l]-1
        get!(phis, l, Int[])
    end
    while !isempty(idf)
        lo = heappop!(idf)
        l = operm[lo]-1
        phi = get!(phis, l, Int[])
        phi_edge = get!(phi_edges, l, Int[])
        nfound = 0
        for (predl,predpc) in dtree.pred[l]
            predl == 0 || dtree.idom[predl][1] != -1 || continue
            orig_def = find_def_fast(code, dtree, d, predpc)[2]
            idx = findfirst(phi, orig_def)
            if idx == 0
                push!(phi, orig_def)
                push!(phi_edge, predpc)
                nfound += 1
                chgd = true
            else
                if idx <= length(phi) - nfound
                    tmp = phi[end - nfound]
                    phi[end - nfound] = phi[idx]
                    phi[idx] = tmp
                    tmp = phi_edge[end - nfound]
                    phi_edge[end - nfound] = phi_edge[idx]
                    phi_edge[idx] = tmp
                    nfound += 1
                end
            end
        end
        if nfound < length(phi)
            ndel = length(phi)-nfound
            deleteat!(phi, 1:ndel)
            deleteat!(phi_edge, 1:ndel)
            chgd = true
        end
        #chgd |= add_val!(d, l, lpc, val)
    end
    d.ndefs += def_delta
    chgd
end
function find_def_fast(code, dtree, ds, pc)
    l = find_label(code, pc)
    defs = ds.defs
    phis = ds.phis
    if haskey(defs, l)
        local_defs = defs[l]
        for i = 1:length(local_defs)
            ld = local_defs[end - i + 1]
            if ld <= pc
                return (l,ld)
            end
        end
    end
    if haskey(phis, l)
        return (l, code.label_pc[l])
    end
    @assert(l != 0, "use not dominated by a def")
    id,pc = dtree.idom[l]
    @assert(id != -1, "no idom for $l : $(dtree.idom) | $(dtree.pred)")
    return find_def_fast(code, dtree, ds, pc)
end
function dom_path_to!(code, dtree, pc_from, pc_to, p)
    from_label = find_label(code, pc_from)
    to_label = find_label(code, pc_to)
    if to_label == from_label
        return p
    else
        @assert(to_label != 0, "asked for a non dominating path from $pc_from")
        _, ipc = dtree.idom[to_label]
        unshift!(p, (ipc,code.label_pc[to_label]))
        return dom_path_to!(code, dtree, pc_from, ipc, p)
    end
end
dom_path_to(code, dtree, pc_from, pc_to) = dom_path_to!(code, dtree, pc_from, pc_to, Tuple{Int,Int}[])
export DefStore,DomTree,find_label,add_def!,find_def_fast,dom_path_to!,dom_path_to,inter_idom
