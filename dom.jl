include("gf.jl")

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

function FZ()
    x = 3
    if ?
        z = x
        x = 2
    else
        z = x
        while ?
            x = 1
        end
    end
    y = x
    @goto a
    return y
    @label a
    print()
end

function FZ()
    while ?
        print()
    end
end

function dep(P, idom)
    (i,j) = P
    if i[1] == 0
        (0, j)
    else
        (i0,j0) = dep(idom[i], idom)
        (i0+1,j0+j)
    end
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

function iterated_df(code, dtree, pc)
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

function find_def_fast(code, dtree, defs, pc)
    l = find_label(code, pc)
    if l in defs
        return l
    else
        id,off = dtree.idom[l]
        pc = (id == 0 ? 1 : code.label_pc[id]) + off
        return find_def_fast(code, dtree, defs, pc)
    end
end
using Color
function test(code, dtree)
    a = rand(1:length(code.body))
    l = find_label(code, a)
    if l > length(dtree.idom) || (l != 0 && dtree.idom[l] == -1) # investigate
        return test(code, dtree)
    end
    df = iterated_df(code, dtree, l == 0 ? 1 : code.label_pc[l]+1)
    defs = Set([0, l, df...])
    @show l
    fdfs = Set{Int}()
    m = Dict{Int,Int}()
    colors = map(hex, distinguishable_colors(length(defs)+1))
    colid = 2
    colnum = Dict{Int,String}()
    for i=1:length(code.body)
        ll = find_label(code,i)
        (ll == 0 || dtree.idom[ll][1] == -1) && continue
        fdef = find_def_fast(code, dtree, defs, i)
        m[i] = fdef
        if !haskey(colnum, fdef)
            colnum[fdef] = colors[colid]
            colid += 1
        end
        push!(fdfs, fdef)
    end
    fdfs == defs, fdfs, defs, [ i => haskey(colnum, m[i]) ? colnum[m[i]] : "000000" for i=keys(m) ]
end

function rndp(dtree)
    path = [0]
    while true
        ep = path[end]
        s = dtree.succ[ep+1]
        isempty(s) && break
        push!(path,rand(s)[1])
    end
    id = [0]
    for i=2:length(path)
        d = dtree.idom[path[i]][1]
        k = findfirst(path,d)
        k > 0 && k <= i || (@show k i d path; error())
        push!(id, d)
    end
    collect(zip(path, id))
end

function to_dot(io, code, dtree,colors = Dict{Int,String}())
    println(io, "digraph g {")
    N = length(code.label_pc)
    println(io, "graph [ rankdir = \"LR\" ];")
    for i = 0:N
        println(io, "\"n$i\" [")
#        i > 0 && haskey(colors, code.label_pc[i]) && println(io, "color = \"#$(colors[code.label_pc[i]])\"")
        println(io, "label = <<table border=\"0\" cellspacing=\"0\">")
        j0 = i == 0 ? 1 : code.label_pc[i]
        j = j0
        println(io, "<tr><td port=\"r\" border=\"1\">", i, "</td></tr>")
        j += 1
        stopnext = false
        while j <= length(code.body)
            e = code.body[j]
            if count(t -> t[2]+j0 == j, dtree.succ[i+1]) > 0
                c = haskey(colors,j) ? colors[j] : "000000"
                print(io, "<tr><td port=\"f$j\" border=\"1\" bgcolor=\"#$c\">")
                if isa(e,Expr) && e.head === :gotoifnot
                    print(io, "br? ", e.args[2])
                elseif isa(e,GotoNode)
                    print(io, "br! ", e.label)
                end
                print(io, "</td></tr>")
            end
            j += 1
            stopnext && break
            (j in code.label_pc) && (stopnext = true)
        end
        println(io, "<tr><td border=\"1\">$(j-j0)</td></tr>")
        println(io, "</table>>")
        println(io, "shape = \"none\"")
        println(io, "];")
    end
    for i=0:N
        rpc = i == 0 ? 1 : code.label_pc[i]
        for (s,o) in dtree.succ[i+1]
            println(io, "\"n$i\":f$(rpc+o) -> \"n$s\":r;")
        end
    end
    for i=1:N
        d,o = dtree.idom[i]
        dest = o == 0 ? "r" : string("f", (d == 0 ? 1 : code.label_pc[d])+o)
        println(io, "\"n$i\":r -> \"n$d\":$dest [ color = \"red\" style = \"dashed\" arrowType=\"empty\" ];")
    end
    for i=0:N
        for (k,o0) in dtree.front[i+1]
            o = o0[2]
            dest = o == 0 ? "r" : string("f", (i == 0 ? 1 : code.label_pc[i])+o)
            #println(io, "\"n$i\":$dest -> \"n$k\":r [ color = \"green\" ];")
        end
    end
    println(io, "}")
end

#A = (Any,Any,Any)
#A = (Matrix{Float64},)
#F = show
#A = (IO, Base.Sys.CPUinfo,Bool,String)
#F = 
#A = (Matrix{Float64},)#(SparseMatrixCSC,SparseMatrixCSC)
#F = Core.Inference.inlining_pass
#A = ()
#F = FZ
F = Pkg.Resolve.sanity_check
A = (Any,Any)
#@show code_lowered(F,A)
code = GreenFairy.code_for_method(Base._methods(F, A, -1)[1], A)
#@show build_dfs(code.v)
dtree = @show (build_dom_tree(code.v))

function allfuns(m,dm = Set{Any}())
    nlabel = Int[]
    fs = []
    push!(dm,m)
    for name in names(m)
        f = try
            getfield(m,name)
        catch
            continue
        end
        if isa(f,Function) && isgeneric(f)
            d = f.env.defs
            while isa(d,Method)
                ast = Base.uncompressed_ast(d.func.code)
                c = count(e->isa(e,LabelNode), ast.args[3].args)
                #count(e->isa(e,Expr) && e.head === :enter, ast.args[3].args) > 0 && @goto endl
                push!(nlabel, c)
                push!(fs, d)
                @label endl
                d = d.next
            end
        end
        if isa(f,Module) && !(f in dm)
            nl2,fs2 = allfuns(f, dm)
            append!(nlabel,nl2)
            append!(fs,fs2)
        end
    end
    nlabel,fs
end

#@show [iterated_df(c.v, dtree, i) for i = 1:length(c.v.body)]
#test(c.v, dtree)
#open(io -> to_dot(io, c.v, dtree), "plop.dot", "w")
