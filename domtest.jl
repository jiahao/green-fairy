include("gf.jl")

using GreenFairy
using Color
function test(code, dtree, N)
    ds = GreenFairy.DefStore()
    add_def!(code, dtree, ds, 0)
    for i=1:N
        a = rand(1:length(code.body))
        @show find_label(code, a)
        add_def!(code, dtree, ds, a)
    end
    m = Dict{Int,Tuple{Int,Int}}()
    colors = map(hex, distinguishable_colors(ds.ndefs+1))
    colid = 2
    colnum = Dict{Tuple{Int,Int},String}()
    for i=1:length(code.body)
        ll = find_label(code,i)
        (ll == 0 || dtree.idom[ll][1] == -1) && continue
        fdef = find_def_fast(code, dtree, ds, i)
        m[i] = fdef
        if !haskey(colnum, fdef)
            colnum[fdef] = colors[colid]
            colid += 1
        end
    end
    ds, [ i => haskey(colnum, m[i]) ? colnum[m[i]] : "000000" for i=keys(m) ]
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
                print(io, "[", j-j0, "]")
                if isa(e,Expr) && e.head === :gotoifnot
                    print(io, "?")
                elseif isa(e,GotoNode)
                    print(io, "!")
                end
                print(io, "</td></tr>")
            end
            j += 1
            stopnext && break
            (j in code.label_pc) && (stopnext = true)
        end
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

function test_dt(F, A, N=10)
    code = GreenFairy.code_for_method(Base._methods(F, A, -1)[1], A)
    dtree = @show (GreenFairy.build_dom_tree(code.v))
    #@show build_dfs(code.v)
    c,d = test(code.v,dtree,N)
    open(io -> to_dot(io,code.v,dtree,d), "plop.dot", "w")
    open(io -> run(pipe(`dot plop.dot -Tsvg`, io)), "plop.svg", "w")
end

function allfuns(m,dm = Set{Any}())
    nlabel = Int[]
    fs = []
    push!(dm,m)
    for name in names(m, true, true)
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
