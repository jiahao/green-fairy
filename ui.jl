if !isdefined(Main,:GreenFairy)
    include("gf.jl")
end
module UI
using GreenFairy
using Patchwork
type CodeTable
    s :: Scheduler
    fc :: Int
    e :: Vector{UTF8String}
    tree :: Elem
    active :: Vector{Int}
end
function CodeTable(s,fc)
    code = s.funs[fc]
    n = length(code.body)
    e = Array(UTF8String, n)
    for i=1:n
        b = IOBuffer()
        Meta.show_sexpr(b, code.body[i])
        e[i] = takebuf_string(b)
    end
    CodeTable(s,fc,e)
end
const arrow_sym = "➡"
function CodeTable(s,fc,e)
    code = s.funs[fc]
    ls = s.states.funs[fc]
    n = length(code.body)
    table = Elem(:table, Elem[Elem(:tr, [Elem(:td, string(i)), Elem(:td), Elem(:td, i <= n ? e[i] : "end", style = Dict(:fontFamily => :monospace)), Elem(:td, GreenFairy.BOT_SYM), Elem(:td, Elem(:ul))]) for i=1:n+1])
    c = CodeTable(s,fc,e,table, Int[1])
    for i=1:n+1
        c.tree = with_sa(c, c.tree, i)
    end
    c.tree, active = with_pcstat(c, c.tree)
    c.active = map(t->t[2],active)
    c.tree = with_ssa(c, c.tree)
    c
end
using FunctionalCollections

function FunctionalCollections.assoc{tag,ns}(e::Elem{ns,tag}, i::Int, v)
    Elem(ns,tag,properties(e),assoc(children(e),i,v))
end

function assocp{tag,ns}(e::Elem{ns,tag}, v)
    Elem(ns,tag,v,children(e))
end

function assocp{tag,ns}(e::Elem{ns,tag}, k, v)
    Elem(ns,tag,Dict(k => v),children(e))
end
function assocstyle(e,k,v)
#=    p = properties(e)
    p = copy(p)
    p[:style] = Dict(k=>v)=#
    #assocp(e,:style,Dict(k=>v))
    e & Dict(:style => Dict(k => v))
end

function with_pcstat(tree, pc, txt, bgcolor)
    assoc(tree, pc, assocstyle(assoc(children(tree)[pc],2,Elem(:td,Elem(:span,txt))), :backgroundColor, bgcolor))
end
function heapstring(h)
    string("[", join(String[string(ref) for ref in h], ", "), "]")
end
function with_sa(c, tree, pc)
    assoc(tree, pc, assoc(children(tree)[pc],4,Elem(:td,string(c.s.states.funs[c.fc].sa[pc], " = ", heapstring(c.s.states.funs[c.fc].heap[pc])))))
end
function with_ssa(c, tree)
    ls = c.s.states.funs[c.fc]
    ssa_info = Dict{Int,Any}()
    for i = 1:length(ls.defs)
        ds = ls.defs[i]
        lname = ls.local_names[i]
        for pcs in values(ds.defs)
            for pc in pcs
                pc <= 0 && continue
                ssa_info[pc] = push(get(ssa_info, pc, PersistentVector{Node}()), Elem(:li,[Elem(:span, Elem(:b, "def"), style = Dict(:color => :green, :fontWeight => :bold)), Elem(:span,"($lname)",style=Dict(:fontWeight=>:bold)),Elem(:span," = $(GreenFairy.eval_def(ls,i,pc))")]))
            end
        end
        for (lbl,incs) in ds.phis
            pc = c.s.funs[c.fc].label_pc[lbl]
            #=hp = ls.phi_heap[i]
            hps = ""
            if haskey(hp, pc)
                hps = " = " * join([heapstring(inc) for inc in hp[pc]], ", ")
            end=#
            ssa_info[pc] = push(get(ssa_info, pc, PersistentVector{Node}()), Elem(:li,[Elem(:span, "ϕ", style = Dict(:color => :red, :fontWeight => :bold)), Elem(:span, "($lname: $incs)", style = Dict(:fontWeight => :bold)), Elem(:span, " = $(GreenFairy.eval_def(ls,i,pc))")]))
        end
    end
    for (pc,v) in ssa_info
        tree = assoc(tree, pc,
                     assoc(children(tree)[pc],5,
                           Elem(:td, Elem(:ul,v))))
    end
    tree
end
waiting_color = "#f2a0a0"
active_color =  "#e099f2"
function with_pcstat(c, tree)
    local_threads = filter(t->t.fc == c.fc, c.s.threads)
    active = map(t->(length(t.wait_on), t.pc), local_threads)
    sort!(active)
    for (lwo, pc) in active
        color = lwo > 0 ? waiting_color : active_color
        tree = with_pcstat(tree, pc, arrow_sym, color)
    end
    tree, active
end
function step(c :: CodeTable)
    (tfc,tpc) = GreenFairy.step!(c.s)
    tfc == c.fc || return c
    tree = c.tree
    for pc in c.active
        tree = with_pcstat(tree, pc, "", :white)
    end
    tree, active = with_pcstat(c, tree)
    tree = with_sa(c, tree, tpc)
    tree = with_ssa(c, tree)
    CodeTable(c.s,c.fc,c.e,tree,map(t->t[2],active))
end
end
function F()
    x = 3
    z = 5
    if ?
        x = 10
        z = 3
    end
    y = x + z
    y
end
const N = 1
#=function K(c::UI.CodeTable, ::Union(Escher.LeftButton,Float64))
    for i=1:N
        c = UI.step(c)
    end
#    println("C : ", length(c.s.funs))
    c
end

function K(c::UI.CodeTable, fc::Int)
    UI.CodeTable(c.s, fc)
    #UI.step(c)
end

function funlist(s, clicked)
    waitset = Set{Int}()
    waitstyle = Dict(:backgroundColor => UI.waiting_color)
    actstyle = Dict(:backgroundColor => UI.active_color)
    actset = Set{Int}()
    for t in s.s.threads
        push!(actset, t.fc)
        isempty(t.wait_on) || push!(waitset, t.fc)
    end
    
    vbox([
          constant(i,clickable(convert(Tile,Elem(:div, Elem(:a,string(s.s.funs[i]),href="#"), style=((i in waitset) ? waitstyle : (i in actset) ? actstyle : Dict{Symbol,Any}()))))) >>> clicked
          for i=1:length(s.s.funs)]...)
end

function page(s)
    
end
function G()
    x = 1
    y = 1
    z = 1
    while UNKNOWN
        if y < 0
            z = -1
        end
        if x < 0
            y = -1
        end
        x = -1
    end
    z

end 
module EM
using GreenFairy
end
function main(w)
    push!(w.assets, "widgets")
    
    #s = GreenFairy.init(F, ())
    #s = GreenFairy.init(G, ())
    #s = GreenFairy.init(Core.Inference.typeinf, ((),(),(),(),(),()))
    #s = GreenFairy.init(*, (GreenFairy.Ty(Matrix{Float64}), GreenFairy.Ty(Matrix{Float64})))
    s = GreenFairy.init(GreenFairy.run, ((),()))
    running = Input(true)
    dostep = Input(Escher.LeftButton())
    ticks = fpswhen(merge(running,w.alive), 30)
    #ticks = fps(60)
    I = UI.step(UI.CodeTable(s,1))
    for i=1:N
        I = UI.step(I)
    end
    clicked = Input(1)
    state = foldl(I, merge(ticks,dostep,clicked)) do old, _
        K(old,_)
    end
    foldl(hbox("loading ..."), state) do sss, e
        #if isa(e, Int)
        #    sss
        #else
        hbox(vbox(#hbox(textinput(), button("go")),
                  hbox(button("step") >>> dostep,
                           checkbox(true, label="running") >>> running,
                           ),
                      vskip(1em),
                      e.tree) |> grow,
                 hskip(3em),
                 vbox(vskip(1em), funlist(e, clicked)))
        #end
    end
end
=#

function loc_name(loc)
    if loc.def.isphi
        return "phi$(loc.def.pc)_ref$(loc.ref_idx)"
    else
        return "pc$(loc.def.pc)ref$(loc.ref_idx)"
    end
end

function edge_to(io, loc1, loc2, bnd,col="black",lbl="")
    if loc2.ref_idx != 0 && loc1 != loc2 && loc1.ref_idx != 0
        bend = string(",bend ", (bnd ? "left":"right"),"=3ex")
        println(io, "\\draw[->,thick,$col", "] (", loc_name(loc1), ") edge (", loc_name(loc2), ");")
    end
end

const COLORS = ["red", "blue", "green", "yellow", "black", "white"]

function to_tikz(sched, fc)
    c = sched.funs[fc]
    ls = sched.states.funs[fc]

    
    
    io = IOBuffer()
    println(io, """\\documentclass[14pt]{article}
            \\usepackage{fullpage}
            \\usepackage{tabularx}
            \\usepackage{tikz}
            \\usetikzlibrary{positioning,arrows.meta,bending,automata}
            \\usepackage{amsfonts}
            \\usepackage{setspace}
            \\usepackage{geometry}
            \\usepackage{verbatim}""")
    println(io, """\\geometry{paperwidth=800mm, paperheight=2800pt, left=40pt, top=40pt, textwidth=800mm, marginparsep=20pt, marginparwidth=100pt, textheight=16263pt, footskip=40pt}""")
    println(io, "\\begin{document}")
    ncol = length(ls.allocs)
    cols = join(["c" for _=1:ncol], " ")
    println(io, """\\tikzstyle{every picture}+=[remember picture]
            \\begin{tabular}{l|l|$cols}""")
    colors = Dict{Int,String}()
    color_i = 1
    for pc=0:length(c.body)
        print(io, "$pc & ")
        if pc > 0 && !isa(c.body[pc], LineNumberNode)
            print(io, "\\verb~")
            Meta.show_sexpr(io, c.body[pc])
            print(io, "~")
        end
        print(io, " & ")
        if pc > 0
            locset = Any[]
            for (refi,ref) in enumerate(ls.heap[pc])
                msg = ""
                msg *= string(ref.gen)
                push!(locset, (GreenFairy.HeapLoc(GreenFairy.Def(false,pc),refi),ref, msg))
            end
            if haskey(ls.phi_heap, pc)
                for (refi,ref) in enumerate(ls.phi_heap[pc].refs)
                        msg = ""
                        msg *= string(ref.gen, ":")
                        msg *= join(map(i->string(ls.local_names[i]), collect(ls.phi_heap[pc].defs[refi])), ":")
                        push!(locset, (GreenFairy.HeapLoc(GreenFairy.Def(true,pc),refi), ref, msg))
                end
            end
            iov = IOBuffer()
            i = 0
            for (alloc_i, alloc) in enumerate(ls.allocs)
                col = get!(colors, alloc) do
                        col = COLORS[color_i]
                        color_i = (color_i+1) % length(COLORS)
                    col
                end
                last_right = ""
                println(io, "\\begin{tikzpicture}")
                for (thisloc,ref,str) in locset
                    alloc == ref.alloc || continue
                    println(io, "\\node[$col,draw$last_right] (", loc_name(thisloc), ") { ", str, " };")
                    last_right = ",right=5ex of $(loc_name(thisloc))"
                    edge_to(iov, thisloc, ref.loc, Bool(i))
                end
                println(io, "\\end{tikzpicture}")
                alloc_i == ncol || println(io, "&")
            end
            println(io, "\\begin{tikzpicture}[overlay]")
            seekstart(iov); write(io, iov)
            println(io, "\\end{tikzpicture}")
        end
        println(io, "\\\\")
    end
    println(io, "\\end{tabular}")
    println(io, "\\begin{tikzpicture}[overlay]")
    for (srcloc,flds) in ls.heap_fields
        for (fld, dstlocs) in flds
            for dstloc in dstlocs
                edge_to(io, srcloc, dstloc, false, COLORS[fld], fld)
            end
        end
    end
    println(io, "\\end{tikzpicture}")
    println(io, "\\end{document}")
    open(f -> print(f, takebuf_string(io)), "out.tex", "w")
    run(`pdflatex out.tex`)
end

function _heap_to_dot(io, ls, pc, objects,lbl="")
    println(io, "graph[rankdir=\"TB\"];")
    println(io, "\tpc$(pc)head [shape=none,label=\"$lbl\"];");
    println(io, "\tpc$(pc)tail [style=invis,shape=none,width=0,height=0,fixedsize=\"false\",label=\"\"];");
    for (i, (locs, vars)) in enumerate(objects)
        println(io, "\tpc$(pc)_",i," [label=\"", Base.join(map(li->string(ls.local_names[li]),vars)," "), "\"];")
        println(io, "\tpc$(pc)head -> pc$(pc)_$i [style=invis]")
        println(io, "\tpc$(pc)_$i -> pc$(pc)tail [style=invis]")
        found_flds = Set{Int}()
        for loc in locs
            haskey(ls.heap_fields, loc) || continue
            for (fld,dsts) in ls.heap_fields[loc]
                fld in found_flds && continue
                push!(found_flds, fld)
                for dst in dsts
                    for (j, (locs, _)) in enumerate(objects)
                        if dst in locs
                            println(io, "\tpc$(pc)_", i, "->pc$(pc)_", j, " [label=\"", fld, "\"];")
                            break
                        end
                    end
                end
            end
        end
    end
end
function heap_to_dot(ls, pc)
    io = IOBuffer()
    println(io, "digraph {")
    _heap_to_dot(io, ls, pc, collect(GreenFairy.materialize_heap(ls,pc)))
    println(io, "}")
    seekstart(io)
    open(f->write(f,readall(io)), "out.dot", "w")
end
function heap_to_dot(ls)
    io = IOBuffer()
    println(io, "digraph {")
    println(io, "graph[rankdir=\"TB\"];")
    println(io, "compound=true;")
    objects = Dict{Int,Vector{Any}}()
    for pc = 1:length(ls.code.body)
        objects[pc] = collect(GreenFairy.materialize_heap(ls,pc))
    end
    edges = Vector{Tuple{Int,Int}}()
    for pc = 1:length(ls.code.body)-1
        if !isa(ls.code.body[pc+1], LabelNode)
            push!(edges, (pc,pc+1))
        end
    end
    for (lbl,preds) in enumerate(ls.dtree.pred)
        srcpc = ls.code.label_pc[lbl]
        for (_, predpc) in preds
            push!(edges, (predpc,srcpc))
        end
    end
    folds = Dict{Int,Int}()
    for pc = 1:length(ls.code.body)
        if  count(e -> e[2] == pc, edges) == 1 &&
            count(e -> e[1] == pc, edges) == 1
            pred = edges[findfirst(e->e[2]==pc, edges)][1]
            @show objects[pred] objects[pc]
            if  count(e->e[1] == pred, edges) == 1 &&
                objects[pred] == objects[pc]
                folds[pc] = pred
                edges = unique(map!(e->map(i -> i == pc ? pred : i, e), edges))
                filter!(e -> e[1] != e[2], edges)
                continue
            end
        end
        println(io, "subgraph cluster$pc {")
        lblio = IOBuffer()
        Meta.show_sexpr(lblio, ls.code.body[pc])
        seekstart(lblio)

        _heap_to_dot(io, ls, pc, objects[pc], readall(lblio))
        println(io, "\tlabel = \"", pc, "\";")
        println(io, "\tstyle = \"dashed\";")
        println(io, "}")
    end
    for (src,dst) in edges
        println(io, "\tpc$(src)tail -> pc$(dst)head [ltail=cluster$(src), lhead=cluster$(dst)];")
    end
    println(io, "}")
    seekstart(io)
    open(f->write(f,readall(io)), "out.dot", "w")
    open(f->run(pipe(pipe(`dot -Tps2 out.dot`, `ps2pdf - -`), stdout=f)), "out.pdf", "w")
end
