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
                ssa_info[pc] = push(get(ssa_info, pc, PersistentVector{Node}()), Elem(:li,[Elem(:span, Elem(:b, "def"), style = Dict(:color => :green, :fontWeight => :bold)), [Elem(:span,"($lname)",style=Dict(:fontWeight=>:bold)),Elem(:span," = $(GreenFairy.eval_def(ls,i,pc))")]]))
            end
        end
        for (lbl,incs) in ds.phis
            pc = c.s.funs[c.fc].label_pc[lbl]
            hp = ls.phi_heap[i]
            hps = ""
            if haskey(hp, pc)
                hps = " = " * join([heapstring(inc) for inc in hp[pc]], ", ")
            end
            ssa_info[pc] = push(get(ssa_info, pc, PersistentVector{Node}()), Elem(:li,[Elem(:span, "ϕ", style = Dict(:color => :red, :fontWeight => :bold)), Elem(:span, "($lname: $incs)", style = Dict(:fontWeight => :bold)), Elem(:span, " = $(GreenFairy.eval_def(ls,i,pc))$hps")]))
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
