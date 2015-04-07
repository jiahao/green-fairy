module GreenFairy

# ========== Lattice stuff

abstract Lattice
istop{L<:Lattice}(x::L) = x == top(L)
isbot{L<:Lattice}(x::L) = x == bot(L)


immutable L3 <: Lattice
    v :: Int8
end
const L3e = L3(0)
top(::Type{L3}) = L3(1)
bot(::Type{L3}) = L3(-1)
<=(x::L3,y::L3) = x.v <= y.v
Base.show(io::IO, x::L3) = print(io, istop(x) ? "top" : isbot(x) ? "bot" : "L3.e")

# ========== Const

immutable Const <: Lattice
    tag :: L3
    v :: Any
end
Const(v::ANY) = Const(L3e, v)
top(::Type{Const}) = Const(top(L3), nothing)
bot(::Type{Const}) = Const(bot(L3), nothing)
istop(x::Const) = istop(x.tag)
isbot(x::Const) = isbot(x.tag)
Base.show(io::IO, x::Const) = (istop(x) | isbot(x)) ? show(io, x.tag) : print(io, "const(", x.v, ")")
<=(x::Const,y::Const) = istop(y) || isbot(x)

# ========== Sign

immutable Sign <: Lattice
    tag :: L3
    s :: Int8
end
Sign(s::Int) = Sign(L3e, Int8(s))
top(::Type{Sign}) = Sign(top(L3), 0)
bot(::Type{Sign}) = Sign(bot(L3), 0)
istop(x::Sign) = istop(x.tag)
isbot(x::Sign) = isbot(x.tag)
Base.show(io::IO, x::Sign) = (istop(x) | isbot(x)) ? show(io, x.tag) : print(io, "sign(", x.s > 0 ? "+" : x.s < 0 ? "-" : "0", ")")
<=(x::Sign,y::Sign) = istop(y) || isbot(x) || x.s == y.s
function join(x::Sign,y::Sign)
    x <= y && return y
    y <= x && return x
    top(Sign)
end
eval_lit(::Type{Sign}, v) = top(Sign)
eval_lit(::Type{Sign}, v::Int) = Sign(sign(v))
# ========== Interpreter

const TRACE = false

immutable Code
    body :: Vector{Any}
    label_pc :: Vector{Int} # label+1 => pc
    locals :: Set{Symbol}
end
function Base.show(io::IO, c::Code)
    print(io, "(anonymous code with locals ", collect(c.locals), ")")
end
Base.getindex(c::Code, pc::Int) = c.body[pc]

type FunctionState{StoreT}
    flow_s :: Vector{StoreT}
end

function join!{S}(s::FunctionState{S}, pc::Int, store::S)
    if !isdefined(s.flow_s, pc)
        s.flow_s[pc] = fork(store)
        true
    else
        join!(s.flow_s[pc], store)
    end
end

type Thread{StoreT,ValueT,StateT}
    state :: StateT
    store :: StoreT
    linear_expr :: Vector{Any}
    stack :: Vector{ValueT}
    code :: Code
    pc :: Int
    ec :: Int
    retval :: ValueT
end

Thread(state,store,ValueT::Type,code::Code) = Thread(state,store, [], Array(ValueT,0), code, 1, 1, bot(ValueT))
function Base.show(io::IO,t::Thread)
    println(io, "abstract thread in ", t.code, " at ", t.pc, ":")
    if !done(t)
        nstep = length(t.linear_expr)
        ex = t.code.body[t.pc]
        println(io, "\tevaluating", (nstep > 0 ? " ($(t.ec)/$nstep)" : ""), " : ", ex)
    else
        println(io, "\treturned : ", t.retval)
    end
    show(io, t.store)
end

function fork{S,V}(t::Thread{S,V})
    @assert isempty(t.linear_expr) && isempty(t.stack)
    Thread(t.state, fork(t.store), [], Array(V,0), t.code, t.pc, 1, bot(V))
end

immutable LocalStore{V}
    map :: Dict{Symbol,V}
end
LocalStore{L<:Lattice}(::Type{L}) = LocalStore(Dict{Symbol,L}())
function Base.show(io::IO,s::LocalStore)
    println(io, "local store (", length(s.map), ") :")
    for (l,v) in s.map
        println(io, "\t", l, " : ", v)
    end
end
fork(l::LocalStore) = LocalStore(copy(l.map))
function join!{V}(s::LocalStore{V}, s2::LocalStore{V})
    changed = false
    for (k,v) in s.map
        haskey(s2.map, k) || continue
        newv = join(v, s2.map[k])
        s.map[k] = newv
        newv <= v || (changed = true)
    end
    for (k,v) in s2.map
        haskey(s.map, k) && continue
        changed = true
        s.map[k] = s2.map[k]
    end
    changed
end
function eval_assign!{V}(s::LocalStore{V}, name::Symbol, v::V)
    s.map[name] = v
end

function eval_local{V}(s::LocalStore{V}, name::Symbol)
    haskey(s.map, name) || return bot(V)
    s.map[name]
end

function linearize!(e, v)
    if !isa(e, Expr)
        push!(v,e)
    else
        e.head == :call || error("not a call " * string(e))
        if isa(e.args[1], TopNode) && e.args[1].name == :box # TODO
            return linearize!(e.args[3], v)
        end
        for a in e.args
            linearize!(a, v)
        end
        push!(v,e)
    end
    nothing
end

function eval_call!{S,V}(t::Thread{S,V}, f, args...)
#    println("call : ", f, args)
    top(V)
end

function step!{StoreT,V,StateT}(t::Thread{StoreT,V,StateT}, queue::Vector{Thread{StoreT,V,StateT}})
    stmt = t.code.body[t.pc]
    if isa(stmt,LabelNode) || isa(stmt,LineNumberNode) || stmt.head == :line
        t.pc += 1
        return step!(t,queue)
    end
    TRACE && @show t
    if isempty(t.linear_expr) # new statement
        if stmt.head == :(=)
            linearize!(stmt.args[2], t.linear_expr)
        elseif stmt.head == :return || stmt.head == :gotoifnot
            linearize!(stmt.args[1], t.linear_expr)
        else
            linearize!(stmt, t.linear_expr)
        end
    end
    if t.ec <= length(t.linear_expr) # continue evaluating expr
        e = t.linear_expr[t.ec]
        if isa(e, SymbolNode)
            e = e.name
        end
        if isa(e, Expr)
            if e.head == :call
                narg = length(e.args)
                res = eval_call!(t, t.stack[end-narg+1:end]...)
                resize!(t.stack, length(t.stack)-narg)
                push!(t.stack, res)
            else
                error(e)
            end
        elseif isa(e, Symbol)
            if e in t.code.locals
                push!(t.stack, eval_local(t.store, e))
            else
                error("symbol ? " * string(e))
            end
        else
            push!(t.stack, eval_lit(V, e))
        end
        t.ec += 1
    end; if t.ec > length(t.linear_expr) # TODO think wether we wa
#    else
        t.ec = 1
        empty!(t.linear_expr)
        @assert length(t.stack) == 1
        res = pop!(t.stack)
        if stmt.head == :(=)
            eval_assign!(t.store, stmt.args[1], res)
        end
        if !join!(t.state, t.pc, t.store)
            t.pc = length(t.code.body)+1
            return
        end
        if stmt.head == :return
            t.retval = res
            t.pc = length(t.code.body)+1
        elseif stmt.head == :gotoifnot
            ft = fork(t)
            ft.pc = t.code.label_pc[stmt.args[2]+1]
            push!(queue, ft)
        end
        t.pc += 1
    end
end

Base.done(t::Thread) = t.pc > length(t.code.body)

type Scheduler{ThreadT}
    threads :: Vector{ThreadT}
end
Scheduler(t::Thread) = Scheduler([t])
Base.done(s::Scheduler) = isempty(s.threads)
function step!(s::Scheduler)
    t = s.threads[1]
    step!(s.threads[1], s.threads)
    if done(t)
        shift!(s.threads)
    end
end
function run(s::Scheduler)
    nstep = 0
    maxthread = length(s.threads)
    while !done(s)
        step!(s)
        maxthread = max(maxthread, length(s.threads))
        nstep += 1
    end
    nstep, maxthread
end

# TEST

function F()
    x = 3
    y = 5
    z = -4
    if x > 0
        y = 3
    end
    while x > 0
        x = y
    end
#    z = $(+)(x,$(+)($(*)(x,x),y))
    return y
end

@show @code_typed F()

function code_from_fun(f)
    ast = code_typed(f, ())[1]
    body = ast.args[3].args
    label_pc = Array(Int, 0)
    for pc = 1:length(body)
        if isa(body[pc], LabelNode)
            lnum = body[pc].label+1
            if lnum > length(label_pc)
                resize!(label_pc, lnum)
            end
            label_pc[lnum] = pc
        end
    end
    locs = Set{Symbol}(ast.args[2][1])
    Code(body, label_pc, locs)
end

const P = code_typed(F, ())[1].args[3]
const KOD = code_from_fun(F)#Code(P.args, Set([:x,:y,:z]))
function RUN()
    state = FunctionState(Array(LocalStore{Sign}, length(KOD.body)+1))
    thr = Thread(state, LocalStore(Sign), Sign, KOD)
    sched = Scheduler(thr)
    stats = run(sched)
    stats, state
end
s = nothing
@time (niter,maxthr), state = RUN()
Z = @time [RUN()[1] for i=1:1000000]
println("finished in ", niter, " ", maxthr, " threads :\n", state)
println(length(Z))
end
