module GreenFairy

# ========== Lattice stuff
abstract Lattice
istop{L<:Lattice}(x::L) = x == top(L)
isbot{L<:Lattice}(x::L) = x == bot(L)

# the one and only 3-element complete lattice
immutable L3 <: Lattice
    v :: Int8
end
const L3e = L3(0)
top(::Type{L3}) = L3(1 % Int8)
bot(::Type{L3}) = L3(-1 % Int8)
<=(x::L3,y::L3) = x.v <= y.v
Base.show(io::IO, x::L3) = print(io, istop(x) ? "top" : isbot(x) ? "bot" : "L3.e")

# ========== Const
immutable Const <: Lattice
    tag :: L3
    v :: Any
    Const(tag::L3,v::ANY) = new(tag,v)
end
Const(v::ANY) = Const(L3e, v)
top(::Type{Const}) = Const(top(L3), ())
bot(::Type{Const}) = Const(bot(L3), ())
istop(x::Const) = istop(x.tag)
isbot(x::Const) = isbot(x.tag)
Base.show(io::IO, x::Const) = (istop(x) | isbot(x)) ? show(io, x.tag) : print(io, "const(", x.v, ")")
function <=(x::Const,y::Const)
    r = (istop(y) || isbot(x) || y.v===x.v)
    r
end

function join(x::Const,y::Const)
    x <= y && return y
    y <= x && return x
    top(Const)
end
eval_lit(::Type{Const}, v::ANY) = Const(v)

# ========== Sign
immutable Sign <: Lattice
    tag :: L3
    s :: Int8
end
Sign(s::Int) = Sign(L3e, s%Int8)
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
meet(x,y) = x <= y ? x : y
eval_lit(::Type{Sign}, v::ANY) = top(Sign)
eval_lit(::Type{Sign}, v::Int) = Sign(sign(v))

# ========== Type
immutable Ty <: Lattice
    ty :: Type
    Ty(t::ANY) = new(t)
end
top(::Type{Ty}) = Ty(Any)
bot(::Type{Ty}) = Ty(Union())
function Base.show(io::IO, x::Ty)
    istop(x) && return print(io, "top")
    isbot(x) && return print(io, "bot")
    print(io, "ty(", x.ty, ")")
end
<=(x::Ty,y::Ty) = x.ty <: y.ty
join(x::Ty,y::Ty) = Ty(typejoin(x.ty,y.ty))
meet(x::Ty,y::Ty) = Ty(typeintersect(x.ty,y.ty))
eval_lit(::Type{Ty}, v::ANY) = Ty(isa(v,Type) ? Type{v} : typeof(v))

# ========== Birth
immutable Birth
    tag :: L3
    pc :: Int
    ec :: Int
end

Birth(pc::Int,ec::Int) = Birth(L3e, pc, ec)
top(::Type{Birth}) = Birth(top(L3), 0, 0)
bot(::Type{Birth}) = Birth(bot(L3), 0, 0)
istop(x::Birth) = istop(x.tag)
isbot(x::Birth) = isbot(x.tag)
Base.show(io::IO, x::Birth) = (istop(x) | isbot(x)) ? show(io, x.tag) : print(io, "birth(", x.pc, ":", x.ec, ")")
<=(x::Birth,y::Birth) = istop(y) || isbot(x) || x.pc == y.pc && x.ec == y.ec
function join(x::Birth,y::Birth)
    x <= y && return y
    y <= x && return x
    top(Birth)
end
meet(x,y) = x <= y ? x : y
eval_lit(::Type{Birth}, v::ANY) = top(Birth)


# ========== Reduced product
# (very inefficient, needs staged)
immutable Prod{Ls} <: Lattice
    values :: Ls
end
#top{Ls}(::Type{Prod{Ls}}) = Prod(map(T->top(T),Ls))
#bot{Ls}(::Type{Prod{Ls}}) = Prod(map(T->bot(T),Ls))
stagedfunction top{Ls}(::Type{Prod{Ls}})
    :(Prod(tuple($([:(top($T)) for T in Ls]...))))
end
stagedfunction bot{Ls}(::Type{Prod{Ls}})
    :(Prod(tuple($([:(bot($T)) for T in Ls]...))))
end
#istop(x::Prod) = all(istop, x.values)
#isbot(x::Prod) = any(isbot, x.values)
function Base.show(io::IO, x::Prod)
    istop(x) && return print(io, "top")
    isbot(x) && return print(io, "bot")
    print(io, "meet(")
    vals = filter(v->!istop(v), x.values)
    for (i,v) in enumerate(vals)
        i == 1 || print(io, ", ") # print(io, "∩")
        print(io, v)
    end
    print(io, ")")
end

function <={Ls}(x::Prod{Ls}, y::Prod{Ls})
    all(map(<=, x.values, y.values))
end


#=function join{Ls}(x::Prod{Ls}, y::Prod{Ls})
    Prod(map(join, x.values, y.values))
end=#
stagedfunction join{Ls}(x::Prod{Ls},y::Prod{Ls})
    args = [:(join(x.values[$i],y.values[$i])) for i=1:length(Ls)]
    :(Prod(tuple($(args...))))
end

function <={L,Ls}(x::Prod{Ls},y::L)
    convert(L,x) <= y
end
#=function convert{L,Ls}(::Type{L},x::Prod{Ls})
    L in Ls || error("converting " * string(L) * " : " * string(x))
    x.values[findfirst(Ls,L)]
end=#
stagedfunction convert{L<:Lattice,Ls}(::Type{L},x::Prod{Ls})
    L in Ls || error("converting " * string(L) * " : " * string(x))
    idx = findfirst(Ls,L)
    :(x.values[$idx])
end
eval_lit{Ls}(::Type{Prod{Ls}}, v) = Prod(map(T->eval_lit(T, v), Ls))
stagedfunction meet{L,Ls}(x::Prod{Ls},y::L)
    L in Ls || error("meet " * string(x) * " : " * string(y))
    idx = findfirst(Ls,L)
    args = [i == idx ? :(meet(x.values[$i],y)) : :(x.values[$i]) for i=1:length(Ls)]
    :(Prod(tuple($(args...))))
end
stagedfunction meet{Ls}(x::Prod{Ls},y::Prod{Ls})
    args = [:(meet(x.values[$i],y.values[$i])) for i=1:length(Ls)]
    :(Prod(tuple($(args...))))
end
convert{L}(::Type{Prod{L}}, y::Prod{L})=y
stagedfunction convert{L,Ls}(::Type{Prod{Ls}},y::L)
    L in Ls || error("convert : ", string(Ls), " < ", string(y))
    idx = findfirst(Ls,L)
    args = [i == idx ? :y : :(top($(Ls[i]))) for i=1:length(Ls)]
    :(Prod(tuple($(args...))))
end
typealias LocalName Union(Symbol,GenSym)
function eval_local(p::Prod,name::LocalName)
    Prod(map(v -> eval_local(v, name), p.values))
end
eval_local{T<:Lattice}(::T,::LocalName) = top(T)
join{Ls}(p::Prod{Ls},v::Lattice) = join(p,convert(Prod{Ls},v))

# ========== Interpreter

const TRACE = false

type Config
    join_strat :: Symbol
end
# static data about a function
type Code
    mod :: Module
    name :: Symbol
    f :: Function
    body :: Vector{Any}
    label_pc :: Vector{Int} # label+1 => pc
    locals :: Set{LocalName}
    args :: Vector{Symbol}
    linear_expr :: Vector{(Vector{Any},Vector{Int})}
end
function Base.show(io::IO, c::Code)
    print(io, "(", c.mod, ".", c.name, ")")
end
abstract State
type FunState{T}
    data :: Vector{T}
    changed :: Bool
end
FunState{T}(::Type{T}) = FunState(Array(T,0), false)
function ensure_filled!{T}(s::FunState{T}, n::Int)
    l = length(s.data)
    if n > l
        resize!(s.data, n)
        for i=1+l:n
            s.data[i] = bot(T)
        end
    end
    nothing
end
function Base.getindex{T}(s::FunState{T}, fc::Int, pc::Int, ec::Int)
    ensure_filled!(s,fc)
    s.data[fc]
end
function join!(s::FunState, fc::Int, pc::Int, ec::Int, v)
    ensure_filled!(s,fc)
    s.data[fc], s.changed = join!(s.data[fc], v)
end
#=function Base.setindex!{T}(s::FunState{T}, val, fc::Int, pc::Int, ec::Int)
    ensure_filled!(s,fc)
    s.data[fc] = join(s.data[fc], val)
end=#

type ExprState{T}
    data::Dict{(Int,Int,Int),T}
    changed :: Bool
end
ExprState{T}(::Type{T}) = ExprState(Dict{(Int,Int,Int),T}(), false)
function Base.getindex{T}(s::ExprState{T}, fc::Int, pc::Int, ec::Int)
    get!(s.data, (fc,pc,ec), bot(T))
end
function Base.setindex!{T}(s::ExprState{T}, v::T, fc::Int,pc::Int,ec::Int)
    orig = s[fc,pc,ec]
    if !(v <= orig)
        s.data[(fc,pc,ec)] = join(orig, v)
        s.changed = true
    end
end
function Base.getindex{T}(s::ExprState{T},fc::Int,pc::Int,ecs::AbstractArray)
    a = Array(T, 0)
    sizehint!(a, length(ecs))
    for ec in ecs
        push!(a, s[fc,pc,ec])
    end
    a
end

immutable ExprVal{T<:Lattice} <: Lattice
    val :: T
end
bot{T}(::Type{ExprVal{T}}) = ExprVal(bot(T))
top{T}(::Type{ExprVal{T}}) = ExprVal(top(T))

immutable FunKey
    fun :: Function
    argtypes :: (Type...,)
    FunKey(f::ANY,a::ANY) = new(f,a)
end

type Thread
    fc :: Int
    pc :: Int
    ec :: Int
end

type Scheduler{ValueT,StateT}
    state :: StateT
    values :: ExprState{ValueT}
    threads :: Vector{Thread}
    config :: Config
    visited :: Set{Any}
    funs :: Vector{Code}
end

#=function Base.show(io::IO,t::Thread)
    println(io, "abstract thread in ", t.state.code, " at ", t.pc, ":")
    if !done(t)
        nstep = length(t.linear_expr)
        ex = t.state.code.body[t.pc]
        println(io, "\tevaluating", (nstep > 0 ? " ($(t.ec)/$nstep)" : ""), " : ", ex)
    else
        println(io, "\treturned")
    end
end=#

#=function fork{S,V}(t::Thread{S,V}, pc::Int, queue)
    @assert isempty(t.linear_expr) && isempty(t.stack)
    # optim
    try
        @show t.state.flow_s[pc] t.store
    end
#    t.state[pc] <= t.store || return
    ft = Thread(t.sched,t.state, fork(t.store), [], Array(V,0), pc, 1, bot(V))
    push!(queue, ft)
    end=#

fork(s::Scheduler,t::Thread,pc::Int) = push!(s.threads, Thread(t.fc,pc,1))

immutable LocalStore{V} <: Lattice
    map :: Dict{LocalName,V}
    LocalStore(m::Dict{LocalName,V} = Dict{LocalName,V}()) = new(m)
end
bot{V}(::Type{LocalStore{V}}) = LocalStore{V}()
<={V}(::LocalStore{V},::LocalStore{V}) = error("???")

function Base.show(io::IO,s::LocalStore)
    println(io, "local store (", length(s.map), ") :")
    ntop = 0
    for (l,v) in s.map
        istop(v) && (ntop += 1; continue)
        println(io, "\t", l, " : ", v)
    end
    if ntop > 0
        print(io, "\t", ntop>1?"(":"")
        i = 0
        for (l,v) in s.map
            istop(v) || continue
            i += 1
            print(io, l)
            ntop == i || print(io, ", ")
        end
        println(io, ntop>1?")":"", " : top")
    end
end
fork{V}(l::LocalStore{V}) = LocalStore{V}(copy(l.map))
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
    s, changed
end
function join!{T<:LocalName,V}(s::LocalStore{V}, v::Pair{T,V})
    k = v.first
    val = v.second
    if !haskey(s.map, k)
        s.map[k] = val
        return s, true
    end
    oldval = s.map[k]
    if val <= oldval
        return s,false
    end
    s.map[k] = join(val, oldval)
    s, true
end
function join{V}(s1::LocalStore{V},s2::LocalStore{V})
    s = LocalStore{V}(copy(s1.map))
    join!(s,s2)
    s
end
function eval_local{V}(s::LocalStore{V}, name::LocalName)
    haskey(s.map, name) || return bot(V)
    s.map[name]
end


const new_fun = :new_tag # maybe we could have Base.new for consistency
eval_call!{V}(t::Thread, ::Type{V}, f, args...) = top(V)
function eval_call!{V}(sched::Scheduler, t::Thread, args::V...)
    any(isbot, args) && return bot(V)
    f = convert(Const,args[1])
    if !istop(f) && (isa(f.v,Function) && isgeneric(f.v) || !isa(f.v,Function))
        fv = f.v
        if !isa(fv,Function)
            fv = eval(sched.funs[t.fc].mod, :call) # call overloading
        else
            args = args[2:end]
        end
        argt = map(a->convert(Ty,a).ty,args)
        println("Calling gf ", fv, " ", argt)
        fcode = code(fv, argt)
        if fcode !== false
            push!(sched.funs, fcode)
            push!(sched.threads, Thread(length(sched.funs),1,1))
        else
            println("no")
        end
        #        spawn!(t.sched, FunKey(fv, argt), args)# || (println("abort ", fv))
        top(V)
    else
        eval_call!(t, V, args...)
    end
end
function eval_new!(t::Thread, args...)
    any(isbot, args) && return bot(V)
    @show args
    eval_call!(t, V, meet(top(V), Const(new_fun)), args...)
end

#=function eval_call!{S,Ls}(t::Thread{S,Prod{Ls}}, ::Type{Prod{Ls}}, f::Prod{Ls}, args::Prod{Ls}...)
    p = top(Prod{Ls})
    for T in Ls
        p = meet(p, eval_call!(t, T, f, args...)) # TODO side effects order
    end
    p
end=#
stagedfunction eval_call!{Ls}(t::Thread, ::Type{Prod{Ls}}, f::Prod{Ls}, args::Prod{Ls}...)
    ex = :(top(Prod{Ls}))
    for L in Ls
        ex = :(meet($ex, eval_call!(t, $L, f, args...)))
    end
    ex
end
const BITS_INTR = [Base.add_int, Base.sub_int, Base.slt_int, Base.sle_int]
const BITS_FUNC = [+, -, <, <=]

function eval_call!{V}(t::Thread, ::Type{Sign}, f::V, args::V...)
    # sign addition
    if f <= Const(Base.add_int)
        all(arg -> arg <= Sign(1)  || arg <= Sign(0), args) && return convert(V,Sign(1))
        all(arg -> arg <= Sign(-1) || arg <= Sign(0), args) && return convert(V,Sign(-1))
        all(arg -> arg <= Sign(0), args) && return convert(V,Sign(0))
    end

    # sign comparison
    is_sle = f <= Const(Base.sle_int)
    is_slt = f <= Const(Base.slt_int)
    if (is_sle || is_slt) && length(args) == 2
        sa, sb = convert(Sign,args[1]), convert(Sign,args[2])
        if !(istop(sa) || istop(sb))
            return convert(V, Const(is_sle ? (sa.s <= sb.s) : sa.s < sb.s))
        end
    end

    top(V)
end


function eval_call!(t::Thread, ::Type{Const}, f::Lattice, args::Lattice...)
    # only evaluate when every argument is constant
    cargs = map(a -> convert(Const, a), args)
    any(a -> istop(a), cargs) && return top(Const)

    # bits functions
    for (bf,rf) in zip(BITS_INTR,BITS_FUNC)
        if f <= Const(bf)
            return Const(rf(map(a -> a.v, cargs)...))
        end
    end

    # module.const
    if f <= Const(Base.getfield) && isa(cargs[1].v, Module)
        mod = cargs[1].v
        name = cargs[2].v
        isa(name, Symbol) || return bot(Const) # module only supports symbol indexing
        isconst(mod, name) || return top(Const) # non const global
        return Const(eval(mod,name))
    end

    top(Const)
end

function eval_call!(t::Thread, ::Type{Birth}, f, args...)
    if f <= Const(new_fun)
        return Birth(t.pc, t.ec)
    end
    top(Birth)
end

function eval_assign!{V}(st,t,name,res::V)
    join!(st, t.fc, t.pc, t.ec, name => res)
end

function step!{V}(sched::Scheduler{V}, t::Thread, conf::Config)
    TRACE && @show t
    code = sched.funs[t.fc]
    state = sched.state
    values = sched.values
    le = code.linear_expr[t.pc]
    if t.ec <= length(le[1]) # continue evaluating expr
        e = le[1][t.ec]
        ed = le[2][t.ec]
        res = if isa(e, Expr)
            if e.head === :call || e.head === :call1 || e.head === :new
                narg = length(e.args)
                args = []
                i = t.ec-1
                while length(args) < narg
                    d = le[2][i]
                    d == ed+1 && unshift!(args, values[t.fc,t.pc,i])
                    i -= 1
                end
                if e.head === :new
                    eval_new!(t, args...)
                else
                    eval_call!(sched, t, args...)
                end
            else
                error("expr ? " * string(e))
            end
        elseif isa(e, LocalName)
            if e === :UNKNOWN
                top(V)
            elseif e in code.locals || isa(e,GenSym)
                eval_local(state[t.fc,t.pc,t.ec], e)
            elseif isa(e,Symbol) && isconst(code.mod,e)
                eval_lit(V, eval(code.mod,e))
            else
                top(V) # global
            end
        else
            if isa(e, TopNode)
                e = eval(Base,e.name)
            elseif isa(e, QuoteNode)
                e = e.value
            end
            eval_lit(V,e)
        end
        values[t.fc,t.pc,t.ec] = res
        t.ec += 1
    end; if t.ec > length(code.linear_expr[t.pc][1]) # TODO think wether we wa
        #    else
        res = values[t.fc,t.pc,t.ec-1]
        t.ec = 1
        stmt = code.body[t.pc]
        TRACE && @show res
        next_pc = t.pc+1
        branch_pc = next_pc
        if isa(stmt, GotoNode)
            next_pc = branch_pc = code.label_pc[stmt.label::Int+1]
        elseif isa(stmt, SymbolNode) || isa(stmt, GenSym) || isa(stmt,Symbol) || isa(stmt, NewvarNode)
        elseif isa(stmt,LineNumberNode) || isa(stmt,LabelNode)
        elseif stmt.head === :(=)
            eval_assign!(state, t, stmt.args[1]::LocalName, res)
        elseif stmt.head === :return
            next_pc = branch_pc = length(code.body)+1
        elseif stmt.head === :gotoifnot
            branch_pc = code.label_pc[stmt.args[2]::Int+1]
            if res <= Const(true)
                branch_pc = next_pc
            elseif res <= Const(false)
                next_pc = branch_pc
            end
        end
        if next_pc != branch_pc
            fork(sched, t, branch_pc)
        end
        t.pc = next_pc
    end
    nothing
end

Base.done(s::Scheduler,t::Thread) = t.pc > length(s.funs[t.fc].body)
Base.done(s::Scheduler) = isempty(s.threads)
function step!(s::Scheduler)
    t = s.threads[1]
    try
        step!(s, s.threads[1], s.config)
    catch x
        println("Exception while executing ", s.threads[1])
        rethrow(x)
    end
    if done(s,t) || !(s.state.changed || s.values.changed)
        shift!(s.threads)
        TRACE && println("THREAD FINISHED ================")
    end
    s.state.changed = s.values.changed = false
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
function Base.show(io::IO, s::Scheduler)
    println(io, "==== scheduler (", length(s.threads), " active threads, ", length(s.states), " functions):")
    for (k,v) in s.states
        println(io, k, ": ", v.ret)
    end
    println(io, "====")
end

function linearize!(e,v,ds,d)
    if isa(e, GlobalRef)
        push!(v,:UNKNOWN) #TODO
        push!(ds,d)
    elseif isa(e, SymbolNode)
        push!(v, e.name)
        push!(ds,d)
    elseif !isa(e, Expr)
        push!(v,e)
        push!(ds,d)
    else
        e.head === :call || e.head ===:call1 || e.head === :new || e.head === :copyast || e.head === :static_typeof || error("not a call " * string(e))
        if isa(e.args[1], TopNode) && e.args[1].name === :box # TODO
            linearize!(e.args[3], v, ds, d)
            return v,ds
        elseif e.head === :copyast # TODO
            push!(v, :UNKNOWN)
            push!(ds,d)
            return v,ds
        elseif e.head === :static_typeof
            push!(v, :UNKNOWN)
            push!(ds,d)
            return v,ds
        end
        for a in e.args
            linearize!(a, v, ds, d+1)
        end
        push!(v,e)
        push!(ds,d)
    end
    v,ds
end
function linearize_stmt!(stmt,v,ds)
    if isa(stmt,LabelNode) || isa(stmt,LineNumberNode) || #TODO enterleave
        isa(stmt,Expr) && (stmt.head === :line || stmt.head === :enter || stmt.head === :leave)
        linearize!(nothing,v,ds,0)
    elseif isa(stmt,GotoNode)
        linearize!(nothing,v,ds,0)
    elseif isa(stmt,NewvarNode) # TODO correct ?
        linearize!(nothing, v,ds,0)
    elseif isa(stmt,SymbolNode)
        linearize!(stmt.name, v,ds,0)
    elseif isa(stmt,Expr) && (stmt.head === :boundscheck || stmt.head === :type_goto) # TODO
        linearize!(nothing, v,ds,0)
    elseif isa(stmt,Expr) && stmt.head === :(=)
        linearize!(stmt.args[2], v, ds, 0)
    elseif isa(stmt,Expr) && (stmt.head === :return || stmt.head === :gotoifnot)
        linearize!(stmt.args[1], v, ds, 0)
    else
        linearize!(stmt, v, ds, 0)
    end
    v,ds
end
function code_from_ast(f,ast,name,mod)
    TRACE && @show ast
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
    locs = Set{LocalName}(ast.args[2][1])
    args = map(ast.args[1]) do a
        if isa(a, Expr) && a.head == :(::)
            a.args[1]
        elseif isa(a, Symbol)
            a
        else
            dump(a)
            error("arg ? " * string(a))
        end
    end
    union!(locs,args)
    lin = [linearize_stmt!(e,[],Int[]) for e in body]
    Code(mod, name, f, body, label_pc, locs, args, lin)
end

function code(f::Function,argtypes::ANY)
    asts = []
    try
        asts = code_lowered(f, argtypes)
    catch
        return false
    end
    length(asts) == 1 || return false
    ast = asts[1]
    code_from_ast(f,ast, f.env.name, f.env.defs.func.code.module)
end

# TEST

function F()
    x = 3
    y = 5
    if x+y < 0 || x >= 0
        z = UNKNOWN
        while UNKNOWN
            y += 1
        end
        z = z+1
        if y < 0
            y = -3
            x = -2
        end
    else
        x = y = -3
    end

    return y
end

function F()
    x = 1
    while x > 0
        x = x+1
    end
#    y = (x+1)*x
end

export Prod,Sign,Const,Ty,Birth,LocalStore,Thread,FunctionState,Scheduler,FunKey,Code,FunState,ExprVal,ExprState

# == client

module Analysis
using GreenFairy
const ValueT = Prod{(Sign,Const,Ty,Birth)}
const StoreT = LocalStore{ValueT}
const StateT = FunState
make_sched(conf) = Scheduler(StateT(LocalStore{ValueT}),ExprState(ValueT),Array(Thread,0),conf,Set{Any}(),Array(Code,0))
end
#@show code_typed(join, (Analysis.ValueT,Analysis.ValueT))
#@show code_typed(step!,(Analysis.ThreadT,Vector{Analysis.ThreadT},Config))
#@show code_typed(eval_local, (Analysis.StoreT,Any))
#@show code_llvm(top, (Type{Analysis.ValueT},))
#exit()

function RUN()
    sched = Analysis.make_sched(Config(:always))
    #    spawn!(sched, FunKey(RUN, ()), [])
    push!(sched.funs, code(RUN, ()))
    push!(sched.threads, Thread(1,1,1))
    p = 2
    niter,maxthr = run(sched)
    @show sched.state
#    println("finished in ", niter, " ", maxthr, " threads :\n",sched)
end
#@show code_typed(eval_call!, (Analysis.ThreadT,Type{Analysis.ValueT},Analysis.ValueT,Analysis.ValueT,Analysis.ValueT))
#exit()
LIM = 1000
@time RUN()
@time RUN()
#file for i=1:10; RUN(); end
#Base.Profile.print()
LIM = 30
#@time RUN()
#@time (niter,maxthr,ss) = RUN()
#@time (niter,maxthr,ss) = RUN()
#Z = @time [RUN()[1] for i=1:1000000]

end
