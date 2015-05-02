#= TODO
- make dispatch pluggable with abstract values (ConstCode & Ty)
  (then add uncertain matches)
- unify generic & anonymous call path (and support capt. vars in generic code)
- find a common interface for mutable state (Final,Thread,...)
- better "visited" (keyed state, what about non increasing state i.e. strong update)

- better representation of the Expr tree (wait for the bytecode ?)
- think about on-the-fly code mutation (inlining, actual constprop, ...)

- think about implementing type_goto
=#

module GreenFairy

const _ELLIPS = "..."
function show_limit(io::IO, x; limit = 80)
    buf = IOBuffer()
    show(buf, x)
    if position(buf) > limit
        seek(buf, limit-length(_ELLIPS))
        write(buf, _ELLIPS)
        truncate(buf, limit)
    end
    seekstart(buf)
    write(io, takebuf_string(buf))
end
show_limit(x; kw...) = show_limit(STDOUT, x; kw...)

typealias LocalName Union(Symbol,GenSym)
# static data about a function
type Code
    mod :: Module
    name :: Symbol
    body :: Vector{Any}
    label_pc :: Vector{Int} # label+1 => pc
    locals :: Set{LocalName}
    args :: Vector{Symbol}
    linear_expr :: Vector{(Vector{Any},Vector{Int})} # ugly representation
    isva :: Bool
    tvar_mapping :: Tuple
    capt :: Vector{Symbol}
    decl_types :: Dict{LocalName,Any}
end

import Base.convert
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

abstract TagLattice <: Lattice
istop(x::TagLattice) = istop(x.tag)
isbot(x::TagLattice) = isbot(x.tag)
Base.show(io::IO, x::TagLattice) = (istop(x) | isbot(x)) ? show(io, x.tag) : (print(io, "const(");show_limit(io,x.v);print(io,")"))
<=(x::TagLattice,y::TagLattice) = (istop(y) || isbot(x) || x.tag == y.tag == L3e && y.v===x.v)
function join(x::TagLattice,y::TagLattice)
    x <= y && return y
    y <= x && return x
    top(Const)
end

# ========== Const
immutable Const <: TagLattice
    tag :: L3
    v :: Any
    Const(tag::L3,v::ANY) = new(tag,v)
end
Const(v::ANY) = Const(L3e, v)
top(::Type{Const}) = Const(top(L3), ())
bot(::Type{Const}) = Const(bot(L3), ())
eval_lit(::Type{Const}, v::ANY) = Const(v)

immutable ConstCode{EnvT} <: TagLattice
    tag :: L3
    v :: Code
    env :: (EnvT...,)
    ConstCode(tag::L3) = new(tag)
    ConstCode(tag::L3,v::Code,env::(EnvT...,)) = new(tag,v,env)
    ConstCode(tag::L3,v::Code,::()) = new(tag,v,())
end
ConstCode{E}(::Type{E},v::Code,::()) = ConstCode{E}(L3e, v, ())
ConstCode{E}(::Type{E},v::Code,env::(E...,)) = ConstCode{E}(L3e, v, env)
top{E}(::Type{ConstCode{E}}) = ConstCode{E}(top(L3))
bot{E}(::Type{ConstCode{E}}) = ConstCode{E}(bot(L3))
eval_lit{E}(::Type{ConstCode{E}}, v) = top(ConstCode{E})

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
<=(x::Sign,y::Sign) = istop(y) || isbot(x) || x.tag == y.tag == L3e && x.s == y.s
function join(x::Sign,y::Sign)
    x <= y && return y
    y <= x && return x
    top(Sign)
end
meet(x,y) = x <= y ? x : y
eval_lit(::Type{Sign}, v::ANY) = top(Sign)
eval_lit(::Type{Sign}, v::Int) = Sign(sign(v))
eval_lit(::Type{Sign}, v::FloatingPoint) = Sign(round(Int, sign(v)))

# ========== Type
immutable Ty <: Lattice
    ty :: Type
    Ty(t::ANY) = isa(t,Tuple) ? new(Base.limit_tuple_type(t)) : new(t)
end
top(::Type{Ty}) = Ty(Any)
bot(::Type{Ty}) = Ty(Union())
function Base.show(io::IO, x::Ty)
    istop(x) && return print(io, "top")
    isbot(x) && return print(io, "bot")
    print(io, "ty(", x.ty, ")")
end
<=(x::Ty,y::Ty) = x.ty <: y.ty
join(x::Ty,y::Ty) = Ty(Base.tmerge(x.ty,y.ty))
meet(x::Ty,y::Ty) = Ty(typeintersect(x.ty,y.ty))
eval_lit(::Type{Ty}, v::ANY) = Ty(typeof(v))

# ========== Birth
immutable Birth <: Lattice
    tag :: L3
    fc :: Int
    pc :: Int
    ec :: Int
end
# TODO join(k:x:y,k:z:w) = k:*:*
Birth(fc::Int,pc::Int,ec::Int) = Birth(L3e, fc, pc, ec)
top(::Type{Birth}) = Birth(top(L3), 0, 0, 0)
bot(::Type{Birth}) = Birth(bot(L3), 0, 0, 0)
istop(x::Birth) = istop(x.tag)
isbot(x::Birth) = isbot(x.tag)
Base.show(io::IO, x::Birth) = (istop(x) | isbot(x)) ? show(io, x.tag) : print(io, "birth(", x.fc, ":", x.pc, ":", x.ec, ")")
<=(x::Birth,y::Birth) = istop(y) || isbot(x) || x.tag == y.tag == L3e && x.fc == y.fc && x.pc == y.pc && x.ec == y.ec
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
prod{Ls}(values::Ls) = Prod(ntuple(i -> reduce(meet, map(v -> meet_ext(values[i], v), values)), length(values)))
#top{Ls}(::Type{Prod{Ls}}) = Prod(map(T->top(T),Ls))
#bot{Ls}(::Type{Prod{Ls}}) = Prod(map(T->bot(T),Ls))
stagedfunction top{Ls}(::Type{Prod{Ls}})
    :(Prod(tuple($([:(top($T)) for T in Ls]...))))
end
stagedfunction bot{Ls}(::Type{Prod{Ls}})
    :(Prod(tuple($([:(bot($T)) for T in Ls]...))))
end
istop(x::Prod) = all(istop, x.values)
isbot(x::Prod) = any(isbot, x.values)
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
    :(prod(tuple($(args...))))
end
stagedfunction meet{Ls}(x::Prod{Ls},y::Prod{Ls})
    args = [:(meet(x.values[$i],y.values[$i])) for i=1:length(Ls)]
    :(prod(tuple($(args...))))
end
convert{L}(::Type{Prod{L}}, y::Prod{L})=y
stagedfunction convert{L,Ls}(::Type{Prod{Ls}},y::L)
    L in Ls || error("convert : ", string(Ls), " < ", string(y))
    idx = findfirst(Ls,L)
    args = [i == idx ? :y : :(top($(Ls[i]))) for i=1:length(Ls)]
    :(prod(tuple($(args...))))
end

function eval_local(p::Prod,name::LocalName)
    prod(map(v -> eval_local(v, name), p.values))
end
eval_local{T<:Lattice}(::T,::LocalName) = top(T)
join{Ls}(p::Prod{Ls},v::Lattice) = join(p,convert(Prod{Ls},v))

# ========== Interpreter

const TRACE = false

type Config
    join_strat :: Symbol
end
function Base.show(io::IO, c::Code)
    ln = c.body[1]
    if ln.head == :line
        lns = @sprintf("%s:%d", ln.args[2], ln.args[1])
    else
        lns = "???"
    end
    print(io, "(", module_name(c.mod), ".", c.name, " at ",lns,", ", length(c.body), " statements, ", sum([length(l[1]) for l in c.linear_expr])," steps)")
end
abstract State
type FunState{T} <: State
    data :: Vector{T}
    changed :: Vector{Bool}
end
FunState{T}(::Type{T}) = FunState(Array(T,0), Array(Bool,0))
function ensure_filled!{T}(s::FunState{T}, fc::Int, ::Code)
    l = length(s.data)
    @assert fc == l+1
    push!(s.data, bot(T))
    push!(s.changed, false)
    nothing
end
function Base.getindex{T}(s::FunState{T}, fc::Int)
    s.data[fc]
end
function join!(s::FunState, fc::Int, v)
    s.data[fc], chg = join!(s.data[fc], v)
    s.changed[fc] |= chg
    nothing
end
has_changed(s::FunState, fc::Int) = s.changed[fc]
reset_changed(s::FunState, fc::Int) = s.changed[fc] = false
# fallback for immutable lattices
function join!(v::Lattice,v2::Lattice)
    j = join(v,v2)
    j, !(j <= v)
end
#=function Base.setindex!{T}(s::FunState{T}, val, fc::Int, pc::Int, ec::Int)
    ensure_filled!(s,fc)
    s.data[fc] = join(s.data[fc], val)
end=#

type ExprState{T}
    data :: Vector{Vector{Vector{T}}} # TODO inefficient
    changed :: Bool
end
ExprState{T}(::Type{T}) = ExprState(Array(Vector{Vector{T}},0), false)
function ensure_filled!{T}(s::ExprState{T}, fc::Int, c::Code)
#    @assert length(s.data)+1 == fc
    push!(s.data, [[bot(T) for j=1:length(c.linear_expr[i][1])] for i = 1:length(c.body)])
end
function Base.getindex{T}(s::ExprState{T}, fc::Int, pc::Int, ec::Int)
    s.data[fc][pc][ec]
    #get!(s.data, (fc,pc,ec), bot(T))
end
function Base.setindex!{T}(s::ExprState{T}, v::T, fc::Int,pc::Int,ec::Int)
    orig = s[fc,pc,ec]
    if !(v <= orig)
        #s.data[(fc,pc,ec)] = join(orig, v)
        s.data[fc][pc][ec] = join(orig, v)
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

type Thread{StateT,FinalT}
    fc :: Int
    pc :: Int
    ec :: Int
    wait_on :: Int # fc we need to continue, or 0 if none
    cycle :: Int
    state :: StateT
    final :: FinalT
    visited :: Set{Int} # inefficient, could be parametrized by modified state, could be a bitfield, ...
    eh_stack :: Vector{Int} # pc of handler
end
Thread(StateT,FinalT,f,p,e) = Thread(f,p,e,0,0,bot(StateT),bot(FinalT),Set{Int}(),Array(Int,0))

type Scheduler{ValueT,StateT,InitialT,FinalT}
    values :: ExprState{ValueT}
    initial :: FunState{InitialT}
    final :: FunState{FinalT}
    done :: Vector{Bool}
    threads :: Vector{Thread{StateT,FinalT}}
    done_threads :: Vector{Thread{StateT,FinalT}}
    config :: Config
    called_by :: Vector{Set{Any}}
    funs :: Vector{Code}
end

function register_fun!(sched::Scheduler, fcode::Code)
    fc = 0
#=    for i = 1:length(sched.funs)
        if sched.funs[i] == fcode
            fc = i
        end
    end=#
    if fc == 0
        push!(sched.funs, fcode)
        fc = length(sched.funs)
        ensure_filled!(sched.values, fc, fcode)
        ensure_filled!(sched.final, fc, fcode)
        ensure_filled!(sched.initial, fc, fcode)
        push!(sched.done, false)
        push!(sched.called_by, Set{Any}())
    end
    fc
end

function Base.show(io::IO,t::Thread)
    println(io, "abstract thread ", pointer_from_objref(t), " at ",t.fc,":",t.pc,":",t.ec, " final:", t.final)
    println(io, t.state)
end
fork(s,t) = fork(s,t,t.pc,t.ec)
fork(s,t,pc) = fork(s,t,pc,1)
function fork{S,F}(s::Scheduler,t::Thread{S,F},pc::Int,ec::Int)
    child = Thread(S,F,t.fc,pc,ec)
    child.eh_stack = copy(t.eh_stack)
    child.cycle = t.cycle
    join!(child.state, t.state)
    join!(child.final, t.final)
    union!(child.visited, t.visited)
    push!(s.threads, child)
    child
end

immutable LocalStore{V} <: Lattice
    map :: Dict{LocalName,V}
    LocalStore(m::Dict{LocalName,V} = Dict{LocalName,V}()) = new(m)
end
bot{V}(::Type{LocalStore{V}}) = LocalStore{V}()
function <={V}(s::LocalStore{V},s2::LocalStore{V})
    for (k,v) in s.map
        haskey(s2.map, k) || return false
        s.map[k] <= s2.map[k] || return false
    end
    true
end

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
join!{V}(s::LocalStore{V}, v::Pair) = join!(s, v.first=>convert(V,v.second))
function join!{T<:LocalName,V}(s::LocalStore{V}, v::Pair{T,V})
    k = v.first
    val = v.second
    isbot(val) && return s, false
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
function eval_local{V}(s::LocalStore{V}, name::LocalName)
    haskey(s.map, name) || return bot(V)
    s.map[name]
end

meet_ext(v::Lattice, v2::Lattice) = v
meet_ext{T}(v::T,v2::T) = v
meet_ext(v::Ty, v2::Const) = istop(v2) ? v : eval_lit(Ty,v2.v)

# canonicalize those to function calls
# there are some special ast node and ccall in there
module OtherBuiltins
const new = :new_tag
const new_array = :new_array_tag
const new_array_1d = :new_array_1d_tag
const new_array_2d = :new_array_2d_tag
const new_array_3d = :new_array_3d_tag
end



eval_call!{V}(t::Thread, ::Type{V}, f, args...) = top(V)

call_gate{T<:Lattice}(v::T) = top(T)
call_gate(v::Const) = isa(v.v, Type)? v : top(Const) # keep constant types for metaprogramming
call_gate(v::Union(Sign,Ty,Birth)) = v
call_gate(v::ConstCode) = v
call_gate(p::Prod) = prod(map(call_gate,p.values))
NOMETH = 0
function eval_call_gf!{V,S,I,F}(sched::Scheduler{V,S,I,F}, state, fv, args)
    argt = map(args) do a
        ca = convert(Const,a)
        if !istop(ca) && isa(ca.v, Type)
            Type{ca.v}
        else
            convert(Ty,a).ty
        end
    end
    fcode = code(fv, argt)
    if fcode === false # TODO fix this interface
        -1
    elseif isa(fcode, Code)
        eval_call_code!(sched, state, fcode, args, ())
    else
        global NOMETH
        NOMETH += 1
        #println("no ", fcode, " ", fv, " ", args)
        0
    end
end
function eval_call_code!{V,S,I,F}(sched::Scheduler{V,S,I,F},state,fcode,args,env)
    child = Thread(S,F,0,1,1)
    child.state, _ = join!(child.state, state)
    child.state = call_gate!(child.state)
    args = map(call_gate, args)
    if any(istop, args)
        #                println("Calling gf ", fv, " ", argt, " with args ", args)
        #                println(sched)
        #                exit()
    end
    narg = length(fcode.args)
    if fcode.isva
        narg -= 1
        vargs = args[narg+1:end]
        args = args[1:narg]
    end
    if narg != length(args)
        warn(@sprintf("Wrong arg count : %s vs %s%s", fcode.args, args, fcode.isva ? " (vararg)" : ""))
        return bot(V)
    end
    for i = 1:narg
        argname = fcode.args[i]
        arg = args[i]
        if haskey(fcode.decl_types, argname)
            cty = convert(Const,eval_sym(sched, state, fcode, fcode.decl_types[argname]))
            istop(cty) || (arg = meet(arg, convert(V,Ty(cty.v))))
        end
        eval_assign!(sched, child, argname, arg)
    end
    if fcode.isva
        tup = eval_call!(sched, child, convert(V,Const(Base.tuple)), vargs...)
        @assert tup !== nothing
        eval_assign!(sched, child, fcode.args[end], tup)
    end
    for i=1:2:length(fcode.tvar_mapping)
        tv = fcode.tvar_mapping[i]
        tval = fcode.tvar_mapping[i+1]
        eval_assign!(sched, child, tv.name, convert(V,Const(tval)))
    end
    length(env) == length(fcode.capt) || warn(@sprintf("Wrong env size %d vs %d : %s vs %s", length(env), length(fcode.capt), env, fcode.capt))
    for i=1:length(fcode.capt)
        eval_assign!(sched, child, fcode.capt[i], i > length(env) ? top(V) : convert(V,env[i]))
    end
    for fc in 1:length(sched.funs)
        if sched.funs[fc] === fcode && child.state <= sched.initial[fc]
            return fc
        end
    end
    fc = register_fun!(sched, fcode)
    child.fc = fc
    join!(sched.initial, fc, child.state)
    push!(sched.threads, child)
    fc
end

function eval_call!{S,V}(sched::Scheduler{V,S}, t::Thread{S}, fun::V, args::V...) #TODO move args to an ANY tuple to avoid recompilation
    any(isbot, args) && (#=println("bot arg ", args); =#return bot(V))
    f = convert(Const,fun)
    if f <= Const(Base._apply)
        actual_args = []
        if args[2] <= Ty(Function)
            fun = args[2]
        else
            fun = args[1]
            push!(actual_args, args[2])
        end
        for i=3:length(args)
            if args[i] <= Ty(Tuple)
                l = convert(Const, eval_call!(t, V, convert(V,Const(Base.tuplelen)), args[i]))
                istop(l) && return top(V)
                for k=1:l.v
                    push!(actual_args, eval_call!(t, V, convert(V,Const(Base.tupleref)), args[i], convert(V,l)))
                end
            else # TODO handle other iterators
                return top(V)
            end
        end
        f = convert(Const,fun)
        args = tuple(actual_args...)
    end
    if !istop(f) && (isa(f.v,Function) && isgeneric(f.v) || !isa(f.v,Function) && !isa(f.v,IntrinsicFunction))
        fv = f.v
        if !isa(fv,Function)
            fv = eval(sched.funs[t.fc].mod, :call) # call overloading
            args = tuple(fun, args...)
        end
        fc = eval_call_gf!(sched, t.state, fv, args)
        if fc > 0
            t.wait_on = fc
            push!(sched.called_by[fc], (t.fc,t.pc))
            nothing
        elseif fc == -1
            bot(V)
        else
            top(V)
        end
    elseif f <= Const(Base.throw) || f <= Const(Base.rethrow)
        join!(t.final, :thrown, args[1])
        t.final.must_throw = true
        bot(V)
    else
        ccode = convert(ConstCode{Ty}, fun)
        if !istop(ccode)
            fcode = ccode.v
            env = ccode.env
            fc = eval_call_code!(sched, t.state, fcode, args, env)
            if fc > 0 # TODO remove dupl
                t.wait_on = fc
                push!(sched.called_by[fc], (t.fc,t.pc))
                nothing
            else
                top(V)
            end
        else
            # canonicalize known ccalls
            if f <= Const(Base.ccall)
                # TODO add rethrow here instead of hijacking Base.rethrow
                known_ccall = # TODO make this less ugly
                (args[2] <= Const(:jl_new_array) ? OtherBuiltins.new_array :
                 args[2] <= Const(:jl_alloc_array_1d) ? OtherBuiltins.new_array_1d :
                 args[2] <= Const(:jl_alloc_array_2d) ? OtherBuiltins.new_array_2d :
                 args[2] <= Const(:jl_alloc_array_3d) ? OtherBuiltins.new_array_3d : nothing)
                if known_ccall !== nothing
                    args = tuple(args[5:end]...)
                    fun = convert(V, known_ccall)
                end
            end
            result = eval_call!(t, V, fun, args...)
            #=if !istop(convert(Const, fun)) && istop(result) && !any(istop, args)
                warn(@sprintf("Top result for %s %s", fun, args))
            end=#
            result
        end
    end
end

function eval_new!{V}(t::Thread, args::V...)
    any(isbot, args) && return bot(V)
    eval_call!(t, V, meet(top(V), Const(OtherBuiltins.new)), args...)
end

stagedfunction eval_call!{Ls}(t::Thread, ::Type{Prod{Ls}}, f::Prod{Ls}, args::Prod{Ls}...)
    ex = :(top(Prod{Ls}))
    for L in Ls
        ex = :(meet($ex, eval_call!(t, $L, f, args...)))
    end
    ex
end
#TODO rename this as const_funs or sthing
# TODO add intrinsics that can throw
const BITS_INTR = [Base.add_int, Base.sub_int, Base.mul_int, Base.srem_int, Base.ctlz_int, Base.slt_int, Base.sle_int, Base.not_int,Base.apply_type, Base.issubtype, Base.tuple, Base.tuplelen, Base.tupleref, Core.sizeof, Base.fieldtype, Base.Union]
const BITS_FUNC = [+, -, *, %, leading_zeros, <, <=, !, Base.apply_type, Base.issubtype, Base.tuple, Base.tuplelen, Base.tupleref, Core.sizeof, Base.fieldtype, Base.Union]
@assert length(BITS_INTR) == length(BITS_FUNC)
function eval_call!{V}(t::Thread, ::Type{Sign}, f::V, args::V...)
    if (f <= Const(Base.unbox) || f <= Const(Base.box))
        return convert(V,convert(Sign,args[2]))
    end
    # sign add
    if f <= Const(Base.add_int) || f <= Const(Base.checked_sadd)
        length(args) == 2 || return bot(V)
        args[1] <= Sign(0) && args[2] <= Sign(0) && return convert(V,Sign(0)) # +(0 0) = 0
        for sgn in (-1,1) # +(+ 0) = +(0 +) = +(+ +) = + and +(- 0) = +(0 -) = +(- -) = -
            (args[1] <= Sign(sgn) || args[1] <= Sign(0)) &&
            (args[2] <= Sign(sgn) || args[2] <= Sign(0)) &&
            return convert(V,Sign(sgn))
        end
    end
    # sign sub
    if f <= Const(Base.sub_int) || f <= Const(Base.checked_ssub)
        length(args) == 2 || return bot(V)
        args[1] <= Sign(0) && args[1] <= Sign(0) && return convert(V,Sign(0))
        for sgn in (-1,1)
            (args[1] <= Sign(sgn) || args[1] <= Sign(0)) &&
            (args[2] <= Sign(-sgn) || args[2] <= Sign(0)) &&
            return convert(V,Sign(sgn))
        end
    end
    # sign comparison
    is_sle = f <= Const(Base.sle_int)
    is_slt = f <= Const(Base.slt_int)
    if (is_sle || is_slt) && length(args) == 2
        sa, sb = convert(Sign,args[1]), convert(Sign,args[2])
        if !(istop(sa) || istop(sb) || sa.s == sb.s)
            return convert(V, Const(is_sle ? (sa.s <= sb.s) : sa.s < sb.s))
        end
    end

    top(V)
end

const INTR_TYPES = [
                    (Int, [Base.add_int, Base.sub_int,Base.check_top_bit, Base.mul_int, Base.srem_int, Base.ctlz_int, Base.ashr_int, Base.checked_ssub, Base.checked_sadd, Base.and_int, Base.flipsign_int, Base.shl_int, Base.lshr_int, Base.xor_int, Base.and_int, Base.neg_int, Base.or_int, Base.sdiv_int, Base.cttz_int, Core.sizeof]),
                    (UInt, [Base.udiv_int, Base.urem_int]),
                    (Float64, [Base.div_float, Base.mul_float, Base.ceil_llvm, Base.sub_float, Base.neg_float]),
                    (Bool, [Base.slt_int, Base.sle_int, Base.not_int, Base.is, Base.ne_float, Base.lt_float, Base.ule_int, Base.ult_int, Base.le_float, Base.eq_float])
                    ]
const FA_INTR = [Base.trunc_int, Base.sext_int, Base.uitofp, Base.sitofp, Base.fptosi, Base.box, Base.unbox, OtherBuiltins.new]

function eval_call!{V}(t::Thread, ::Type{Ty}, f::V, args::V...)
    if length(args) >= 1
        for bf in FA_INTR
            if f <= Const(bf)
                cty = convert(Const, args[1])
                istop(cty) && return top(V)
                return convert(V, Ty(cty.v))
            end
        end
    end
    # cglobal takes the return type as second argument ...
    if f <= Const(Base.cglobal)
        cty = convert(Const, args[2])
        istop(cty) && return top(V)
        return convert(V, Ty(cty.v))
    end
    if  f <= Const(OtherBuiltins.new_array) ||
        f <= Const(OtherBuiltins.new_array_1d) ||
        f <= Const(OtherBuiltins.new_array_2d) ||
        f <= Const(OtherBuiltins.new_array_3d)
        aty = convert(Const, args[1])
        istop(aty) && return convert(V,Ty(Array))
        return convert(V, Ty(aty.v))
    end
    argtypes = map(a->convert(Ty,a),args)
    for (retty,intrs) in INTR_TYPES
        for bf in intrs
            if f <= Const(bf)
                return convert(V, Ty(retty))
            end
        end
    end
    if f <= Const(Base.select_value)
        return convert(V,reduce(join, args[2:end]))
    end
    if f <= Const(Base.typeof)
        isleaftype(argtypes[1].ty) || return Ty(Type)
        return convert(V,Const(argtypes[1].ty))
    end
    if f <= Const(Base.tuple)
        # TODO rebase on top of new tuple types
        return convert(V,Ty(map(a->a.ty,argtypes)))
    end
    if f <= Const(Base.arraylen) || f <= Const(Base.arraysize)
        argtypes[1] <= Ty(Array) || return bot(V)
        return convert(V, Ty(Int))
    end
    if f <= Const(Base.tuplelen)
        argtypes[1] <= Ty(Tuple) || return bot(V)
        tty = argtypes[1].ty
        len = length(tty)
        len == 0 && return convert(V,Const(0))
        tty[end] <: Vararg && return convert(V,Ty(Int))
        return convert(V, Const(len))
    end
    if f <= Const(Base.getfield)
        aty = argtypes[1].ty
        isleaftype(aty) && aty !== Module || return top(V)
        fld = convert(Const, args[2])
        istop(fld) && return top(V) # could join() all field types
        fldv = fld.v
        fidx = if isa(fldv, Symbol)
            findfirst(fieldnames(aty), fldv)
        elseif isa(fldv, Int)
            fldv
        else
            0
        end
        1 <= fidx <= length(aty.types) || return bot(V)
        return convert(V, Ty(aty.types[fidx]))
    end
    if f <= Const(Base.setfield!)
        # TODO return bot for wrong fields
        return args[3]
    end
    # first argument is return type
    if  f <= Const(Base.checked_trunc_uint) ||
        f <= Const(Base.checked_trunc_sint) ||
        f <= Const(Base.zext_int)
        cty = convert(Const,args[1])
        istop(cty) && return top(V)
        return convert(V,Ty(cty.v))
    end
    if f <= Const(Base.ccall)
        # TODO add known ccalls here
        retty = convert(Const,args[2])
        istop(retty) || return convert(V,Ty(retty.v))
    end
    if f <= Const(Base.typeassert)
        typ = convert(Const, args[2])
        istop(typ) && return top(V)
        return convert(V, Ty(typ.v))
    end
    if f <= Const(Base.tupleref)
        argtypes[1] <= Ty(Tuple) || return top(V)
        tty = argtypes[1].ty
        len = length(tty)
        len == 0 && return bot(V)
        va = bot(Ty)
        isva = false
        if tty[end] <: Vararg
            va = Ty(tty[end].parameters[1])
            isva = true
            len -= 1
        end
        idx = convert(Const,args[2])
        # unknown index access :
        istop(idx) && return convert(V,foldl(join, va, map(Ty, tty[1:len])))
        # OOB access :
        idx.v >= 1 || return bot(V)
        isva || idx.v <= len || return bot(V)
        # we know everything
        return idx.v <= len ? Ty(tty[idx.v]) : va
    end
    if f <= Const(Base.arrayref)
        argtypes[1] <= Ty(Array) || return top(V)
        return convert(V,Ty(argtypes[1].ty.parameters[1]))
    end
    if f <= Const(Base.arrayset)
        argtypes[1] <= Ty(Array) || return top(V)
        return convert(V,argtypes[1])
    end
    if f <= Const(Base.isa)
        cty = convert(Const,args[2])
        istop(cty) && return top(V)
        isa_ty = Ty(cty.v)
        argtypes[1] <= isa_ty && return convert(V, Const(true))
        isbot(meet(argtypes[1], isa_ty)) && return convert(V, Const(false))
        return convert(V, Ty(Bool))
    end
    if f <= Ty(IntrinsicFunction)
        cv = convert(Const,f).v
        intrname = string(cv)
        for fn in names(Core.Intrinsics)
            intr = Core.Intrinsics.(fn)
            if intr === cv
                intrname = string(fn)
                break
            end
        end
        warn(@sprintf("Unknown intrinsic %s with args %s", intrname, args))
    end
    top(V)
end

function eval_call!{V}(t::Thread, ::Type{Const}, f::V, args::V...)
    # only evaluate when every argument is constant
    cargs = map(a -> convert(Const, a), args)
    any(a -> istop(a), cargs) && return top(V)

    # bits functions
    for (bf,rf) in zip(BITS_INTR,BITS_FUNC)
        if f <= Const(bf)
            argvals = map(a -> a.v, cargs)
            res = bot(Const)
            try
                res = Const(rf(argvals...))
            catch
                warn("thrown calling ", f, " ", argvals)
            end
            return convert(V,res)
        end
    end

    # module.const
    if f <= Const(Base.getfield) && isa(cargs[1].v, Module)
        mod = cargs[1].v
        name = cargs[2].v
        isa(name, Symbol) || return bot(V) # module only supports symbol indexing
        isconst(mod, name) || return top(V) # non const global
        return convert(V,Const(eval(mod,name)))
    end

    # immutable.const (types are immutable for all intent and purposes)
    if f <= Const(Base.getfield) && (isimmutable(cargs[1].v) || isa(cargs[1].v, Type))
        v = cargs[1].v
        name = cargs[2].v
        if (isa(name,Symbol) || isa(name,Int)) && isdefined(v, name)
            return convert(V,Const(getfield(v, name)))
        else
            return bot(V)
        end
    end

    top(V)
end
function eval_call!{V}(t::Thread, ::Type{Birth}, f::V, args::V...)
    if  f <= Const(OtherBuiltins.new) ||
        f <= Const(OtherBuiltins.new_array) ||
        f <= Const(OtherBuiltins.new_array_1d) ||
        f <= Const(OtherBuiltins.new_array_2d) ||
        f <= Const(OtherBuiltins.new_array_3d)
        return convert(V,Birth(t.fc,t.pc, t.ec))
    end
    top(V)
end
function eval_call!{V,EV}(t::Thread, ::Type{ConstCode{EV}}, f::V, args::V...)
    if f <= Const(OtherBuiltins.new)
        ty = convert(Const, args[1])
        (istop(ty) || ty.v != Function) && return top(V)
        code = convert(Const, args[2])
        istop(code) && return top(V)
        actual_code = code_from_ast(code.v, ())
        # TODO the env evaluation should be part of the expr tree
        env = map!(capt_var -> convert(EV,eval_local(t.state, capt_var)), Array(EV, length(actual_code.capt)), actual_code.capt)
        return convert(V,ConstCode(EV, actual_code, tuple(env...)))
    end
    top(V)
end

function eval_assign!{V}(s,t,name,res::V)
    t.state, changed = join!(t.state, :locals, name => res)
    if changed
        empty!(t.visited)
    end
    nothing
end

function eval_sym {V}(sched::Scheduler{V},state,code,e)
    if e in code.locals || isa(e,GenSym)
        eval_local(state, e)
    elseif isa(e,Symbol) && isconst(code.mod,e)
        eval_lit(V, eval(code.mod,e))
    else
        top(V) # global
    end
end

function step!{V,S}(sched::Scheduler{V,S}, t::Thread{S}, conf::Config)
    code = sched.funs[t.fc]
    values = sched.values
    le = code.linear_expr[t.pc]
    if t.ec == 1 && t.pc in t.visited
        t.pc =length(code.body)+1
        return
    end
    TRACE && println("Step thread ",t.fc, ":", t.pc, ":", t.ec)
    if t.ec <= length(le[1]) # continue evaluating expr
        e = le[1][t.ec]
        ed = le[2][t.ec]
        res = if t.wait_on > 0
            if sched.done[t.wait_on]
                final = sched.final[t.wait_on]
                t.wait_on = 0
            else # cycle
                ft = fork(sched, t)
                ft.wait_on = t.wait_on
                ft.cycle += 1
                t.wait_on = 0
                final = sched.final[ft.wait_on]
            end
            # TODO move into function
            t.final, _ = join!(t.final, :thrown, final.thrown)
            t.final.must_throw = t.final.must_throw | final.must_throw
            t.final.must_throw && println("Thread ", t.fc, " must throw is now ", t.final.must_throw)
            final.ret_val
        elseif isa(e, Expr)
            if e.head === :call || e.head === :call1 || e.head === :new
                narg = length(e.args)
                args = []
                i = t.ec-1
                argex = [] # debug
                while length(args) < narg
                    d = le[2][i]
                    d == ed+1 && (unshift!(args, values[t.fc,t.pc,i]); unshift!(argex, le[1][i]))
                    i -= 1
                end
#                @show argex
                if e.head === :new
                    eval_new!(t, args...)
                else
                    eval_call!(sched, t, args[1], args[2:end]...)
                end
            else
                error("expr ? " * string(e))
            end
        elseif isa(e, LocalName)
            if e === :UNKNOWN
                top(V)
            else
                eval_sym(sched, t.state, code, e)
            end
        elseif isa(e, LambdaStaticData)
            # canonicalize static AST into : new(Function, ast)
            # should probably be new(Function, ast, env) but for now this is done
            # internally
            eval_new!(t, convert(V,Const(Function)), convert(V,Const(e)))
        else
            if isa(e, TopNode)
                e = eval(Base,e.name)
            elseif isa(e, QuoteNode)
                e = e.value
            end
            eval_lit(V,e)
        end
        if res === nothing
            return
        end
        values[t.fc,t.pc,t.ec] = res
        TRACE && (print("Result of expr ");Meta.show_sexpr(e);println(" : ", res))
        t.ec += 1
    end;if t.ec > length(le[1]) # TODO think wether we wa
        #    else
        res = values[t.fc,t.pc,t.ec-1]
        t.ec = 1
        stmt = code.body[t.pc]
        TRACE && (print("Result of ");Meta.show_sexpr(stmt);println(" : ", res))
        next_pc = t.pc+1
        branch_pc = next_pc
        if isa(stmt, GotoNode)
            next_pc = branch_pc = code.label_pc[stmt.label::Int+1]
        elseif isa(stmt, SymbolNode) || isa(stmt, GenSym) || isa(stmt,Symbol) || isa(stmt, NewvarNode)
        elseif isa(stmt,LineNumberNode) || isa(stmt,LabelNode)
        elseif stmt.head === :return
            next_pc = branch_pc = length(code.body)+1
        elseif stmt.head === :gotoifnot
            branch_pc = code.label_pc[stmt.args[2]::Int+1]
            if res <= Const(true)
                branch_pc = next_pc
            elseif res <= Const(false)
                next_pc = branch_pc
            end
        elseif stmt.head == :enter
            push!(t.eh_stack, code.label_pc[stmt.args[1]::Int+1])
        elseif stmt.head == :leave
            if !isbot(t.final.thrown) # could throw
                handler_pc = t.eh_stack[end]
                ft = fork(sched, t, handler_pc)
                ft.final.thrown = bot(Ty)
                ft.final.must_throw = false
                eval_assign!(sched, ft, :the_exception, t.final.thrown)
                t.final.thrown = bot(Ty)
                if t.final.must_throw # thrown for sure
                    next_pc = branch_pc = length(code.body)+1
                end
                t.final.must_throw = false
            end
            for i=1:(stmt.args[1]::Int)
                pop!(t.eh_stack)
            end
        end
        push!(t.visited, t.pc)
        if isa(stmt,Expr) && stmt.head === :(=)
            @assert next_pc == branch_pc
            eval_assign!(sched, t, stmt.args[1]::LocalName, res)
        end
        if next_pc != branch_pc
            ft = fork(sched, t, branch_pc)
        end
        t.pc = next_pc
        if done(sched, t)
            join!(t.final, :ret_val, res)
        end
    end
    nothing
end

Base.done(s::Scheduler,t::Thread) = t.pc > length(s.funs[t.fc].body)
Base.done(s::Scheduler) = isempty(s.threads)
function step!(s::Scheduler)
    #=n = length(s.threads)
    while n > 0
        t = s.threads[n]
        if t.wait_on == 0
            break
        end
        n -= 1
    end=#
    sort!(s.threads, by = t -> (-t.fc, t.cycle, t.wait_on == 0, t.pc))
#=    if n == 0
        n = length(s.threads)
    end=#
    n = 1
    t = s.threads[n]
    k = 0
    while n < length(s.threads) &&
        s.threads[n+1].fc == t.fc &&
        s.threads[n+1].cycle == t.cycle &&
        s.threads[n+1].wait_on == t.wait_on &&
        s.threads[n+1].pc == t.pc &&
        s.threads[n+1].ec == t.ec
        k+=1
        t.state,chg = join!(t.state, s.threads[n+1].state)
        t.final,chg2 = join!(t.final, s.threads[n+1].final)
        if chg | chg2
            t.visited = intersect(t.visited, s.threads[n+1].visited)
        else
            union!(t.visited, s.threads[n+1].visited)
        end
        deleteat!(s.threads, n+1)
    end
    try
        step!(s, t, s.config)
    catch x
        println("Exception while executing ", t)
        println("Function : ", s.funs[t.fc])
        read(STDIN, Char)
        println(s)
        rethrow(x)
    end
#=    if s.state.changed
        t.pc = 1
        t.ec = 1
        t.wait_on = nothing
    else=#if done(s,t)# || !(.state.changed || s.values.changed || t.wait_on != nothing)
        fc = t.fc
        t.pc = length(s.funs[fc].body) + 1
        join!(s.final, fc, t.final)
        deleteat!(s.threads,n)
        push!(s.done_threads,t)
        same_func = find(th->th.fc==fc, s.threads)
        isdone = isempty(same_func)
        mincycle = isdone ? -1 : minimum([s.threads[i].cycle for i in same_func])
        #println("Thread finished at ", s.funs[fc], " : ", t.cycle, " min ", mincycle)
        if !isdone && mincycle > t.cycle
            isdone = !has_changed(s.final, fc)
            reset_changed(s.final, fc)
        end
        if isdone
            if isbot(s.final[fc])
                println(s)
                println("Reached bot for ", s.funs[fc])
                for b in s.funs[fc].body
                    Meta.show_sexpr(b);println()
                end
                exit()
            end
            deleteat!(s.threads, same_func)
            s.done[t.fc] = true
        end
        TRACE && println("THREAD FINISHED ", false, "/", s.values.changed, "/", t.wait_on != nothing, " ================")
    end
end
LIM = 500000
function run(s::Scheduler)
    nstep = 0
    maxthread = length(s.threads)
    while !done(s) && nstep < LIM
        step!(s)
        maxthread = max(maxthread, length(s.threads))
        if nstep % 10000 == 0
            println("...")
#            println(s)
        end
        nstep += 1
    end
    nstep, maxthread
end
function Base.show(io::IO, s::Scheduler)
    println(io, "====== scheduler (", length(s.threads), " active threads, ", length(s.funs), " functions):")
#=    for t in s.threads
        println(io, "thread ", t)
    end=#
    fcs = [t.fc for t in s.threads]
    dfcs = [t.fc for t in s.done_threads]
    nthr = Dict([u => length(findin(fcs,u)) for u in unique(fcs)])
    dnthr = Dict([u => length(findin(dfcs,u)) for u in unique(dfcs)])
    for (k,v) in enumerate(s.funs)
        #        get(nthr,k,0) > 0 || continue
        #if !istop(s.final[k].ret_val); continue; end
        println(io, "==== fun ", k, ": ", v)
        println(io, "threads : ", get(nthr,k,0), " active, ", get(dnthr,k,0), " done")
        callers = map(cfc -> (s.funs[cfc[1]], cfc[2]), collect(s.called_by[k]))
        println(io, "called by : ")
        for (fun, pc) in callers
            println(io, "\t- ", fun, " at ", pc)
        end
        println(io, "final : ", s.final[k])
        println(io, "initial : ", s.initial[k])
    end
    println(io, "======")
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
        e.head === :call || e.head ===:call1 || e.head === :new || e.head === :copyast || e.head === :static_typeof || e.head === :the_exception || error("not a call " * string(e) * " : " * string(v))
        if e.head == :the_exception
            push!(v, :the_exception) # TODO name collision ?
            push!(ds,d)
            return v,ds
        elseif e.head === :copyast # TODO
            push!(v, :UNKNOWN)
            push!(ds,d)
            return v,ds
        elseif e.head === :static_typeof
            push!(v, :UNKNOWN)
            push!(ds,d)
            return v,ds
        #=elseif isa(e.args[1], TopNode) && e.args[1].name in (:box,:unbox) ||# TODO
            e.args[1] in (:box,:unbox)
            linearize!(e.args[3], v, ds, d)
            return v,ds=#
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
    elseif isa(stmt,Expr) && (stmt.head === :boundscheck || stmt.head === :type_goto || stmt.head === :meta) # TODO
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

const _code_cache = Dict{Any,Code}()
const SR = []
function code_from_ast(linf,tenv)
    key = (linf,tenv)
    haskey(_code_cache, key) && return _code_cache[key]
    TRACE && @show ast
    fun_name = linf.name
    mod = linf.module
    ast = Base.uncompressed_ast(linf)
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
    # TODO ask Jeff if this is the easiest way to sort out this mess
    # probably not
    locs = Set{LocalName}(ast.args[2][1])
    isva = false
    args = map(ast.args[1]) do a
        if isa(a, Expr) && a.head == :(::) # TODO ugh
            if isa(a.args[2],Expr) && a.args[2].head === :call && a.args[2].args[1] === TopNode(:apply_type) && a.args[2].args[2] === :Vararg
                isva = true
            end
            a.args[1]
        elseif isa(a, Symbol)
            a
        else
            dump(a)
            error("arg ? " * string(a))
        end
    end
    decltypes = Dict{LocalName,Any}()
    capt = Array(Symbol, 0)
    union!(locs,args)
    for varinfo in ast.args[2][2]
        name = varinfo[1]
        if !(name in locs)
            error(@sprintf("Unknown varinfo : %s", varinfo))
        end
        decltypes[name] = varinfo[2]
    end
    for varinfo in ast.args[2][3]
        name = varinfo[1]
        decltypes[name] = varinfo[2]
        push!(capt, name)
    end
    union!(locs,capt)
    push!(locs, :the_exception) #TODO ugh
    lin = [linearize_stmt!(e,[],Int[]) for e in body]
    c = Code(mod, fun_name, body, label_pc, locs, args, lin, isva, tenv, capt, decltypes)
    for i=1:2:length(tenv)
        push!(c.locals, tenv[i].name)
    end
    _code_cache[key] = c
    c
end

function code(f::Function,argtypes::ANY)
    meths = Base._methods(f,argtypes, -1)
    if meths === false || length(meths) > 1
        return length(meths)
    end
    if length(meths) == 0
        return false
    end
    meth = meths[1][3]
    func = meth.func
    tenv = meths[1][2]
    if meth.isstaged
        func = ccall(:jl_instantiate_staged, Any,(Any,Any,Any), meth, argtypes, tenv)
    end
    c = code_from_ast(func.code, tenv)
    c
end

function displayfun(s::Scheduler, fc::Int)
    b = IOBuffer()
    code = s.funs[fc]
    @printf(b, "<table>")
    for pc = 1:length(code.body)
        @printf(b, "<tr>")
        @printf(b, "<td>")
        Meta.show_sexpr(b, code.body[pc])
        @printf(b, "</td></tr>")
    end
    @printf(b, "</table>")
    seekstart(b)
    display("text/html", readall(b))
end


type FinalState{V} <: Lattice
    ret_val :: V
    thrown :: Ty
    must_throw :: Bool
end
bot{V}(::Type{FinalState{V}}) = FinalState(bot(V),bot(Ty),false)
function join!{V}(s::FinalState{V}, fld::Symbol, v)
    if fld == :ret_val
        s.ret_val, chg = join!(s.ret_val, v)
    elseif fld == :thrown
        s.thrown, chg = join!(s.thrown, convert(Ty,v))
    elseif fld == :must_throw
        error("!!")
        s.must_throw, chg = v,(s.must_throw!=v)#join!(s.must_throw, convert(Const,v)) #TODO STRONG UPDATE THIS IS WRONG
    else
        error("..??")
    end
    s, chg
end
function join!{V}(s::FinalState{V},s2::FinalState{V})
    s.ret_val, chg = join!(s.ret_val, s2.ret_val)
    s.thrown, chg2 = join!(s.thrown, s2.thrown)
    s.must_throw, chg3 = (s.must_throw & s2.must_throw), (s.must_throw && !s2.must_throw)
    s, (chg | chg2 | chg3)
end
function Base.show(io::IO, s::FinalState)
    print(io, "(returned: ", s.ret_val)
    if !isbot(s.thrown)
        print(io, ", ", s.must_throw ? "must" : "may", " throw ", s.thrown)
    end
    print(io, ")")
end

type ThreadState{Loc} <: Lattice
    locals :: Loc
end
top{L}(::Type{ThreadState{L}}) = ThreadState(top(L))
bot{L}(::Type{ThreadState{L}}) = ThreadState(bot(L))
eval_local(s::ThreadState, name::LocalName) = eval_local(s.locals, name)
<=(s::ThreadState,s2::ThreadState) = s.locals <= s2.locals
function call_gate!(s::ThreadState)
    empty!(s.locals.map)
    s
end

function join!(s::ThreadState, fld::Symbol, v)
    if fld == :locals
        s.locals, chg = join!(s.locals, v)
    else
        error(@sprintf("??? %s", fld))
    end
    s, chg
end

function join!{V}(s::ThreadState{V}, s2::ThreadState{V})
    s.locals, chg = join!(s.locals, s2.locals)
    #=l1,l2 = length(s.eh_stack), length(s2.eh_stack)
    n = max(l1,l2)
    for i = 1:n
        if i > l1 || i > l2 || s.eh_stack[i] != s2.eh_stack[i]
            chg |= (i > l1 || s.eh_stack[i] != (0,0))
            resize!(s.eh_stack, i)
            s.eh_stack[i] = (0,0)
            break
        end
    end=#
    s, chg
end

export Prod,Sign,Const,Ty,Birth,LocalStore,Thread,FunctionState,Scheduler,Code,FunState,ExprVal,ExprState,FinalState,ThreadState,ConstCode

# == client

module Analysis
using GreenFairy
const ValueT = Prod{(Const,Ty,Sign,Birth,ConstCode{Ty})}
const StateT = ThreadState{LocalStore{ValueT}}
const FinalT = FinalState{ValueT}
make_sched(conf) = Scheduler(ExprState(ValueT),FunState(StateT),FunState(FinalT),Array(Bool,0),Array(Thread{StateT,FinalT},0),Array(Thread{StateT,FinalT},0),conf,Array(Set{Any},0),Array(Code,0))
end
#@show code_typed(join, (Analysis.ValueT,Analysis.ValueT))
#@show code_typed(step!,(Analysis.ThreadT,Vector{Analysis.ThreadT},Config))
#@show code_typed(eval_local, (Analysis.StoreT,Any))
#@show code_llvm(top, (Type{Analysis.ValueT},))
#exit()

function run(f::Function, args)
    sched = Analysis.make_sched(Config(:always))
    eval_call_gf!(sched, bot(Analysis.StateT), f, map(a->convert(Analysis.ValueT, a), args))
    #=fc = register_fun!(sched, code(F, args))
    push!(sched.threads, Thread(Analysis.StateT,Analysis.FinalT,fc,1,1))=#
    dt = @elapsed begin
        niter,maxthr = run(sched)
    end
    println("Finished in ", niter, " ", maxthr, " threads :")
    @printf("Speed %.2f Kit/s for %.2f s\n", (niter/1000)/dt, dt)
    println("Result : ", sched.final[1])
    read(STDIN,Char)
    sched
end

function RUN(F::Function,args::ANY)
    sched = Analysis.make_sched(Config(:always))
    eval_call_gf!(sched, bot(Analysis.StateT), F, map(a->convert(Analysis.ValueT, Ty(a)), args))
    #=fc = register_fun!(sched, code(F, args))
    push!(sched.threads, Thread(Analysis.StateT,Analysis.FinalT,fc,1,1))=#
    dt = @elapsed begin
        niter,maxthr = run(sched)
    end
    println("Finished in ", niter, " ", maxthr, " threads :")
    @printf("Speed %.2f Kit/s for %.2f s\n", (niter/1000)/dt, dt)
    println("Result : ", sched.final[1])
    read(STDIN,Char)
    sched
end
#@show code_typed(eval_call!, (Analysis.ThreadT,Type{Analysis.ValueT},Analysis.ValueT,Analysis.ValueT,Analysis.ValueT))
#exit()
#@time RUN(RUN, (Function,Any))
#file for i=1:10; RUN(); end
#Base.Profile.print()
#@time RUN()
#@time (niter,maxthr,ss) = RUN()
#@time (niter,maxthr,ss) = RUN()
#Z = @time [RUN()[1] for i=1:1000000]
DOIT() = GreenFairy.RUN(DOIT, ())
end
#=sched = GreenFairy.RUN(GreenFairy.F, ())
@show @code_typed GreenFairy.eval_call!(sched, sched.done_threads[1], sched.ret_values[1])
sched = @time for i=1:2; GreenFairy.RUN(GreenFairy.DOIT, ()); end=#

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

G(z) = z-2

function K()
    x = 3
    while UNKNOWN
        x = x+1
    end
    return x
    x = 3
    y = G(x+1)
    return y
    y = (x+1)*x
end

FA(n) = n > 0 ? FA(n-1) : UNKNOWN ? throw(n) : n
FB(n) = throw(n)
function F()
    try
        #FB(3)
        throw(3)
    catch x
        return x
    end
    return 32.0
end
