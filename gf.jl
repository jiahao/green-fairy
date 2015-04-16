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
Base.show(io::IO, x::Const) = (istop(x) | isbot(x)) ? show(io, x.tag) : (print(io, "const(");show_limit(io,x.v);print(io,")"))
<=(x::Const,y::Const) = (istop(y) || isbot(x) || y.v===x.v)
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
eval_lit(::Type{Sign}, v::FloatingPoint) = Sign(round(Int, sign(v)))

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
eval_lit(::Type{Ty}, v::ANY) = Ty(typeof(v))

# ========== Birth
immutable Birth <: Lattice
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
typealias LocalName Union(Symbol,GenSym)
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
    isva :: Bool
    tvar_mapping :: Tuple
end
function Base.show(io::IO, c::Code)
    ln = c.body[1]
    if ln.head == :line
        lns = @sprintf("%s:%d", ln.args[2], ln.args[1])
    else
        lns = "???"
    end
    print(io, "(", c.mod, ".", c.name, " at ",lns,", ", length(c.body), " statements, ", sum([length(l[1]) for l in c.linear_expr])," steps)")
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
    #data::Dict{(Int,Int,Int),T} # TODO really inefficient
    data :: Vector{Vector{Vector{T}}} 
    changed :: Bool
end
ExprState{T}(::Type{T}) = ExprState(Array(Vector{Vector{T}},0), false)
function ensure_filled!{T}(s::ExprState{T}, fc::Int, c::Code)
    @assert length(s.data)+1 == fc
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

type Thread{StateT}
    fc :: Int
    pc :: Int
    ec :: Int
    wait_on :: Int # fc we need to continue, or 0 if none
    cycle :: Int
    state :: StateT
    visited :: Set{Int} # inefficient, could be parametrized by modified state, could be a bitfield, ...
end
Thread(StateT,f,p,e) = Thread(f,p,e,0,0,bot(StateT),Set{Int}())

type Scheduler{ValueT,InitialT}
    values :: ExprState{ValueT}
    ret_values :: FunState{ValueT}
    initial :: FunState{InitialT}
    done :: Vector{Bool}
    threads :: Vector{Thread}
    done_threads :: Vector{Thread}
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
        ensure_filled!(sched.ret_values, fc, fcode)
        ensure_filled!(sched.initial, fc, fcode)
        push!(sched.done, false)
        push!(sched.called_by, Set{Any}())
    end
    fc
end

function Base.show(io::IO,t::Thread)
    println(io, "abstract thread at ",t.fc,":",t.pc,":",t.ec)
    print(io, t.state)
end

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
fork(s,t) = fork(s,t,t.pc,t.ec)
fork(s,t,pc) = fork(s,t,pc,1)
function fork{S}(s::Scheduler,t::Thread{S},pc::Int,ec::Int)
    child = Thread(S,t.fc,pc,ec)
    child.cycle = t.cycle
    join!(child.state, t.state)
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
#=function join{V}(s1::LocalStore{V},s2::LocalStore{V})
    s = LocalStore{V}(copy(s1.map))
    join!(s,s2)
    s
end=#
function eval_local{V}(s::LocalStore{V}, name::LocalName)
    haskey(s.map, name) || return bot(V)
    s.map[name]
end

meet_ext(v::Lattice, v2::Lattice) = v
meet_ext{T}(v::T,v2::T) = v
meet_ext(v::Ty, v2::Const) = istop(v2) ? v : eval_lit(Ty,v2.v)
#=function meet_ext(v::Const, v2::Ty)
    isleaftype(v2.ty) || return top(Const)
    v2.ty <: Tuple && (println("RETURNING ", v2.ty); return Const(v2.ty)) # TODO rebase ontop tuple branch
    v2.ty.name === Type.name && isleaftype(v2.ty.parameters[1]) ? (println("RETURNING ", v2.ty); Const(v2.ty.parameters[1])) : top(Const)
end=#
const new_fun = :new_tag # maybe we could have Base.new for consistency
eval_call!{V}(t::Thread, ::Type{V}, f, args...) = top(V)
function spawn!(sched::Scheduler, f :: Function, args...)

end

call_gate{T<:Lattice}(v::T) = top(T)
call_gate(v::Const) = isa(v.v, Type) ? v : top(Const)
call_gate(v::Union(Sign,Ty,Birth)) = v
call_gate(p::Prod) = prod(map(call_gate,p.values))

function eval_call!{S,V}(sched::Scheduler, t::Thread{S}, args::V...)
    any(isbot, args) && (println("bot arg ", args); return bot(V))
    f = convert(Const,args[1])
    if !istop(f) && (isa(f.v,Function) && isgeneric(f.v) || !isa(f.v,Function) && !isa(f.v,IntrinsicFunction))
        fv = f.v
        if !isa(fv,Function)
            fv = eval(sched.funs[t.fc].mod, :call) # call overloading
        else
            args = args[2:end]
        end
        argt = map(args) do a
            ca = convert(Const,a)
            if !istop(ca) && isa(ca.v, Type) && isleaftype(ca.v)
                Type{ca.v}
            else
                convert(Ty,a).ty
            end
        end
        fcode = code(fv, argt)
        if fcode !== false
#            fc = register_fun!(sched, fcode)
            child = Thread(S,0,1,1)
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
            narg == length(args) || error(@sprintf("Wrong arg count : %s vs %s%s", fcode.args, args, fcode.isva ? " (vararg)" : ""))#return bot(V)
            for i = 1:narg
                argname = fcode.args[i]
                arg = args[i]
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
            for fc in 1:length(sched.funs)
                if sched.funs[fc] === fcode && child.state <= sched.initial[fc]
                    t.wait_on = fc
                    push!(sched.called_by[fc], t.fc)
                    return nothing
                end
            end
            fc = register_fun!(sched, fcode)
            child.fc = fc
            join!(sched.initial, fc, child.state)
            push!(sched.threads, child)
            push!(sched.called_by[fc], t.fc)
            t.wait_on = fc
            return nothing
        else
#=            println("no : ", fv, " ", argt, " ", args)
            println(t)
            println(sched)
            exit()=#
        end
        top(V)
    elseif f <= Const(Base.throw) || f <= Const(Base.rethrow)
        bot(V)
    else
        eval_call!(t, V, args...)
    end
end
function eval_new!{V}(t::Thread, args::V...)
    any(isbot, args) && return bot(V)
    eval_call!(t, V, meet(top(V), Const(new_fun)), args...)
end

stagedfunction eval_call!{Ls}(t::Thread, ::Type{Prod{Ls}}, f::Prod{Ls}, args::Prod{Ls}...)
    ex = :(top(Prod{Ls}))
    for L in Ls
        ex = :(meet($ex, eval_call!(t, $L, f, args...)))
    end
    ex
end
const BITS_INTR = [Base.add_int, Base.sub_int, Base.mul_int, Base.srem_int, Base.ctlz_int, Base.slt_int, Base.sle_int, Base.not_int,Base.apply_type]
const BITS_FUNC = [+, -, *, %, leading_zeros, <, <=, !, Base.apply_type]

function eval_call!{V}(t::Thread, ::Type{Sign}, f::V, args::V...)
    # sign add
    if f <= Const(Base.add_int)
        length(args) == 2 || return bot(V)
        args[1] <= Sign(0) && args[2] <= Sign(0) && return convert(V,Sign(0)) # +(0 0) = 0
        for sgn in (-1,1) # +(+ 0) = +(0 +) = +(+ +) = + and +(- 0) = +(0 -) = +(- -) = -
            (args[1] <= Sign(sgn) || args[1] <= Sign(0)) &&
            (args[2] <= Sign(sgn) || args[2] <= Sign(0)) &&
            return convert(V,Sign(sgn))
        end
    end
    # sign sub
    if f <= Const(Base.sub_int)
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
                    (Int, [Base.add_int, Base.sub_int,Base.check_top_bit, Base.mul_int, Base.srem_int, Base.ctlz_int, Base.ashr_int])
                    ]
const BOOL_INTR = [Base.slt_int, Base.sle_int, Base.not_int]
#const 

function eval_call!{V}(t::Thread, ::Type{Ty}, f::V, args::V...)
    if f <= Const(new_fun) && length(args) >= 1
        cty = convert(Const, args[1])
        istop(cty) && return top(Ty)
        return Ty(cty.v)
    end
    argtypes = map(a->convert(Ty,a),args)
    for (retty,intrs) in INTR_TYPES
        for bf in intrs
            if f <= Const(bf)
                return convert(V, Ty(retty))
            end
        end
    end
    for bf in BOOL_INTR
        if f <= Const(bf)
            return Ty(Bool)
        end
    end
    if f <= Const(Base.select_value)
        return reduce(join, args)
    end
    if f <= Const(Base.typeof)
        isleaftype(argtypes[1].ty) || return Ty(Type)
        return Const(argtypes[1].ty)
    end
    if f <= Const(Base.tuple)
        # TODO rebase on top of new tuple types
        return Ty(map(a->a.ty,argtypes))
    end
    if f <= Const(Base.arraylen)
        argtypes[1] <= Ty(Array) || return bot(V)
        return convert(V, Ty(Int))
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
    # first argument is return type
    if  f <= Const(Base.checked_trunc_uint) ||
        f <= Const(Base.checked_trunc_sint) ||
        f <= Const(Base.zext_int)
        cty = convert(Const,args[1])
        istop(cty) && return top(V)
        return Ty(cty.v)
    end
    if f <= Const(Base.ccall)
        # TODO add known ccalls here
        return top(V)
    end
    if f <= Const(Base.typeassert)
        typ = convert(Const, args[2])
        istop(typ) && return top(V)
        return convert(V, Ty(typ.v))
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
            return convert(V,Const(rf(map(a -> a.v, cargs)...)))
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

    top(V)
end
function eval_call!(t::Thread, ::Type{Birth}, f, args...)
    if f <= Const(new_fun)
        return Birth(t.pc, t.ec)
    end
    top(Birth)
end

function eval_assign!{V}(s,t,name,res::V)
    t.state, changed = join!(t.state, name => res)
    if changed
        empty!(t.visited)
    end
    nothing
end

function step!{V}(sched::Scheduler{V}, t::Thread, conf::Config)
    code = sched.funs[t.fc]
    values = sched.values
    le = code.linear_expr[t.pc]
    if t.ec == 1 && t.pc in t.visited
        t.pc =length(code.body)+1
        return
    end
    TRACE && println("Step thread ", t)
    if t.ec <= length(le[1]) # continue evaluating expr
        e = le[1][t.ec]
        ed = le[2][t.ec]
        res = if t.wait_on > 0
            if sched.done[t.wait_on]
                r = sched.ret_values[t.wait_on]
                t.wait_on = 0
                r
            else # cycle
                ft = fork(sched, t)
                ft.wait_on = t.wait_on
                ft.cycle += 1
                t.wait_on = 0
                sched.ret_values[ft.wait_on]
            end
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
                    eval_call!(sched, t, args...)
                end
            else
                error("expr ? " * string(e))
            end
        elseif isa(e, LocalName)
            if e === :UNKNOWN
                top(V)
            elseif e in code.locals || isa(e,GenSym)
                eval_local(t.state, e)
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
        end
        push!(t.visited, t.pc)
        if next_pc != branch_pc
            fork(sched, t, branch_pc)
        end
        t.pc = next_pc
        if isa(stmt,Expr) && stmt.head === :(=)
            @assert next_pc == branch_pc
            eval_assign!(sched, t, stmt.args[1]::LocalName, res)
        end
        if done(sched, t)
            join!(sched.ret_values,t.fc,res)
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
        s.threads[n+1].pc == t.pc
        k+=1
        t.state,chg = join!(t.state, s.threads[n+1].state)
        if chg
            t.visited = intersect(t.visited, s.threads[n+1].visited)
        end
        deleteat!(s.threads, n+1)
    end
    try
        step!(s, t, s.config)
    catch x
        println("Exception while executing ", t)
        rethrow(x)
    end
#=    if s.state.changed
        t.pc = 1
        t.ec = 1
        t.wait_on = nothing
    else=#if done(s,t)# || !(.state.changed || s.values.changed || t.wait_on != nothing)
        fc = t.fc
        t.pc = length(s.funs[fc].body) + 1
        deleteat!(s.threads,n)
        push!(s.done_threads,t)
        same_func = find(th->th.fc==fc, s.threads)
        isdone = isempty(same_func)
        mincycle = isdone ? -1 : minimum([s.threads[i].cycle for i in same_func])
        #println("Thread finished at ", s.funs[fc], " : ", t.cycle, " min ", mincycle)
        if !isdone && mincycle > t.cycle
            #println("cycle done : ", has_changed(s.ret_values,fc))
            isdone = !has_changed(s.ret_values, fc)
            reset_changed(s.ret_values, fc)
        end
        if isdone
            if isbot(s.ret_values[fc])
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
function run(s::Scheduler)
    nstep = 0
    maxthread = length(s.threads)
    while !done(s) && nstep < LIM
        step!(s)
        maxthread = max(maxthread, length(s.threads))
        if nstep % 10000 == 0
            println(s)
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
        println(io, "==== fun ", k, ": ", v)
        println(io, "threads : ", get(nthr,k,0), " active, ", get(dnthr,k,0), " done")
        println(io, "called by : ", s.called_by[k])
        println(io, "return : ", s.ret_values[k])
        print(io, "initial : ", s.initial[k])
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
            push!(v, :UNKNOWN)
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
        elseif isa(e.args[1], TopNode) && e.args[1].name in (:box,:unbox) ||# TODO
            e.args[1] in (:box,:unbox)
            linearize!(e.args[3], v, ds, d)
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
    isva = false
    args = map(ast.args[1]) do a
        if isa(a, Expr) && a.head == :(::)
            if eval(a.args[2]) <: Vararg
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
    union!(locs,args)
    lin = [linearize_stmt!(e,[],Int[]) for e in body]
    Code(mod, name, f, body, label_pc, locs, args, lin, isva, ())
end

const _code_cache = Dict{Any,Code}()

function code(f::Function,argtypes::ANY)
    key = (f,argtypes)
    if !haskey(_code_cache, key)
        meths = Base._methods(f,argtypes, 1)
        meths !== false && length(meths) > 0 || return false # TODO handle no method error
        meth = meths[1][3]
        ast = Base.uncompressed_ast(meth.func.code)
        c = code_from_ast(f, ast, f.env.name, meth.func.code.module)
        c.tvar_mapping = meths[1][2]
        for i=1:2:length(c.tvar_mapping)
            push!(c.locals, c.tvar_mapping[i].name)
        end
        _code_cache[key] = c
    end
    _code_cache[key]
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

FA(n) = n > 0 ? FA(n-1) : n
function F()
    FA(3)
end

export Prod,Sign,Const,Ty,Birth,LocalStore,Thread,FunctionState,Scheduler,Code,FunState,ExprVal,ExprState

# == client

module Analysis
using GreenFairy
const ValueT = Prod{(Sign,Const,Ty,Birth)}
const StoreT = LocalStore{ValueT}
make_sched(conf) = Scheduler(ExprState(ValueT),FunState(ValueT),FunState(StoreT),Array(Bool,0),Array(Thread,0),Array(Thread,0),conf,Array(Set{Any},0),Array(Code,0))
end
#@show code_typed(join, (Analysis.ValueT,Analysis.ValueT))
#@show code_typed(step!,(Analysis.ThreadT,Vector{Analysis.ThreadT},Config))
#@show code_typed(eval_local, (Analysis.StoreT,Any))
#@show code_llvm(top, (Type{Analysis.ValueT},))
#exit()

function RUN(F::Function,args::ANY)
    sched = Analysis.make_sched(Config(:always))
    fc = register_fun!(sched, code(F, args))
    push!(sched.threads, Thread(Analysis.StoreT,fc,1,1))
    dt = @elapsed begin
        niter,maxthr = run(sched)
    end
    println("Finished in ", niter, " ", maxthr, " threads :\n",sched)
    @printf("Speed %.2f Kit/s for %.2f s\n", (niter/1000)/dt, dt)
    println("Result : ", sched.ret_values[1])
    sched
end
#@show code_typed(eval_call!, (Analysis.ThreadT,Type{Analysis.ValueT},Analysis.ValueT,Analysis.ValueT,Analysis.ValueT))
#exit()
DOIT() = RUN(F, ())
LIM = 20000
#@time RUN(RUN, (Function,Any))
#file for i=1:10; RUN(); end
#Base.Profile.print()
#@time RUN()
#@time (niter,maxthr,ss) = RUN()
#@time (niter,maxthr,ss) = RUN()
#Z = @time [RUN()[1] for i=1:1000000]

end
sched = GreenFairy.RUN(GreenFairy.F, ())
@show @code_typed GreenFairy.eval_call!(sched, sched.done_threads[1], sched.ret_values[1])
sched = @time for i=1:2; GreenFairy.RUN(GreenFairy.DOIT, ()); end

