type StateCell{T}
    val_isset :: BitVector
    val_rle :: Vector{T}
end

StateCell{T}(::Type{T},n::Int) = StateCell(fill!(BitVector(n+1),false),Array(T,0))
function Base.getindex{T}(s::StateCell{T}, pc)
    idx = countnz(s.val_isset, pc)
    v2 = if idx == 0
        bot(T)
    else
        s.val_rle[idx]
    end
    v2
end
# ASSUMES NON TRIVIAL INSERT
function Base.setindex!{T}(s::StateCell{T},v::T,pc::Int)
    isset = s.val_isset
    val = s.val_rle
    self_isset = s.val_isset[pc]
    idx = countnz(isset, pc)
    not_last = pc < length(isset)
    @inbounds if self_isset # already set
        if idx == 1 && isbot(v) || idx > 1 && val[idx-1] == v # collapse into prev
            if not_last && !isset[pc+1] # reuse current for next
                isset[pc+1] = true
            else
                if not_last && isset[pc+1] && val[idx+1] == v # collapse current & next into prev
                    isset[pc+1] = false
                    deleteat!(val, idx+1)
                end
                deleteat!(val, idx)
            end
            isset[pc] = false
        elseif not_last && !isset[pc+1] # preserve next
            insert!(val, idx+1, idx > 0 ? val[idx] : bot(T))
            val[idx] = v
            isset[pc+1] = true
        elseif not_last && val[idx+1] == v
            deleteat!(val, idx)
            isset[pc+1] = false
        else # update in place
            val[idx] = v
        end
    elseif idx == 0 && !isbot(v) || idx > 0 && val[idx] != v # need to set
        isset[pc] = true
        if not_last && isset[pc+1] && val[idx+1] == v # reuse next for current
            isset[pc+1] = false
        else
            insert!(val, idx+1, v)
            if not_last && !isset[pc+1] # preserve next
                insert!(val, idx+2, idx > 0 ? val[idx] : bot(T))
                isset[pc+1] = true
            end
        end
    end
    s
end

@inline function propagate!{T}(s::StateCell{T},pc::Int,next::Int)
    pc > 0 || return false
    @inbounds begin
        next != pc+1 || s.val_isset[next] || return false
        s_pc = s[pc]
        s_next = s[next]
        return if s_pc <= s_next
            false
        else
            val = isbot(s_next) ? s_pc : join(s_next,s_pc)
            if !(val <= s_next)
                s[next] = val
                true
            else
                false
            end
        end
    end
end
function propagate!{T}(s::StateCell{T},pc::Int,next::Int,d::T)
    s_next = s[next]
    if d <= s_next
        false
    else
        val = isbot(s_next) ? d : join(s_next,d)
        if !(val <= s_next)
            s[next] = val
            true
        else
            false
        end
    end
end
function same_state{T}(s::StateCell{T},pc::Int,d::T)
    d == s[pc]
end


abstract MProd{T <: Tuple{Vararg{Lattice}}}
abstract MCell{T <: Tuple{Vararg{Lattice}}}

function make_mprod(Ts)
    name = gensym()
    cname = gensym()
    n = length(Ts)
    eval(quote
         type $name <: MProd{Tuple{$(Ts...)}}
         $([:($(symbol("v$i")) :: $(Ts[i])) for i=1:n]...)
         end
         type $cname <: MCell{Tuple{$(Ts...)}}
         $([:($(symbol("v$i")) :: StateCell{$(Ts[i])}) for i=1:n]...)
         end
         end)
    @eval $cname(n::Int) = $cname($([:(StateCell($(Ts[i]), n)) for i=1:n]...))
    @eval Base.eltype(::Type{$cname}) = Prod{Tuple{$(Ts...)}}
    @eval top(::Type{$name}) = $name($([:(top($T)) for T in Ts]...))
    @eval bot(::Type{$name}) = $name($([:(bot($T)) for T in Ts]...))
    @eval setbot!(x::$name) = $([:(x.($i) = bot($T)) for (i,T) in enumerate(Ts)]...)
    @eval isbot(x::$name) = isbot(x.(1))
    @eval istop(x::$name) = $(foldl((x,y) -> :($x && istop(x.($y))), :(true), 1:n))
    for (i,T) in enumerate(Ts)
        @eval function convert(::Type{$T}, x::$name)
            x.($i)
        end
        @eval function <=(x::$name, y::$T)
            convert($T,x) <= y
        end
        @eval function meet!(x::$name, y::$T)
            x.($i) = meet(x.($i), y)
            if isbot(x.($i))
                setbot!(x)
            end
            nothing
        end
    end
    @eval function meet!(x::$name, y::$name)
        $([:(meet!(x, y.($i))) for i=1:n]...)
        x
    end
    @eval function join!(x::$name, y::$name)
        $([:(x.($i) = join(x.($i), y.($i))) for i=1:n]...)
        x
    end
    @eval function <=(x::$name, y::$name)
        $(foldl((x,y) -> :($x && x.($y) <= y.($y)), :(true), 1:n))
    end
    @eval function propagate!(s::$cname, pc::Int, next::Int)
        $(foldl((x,i) -> :($x | propagate!(s.($i),pc,next)), :(false), 1:n))
    end
    @eval function propagate!(s::$cname, pc::Int, next::Int, d)
        r = false
        $(foldl((x,i) -> :($x | propagate!(s.($i),pc,next,convert($(Ts[i]),d))), :(false), 1:n))
    end
    @eval function same_state(s::$cname, pc::Int, d)
        $(foldl((x,i) -> :($x && same_state(s.($i), pc, convert($(Ts[i]),d))), :(true), 1:n))
    end
    @eval function Base.getindex(s::$cname, pc::Int)
        Prod(tuple($([:(s.($i)[pc]) for i=1:n]...)))
    end

    eval(:(($name,$cname)))
end

function Base.show{T <: MProd}(io::IO, M::Type{T})
    print(io, "meet(", Base.join([sprint(show, fieldtype(T,l)) for l = 1:nfields(T)], ","), ")")
end
function Base.show{T <: MCell}(io::IO, M::Type{T})
    print(io, "meet(", Base.join([sprint(show, fieldtype(T,l)) for l = 1:nfields(T)], ","), ")")
end
function Base.show{T <: MProd}(io::IO, v::T)
    if istop(v)
        print(io, "top")
    elseif isbot(v)
        print(io, "bot")
    else
        print(io, "meet(", Base.join([sprint(show, convert(fieldtype(T,l), v)) for l = 1:nfields(T)], ","), ")")
    end
end



