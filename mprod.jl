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



