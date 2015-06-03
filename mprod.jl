include("gf.jl")
using GreenFairy

abstract MProd{T <: Tuple{Vararg{Lattice}}}
meet!(x,y) = GreenFairy.meet(x,y)
import GreenFairy: meet, join, bot, top,istop,isbot
import Base: convert
function make_mprod(Ts)
    name = gensym()
    eval(quote
         type $name <: MProd{Tuple{$(Ts...)}}
         $([:($(symbol("v$i")) :: $(Ts[i])) for i=1:length(Ts)]...)
         end
         end)
    @eval top(::Type{$name}) = $name($([:(top($T)) for T in Ts]...))
    @eval bot(::Type{$name}) = $name($([:(bot($T)) for T in Ts]...))
    @eval setbot!(x::$name) = $([:(x.($i) = bot($T)) for (i,T) in enumerate(Ts)]...)
    @eval isbot(x::$name) = isbot(x.(1))
    @eval istop(x::$name) = $(foldl((x,y) -> :($x && istop(x.($y))), :(true), 1:length(Ts)))
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
        $([:(meet!(x, y.($i))) for i=1:length(Ts)]...)
        x
    end
    @eval function join!(x::$name, y::$name)
        $([:(x.($i) = join(x.($i), y.($i))) for i=1:length(Ts)]...)
        x
    end
    @eval function <=(x::$name, y::$name)
        $(foldl((x,y) -> :($x && x.($y) <= y.($y)), :(true), 1:length(Ts)))
    end
    eval(name)
end

function Base.show{T <: MProd}(io::IO, M::Type{T})
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

const Value = make_mprod((Const,Ty))
@show Value
z = top(Value)
meet!(z,Const(3))
meet!(z,Ty(Real))
@show z
@show convert(Ty,z)
#meet!(z, Ty(Int))
#@show z
#join!(z, Const(2))
#@show z
y = top(Value)
meet!(y, Const(44))
meet!(y, Ty(Integer))
x = top(Value)
@show z <= join!(z,y)
@show y <= z
@show x <= join!(z,x)
#=@show y
meet!(z,y)
@show z y isbot(z) isbot(y)
@show top(Value) istop(top(Value))
@show bot(Value) istop(bot(Value))=#

