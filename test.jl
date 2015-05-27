#=
not done
=#
include("gf.jl")
using GreenFairy
using Base.Test

VERB = true


VERB && println("basics")
function f2()
    x = 2
    x = 1
    return x
end
GreenFairy.test(f2) do r
    @test r.ret_val <= Const(1)
    @test isbot(r.thrown)
end


VERB && println("recursion")
function f4(x)
    if UNKNOWN
        x
    else
        f4(x+1)
    end
end
GreenFairy.test(f4, (Ty(Int),Sign(1))) do r
    @test r.ret_val <= Sign(1)
end
function f5(x)
    if x > 0
        f5(x+1)
    else
        x
    end
end
GreenFairy.test(f5, (Ty(Int), Sign(-1))) do r
    @test r.ret_val <= Sign(-1)
end
GreenFairy.test(f5, (Ty(Int), Sign(1))) do r
    @test isbot(r.ret_val)
end


VERB && println("tuple widening")
function f6(x)
    if UNKNOWN
        f6((x,x))
    else
        x
    end
end
GreenFairy.test(f6, Ty(Tuple{Int})) do r
    @test r.ret_val <= Ty(Tuple)
end
function f7(x)
    if UNKNOWN
        f7((1,x...))
    else
        x
    end
end
# the two following could be more precise
# we need to handle _apply of unknown length better
GreenFairy.test(f7, Ty(Tuple{Int})) do r
    #@test r.ret_val <= Ty(Tuple{Vararg{Int}})
    @test r.ret_val <= Ty(Tuple)
end
#=GreenFairy.test(f7, Ty(Tuple{Vararg{Int}})) do r
    @test r.ret_val <= Ty(Tuple{Vararg{Int}})
end=#

VERB && println("exceptions")
f8() = throw(3)
GreenFairy.test(f8) do r
    @test r.must_throw
    @test r.thrown <= Const(3)
    @test isbot(r.ret_val)
end
f9() = UNKNOWN ? throw(3) : 22
GreenFairy.test(f9) do r
    @test !r.must_throw
    @test r.thrown <= Const(3)
    @test r.ret_val <= Const(22)
end
function f10()
    x = 3
    try
        f8()
        x = 44
    catch y
        return UNKNOWN ? x : y
    end
    x
end
GreenFairy.test(f10) do r
    @test isbot(r.thrown)
    @test r.ret_val <= Const(3)
end
function f11()
    x = 3
    try
        f9()
        x = -1
    catch y
        return UNKNOWN ? x : y
    end
    if x < 0
        3
    else
        22
    end
end
GreenFairy.test(f10) do r
    @test isbot(r.thrown)
    @test r.ret_val <= Const(3)
end

VERB && println("ok !")
