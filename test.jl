#=
not done
=#
include("gf.jl")
using GreenFairy
using Base.Test

VERB = true
GreenFairy.start_test()

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
function f3(y)
    x = 1
    while UNKNOWN
        x = x + y
    end
    x
end
GreenFairy.test(f3, (Ty(Int),Sign(1))) do r
    @test r.ret_val <= Sign(1)
end
GreenFairy.test(f3, (Ty(Int),Sign(0))) do r
    @test r.ret_val <= Sign(1)
end
function g2()
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
GreenFairy.test(g2) do r
    @test !(r.ret_val <= Sign(1))
end
# test argument declarations
g1(x::Int) = x
GreenFairy.test(g1, ()) do r
    @test r.ret_val <= Ty(Int)
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

VERB && println("non-const functions")
function g12()
end
let z = 3
    function g12(y)
        UNKNOWN ? z : y
    end
end

function f12()
    x = 3
    h = (y -> UNKNOWN ? x : y)
    #UNKNOWN ? g12(2) : h(2) # environment for generic functions does not work yet
    h(2)
end
GreenFairy.test(f12) do r
    @test r.ret_val <= Ty(Int)
end

f13() = map(y -> y + 1, [1,2,3])
GreenFairy.test(f13) do r
    @test r.ret_val <= Ty(Vector{Int})
end
f14() = map(y -> y*1.0, [1,2,3])
GreenFairy.test(f14) do r
    @test r.ret_val <= Ty(Union(Vector{Int},Vector{Float64})) # due to map implementation for empty array
end
# base implementation special case a lot of function with a runtime test
# it's confusing to the fairy for now
rec_foldl(f,v,A) = isempty(A) ? v : rec_foldl(f, f(v,A[1]), A[2:end])
imp_foldl(f,v,A) = (for x in A; v = f(x,v); end; v)
function f15()
    f = (x,y) -> x*y
    v = 1.0
    A = [1,2,3]
    UNKNOWN ? imp_foldl(f,v,A) : rec_foldl(f,v,A)
end
GreenFairy.test(f15) do r
    @test r.ret_val <= Ty(Float64)
end

VERB && GreenFairy.end_test()
