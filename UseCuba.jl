module UseCuba
using Cuba, SpecialFunctions
export NIntgrate, NIntExpr
#  int1numsc = cuhre(intSec1s, numvar, 2, atol=1e-10, rtol=1e-10);
# int1numsc = vegas(intSec1s, numvar, 2, atol=1e-10, rtol=1e-10);
#  int1numsc = suave(intSec1s, numvar, 2, atol=1e-6, rtol=1e-6);
macro expr2fun(expr,args) #This is genfun in SyntaxTree.jl by @chakravala
    :($(Expr(:tuple,args.args...))->$expr)
end
expr2fun(expr,args) = :(@expr2fun $expr [$(args...)]) |> eval
curry(f,params...)=(xs...)->f(xs...,params...)
function Power(f::T,n::Rational{Int64}) where T Union{Int64,Float64}
  Power(1.0*f,1.0*n)
end
function Power(f::T1,g::T2) where {T1 <: Union{Irrational,Int, Int64, Float32, Float64,Complex{Float64}},T2 <: Union{Irrational,Int, Int64, Float32, Float64, Complex{Float64}}}
    typeof(f)==Complex{Float64} ? fc=f : fc=Complex(f,0)
   if imag(fc)==0.0
       fc=real(fc)+0.0im
   end
 fc^g
end
function wedge(args...)
    args
end
function Length(f::Expr)
    length(f.args)-1
end
function NIntgrate(fname::String,numvar::Int64,D::Float64,t::Float64,method::String="cuhre", PrintErr::Bool=false)
    jufun=curry(getfield(Main, Symbol(fname)),D,t)
    function intSec1s(x,f)#α1 sector decomposition
        tmp=jufun(Complex.(x)...)
        f[1], f[2]=reim(tmp)
    end
    cubafun=getfield(UseCuba, Symbol(method))
    int1numsc = cubafun(intSec1s, numvar, 2, atol=1e-10, rtol=1e-10);
    PrintErr ? print(int1numsc) : Nothing;
    int1numC = int1numsc[1][1]+int1numsc[1][2]im;
    return int1numC
end
function NIntgrate(fname::String,numvar::Int64,method::String="cuhre", PrintErr::Bool=false)
    jufun=getfield(Main, Symbol(fname))
    function intSec1s(x,f)#α1 sector decomposition
        tmp=jufun(Complex.(x)...)
        f[1], f[2]=reim(tmp)
    end
    cubafun=getfield(UseCuba, Symbol(method))
    int1numsc = cubafun(intSec1s, numvar, 2, atol=1e-10, rtol=1e-10);
    PrintErr ? print(int1numsc) : Nothing;
    int1numC = int1numsc[1][1]+int1numsc[1][2]im;
    return int1numC
end
function NIntgrate(g::Function,numvar::Int64,D::Float64,t::Float64,method::String="cuhre", PrintErr::Bool=false)
    jufun=curry(g,D,t)
    function intSec1s(x,f)#α1 sector decomposition
        tmp=jufun(Complex.(x)...)
        f[1], f[2]=reim(tmp)
    end
    cubafun=getfield(UseCuba, Symbol(method))
    int1numsc = cubafun(intSec1s, numvar, 2, atol=1e-10, rtol=1e-10);
    PrintErr ? print(int1numsc) : Nothing;
    int1numC = int1numsc[1][1]+int1numsc[1][2]im;
    return int1numC
end
function NIntgrate(g::Function,numvar::Int64,method::String="cuhre", PrintErr::Bool=false)
    function intSec1s(x,f)#α1 sector decomposition
        tmp=g(Complex.(x)...)
        f[1], f[2]=reim(tmp)
    end
    cubafun=getfield(UseCuba, Symbol(method))
    int1numsc = cubafun(intSec1s, numvar, 2, atol=1e-10, rtol=1e-10);
    PrintErr ? print(int1numsc) : Nothing;
    int1numC = int1numsc[1][1]+int1numsc[1][2]im;
    return int1numC
end

function NIntExpr(f::Array{Array{Expr,1},1},method::String="vegas")
    resint=Any[];
    for i in 1:length(f)
        print(i)
        jfunc=expr2fun(f[i][1],[(f[i][2].args[2:end])...])
        vnum=f[i][2]|>Length
        push!(resint,NIntgrate(jfunc,vnum,method))
    end

end
function NIntExpr(f::Array{Expr,1},method::String="vegas",PrintErr::Bool=false)
    jfunc=expr2fun(f[1],[(f[2].args[2:end])...]);
    vnum=f[2]|>Length;
    NIntgrate(jfunc,vnum,method,PrintErr)
end

#NIntExpr([Expr(:call,+,:x1,:x2),Expr(:call,wedge,:x1,:x2)])
end
