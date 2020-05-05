module UseMathLink
using MathLink
using SpecialFunctions, MacroTools
export math2Expr, expr2fun, curry
export Power, List # @vars
export wedge, Length, remove!, ObFunctor, rep!
export @wvar, @wvars, @jvar, @jvars
export @>, @<, @~
macro expr2fun(expr,args) #This is genfun in SyntaxTree.jl by @chakravala
    :($(Expr(:tuple,args.args...))->$expr)
end
expr2fun(expr,args) = :(@expr2fun $expr [$(args...)]) |> eval
curry(f,params...)=(xs...)->f(xs...,params...)
#overwrite binary operators for MathLink expression and numbers
import Base: +,  ^,  //, *, ==
function ==(w1::T1, w2::T2) where {T1<:Union{MathLink.WSymbol,MathLink.WExpr,Number}, T2<: Union{MathLink.WSymbol,MathLink.WExpr,Number}}
     W"Equal"(w1,w2)
end
for (op, binarymethod) in ((:+, W"Plus"), (:*, W"Times"),  (://, W"Rational"), (:^, W"Power"))
    @eval begin
        ($op)(w1::T1, w2::T2) where {T1<:Union{MathLink.WSymbol,MathLink.WExpr}, T2<: Union{MathLink.WSymbol,MathLink.WExpr}}= ($binarymethod)(w1,w2)
        ($op)(w1::T1, w2::Number) where {T1<:Union{MathLink.WSymbol,MathLink.WExpr}}= ($binarymethod)(w1,w2)
        ($op)(w1::Number, w2::T2) where {T2<:Union{MathLink.WSymbol,MathLink.WExpr}}= ($binarymethod)(w1,w2)
        ($op)(w1::Complex, w2::T2) where {T2<:Union{MathLink.WSymbol,MathLink.WExpr}}= ($binarymethod)(W"Complex"(real(w1),imag(w1)),w2)
        ($op)(w1::T1, w2::Complex) where {T1<:Union{MathLink.WSymbol,MathLink.WExpr}}= ($binarymethod)(w1,W"Complex"(real(w2),imag(w2)))
    end
end


#Mathematica to julia expr
function math2Expr(symb::MathLink.WSymbol)
    Symbol(symb.name)
end
function math2Expr(num::Number)
    num
end
binanyOPSymbol=Dict("Times" => :*,"Plus"=> :+,"Rational"=>://)
function math2Expr(expr::MathLink.WExpr)
    haskey(binanyOPSymbol,expr.head.name) ? op=binanyOPSymbol[expr.head.name] : op=Symbol(expr.head.name)
    if  expr.head.name=="List"
        return  List(map(math2Expr,expr.args)...)
    else
        return Expr(:call, op, map(math2Expr,expr.args)...)
    end
end


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


#function Rule(f::Any,g::Any)
#    f=>g
#end

function List(args...)
 [args...]
end
#replace of the symbols in an expression
function rep!(e, old, new)
   for (i,a) in enumerate(e.args)
       if a==old
           e.args[i] = new
       elseif a isa Expr
           rep!(a, old, new)
       end
       ## otherwise do nothing
   end
   e
end
#remove an item in the list
function remove!(list, item)
    deleteat!([list...], findall(x->x==item, list))
end

function wedge(args...)
    args
end
function Length(f::Expr)
    length(f.args)-1
end




#useful MacroTools
mutable struct  ObFunctor  #transform to the functior for a given function (方便但慢一些)
    name::String
    numvar::Int
    ObFunctor(name,numvar)=new(name,numvar)
end
function (odF::ObFunctor)(args...)
    if length(args)==odF.numvar
        getfield(Main, Symbol(odF.name))(args...)
    else
        print("wrong args")
    end
end


macro >(exs...)
  thread(x) = isexpr(x, :block) ? thread(rmlines(x).args...) : x

  @static if VERSION < v"0.7"

    thread(x, ex) =
    isexpr(ex, :call, :macrocall) ? Expr(ex.head, ex.args[1], x, ex.args[2:end]...) :
    @capture(ex, f_.(xs__))       ? :($f.($x, $(xs...))) :
    isexpr(ex, :block)            ? thread(x, rmlines(ex).args...) :
    Expr(:call, ex, x)

  else

    thread(x, ex) =
    isexpr(ex, :macrocall)        ? Expr(ex.head, ex.args[1], ex.args[2], x, ex.args[3:end]...) :
    isexpr(ex, :call,)            ? Expr(ex.head, ex.args[1], x, ex.args[2:end]...) :
    @capture(ex, f_.(xs__))       ? :($f.($x, $(xs...))) :
    isexpr(ex, :block)            ? thread(x, rmlines(ex).args...) :
    Expr(:call, ex, x)

  end

  thread(x, exs...) = reduce(thread, exs, init=x)

  esc(thread(exs...))
end

macro <(exs...)
  thread(x) = isexpr(x, :block) ? thread(rmlines(x).args...) : x

  thread(x, ex) =
    isexpr(ex, Symbol, :->)       ? Expr(:call, ex, x) :
    isexpr(ex, :call, :macrocall) ? Expr(ex.head, ex.args..., x) :
    @capture(ex, f_.(xs__))       ? :($f.($(xs...), $x)) :
    isexpr(ex, :block)            ? thread(x, rmlines(ex).args...) :
                                    error("Unsupported expression $ex in @>>")

  thread(x, exs...) = reduce(thread, exs; init=x)

  esc(thread(exs...))
end

macro ~(as, exs...)
  thread(x) = isexpr(x, :block) ? thread(rmlines(x).args...) : x

  thread(x, ex) =
    isexpr(ex, Symbol, :->) ? Expr(:call, ex, x) :
    isexpr(ex, :block)      ? thread(x, rmlines(ex).args...) :
    :(let $as = $x
        $ex
      end)

  thread(x, exs...) = reduce((x, ex) -> thread(x, ex), exs, init=x)

  esc(thread(exs...))
end
macro wvar(x...)
    vars=Expr(:block)
    for s in x
        push!(vars.args, Expr(:(=), esc(s), Expr(:call, MathLink.WSymbol, Expr(:quote, s))))
    end
    push!(vars.args, Expr(:tuple, map(esc, x)...))
    vars
end
macro wvars(x, j::Int64)
    vars=Expr(:block)
    for i = 1:j
        push!(vars.args, Expr(:(=), esc(Symbol("$x$i")), Expr(:quote,MathLink.WSymbol("$x$i"))))
    end
    push!(vars.args,  Expr(:tuple,map(esc, "$x".*map(string,1:j).|>MathLink.WSymbol)...))
    vars
end

macro wvars(x, j...)
    vars=Expr(:block)
    for i in Iterators.product((1:k for k in j)...)
        push!(vars.args, Expr(:(=), esc(Symbol("$x$(i...)")), Expr(:quote,MathLink.WSymbol("$x$(i...)"))))
    end
    push!(vars.args,  Expr(:tuple,map(esc, "$x".*map(string,["$(i...)" for i in Iterators.product((1:k for k in j)...) ]).|>MathLink.WSymbol)...))
    vars
end

macro jvar(x...)
    vars=Expr(:block)
    for s in x
        push!(vars.args, Expr(:(=), esc(s), Expr(:call, Symbol, Expr(:quote, s))))
    end
    push!(vars.args, Expr(:tuple, map(esc, x)...))
    vars
end

macro jvars(x, j::Int64)
    vars=Expr(:block)
    for i = 1:j
        push!(vars.args, Expr(:(=), esc(Symbol("$x$i")), Expr(:quote,Symbol("$x$i"))))
    end
    push!(vars.args,  Expr(:tuple,map(esc, "$x".*map(string,1:j).|>Symbol)...))
    vars
end

macro jvars(x, j...)
    vars=Expr(:block)
    for i in Iterators.product((1:k for k in j)...)
        push!(vars.args, Expr(:(=), esc(Symbol("$x$(i...)")), Expr(:quote,Symbol("$x$(i...)"))))
    end
    push!(vars.args,  Expr(:tuple,map(esc, "$x".*map(string,["$(i...)" for i in Iterators.product((1:k for k in j)...) ]).|>Symbol)...))
    vars
end
#Power(pi+0.0im,-0.3)
Power(0.4-0.0im,-0.2)
#@varj x1 x2
end
