module UseSymEngine
using SymEngine, SpecialFunctions
using MathLink
export math2symEngine, seval, sneval, evalSym
export @varss
function math2symEngine(symb::MathLink.WSymbol)
    SymEngine.symbols(symb.name)
end

function math2symEngine(num::Number)
    Basic(num)
end

binanyOPSymEngine=Dict("Times" => *,"Plus"=> +,"Power"=>^,"Rational"=>//)
function math2symEngine(expr::MathLink.WExpr)
    haskey(binanyOPSymEngine,expr.head.name) ? op=binanyOPSymEngine[expr.head.name] : op=SymFunction(expr.head.name)
    if expr.head.name=="List"
        return List(map(math2symEngine,expr.args)...)
    else
        #return Expr(:call, Symbol(expr.head.name), map(math2symEngine,expr.args)...)|>eval
        return op(map(math2symEngine,expr.args)...)
    end
end

# (gamma(symbols("D")))|>SymEngine.get_symengine_class
biOpSymEn=Dict(:Mul => *,:Add=> +,:Pow=>^)
function seval(ex::SymEngine.Basic)  #evaluate symengine functions
    fn = SymEngine.get_symengine_class(ex)
    if ((fn == :FunctionSymbol))
        isdefined(UseSymEngine,Symbol(get_name(ex))) ? op=getfield(UseSymEngine, Symbol(get_name(ex))) : op=SymFunction(get_name(ex))
        as=get_args(ex)
        return op([seval(a) for a in as]...)
    elseif haskey(biOpSymEn,fn)
        op=biOpSymEn[fn]
        as=get_args(ex)
        return op([seval(a) for a in as]...)
    else
        ex
    end
end

#biOpSymEn[:Pow](symbols("x"),Basic(-1))
#Basic(1)/symbols("x")*Basic(1)/symbols("x")|>seval|>seval
#SymFunction("gamma")(symbols("x")+Basic(1))*Basic(1)/symbols("x")|>seval
#SymFunction("Subscript")(symbols("x"),Basic(2))|>SymEngine.get_symengine_class
#Basic(1)/Basic(2)|>seval
#Basic(1)+symbols("x")|>get_args
#biOpSymEn=Dict(:Mul => *,:Add=> +,:Pow=>^)
#= function sneval(ex::SymEngine.Basic) #For numerical evaluation of SymEngine expression
    fn = SymEngine.get_symengine_class(ex)
    if fn == :FunctionSymbol || haskey(biOpSymEn,fn)
        haskey(biOpSymEn,fn) ? op=Symbol(biOpSymEn[fn]) : op=Symbol(get_name(ex))
        as=get_args(ex)
        return Expr(:call, op, [evalSym(a) for a in as]...)|>eval
    elseif (fn in SymEngine.number_types) || (fn == :Constant)
        return N(ex)|>eval
    end
end
=#
function evalSym(ex::SymEngine.Basic) #from SymEngine to Expr
    fn = SymEngine.get_symengine_class(ex)
    if fn == :Symbol
        return Symbol(SymEngine.toString(ex))
    elseif (fn in SymEngine.number_types) || (fn == :Constant)
        return N(ex)
    else
        if haskey(biOpSymEn,fn) # for math binary operators
            op=Symbol(biOpSymEn[fn])
        elseif fn==:FunctionSymbol #for my functions or undefined functions
            op=Symbol(get_name(ex))
        else    #for symegine functions
            op=Symbol(lowercase(string(fn)))
        end
        as=get_args(ex)
        return Expr(:call, op, [evalSym(a) for a in as]...)
    end
end

#N(Basic(pi))
#symbols("x")|>evalSym
#symbols("x")
#seval(symbols("x"))
#(symbols("x")+Basic(1))|>evalSym|>typeof
#Basic(pi)|>SymEngine.get_symengine_class
#SymEngine functions
function Subscript(f1::Basic,n1::Basic)
   symbols("$f1"*"_"*"$n1")
end
#symbols("x")+Basic(1)|>get_args
#SymFunction("Subscript")(1,2)|>get_name

#Subscript(Basic(1),Basic(2))
#julia Symbol functions
#define the symbol variables

macro varss(x,n::Int64)
    q=Expr(:block)
    for i = 1:n
        push!(q.args, Expr(:(=), esc(Symbol("$x$i")), Expr(:call, :(SymEngine._symbol), Expr(:quote, Symbol("$x$i")))))
    end
    push!(q.args, Expr(:tuple, map(esc, "$x".*map(string,1:n).|>Symbol)...))
    q
end

end
