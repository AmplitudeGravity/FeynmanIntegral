using LightGraphs
using MetaGraphs
using IterTools
using GraphPlot: gplot
sg=SimpleGraph(4)
add_edge!(sg,1,2)
add_edge!(sg,2,3)
add_edge!(sg,1,4)
add_edge!(sg,2,4)
add_edge!(sg,3,4)
gplot(sg,nodelabel=vertices(sg))
eds=edges(sg)
eds|>dump
function Subsets(a::Array,n::Int)
    res=Any[]
    for i in subsets(a, n)
          push!(res,i)
       end
     res
end
function Subsets(a::Base.OneTo{Int64},n::Int)
    res=Any[]
    for i in subsets(a, n)
          push!(res,i)
       end
     res
end

function adjacent(edge1::LightGraphs.SimpleGraphs.SimpleEdge{Int64},edge2::LightGraphs.SimpleGraphs.SimpleEdge{Int64})
   ([src(edge1),dst(edge1),src(edge2),dst(edge2)]|> union|>length)<4 ? true : false
end

function dualgraph(sg::SimpleGraph{Int64})
    alleds=collect(edges(sg))
    dualSg=SimpleGraph(sg.ne)
    sbs=Subsets(vertices(dualSg),2)
    for i=1:length(sbs)
        adjacent(alleds[sbs[i][1]],alleds[sbs[i][2]]) ? add_edge!(dualSg,sbs[i]...) : nothing
    end
    return dualSg
end


function Ufunc(sg::SimpleGraph{Int64})
    U=Any[]
    alleds=collect(edges(sg)) #generating all the edges
    for i in Subsets(alleds,2) #iterate over all 3-subsets the edges
       sgt=copy(sg)
       i1=findfirst(isequal(i[1]),alleds)
       i2=findfirst(isequal(i[2]),alleds)
       rem_edge!(sgt,i[1])
       rem_edge!(sgt,i[2])
       cpNo=connected_components(sgt)|>length
       cpNo==1 ? push!(U,Expr(:call, *, Symbol("α$i1"), Symbol("α$i2"))) : nothing
    end
    return U
end
function Ffunc(sg::SimpleGraph{Int64})
    F=Any[]
    alleds=collect(edges(sg)) #generating all the edges
    for i in Subsets(alleds,3) #iterate over all 3-subsets the edges
       sgt=copy(sg)
       i1=findfirst(isequal(i[1]),alleds)
       i2=findfirst(isequal(i[2]),alleds)
       i3=findfirst(isequal(i[3]),alleds)
       rem_edge!(sgt,i[1])
       rem_edge!(sgt,i[2])
       rem_edge!(sgt,i[3])
       comp=connected_components(sgt)
       cpNo=comp|>length
       cpNo==2 ? push!(F,[Expr(:call, *, Symbol("α$i1"), Symbol("α$i2"), Symbol("α$i3")),Expr(:call,:dot,comp[1],comp[2])]) : nothing
    end
    return F
end

Ufunc(sg)

Ffunc(sg)
