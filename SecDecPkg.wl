(* ::Package:: *)

BeginPackage["SubP`"]
Begin["Global`"]


nice={\[Alpha][i_]:> Subscript[\[Alpha], i],Wedge[f___]:> 1,tt-> x,DD-> D}


UF[xx_,yy_,z_]:=Module[{degree,coeff,i,t2,t1,t0,zz},zz=Map[Rationalize[##,0]&,z,{0,Infinity}];degree=-Sum[yy[[i]]*\[Alpha][i],{i,1,Length[yy]}];coeff=1;For[i=1,i<=Length[xx],i++,t2=Coefficient[degree,xx[[i]],2];t1=Coefficient[degree,xx[[i]],1];t0=Coefficient[degree,xx[[i]],0];coeff=coeff*t2;degree=Together[t0-((t1^2)/(4 t2))];];degree=Together[-coeff*degree]//.zz;coeff=Together[coeff]//.zz;{coeff,Expand[degree],Length[xx]}]


AlphaIntgrand[a_List,U_,F_,NL_,Dim_]:=(+1)^Sum[a[[ii]],{ii,Length@a}](*(I Pi^(Dim/2))^NL*)Gamma[Sum[a[[ii]],{ii,Length@a}]-(NL) Dim/2]/Product[Gamma[a[[i]]],{i,Length@a}] DiracDelta[1-Sum[\[Alpha][i],{i,Length@a}]] Product[\[Alpha][i]^(a[[i]]-1),{i,Length@a}] U^(Sum[a[[ii]],{ii,Length@a}]-(NL+1) Dim/2)/F^(Sum[a[[ii]],{ii,Length@a}]-(NL) Dim/2)


DecList[f_]:=Module[{res,vars=f//Cases[#,\[Alpha][i_],\[Infinity]]&//Union},
If[(f/.(vars/.\[Alpha][ii_]:> Rule[\[Alpha][ii],0]))===0,
res=MapThread[List,{Drop[(Subsets[vars]),1]/.\[Alpha][ii_]:> Rule[\[Alpha][ii],0],ReplaceAll[f,Drop[(Subsets[vars]),1]/.\[Alpha][ii_]:> Rule[\[Alpha][ii],0]]}]//Cases[#,{_,0}]&,Return[{}]];
res[[1,1]]//Cases[#,\[Alpha][i_],\[Infinity]]&
]


intSec0[f_,i_]:=(f/.{\[Alpha][ii_]:> \[Alpha][ii]\[Alpha][i]/;ii!=i}/.Wedge[gg___]:>  \[Alpha][i]^(-1+Length@Wedge[gg]) Drop[Wedge[gg],{i}]/.DiracDelta[gg_]-> \[Alpha][i]/.Power[gg_,ftt_-(3 DD)/2]:> Power[Collect[gg,\[Alpha][i]],ftt-(3 DD)/2]/.Power[gg_,ftt_+DD]:> Power[Collect[gg,\[Alpha][i]],ftt+DD]//PowerExpand)/.Power[\[Alpha][i],ftt__]:> Power[\[Alpha][i],ftt//Simplify]


intSec[f_,i_]:=f/.{\[Alpha][ii_]:> \[Alpha][ii]\[Alpha][i]/;ii!=i}/.Wedge[gg___]:>  \[Alpha][i]^(-1+Length@Wedge[gg]) Wedge[gg]//Simplify//PowerExpand//Simplify


intSec[f_,i_,shiftvars_List]:=(f/.MapThread[RuleDelayed,{\[Alpha]/@shiftvars,(\[Alpha]/@shiftvars)*\[Alpha][i] }]/.Wedge[gg___]:>  \[Alpha][i]^Length@shiftvars Wedge[gg]/.Power[gg_,ftt_-(3 DD)/2]:>Power[ \[Alpha][i],LeadingPower[gg,\[Alpha][i]](ftt-(3 DD)/2 )]Power[Collect[gg/Power[ \[Alpha][i],LeadingPower[gg,\[Alpha][i]]],\[Alpha][i]],ftt-(3 DD)/2]/.Power[gg_,ftt_+DD]:> Power[ \[Alpha][i],LeadingPower[gg,\[Alpha][i]](ftt+DD )]Power[Collect[gg/Power[ \[Alpha][i],LeadingPower[gg,\[Alpha][i]]],\[Alpha][i]],ftt+DD]//PowerExpand)/.Power[\[Alpha][i],ftt__]:> Power[\[Alpha][i],ftt//Simplify]


LeadingPower[f_,var_]:=mainTerm[f/.DD-> 0/.var->1/var,var]
mainTerm[expr_,x_]:=Module[{approxpoly,prec=1,j=0,expon,coef},approxpoly=Normal[Series[expr,{x,Infinity,prec}]];While[approxpoly===0&&j<=5,j++;prec=2*prec+j;approxpoly=Normal[Series[expr,{x,Infinity,prec}]];];approxpoly=PowerExpand@approxpoly;expon=-Exponent[approxpoly,x](*;coef=Coefficient[approxpoly,x,expon];coef*x^expon*)]


deg[f_,homovar_]:=Max[Plus@@@CoefficientRules[#,homovar][[All,1]]]&@(f)
LDterms[f_]:=Module[{vars,listf},listf=List@@f;vars=listf//Cases[#,\[Alpha][_],\[Infinity]]&//Union;listf//((Cases[#,gg_/;deg[gg,vars]==1]&))]
LDterms[f_,degree_]:=Module[{vars,listf},listf=List@@f;vars=listf//Cases[#,\[Alpha][_],\[Infinity]]&//Union;listf//((Cases[#,gg_/;deg[gg,vars]==degree]&))]


secDec[intf_,nd_]:=Module[{g,varsid,notscalers,scalers,intLD5re},
g=((List@@(intf))//Cases[Power[f_,nd-(3 DD)/2]])[[1]]/.Power[f_,nd-(3 DD)/2]:> f//Expand;
varsid=LDterms[g]/.\[Alpha][i_]:> i;
notscalers=varsid//Subsets[#,{Length[varsid]-1}]&;
scalers=Complement[varsid,#]&/@notscalers//Flatten;
Print[scalers];
intLD5re=Table[intSec[intf,scalers[[ii]],notscalers[[ii]]],{ii,Length@varsid}]]


DecomposeF[ff_]:=Module[{fflist,rescalingvar,intDecomposed},fflist=List@@ff;
fflist=fflist//Cases[Power[f_Plus,n_]/;((f/.\[Alpha][i_]:> 0)==0)]//Union;
If[fflist=={},Return[ff]];
rescalingvar=(fflist//First)/.Power[f_,n_]:> f//DecList;
(*Print[rescalingvar];*)
rescalingvar=rescalingvar/.\[Alpha][i_]:> i;
If[rescalingvar=={},Return[ff],intDecomposed=Table[intSec[ff,rescalingvar[[ii]],Delete[rescalingvar,{ii}]],{ii,Length@rescalingvar}]];
Return[intDecomposed] ]
DecomposeF[ff_List]:=Map[DecomposeF,ff]//Flatten


MyNIntegrate[fun_]:=Module[{vars},vars=(fun//Cases[#,\[Alpha][_],\[Infinity]]&//Union)/.\[Alpha][i_]:> {\[Alpha][i],0,1};NIntegrate@@Join[{fun},vars]]
MyNIntegrate[fun_,sed_]:=Module[{vars},vars=(fun//Cases[#,\[Alpha][_],\[Infinity]]&//Union)/.\[Alpha][i_]:> {\[Alpha][i],0+sed,1};NIntegrate@@Join[{fun},vars]]


MySeries[fun_,tt_,zero_,power_]:=Series[fun[tt],{tt,zero,power}]//Normal
MySeries[fun_,{tt_,power_}]:=Series[fun,{tt,0,power}]//Normal
MySeries[fun_,mono_List,tt_,power_List]:=Module[{remaTerms},remaTerms=fun-Sum[mono[[ii]]Coefficient[fun,mono[[ii]]],{ii,Length@mono}]//Simplify;
(*Print[remaTerms];*)(Series[remaTerms,{tt,0,power[[-1]]}]//Normal)+Sum[mono[[ii]]Series[Coefficient[fun,mono[[ii]]],{tt,0,power[[ii]]}]//Normal,{ii,Length@mono}]]


MonoAlpha[ff_]:=(((List@@ff)//Cases[Power[f_,n_]])/.Power[f_Plus,n_]:> 0)//Cases[#,Power[\[Alpha][i_],n_]]&


EDSingularResolve[intreg0_,prodMono0_,DD0_]:=Module[{sinMono,alphadegrees,ResolvedTerm,intreg,Reso,divdegrees,prodMono},
sinMono=prodMono0//Cases[#,Power[\[Alpha][ri_],n_],\[Infinity]]&;
(*Print[sinMono];*)
alphadegrees=(List@@sinMono)/.Power[\[Alpha][i_],j_]:> {\[Alpha][i],-j};
divdegrees=(alphadegrees/.DD-> DD0//Cases[{_,j_}/;j>0])/.{\[Alpha][i_],num_}:> {\[Alpha][i],IntegerPart[num]};
If[divdegrees=={},Print["This integral over", \[Alpha],"is regular."];Return[{prodMono0*intreg0}]];
(*Print[alphadegrees,divdegrees];*)
intreg=intreg0;
Do[
intreg=(MySeries[intreg,divdegrees[[ii]]]),{ii,Length@divdegrees}
];
ResolvedTerm=prodMono0(intreg0-intreg);
(*Print[intreg];*)
prodMono=prodMono0;
Do[
intreg=Integrate[prodMono intreg,divdegrees[[ii,1]]];
(*Print[intreg];*)
intreg=intreg/.{divdegrees[[ii,1]]-> 1}/.Wedge[f___]:>DeleteCases[ Wedge[f],d\[Alpha][divdegrees[[ii,1,1]]]];
prodMono=prodMono/.{divdegrees[[ii,1]]-> 1},{ii,Length@divdegrees}
];
Return[{ResolvedTerm,intreg}]
]
EDSingularResolve[ff_,DD_]:=Module[{monos,reslist,res,mono},If[MonoAlpha[ff]=={},Return[ff]];monos=MonoAlpha[ff];
reslist={ff};
For[ii=1,ii<= Length@monos,ii++,
  mono=monos[[ii]];Print[mono];
For[jj=1,jj<= Length@reslist,jj++,
ft=reslist[[jj]];res[jj]=EDSingularResolve[ft/mono//Expand,{mono},DD]//PowerExpand//Flatten//Collect[#,Wedge[f___]]&];
reslist=Table[res[jj],{jj,1,Length@reslist}]//Flatten;
];
reslist
]
EDSingularResolve[ff_List,DD_]:=Map[EDSingularResolve[#,DD]&,ff]//Flatten


scalingtt[ff_]:=Module[{fflist,h0,rescalingvar,rescalingvarRule,effvar},fflist=List@@ff;
fflist=fflist//Cases[Power[f_Plus,n_]/;((Cases[f,tt,\[Infinity]]//Union)=={tt})];
If[fflist=={},Return[{}]];
h0=(fflist//First)/.Power[f_,n_]:> f/.tt-> 0;
rescalingvar=h0//Cases[ #,\[Alpha][_],\[Infinity]]&//Union;
rescalingvarRule=rescalingvar/.\[Alpha][i_]:> Rule[\[Alpha][i],0];
effvar=(MapThread[T,{rescalingvar,ReplaceAll[h0,#]&/@rescalingvarRule}]//Cases[T[\[Alpha][_],0]])/.T[f_,0]:> f
]


ScalingF[ff_, varsc_]:=Module[{ffsc0to1,ffsc1toinf,ffsctttoinf},
(*Print[varsc];*)
ffsc0to1=
(ff/.varsc-> tt varsc/.Wedge[g___]:> tt Wedge[g] /.Power[f_Plus,n_]:> Power[f//Collect[#,tt]&,n]/.Power[tt,n_]:> 0/;IntegerQ[n]//PowerExpand)/.Power[f_Plus,n_]:> Power[f/.tt-> 0,n];
ffsc1toinf=-(ffsc0to1/.varsc-> 1/varsc/.Wedge[g___]:> -1/varsc^2 Wedge[g] /.Power[f_Plus,n_]:> Power[f//Together[#]&,n]//PowerExpand);
ffsctttoinf=(ffsc0to1/.varsc-> 1/varsc/.Wedge[g___]:> -1/varsc^2 Wedge[g] /.Power[f_Plus,n_]:> Power[f//Together[#]&,n]//PowerExpand)/.varsc-> tt varsc/.Wedge[g___]:> tt Wedge[g] //PowerExpand;
{ffsc0to1,ffsc1toinf,ffsctttoinf}]
ScalingAllF[ff_]:=If[scalingtt[ff]=={},Return[ff],ScalingF[ff,scalingtt[ff][[1]]]]
(*ScalingAllF[ff_]:=If[scalingtt[ff]\[Equal]{},Return[ff],Table[ScalingF[ff,scalingtt[ff][[ii]]],{ii,Length@scalingtt[ff]}]//Flatten]*)
ScalingAllF[ff_List]:=Map[ScalingAllF,ff]//Flatten
ScalingF[ff_List,varsc_]:=Map[ScalingF[#,varsc]&,ff]//Flatten


PickLD[ff_,id_List]:=Module[{alpharep,ufun,ffun,gfun,hfun,fac,tli,upower,fpower},
alpharep=MapThread[Rule,{\[Alpha]/@id,ConstantArray[0,Length@id]}];
fac=Times@@Complement[(List@@ff),ff//Cases[Power[f_Plus,n_]]];
tli=(ff//Cases[Power[f_Plus,n_-(3 DD)/2]])[[1]]/.Power[f_,n_]:> {f/.alpharep,n};
ufun=tli[[1]];
upower=tli[[2]];
tli=(ff//Cases[Power[f_Plus,n_+ DD]])[[1]]/.Power[f_,n_]:> {f,n};
ffun=tli[[1]];fpower=tli[[2]];
gfun=(ffun-(ffun/.tt-> 0)//Expand)/.alpharep;
hfun=(ffun/.tt-> 0)//Expand;
fac*Power[ufun,upower]*Power[(gfun+hfun),fpower]
]


SeparateWedge[ff_]:=(T@ff)/.T[f_]:> List[f/.Wedge[g___]:> 1,Cases[f,Wedge[g___],\[Infinity]]//Union//First]


(*repJulia={s23-> 1,Gamma->gamma,\[Alpha][i_]:>ToExpression[StringJoin[{{ToString[x]},ToString[i]}]],Pi->pi,d\[Alpha]\[Rule]\[Alpha] };*)
repJulia={s23-> 1,Gamma->gamma,\[Alpha][i_]:>ToExpression[StringJoin[{{ToString[x]},ToString[i]}]],Pi->pi,Times[f___,Wedge[i___],gg___]:> List[(Times@f)(Times@gg),wedge[i]/.d\[Alpha]-> \[Alpha]]};


End[]
EndPackage[]
