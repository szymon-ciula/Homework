 (* ::Package:: *)

BeginPackage["Relations`"];
(* Prosty pakiet analizujący i wizualizący relacje.
   Autor: Marian Mrozek, (c) 2012 

   Updates: Michał Lipiński, (c) 2020
            Jakub Banaśkiewicz (c) 2020
*)

Relation::usage="Relation[set,pairs]";
RMatrix::usage="RMatrix[Relation[set,pairs]]";
RMatrixBase::usage="RMatrixBase[Relation[set,pairs]]";
IsReflexive::usage="IsReflexive[Relation[set,pairs]]";
ReflexiveClosure::usage="ReflexiveClosure[Relation[set,pairs]]";
IsSymmetric::usage="IsSymmetric[Relation[set,pairs]]";
IsTransitive::usage="IsTransitive[Relation[set,pairs]]";
TransClosure::usage="TransClosure[Relation[set,pairs]]";
ReflexiveReduction::usage="ReflexiveReduction[Relation[set,pairs]]";
TransReduction::usage="TransReduction[Relation[set,pairs]]";
IsAntisymmetric::usage="IsAntisymmetric[Relation[set,pairs]]";
(* IsTotal::usage="IsTotal[Relation[set,pairs]]"; *)
IsConnex::usage="IsConnex[Relation[set,pairs]";
IsInjective::usage="IsInjective[Relation[set,pairs]]";
IsSurjective::usage="IsSurjective[Relation[set,pairs]]";
IsBijective::usage="IsBijective[Relation[set,pairs]]";
IsPartialFunction::usage="IsPartialFunction[Relation[set,pairs]]";
HasFullDomain::usage="HasFullDomain[Relation[set,pairs]]";
IsFunction::usage="IsFunction[Relation[set,pairs]]";
IsEquivalence::usage="IsEquivalence[Relation[set,pairs]]";
IsIdentity::usage="IsIdentity[Relation[set,pairs]]";
IsPartialOrder::usage="IsPartialOrder[Relation[set,pairs]]";
IsLinearOrder::usage="IsLinearOrder[Relation[set,pairs]]";

RRestricted::usage="RRestricted[Relation[set,pairs],set]";
RCompose::usage="RCompose[Relation[set,pairs],Relation[set,pairs]]";
RInverse::usage="RInverse[Relation[set,pairs]]";
RDifference::usage="RDifference[Relation[set,pairs],Relation[set,pairs]]";

Base::usage="Base[Relation[set,pairs]]";
Source::usage="Source[Relation[set,pairs,set]]";
Target::usage="Target[Relation[set,pairs,set]]";
BCard::usage="BCard[Relation[set,pairs]]";
RCard::usage="RCard[Relation[set,pairs]]";

IsMinimal::usage="IsMinimal[Relation[set,pairs],x]";
IsMaximal::usage="IsMaximal[Relation[set,pairs],x]";
IsGreatest::usage="IsGreatest[Relation[set,pairs],x]";
IsLeast::usage="IsLeast[Relation[set,pairs],x]";

GetLeast::usage="IsGreatest[Relation[set,pairs]]";
GetMinimal::usage="GetMaximal[Relation[set,pairs]]";
GetGreatest::usage="IsGreatest[Relation[set,pairs]]";
GetMaximal::usage="GetMaximal[Relation[set,pairs]]";

IsUpperBound::usage="IsUpperBound[Relation[set,pairs],subset,x]";
IsLowerBound::usage="IsLowerBound[Relation[set,pairs],subset,x]";
GetUpperBounds::usage="GetUpperBounds[Relation[set,pairs],subset]";
GetLowerBounds::usage="GetLowerBounds[Relation[set,pairs],subset]";
GetSupremum::usage="GetSupremum[Relation[set,pairs],subset]";
GetInfimum::usage="GetLowerBounds[Relation[set,pairs],subset]";
RImage::usage="RImage[Relation[set,pairs],element]";
RSetImage::usage="RSetImage[Relation[set,pairs],element]";
IsIncreasing::usage="IsIncreasing[f,o1,o2]";
IsDecreasing::usage="IsDecreasing[f,o1,o2]";
NewFunction::usage="NewFunction[so,arg\[Rule]val,ta]";

RelMatrix::usage="RMatrix[Relation[set,pairs]]"
RGraph::usage="RGraph[Relation[set,pairs]]";
Reduced::usage="  Reduced->True/False ";

RChart::usage="RChart[Relation[set,pairs]]";

ExploreRelations::usage="ExploreRelations[setX, setY]"
ExploreCompositions::usage="ExploreRelations[setX, setY, setZ]"

Begin["`Private`"];
Needs["FSets`"]; 

SetAttributes[NewFunction,HoldAll]


GetIndex[s_,x_]:=Position[s,x][[1]][[1]];
Weight[x_]:=Sum[x[[i]],{i,Length[x]}]

Base[Relation[s_,p_]]:=ReplacePart[s,FSet,0];

Source[Relation[vi_,sop_,vo_]]:=ReplacePart[vi,FSet,0];
Target[Relation[vi_,sop_,vo_]]:=ReplacePart[vo,FSet,0];
Source[Relation[v_,sop_]]:=ReplacePart[v,FSet,0];
Target[Relation[v_,sop_]]:=ReplacePart[v,FSet,0];

BCard[r_]:=Length[r[[1]]] 
RCard[Relation[s_,p_]]:=Length[p] 

(*
Relation[FSet[e1__],FSet[e2__],List[p__]]:=Relation[FSet[e1],List[p],FSet[e2]]
Format[Relation[FSet[e1__],List[p__],FSet[e2__]]]:=
*)

Unprotect[Dot];
x_ \[CenterDot] Relation[s_,p_] \[CenterDot] y_ := MemberQ[p,x->y]
x_ \[CenterDot] Relation[vi_,sop_,vo_] \[CenterDot] y_ := MemberQ[sop,x->y]
Protect[Dot];

Unprotect[Power];
Relation[v_,sop_]^-1:= RInverse[Relation[v,sop,v]]
Relation[vi_,sop_,vo_]^-1:= RInverse[Relation[vi,sop,vo]]
Relation[s_,p_]^-1[x_]:=RImage[Relation[s,p]^-1,x]
Relation[vi_,sop_,vo_]^-1[x_]:=RImage[Relation[vi,sop,vo]^-1,x]
Protect[Power];


Relation[s1_,p1_] \[SmallCircle] Relation[s2_,p2_]:=
    RCompose[Relation[s1,p1],Relation[s2,p2]]

Relation[vi1_,sop1_,vo1_] \[SmallCircle] Relation[vi2_,sop2_,vo2_]:=
    RCompose[Relation[vi1,sop1,vo1],Relation[vi2,sop2,vo2]]

Relation[vi1_,sop1_,vo1_] \[SmallCircle] Relation[vi2_,sop2_]:=
    RCompose[Relation[vi1,sop1,vo1],Relation[vi2,sop2,vi2]]

Relation[vi1_,sop1_] \[SmallCircle] Relation[vi2_,sop2_,vo2_]:=
    RCompose[Relation[vi1,sop1,vi1],Relation[vi2,sop2,vo2]]

Unprotect[Times];
x_  Relation[s_,p_]  y_ := MemberQ[p,x->y]
Protect[Times];

Relation[s_,p_][x_]:=RImage[Relation[s,p],x]
Relation[vi_,sop_,vo_][x_]:=RImage[Relation[vi,sop,vo],x]
Relation[s_,p_]\[CenterDot]x_:=RSetImage[Relation[s,p],x]
Relation[vi_,sop_,vo_]\[CenterDot]x_:=RSetImage[Relation[vi,sop,vo],x]


Zero[i_,j_]:=0

GetVertices[sop_]:=Module[{v},
  v={};
  For[i=1,i<=Length[sop],++i,
    v=Append[v,sop[[i]][[1]]];
    v=Append[v,sop[[i]][[2]]];
  ];
  DeleteDuplicates[v]
]
GetLeftVertices[sop_]:=Module[{v},
  v={};
  For[i=1,i<=Length[sop],++i,
    v=Append[v,sop[[i]][[1]]];
  ];
  DeleteDuplicates[v]
]
GetRightVertices[sop_]:=Module[{v},
  v={};
  For[i=1,i<=Length[sop],++i,
    v=Append[v,sop[[i]][[2]]];
  ];
  DeleteDuplicates[v]
]


(* ::Text:: *)
(*Adjacency Matrix*)


AdjacencyM[r_]:=Print["Not a relation: ",r]
AdjacencyM[Relation[v_,sop_]]:=AdjacencyM[Relation[v,sop,v]]
AdjacencyM[Relation[vi_,sop_,vo_]]:=Module[{s,si,so,soploc,wi,wo,ri,v,m,i,j,k,t,li,lo},  
  si=ReplacePart[vi,List,0];
  so=ReplacePart[vo,List,0];
  si=DeleteDuplicates[si];
  so=DeleteDuplicates[so];
  soploc=DeleteDuplicates[ReplacePart[sop,List,0]];
  wi=GetLeftVertices[soploc]; 
  wo=GetRightVertices[soploc]; 
  If[Complement[wi,si]!={} || Complement[wo,so]!={},
    Print[Error: not all vertices listed!'];
    Return[False];
  ];
  li=Length[si];
  lo=Length[so];
  m=Table[Table[0,{lo}],{li}];
  For[i=1,i<=Length[soploc],++i,
    t=soploc[[i]];
    j=Position[si,t[[1]]][[1]][[1]];
    k=Position[so,t[[2]]][[1]][[1]];
    m[[j]][[k]]=1;
  ];
  (* m[[i]][[j]]!=0 means an edge from i to j *)
  Return[{si,m,so}];
]

RMatrix[r_]:=AdjacencyM[r][[2]]
RMatrixBase[r_]:=AdjacencyM[r][[1]]

RelationFromAdjacency[v_,m_]:=Module[{i,j,r,k},
  r={};
  k=Length[m];
  For[i=1,i<=k,++i,
    For[j=1,j<=k,++j,
      If[ m[[i]][[j]]!=0, r=Append[r,v[[i]]->v[[j]]] ];
    ];
  ];
  Relation[v,r]
]

RelationFromAdjacency[vi_,m_,vo_]:=Module[{i,j,r,ki,ko},
  r={};
  ki=Length[vi];
  ko=Length[vo];
  For[i=1,i<=ki,++i,
    For[j=1,j<=ko,++j,
      If[ m[[i]][[j]]!=0, r=Append[r,vi[[i]]->vo[[j]]] ];
    ];
  ];
  If[SameQ[vi,vo],
    Relation[vi,r],
    Relation[vi,r,vo]
  ]
]


(* ::Text:: *)
(*Composition and inversion*)


RRestricted[r_,s_]:=Module[{ri,m,n,v,w,i,j,d},
  If[!(Source[r]==Target[r]),Print["Error"];Return[Null];];
  v=r[[1]];
  w=Intersection[ReplacePart[s,List,0],ReplacePart[v,List,0]];
  ri=AdjacencyM[r];
  m=ri[[2]];
  d=Length[w];
  n=Table[Table[0,{d}],{d}];
  For[i=1,i<=d,++i,
    For[j=1,j<=d,++j,
      n[[i]][[j]]=m[[ GetIndex[v,w[[i]]] ]][[ GetIndex[v,w[[j]]] ]];
    ];
  ];
  RelationFromAdjacency[w,n]
]

RCompose[r1_,r2_]:=Module[{ri1,ri2,m1,m2,m,vi,vo,i},
  If[!(Source[r1]==Target[r2]),Print["Error: composition not possible"];Return[Null];];
  ri1=AdjacencyM[r1];
  ri2=AdjacencyM[r2];
  vo=ri1[[3]];
  vi=ri2[[1]];
  m1=ri1[[2]];
  m2=ri2[[2]];
  RelationFromAdjacency[vi,Sign[m2.m1],vo]
]

RInverse[Relation[vi_,sop_,vo_]]:=Module[{r,m,si,so},
  r=AdjacencyM[Relation[vi,sop,vo]];
  si=r[[1]];
  m=r[[2]];
  so=r[[3]];
  RelationFromAdjacency[so,Transpose[m],si]
]

RDifference[r1_,r2_]:=Module[{ri1,ri2,m1,m2,v,i,j},
  If[!(Base[r1]==Base[r2]),Print["Error"];Return[Null];];
  ri1=AdjacencyM[r1];
  ri2=AdjacencyM[r2];
  v=ri1[[1]];
  m1=ri1[[2]];
  m2=ri2[[2]];
  For[i=1,i<=Length[m1],++i,
    For[j=1,j<=Length[m1],++j,
      If[ m2[[i]][[j]]==1,m1[[i]][[j]]=0; ];
    ];
  ];
  RelationFromAdjacency[v,Sign[m1]]
]

RImage[r_,a_]:=Module[{result,target,i,func,t},
  result=FSet[];
  func=IsFunction[r];
  target=Target[r];
  For[i=1,i<=FCard[target],++i,
    t=target[[i]];
    If[a\[CenterDot]r\[CenterDot]t,
      If[func,
        Return[t],
        result=Append[result,t];
      ]
    ]
  ];
  Return[result]
]

RSetImage[r_,FSet[a___]]:=Module[{s,result,i,func,t},
  s=FSet[a];
  result=FSet[];
  func=IsFunction[r];
  For[i=1,i<=FCard[s],++i,
    t=s[[i]];
    If[func,
      result=result\[Union]FSet[RImage[r,t]],
      result=result\[Union]RImage[r,t];
    ]
  ];
  Return[result]
]



(* ::Text:: *)
(*General Properties*)


IsReflexive[r_]:=Module[{ri,m,v,i},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  Sum[m[[i]][[i]],{i,Length[m]}]==Length[m]
]

ReflexiveClosure[r_]:=Module[{ri,m,v,i},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  For[i=1,i<=Length[m],++i,m[[i]][[i]]=1];
  RelationFromAdjacency[v,m]
]

ReflexiveReduction[r_]:=Module[{ri,m,v,i},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  For[i=1,i<=Length[m],++i,m[[i]][[i]]=0];
  RelationFromAdjacency[v,m]
]


IsSymmetric[r_]:=Module[{ri,m},
  ri=AdjacencyM[r];
  (* v=ri[[1]];*)
  m=ri[[2]];
  m==Transpose[m]
]

IsTransitive[r_]:=Module[{ri,m,v,n},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  n=Sign[m.m+m];
  m==n
]

TransClosure[r_]:=Module[{ri,m,v,n},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  While[True,
    n=Sign[m.m+m];
    If[n==m,Break[]];
    m=n;
  ];
  RelationFromAdjacency[v,m]
]

TransReduction[r_]:=Module[{rc,r0,rt,ri,m,v,n},
  rc=TransClosure[r];
  r0=ReflexiveReduction[r];
  rc=ReflexiveReduction[rc];
  rc=RCompose[r0,rc];
  RDifference[r0,rc]
]

IsAntisymmetric[r_]:=Module[{ri,m,v,n,k},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  k=Length[m];
  n=Transpose[m];
  n*m*(1-IdentityMatrix[k])==Array[Zero,{k,k}]
]

IsConnex[r_]:=Module[{ri,m,v,n,k},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  k=Length[m];
  n=Sign[Transpose[m]+m];
  1-n==Array[Zero,{k,k}]
]


IsEquivalence[r_]:=IsReflexive[r] && IsSymmetric[r] && IsTransitive[r]
IsIdentity[r_]:=ForAll[x\[Element]Source[r],r\[CenterDot]FSet[x]==FSet[x]]


(* ::Text:: *)
(*Graphs and charts*)


(*Options[RGraph]={Reduced->False, Method->"SpringElectricalEmbedding"};*)
Options[RGraph]={Reduced->False, Method->"SpringElectricalEmbedding"};
RGraph[Relation[v_,sop_],opts___]:=Module[{r,ri,rr,m,s,n,k,redu,meth},
	redu=Reduced/.{opts}/.Options[RGraph];
	meth=Method/.{opts}/.Options[RGraph];
	r=Relation[v,sop];
	If[Equal[redu,True],
		rr=TransReduction[r],
		rr=r
	];
	ri=AdjacencyM[rr];
	s=ri[[1]];
	m=ri[[2]];
	GraphPlot[m,
		(* VertexLabeling->True, *)
		DirectedEdges->True,
		SelfLoopStyle->0.75,
		Method->meth,
		VertexSize->0.3,
		VertexStyle->Yellow,
		VertexLabels->Table[i->Text[v[[i]]], {i,Range[Length[v]]}]
		(* VertexShapeFunction->
			({Disk[#,0.05],
				Black,Text[s[[#2]],#1]}&)
		*)
		(* 
		VertexRenderingFunction->({
			Yellow,
			EdgeForm[Black],
			Disk[#,.1],
			Black,Text[s[[#2]],#1]}&)
		*)
	  ]
]

RGraph[Relation[vi_,sop_,vo_],opts___]:=Module[{vcri,vcro,vcr,k,i,soploc},
	k=1+Max[Length[vi],Length[vo]];
	vcr={};
	soploc=sop;
	For[i=1,i<=Length[vi],++i,
		soploc=Append[ soploc,vi[[i]]->vi[[i]] ];
		vcr=Append[ vcr,vi[[i]]->{1,i} ];
	];
	For[i=1,i<=Length[vo],++i,
		soploc=Append[ soploc,vo[[i]]->vo[[i]] ];
		vcr=Append[ vcr,vo[[i]]->{k,i} ];    
	];
	GraphPlot[soploc,
			VertexCoordinateRules->vcr,
			VertexLabeling->True,
			DirectedEdges->True,
			SelfLoopStyle->None
			(*VertexRenderingFunction->({
			  Yellow,
			  EdgeForm[Black],
			  Disk[#,.1]}&
			)*)
	]
]

Options[RChart]={Reduced->False};
RChart[r_,opts___]:=Module[{ri,rr,m,vi,vo,rn,i,j,ki,ko,redu},
  redu=Reduced/.{opts}/.Options[RChart];
  If[redu==True,
    rr=TransReduction[r],
    rr=r
  ];
  ri=AdjacencyM[rr];
  vi=ri[[1]];
  m=ri[[2]];
  vo=ri[[3]];
  rn={};
  ki=Length[vi];
  ko=Length[vo];
  For[i=1,i<=ki,++i,
    For[j=1,j<=ko,++j, 
      If[m[[i]][[j]]!=0,rn=Append[rn,{i,j}]];
    ];
  ];
  ListPlot[rn,PlotStyle->{PointSize[0.05],Red}, 
    AspectRatio->Automatic,PlotRange->{{0.0,ki+0.5},{0.0,ko+0.5}}
  ]
]

RelMatrix[relation_]:=Module[{elements=Map[{#[[1]],#[[2]]}&, relation[[2]]],set,ticks},
	set=Sort@DeleteDuplicates[Flatten[elements]];ticks=Transpose[{Range[Length[set]],Map[ToString[#]&,set]}];
ArrayPlot[Table[If[MemberQ[elements,{x,y}],1,0],{x,set},{y,set}],FrameTicks->{ticks,ticks},DataReversed->True]]


(* ::Text:: *)
(*Functions*)


NewFunction[so_,arg_->val_,ta_]:=Module[{i,x,y,pairs,result},
  pairs=FSet[];
  For[i=1,i<=FCard[so],++i,
    x=so[[i]];
    (*pairs=Append[pairs,x->(ReleaseHold[Hold[val]/. arg->x])]*)
    pairs=Append[pairs,x->(ReplaceAll[Unevaluated[val],Unevaluated[arg->x]])]
  ];
  If[so==ta,
    result=Relation[so,pairs],
    result=Relation[so,pairs,ta]
  ];
  result
]

IsInjective[r_]:=Module[{ri,m,v,n,i},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  n=Transpose[m];
  For[i=1,i<=Length[n],++i,
    If[Weight[n[[i]]]>1,Return[False];]
  ];
  Return[True]
]

IsSurjective[r_]:=Module[{ri,m,v,n,i},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  n=Transpose[m];
  For[i=1,i<=Length[n],++i,
    If[Weight[n[[i]]]==0,Return[False];]
  ];
  Return[True]
]

IsPartialFunction[r_]:=Module[{ri,m,v,n,i},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  For[i=1,i<=Length[m],++i,
    If[Weight[m[[i]]]>1,Return[False];]
  ];
  Return[True]
]

HasFullDomain[r_]:=Module[{ri,m,v,n,i},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  For[i=1,i<=Length[m],++i,
    If[Weight[m[[i]]]==0,Return[False];]
  ];
  Return[True]
]

IsFunction[r_]:=IsPartialFunction[r] && HasFullDomain[r]
IsBijective[r_]:=IsInjective[r] && IsSurjective[r] && IsFunction[r]

IsIncreasing[f_,o1_,o2_]:=ForAll[x\[Element]Subsets[Source[f],{2}],x[[1]]\[CenterDot]o1\[CenterDot]x[[2]]\[Implies]f[x[[1]]]\[CenterDot]o2\[CenterDot]f[x[[2]]]]
IsDecreasing[f_,o1_,o2_]:=ForAll[x\[Element]Subsets[Source[f],{2}],x[[1]]\[CenterDot]o1\[CenterDot]x[[2]]\[Implies]f[x[[2]]]\[CenterDot]o2\[CenterDot]f[x[[1]]]]


(* ::Text:: *)
(*Orders*)


IsPartialOrder[r_]:=IsReflexive[r] && IsAntisymmetric[r] && IsTransitive[r]
IsLinearOrder[r_]:=IsPartialOrder[r] && IsConnex[r]

IsUpperBound[r_,s_,x_]:=Module[{i},
  For[i=1,i<=FCard[s],++i,
    If[!(s[[i]]\[CenterDot]r\[CenterDot]x),Return[False]];
  ];
  Return[True]
]

IsLowerBound[r_,s_,x_]:=Module[{i},
  For[i=1,i<=FCard[s],++i,
    If[!(x\[CenterDot]r\[CenterDot]s[[i]]),Return[False]];
  ];
  Return[True]
]

GetUpperBounds[r_,s_]:=Module[{t,u},
  t={};
  u=Base[r];
  For[i=1,i<=FCard[u],++i,
    If[IsUpperBound[r,s,u[[i]]],t=Append[t,u[[i]]]];
  ];
  FSet[t]
]

GetLowerBounds[r_,s_]:=Module[{t,u},
  t={};
  u=Base[r];
  For[i=1,i<=FCard[u],++i,
    If[IsLowerBound[r,s,u[[i]]],t=Append[t,u[[i]]]];
  ];
  FSet[t]
]

GetSupremum[r_,s_]:=GetLeast[r,GetUpperBounds[r,s]]
GetInfimum[r_,s_]:=GetGreatest[r,GetLowerBounds[r,s]]

IsMaximal[r_,x_]:=Module[{ri,m,v,i},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  i=GetIndex[v,x];
  1==Weight[m[[i]]]
]

IsMinimal[r_,x_]:=Module[{ri,m,v,i},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  i=GetIndex[v,x];
  1==Weight[Transpose[m][[i]]]
]

IsGreatest[r_,x_]:=Module[{ri,m,v,i},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  i=GetIndex[v,x];
  Length[m]==Weight[Transpose[m][[i]]]
]

IsLeast[r_,x_]:=Module[{ri,m,v,i},
  ri=AdjacencyM[r];
  v=ri[[1]];
  m=ri[[2]];
  i=GetIndex[v,x];
  Length[m]==Weight[m[[i]]]
]

GetGreatest[r_]:=Module[{i,v,g},
  g={};
  v=r[[1]];
  For[i=1,i<=Length[v],++i,
    If[ IsGreatest[r,v[[i]]],g=Append[g,v[[i]]];Break[] ];
  ];
  FSet[g]
]

GetMaximal[r_]:=Module[{i,v,g},
  g={};
  v=r[[1]];
  For[i=1,i<=Length[v],++i,
    If[ IsMaximal[r,v[[i]]],g=Append[g,v[[i]]] ];
  ];
  FSet[g]
]

GetLeast[r_]:=Module[{i,v,g},
  g={};
  v=r[[1]];
  For[i=1,i<=Length[v],++i,
    If[ IsLeast[r,v[[i]]],g=Append[g,v[[i]]];Break[] ];
  ];
  FSet[g]
]

GetMinimal[r_]:=Module[{i,v,g},
  g={};
  v=r[[1]];
  For[i=1,i<=Length[v],++i,
    If[ IsMinimal[r,v[[i]]],g=Append[g,v[[i]]] ];
  ];
  FSet[g]
]

GetLeast[r_,s_]:=GetLeast[RRestricted[r,s]]
GetMinimal[r_,s_]:=GetMinimal[RRestricted[r,s]]
GetGreatest[r_,s_]:=GetGreatest[RRestricted[r,s]]
GetMaximal[r_,s_]:=GetMaximal[RRestricted[r,s]]


ExploreRelations[X_] := DynamicModule[{Rel = {}},
	Column[{
		TogglerBar[Dynamic[Rel], 
			 Flatten[Table[{X[[i]], X[[j]]}, {i, 1, Length[X]}, {j, 1, Length[X]}], 1], 
			Appearance -> "Vertical" -> {Length[X], Automatic}
		],
		Dynamic[StringTemplate["Elementy relacji: ``"][Rel]],
		Dynamic[StringTemplate["Liczba elementów relacji: ``"][Length@Rel]],
		Dynamic[StringTemplate["Zwrotna: ``"][IsReflexive[Relation[X, Rel]]]],
		Dynamic[StringTemplate["Symetryczna: ``"][IsSymmetric[Relation[X, Rel]]]],
		Dynamic[StringTemplate["Antysymetryczna: ``"][IsAntisymmetric[Relation[X, Rel]]]],
		Dynamic[StringTemplate["Przechodnia: ``"][IsTransitive[Relation[X, Rel]]]],
		Dynamic[StringTemplate["Spójna: ``"][IsConnex[Relation[X, Rel]]]],
		Dynamic[StringTemplate["Równoważności: ``"][IsEquivalence[Relation[X, Rel]]]],
		Dynamic[RGraph[Relation[X, Rel]]]
	}]
]

ExploreRelations[X_, Y_] :=
	DynamicModule[{RelXY = {}}, Column[{
		TogglerBar[Dynamic[RelXY], 
			Flatten[Table[{X[[i]], Y[[j]]}, {i, 1, Length[X]}, {j, 1, Length[Y]}], 1], 
			Appearance -> "Vertical" -> {Length[Y], Automatic}
		],
		Dynamic[StringTemplate["Elementy relacji: ``"][RelXY]],
		Dynamic[StringTemplate["Liczba elementów relacji: ``"][Length@RelXY]],
		Dynamic[RGraph[Relation[FSet[X], Map[#[[1]] -> #[[2]] &, RelXY], FSet[Y]]]]
	}]
]

ExploreCompositions[X_, Y_, Z_] :=
	DynamicModule[{RelXY = {}, RelYZ = {}, RelXZ = {}}, Column[{
		Row[{
			TogglerBar[Dynamic[RelXY], 
				Flatten[Table[{X[[i]], Y[[j]]}, {i, 1, Length[X]}, {j, 1, Length[Y]}], 1],
				Appearance -> "Vertical" -> {Length[Y], Automatic}
			], 
			"    ",
			TogglerBar[Dynamic[RelYZ], 
				Flatten[Table[{Y[[i]], Z[[j]]}, {i, 1, Length[Y]}, {j, 1, Length[Z]}], 1], 
				Appearance -> "Vertical" -> {Length[Z], Automatic}
			]
		}],
		Dynamic[StringTemplate[
			"Elementy relacji \!\(\*SubscriptBox[\(R\), \(1\)]\)\ \[SubsetEqual]X\[Times]Y: ``"][RelXY]],
		Dynamic[StringTemplate[
			"Elementy relacji \!\(\*SubscriptBox[\(R\), \(2\)]\)\ \[SubsetEqual]Y\[Times]Z: ``"][RelYZ]],
		Dynamic[StringTemplate[
			"Liczba elementów relacji \!\(\*SubscriptBox[\(R\), \(1\)]\): ``"][Length@RelXY]],
		Dynamic[StringTemplate[
			"Liczba elementów relacji \!\(\*SubscriptBox[\(R\), \(2\)]\): ``"][Length@RelYZ]],
		"Relacje 
			\!\(\* StyleBox[SubscriptBox[\"R\", \"1\"],\nFontWeight->\"Plain\"]\) 
			oraz \
			\!\(\* StyleBox[SubscriptBox[\"R\", \"2\"],\nFontWeight->\"Plain\"]\):",
		Row[{
			Dynamic[RGraph[Relation[FSet[X], Map[#[[1]] -> #[[2]] &, RelXY], FSet[Y] ]]],
			Dynamic[RGraph[Relation[FSet[Y], Map[#[[1]] -> #[[2]] &, RelYZ], FSet[Z] ]]]
		}],
		Dynamic[StringTemplate[
			"Elementy relacji \!\(\*SubscriptBox[\(R\), \ \(3\)]\)=\!\(\*SubscriptBox[\(R\), \ 
			\(2\)]\)\[SmallCircle]\!\(\*SubscriptBox[\(R\), \ \(1\)]\)\[SubsetEqual]X\[Times]Z: ``"]
			[(Relation[Y, RelYZ, Z]\[SmallCircle]Relation[X, RelXY, Y])[[2]]]],
		Dynamic[StringTemplate[
			"Liczba elementów relacji \!\(\*SubscriptBox[\(R\), \(3\)]\): ``"]
			[Length@(Relation[Y, RelYZ, Z]\[SmallCircle]Relation[X, RelXY, Y])[[2]]]],
		"Relacje 
			\!\(\*
			StyleBox[SubscriptBox[\"R\", \"1\"],\nFontWeight->\"Plain\"]\) oraz \
			\!\(\*
			StyleBox[SubscriptBox[\"R\", \"2\"],\nFontWeight->\"Plain\"]\):",
		Dynamic[RGraph[Relation[Y, RelYZ, Z]\[SmallCircle]Relation[X, RelXY, Y]]]
	}]
]

End[];
EndPackage[];
