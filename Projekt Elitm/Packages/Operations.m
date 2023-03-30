(* ::Package:: *)

BeginPackage["Operations`"];
(* Prosty pakiet analizuj\:0105cy dzia\[LSlash]ania.
   Autor: Marian Mrozek, (c) 2012 
*)
OpFSet::usage="OpFSet[set,operationMatrix]";
IsAssociative::usage="IsAssociative[operation]";
HasNeutral::usage="HasNeutral[operation]";
GetNeutral::usage="GetNeutral[operation]";
HasInverses::usage="HasInverses[operation]";
GetInverse::usage="GetInverse[operation,element]";
IsAbelian::usage="IsAbelian[operation]";
IsGroup::usage="IsGroup[operation]";
GetIndexMatrix::usage="GetIndexMatrix[operation]";
OpFSetTable::usage="OpFSetTable[operation]";
OProd::usage="OProd[operation,x,y]";
Eval::usage="Eval[operation,exp]";
Order::usage="Order[operation]";
OpBase::usage="OpBase[operation]";
NewOpFSet::usage="NewOpFSet[operation]";
NewGroup::usage="NewGroup[operation]";

QSqrt::usage="QSqrt[a,b,p]";
NewQSqrt::usage="NewQSqrt[a,b,p]";
NewZp::usage="NewZp[a,p]";

PlotComplex::usage="PlotComplex[z1,z2,...,zn]";


Begin["`Private`"];

GetIndex[s_,x_]:=Position[s,x][[1]][[1]];

(* OpFSet[s_,o_][x_]:=If[MemberQ[s,x],x,Null]*)

OProd[OpFSet[s_,m_],x_,y_]:=Module[{},
  If[ !MemberQ[s,x] || !MemberQ[s,y], Return[Null]; ];
  m[[GetIndex[s,x]]][[GetIndex[s,y]]]
]

Unprotect[Order];
Order[OpFSet[s_,m_]]:=Length[s]
OpBase[OpFSet[s_,m_]]:=s
Protect[Order];

Unprotect[Power];
x_\[CircleDot]y_\[CircleDot]z__:=(x\[CircleDot]y)\[CircleDot]z
(x_\[CircleDot]y_)^-1:=(x^-1)\[CircleDot](y^-1)
x_\[CenterDot]y_\[CenterDot]z__:=(x\[CenterDot]y)\[CenterDot]z
(x_\[CenterDot]y_)^-1:=(x^-1)\[CenterDot](y^-1)

(* Eval seems to be not needed anymore *)

Eval[o_,x_ y_]:=OProd[o,Eval[o,x],Eval[o,y]]
Eval[o_,x_ y_ z__]:=Eval[o,Eval[o,x y] z]

Eval[o_,x_\[CenterDot]y_]:=OProd[o,Eval[o,x],Eval[o,y]]
Eval[o_,x_\[CircleDot]y_]:=OProd[o,Eval[o,x],Eval[o,y]]
Eval[o_,x_]:=x /;AtomQ[x]
Eval[o_,x_^1]:=x /;AtomQ[x]
Eval[o_,x_^-1]:=GetInverse[o,x] /;AtomQ[x]
Eval[o_,x_^n_]:=Eval[o,x^(n-1)\[CircleDot]x] /;AtomQ[x] && n>1
Eval[o_,x_^n_]:=Eval[o,x^(n+1)\[CircleDot]x^-1] /;AtomQ[x] && n<-1

x_^1:=x /; OpFSetElQ[x] 
x_^n_:=x^(n-1)*x /; OpFSetElQ[x] && IntegerQ[n] && n>1
x_^n_:=x^(n+1)*x^-1 /; OpFSetElQ[x] && IntegerQ[n] && n<-1

Protect[Power];

Unprotect[Times];
x_\[CirclePlus]y_\[CirclePlus]z__:=(x\[CirclePlus]y)\[CirclePlus]z
-(x_\[CirclePlus]y_):=(-x)\[CirclePlus](-y)
Eval[o_,x_\[CirclePlus]y_]:=OSum[o,Eval[o,x],Eval[o,y]]
Eval[o_,x_]:=x /;AtomQ[x]
Eval[o_,-x_]:=GetInverse[o,x] /;AtomQ[x]
Protect[Times];


GetIndexMatrix[o_]:=Module[{s,m,n,d,i,j,u},
  s=o[[1]];  
  d=Length[o[[2]]];
  If[d!=Length[s],Print["Error: Inconsistent data"];];
  m=Table[0,{i,d},{j,d}];
  For[i=1,i<=d,++i,
    For[j=1,j<=d,++j,
      u=GetIndex[s,o[[2]][[i]][[j]]];
      m[[i]][[j]]=u;
    ];
  ];
  m
]

IsAssociative[o_]:=Module[{m,d,i,j,k},
  m=GetIndexMatrix[o];
  d=Length[m];
  For[i=1,i<=d,++i,
    For[j=1,j<=d,++j,
      For[k=1,k<=d,++k,
        If[m[[m[[i]][[j]]]][[k]]!=m[[i]][[m[[j]][[k]]]],Return[False]];
      ];
    ];
  ];
  Return[True];
]

IsAbelian[o_]:=Module[{m,d,i,j,k},
  m=GetIndexMatrix[o];
  d=Length[m];
  For[i=1,i<=d,++i,
    For[j=1,j<=d,++j,
      If[m[[i]][[j]]!=m[[j]][[i]],Return[False]];
    ];
  ];
  Return[True];
]

IsNeutral[o_,x_]:=Module[{m,d,i,j,e},
  m=GetIndexMatrix[o];
  d=Length[m];
  e=GetIndex[o[[1]],x];
  For[i=1,i<=d,++i,
    If[m[[i]][[e]]!=i,Return[False];];
  ];
  For[i=1,i<=d,++i,
    If[m[[e]][[i]]!=i,Return[False];];
  ];
  Return[True];
]

GetNeutral[o_]:=Module[{s,m,d,i,j,e},
  s=o[[1]];
  m=GetIndexMatrix[o];
  d=Length[m];
  For[j=1,j<=d,++j,
    For[i=1,i<=d,++i,
      If[m[[i]][[j]]!=i,Goto[next];];
    ];
    For[i=1,i<=d,++i,
      If[m[[j]][[i]]!=i,Goto[next];];
    ];
    Return[s[[j]]];
    Label[next];
  ];
  Return[False];
]
HasNeutral[o_]:=If[SameQ[GetNeutral[o],False],False,True];

GetInverse[o_,x_]:=Module[{s,m,d,i,j,e},
  s=o[[1]];
  m=GetIndexMatrix[o];
  d=Length[m];
  e=GetNeutral[o];
  If[SameQ[e,False],Print["No neutral element!"];Return[False];];
  e=GetIndex[s,e];
  j=GetIndex[s,x];
  For[i=1,i<=d,++i,
      If[m[[i]][[j]]==e && m[[j]][[i]]==e,Return[s[[i]]];];
  ];
  Return[False];
]

HasInverses[o_]:=Module[{s,m,d,i,j,e},
  s=o[[1]];
  m=GetIndexMatrix[o];
  d=Length[m];
  e=GetNeutral[o];
  If[SameQ[e,False],Print["No neutral element!"];Return[False];];
  e=GetIndex[s,e];
  For[i=1,i<=d,++i,
    j=GetInverse[o,s[[i]]];
    If[SameQ[j,False],
      (* Print["Element ",s[[i]]," has no inverse!"];*)
      Return[False];
    ];
  ];
  Return[True];
]

IsGroup[o_]:=IsAssociative[o] && HasNeutral[o] && HasInverses[o]

OpFSetTable[o_]:=Module[{s,m,n,d,i,j,e},
  s=o[[1]];
  m=GetIndexMatrix[o];
  d=Length[m];
  n=Table[0,{d+1},{d+1}];
  n[[1]][[1]]=" ";
  For[i=1,i<=d,++i,
    n[[i+1]][[1]]=n[[1]][[i+1]]=s[[i]];
    For[j=1,j<=d,++j,
      n[[i+1]][[j+1]]=s[[m[[i]][[j]]]];
  ]];
  d=Length[n];
  Grid[n,Frame->All,Dividers->{{1->Thick,2->Thick,-1->Thick},{1->Thick,2->Thick,-1->Thick}}]
]

SetAttributes[ForEach,HoldAll]
ForEach[x_,s_,ins_]:=
  For[i=1,i<=Length[s],++i,
    x=s[[i]];ins
  ]




NewOpFSet[set_,opm_]:=Module[{op,i,j,m,remove},
    remove=set;
    remove[0]=Remove;
    remove;
    op=OpFSet[set,opm];
    m=GetIndexMatrix[op];
    Unprotect[Times];
    Unprotect[Power];
    ClearAttributes[Times,Orderless];
    For[i=1,i<=Length[set],++i,
      OpFSetElQ[set[[i]]]=True;
      For[j=1,j<=Length[set],++j,
       set[[i]]\[CenterDot]set[[j]]=set[[m[[i]][[j]]]]; 
       set[[i]] set[[j]]=set[[m[[i]][[j]]]]; 
      ];
    ];
    Protect[Power];
    Protect[Times];
    Return[op]
]

NewGroup[set_,opm_]:=Module[{op,i,j,m,remove},
  remove=set;
  remove[0]=Remove;
  remove;
  op=OpFSet[set,opm];
  If[IsAssociative[op] && HasNeutral[op] && HasInverses[op],
    m=GetIndexMatrix[op];
    Unprotect[Times];
    ClearAttributes[Times,Orderless];
    Unprotect[Power];
    For[i=1,i<=Length[set],++i,
      OpFSetElQ[set[[i]]]=True;
      For[j=1,j<=Length[set],++j,
       set[[i]]\[CenterDot]set[[j]]=set[[m[[i]][[j]]]]; 
       set[[i]] set[[j]]=set[[m[[i]][[j]]]]; 
      ];
    ];
    For[i=1,i<=Length[set],++i,
      set[[i]]^-1=GetInverse[ op,set[[i]] ];
    ];
    Protect[Power];
    Protect[Times];
    Return[op]
  ,
    Return["This is not a group!"]
  ];  
]




NewQSqrt[a_,b_,p_]:=If[IntegerQ[p] && p>0,
 If[IntegerQ[a]&&IntegerQ[b],
   QSqrt[a,b,p],
   "a,b must be integers"
 ],
 "p must be a positive integer"
]
Format[QSqrt[a_,b_,p_]]:=If[b==0,
  a,
  If[a==0,
    If[b==1,
      HoldForm[Sqrt[p]],
      HoldForm[b Sqrt[p]]
    ],
    If[Abs[b]!=1,
      HoldForm[a+b Sqrt[p]],
      If[b==1,
        HoldForm[a+Sqrt[p]],
        HoldForm[a-Sqrt[p]]
]]]]
Unprotect[Plus];
QSqrt/: QSqrt[a_,b_,p_]+QSqrt[c_,d_,p_]:=QSqrt[a+c,b+d,p]
QSqrt/: QSqrt[a_,b_,p_]+u_:=QSqrt[a+u,b,p] /; NumberQ[u]
QSqrt/: u_+QSqrt[a_,b_,p_]:=QSqrt[a+u,b,p] /; NumberQ[u]
Protect[Plus];
Unprotect[Times];
QSqrt/: QSqrt[a_,b_,p_] QSqrt[c_,d_,p_]:=QSqrt[a c + b d p,a d+b c,p]
QSqrt/: QSqrt[a_,b_,p_] u_:=QSqrt[a u,b u,p]
QSqrt/: u_ QSqrt[a_,b_,p_]:=QSqrt[a u,b u,p]
Protect[Times];
Unprotect[Power];
QSqrt/: QSqrt[a_,b_,p_]^1:=QSqrt[a,b,p];
QSqrt/: QSqrt[a_,b_,p_]^-1:=QSqrt[a/(a^2-p b^2),-b/(a^2-p b^2),p];
QSqrt/: QSqrt[a_,b_,p_]^n_:=QSqrt[a,b,p] QSqrt[a,b,p]^(n-1) /; IntegerQ[n] && n>1;
QSqrt/: QSqrt[a_,b_,p_]^n_:=QSqrt[a,b,p]^-1 QSqrt[a,b,p]^(n+1) /; IntegerQ[n] && n<-1;
Protect[Power];




Subscript[a_Integer,p_Integer]:=NewZp[a,p];
NewZp[a_,p_]:=If[IntegerQ[p] && p>1,
 If[IntegerQ[a],
   Zp[Mod[a,p],p],
   "a must be integer"
 ],
 "p must be a positive integer"
]
Format[Zp[a_,p_]]:=HoldForm[Subscript[a,p]]
Unprotect[Plus];
Zp/: Zp[a_,p_]+Zp[b_,p_]:=Zp[Mod[a+b,p],p]
Zp/: Zp[a_,p_]+n_Integer:=Zp[Mod[a+n,p],p]
Zp/: n_Integer+Zp[a_,p_]:=Zp[Mod[a+n,p],p]
Protect[Plus];
Unprotect[Times];
Zp/: Zp[a_,p_] Zp[b_,p_]:=Zp[Mod[a b,p],p]
Zp/: n_Integer Zp[b_,p_]:=Zp[Mod[n b,p],p]
Zp/: Zp[b_,p_] n_Integer :=Zp[Mod[n b,p],p]
Zp/: Rational[n_Integer,m_Integer] Zp[b_,p_]:=Zp[Mod[n b,p],p] Zp[m,p]^-1
Zp/: Zp[b_,p_] Rational[n_Integer,m_Integer] :=Zp[Mod[n b,p],p] Zp[m,p]^-1
Zp/: Zp[b_,p_] n_Integer :=Zp[Mod[n b,p],p]
Protect[Times];
Unprotect[Power];
Zp/: Zp[a_,p_]^1:=Zp[a,p]
Zp/: Zp[a_,p_]^-1:=Module[{i},
  For[i=1,i<p,++i,
    If[Mod[i a,p]==1,Return[Zp[i,p]]]
  ];
  Return[List[]]
]
Zp/: Zp[a_,p_]^n_:=Zp[a,p] Zp[a,p]^(n-1) /; IntegerQ[n] && n>1
Zp/: Zp[a_,p_]^n_:=Zp[a,p]^-1 Zp[a,p]^(n+1) /; IntegerQ[n] && n<-1
Protect[Power];
Unprotect[Sqrt];
Zp/: Sqrt[Zp[a_,p_]]:=Module[{i},
  For[i=0,i<p,++i,
    If[Mod[i i,p]==a,Return[Zp[i,p]]]
  ];
  Return[List[]]
]
Protect[Sqrt];





PlotComplex[List[c__]]:=PlotComplex[c];
PlotComplex[c__]:=Module[{t,r,z,col},
  r=1;
  t={Circle[{0,0},1],Line[{{0,0},{1,0}}]};
  For[i=1,i<=Length[List[c]],++i,
    z=List[c][[i]];
    If[!SameQ[Head[z],List],
      col=Blue,
      If[SameQ[Head[z[[2]]],RGBColor],
        col=z[[2]];z=z[[1]],
        col=z[[1]];z=z[[2]]
      ];
    ];
    z=N[z];
    If[!SameQ[Head[z],Complex],z=Complex[z,0]];
    r=Max[r,Abs[z]];
    t=Append[t,{col,Arrow[{{0,0},{Re[z],Im[z]}}]}];
  ];
(* Print["t=",t];*)
  r=r*1.1;
  Graphics[t,PlotRange->{{-r,r},{-r,r}}]
];



End[];
EndPackage[];
