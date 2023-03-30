(* ::Package:: *)

BeginPackage["FSets`"];
(* Prosty pakiet do arytmetyki mnogościowej zbiorów skończonych.
   Autor: Marian Mrozek, (c) 2012 
*)
FSet::usage="FSet[a,b,c,...]";
FCard::usage="FCard[FSet[a,b,c,...]]";
(*FUnion::usage="FUnion[FSet[a,b,c,...],FSet[a,b,c,...]]";*)
CartProd::usage="CartProd[FSet[a,b,c,...],FSet[a,b,c,...]]";
FInsert::usage="Subsets[x,FSet[a,b,c,...]]";
FSubsets::usage="Subsets[FSet[a,b,c,...]]";
FSetOf::usage="FSetOf[x\[Element]S,h[x]]";
FPair::usage="FPair[x,y]";

TruthTable::usage="TruthTable[expression, variables]"


Begin["`Private`"];
Format[FSet[a__]]:={a} 
Format[FSet[]]:={}
FPair[x_,y_]:=x->y
SetAttributes[FSetOf,HoldAll]

(*FSet/: FSet[a1__]\[Union]FSet[a2__]:=FUnion[FSet[a1],FSet[a2]]
FSet/: FSet[a1__]\[Intersection]FSet[a2__]:=Intersection[FSet[a1],FSet[a2]]*)
FSet/: FSet[a1___]\[Backslash]FSet[a2___]:=Complement[FSet[a1],FSet[a2]] 
FSet/: FSet[a1___] \[CircleMinus] FSet[a2___]:=
  (FSet[a1] \[Backslash] FSet[a2]) \[Union] (FSet[a2] \[Backslash] FSet[a1])

FSet/: FSet[a1___]\[Cross]FSet[a2___]:=CartProd[FSet[a1],FSet[a2]] 

FSet/: Element[x_,FSet[]]:=False
FSet/: Element[x_,FSet[a__]]:=MemberQ[FSet[a],x]
FSet/: FCard[FSet[a__]]:=Length[FSet[a]]
FSet/: FCard[FSet[]]:=0
FSet/: FSet[List[a___]]:=FSet[a]
FCard[a___]:=Length[a]


Unprotect[Element];
Unprotect[ForAll];
(* Trzeba poprawić!!! Hold nie zapewnia poprawności. 
   Źle działa, gdy zdefiniowane są zmienne, które są używane
   w argumencie formalnym x!!!*)
Element/: ForAll[Element[x_,s_],psi_]:=Module[{r,i},
  r=True;
  For[i=1,i<=Length[s],++i, 
    r=r && ReleaseHold[Hold[psi] /. x->s[[i]] ];
    (* Print[s[[i]]," - ",Hold[psi] /. x->s[[i]]," - ",ReleaseHold[Hold[psi] /. x->s[[i]] ]];*)
  ];
  r
]
Protect[ForAll];
Unprotect[Exists];
Element/: Exists[Element[x_,s_],psi_]:=!ForAll[Element[x,s],!psi]
Protect[Exists];
Protect[Element];

FSet/: FSet[a1___]\[Subset]FSet[a2___]:=ForAll[x\[Element]FSet[a1],x\[Element]FSet[a2]]
FSet/: FSet[a1___]\[Superset]FSet[a2___]:=ForAll[x\[Element]FSet[a2],x\[Element]FSet[a1]]
FSet/: FSet[a1___]==FSet[a2___]:= FSet[a1]\[Subset]FSet[a2]&&FSet[a1]\[Superset]FSet[a2]

(*FSet/: FUnion[FSet[],FSet[a___]]:=FSet[a]
FSet/: FUnion[FSet[x_,b___],FSet[a___]]:=FSet[a]*)

Pairer[y_]:=Function[x,FPair[x,y]]
CartProd[FSet[a__],FSet[]]:=FSet[]
CartProd[FSet[],FSet[a__]]:=FSet[]
CartProd[FSet[a__],FSet[b_]]:=Map[Pairer[b],FSet[a]]
CartProd[FSet[a__],FSet[b_,c__]]:=CartProd[FSet[a],FSet[b]]\[Union]CartProd[FSet[a],FSet[c]]




FInsert[x_,FSet[a___]]:=FSet[a]\[Union]FSet[x]
FInsert[x_][FSet[a___]]:=FSet[a]\[Union]FSet[x]
FSubsets[FSet[]]:=FSet[FSet[]]
FSubsets[FSet[x_]]:=FSet[FSet[],FSet[x]]
FSubsets[FSet[x_,y__]]:=FSubsets[FSet[y]]\[Union]Map[FInsert[x],FSubsets[FSet[y]]]

(* Trzeba poprawić!!! Hold nie zapewnia poprawności. 
   Źle działa, gdy zdefiniowane są zmienne, które są używane
   w argumencie formalnym x!!!*)
FSetOf[x_\[Element]sX_,expr_]:=Module[{result,i,t,substitution},
  result=FSet[];
  For[i=1,i<=FCard[sX],++i,
    t=sX[[i]];
    substitution=(x->t);
    If[Length[x]>0,
      substitution=Table[x[[j]]->t[[j]],{j,1,Length[x]}];
    ];
    If[ReleaseHold[Hold[expr] /. substitution],
      result=FInsert[t,result]
    ]; 
  ];
  result
]

TruthTable[formula_, variables_] := Block[
	{tree = TreeForm[formula], truthTable = {}, depth, levels, tuples, vals},
	depth = Depth[tree];
	levels = DeleteDuplicates@Level[tree, depth];
	Do[
		vals = Table[variables[[i]] -> bools[[i]], {i, Length[variables]}];
		AppendTo[truthTable, Boole@Map[# /. vals &, levels]], {bools, Tuples[{True, False}, Length[variables]]} 
	];
	TableForm[truthTable, TableAlignments -> Center, TableHeadings -> {None, levels}]
]

End[];
EndPackage[];
