(* ::Package:: *)

(*  ColorJones.m                                                         *)
(*  Author: Jesse S. F. Levitt                                           *)
(*    Date: Sept 2017                                                    *)
(* Version: 1.0 ( initial implementations )                               *)
<<NC`
<<NCAlgebra`

BeginPackage[ "ColorJones`",{"KnotTheory`",(*"NC`","NCAlgebra`",*)"NCPolyInterface`","NCDot`","NonCommutativeMultiply`","NCPoly`"}];

CJ::usage = "To calculate the Colored Jones Polynomial of a Braid using the Approaches of Armond, Hunyh and L\[EHat]."

SimpleWalkCalculator::usage = "To calculate the simple walks along a Braid representation of a knot."

Begin["`Private`"];


(*<<Combinatorica`*)
(* This material added since combinatorica was depricated *)
(* The following functions enable the calculation of the number of inversions of a permutation 'p' *)
MInversions[{}] := 0
MInversions[p_?MPermutationQ] := Apply[Plus,MToInversionVector[p]]
MPermutationQ[e_List] := (Sort[e] === Range[Length[e]])
MToInversionVector[p_?MPermutationQ] :=
	Block[{i,inverse=InversePermutation[p]},
		Table[ Length[ Select[Take[p,inverse[[i]]], (# > i)&] ], {i,Length[p]-1}]
	] /; (Length[p] > 0)


(* package variables for use *)

CJP`q; CJP`a; CJP`b; CJP`c;



(* The function SWdetq is a modified quantum determinant function for use with Braids.
(SW stands for Simple Walks)
It takes as input the skewcommutative element 'q', the matrix 'm', and the number of crossing in the ambient braid 'Ncrs'.

Given these inputs it modifies the Leibnitz formula for the determinant:
Underscript[\[Sum], \[Sigma]\[Element]S^n](sgn \[Sigma]) Subscript[mlen, \[Sigma](1)1]Subscript[mlen, \[Sigma](2)2]... Subscript[mlen, \[Sigma](n)n]
replacing the (sgn \[Sigma]) with q^(# of inversions of the permutation \[Sigma]) - Note that for q=-1 this returns the normal determinant.
During the evaluation of the product: Subscript[mlen, \[Sigma](1)1]Subscript[mlen, \[Sigma](2)2]... Subscript[mlen, \[Sigma](n)n],
it tests for violations of the simple walks condition on braid words (see Armond arXiv:1101.3810v2),
it deletes these as they occur to eliminate terms that will eventually evaluate to zero, with the goal of reducing memory load and increase computation speed (which it does by orders of magnitude for bad cases).

SWdetq outputs the quantum determinant of a Braid modulo terms that will eventually evaluate to zero in the calculation of the Jones Polynomial
*)

SWdetq[q_, m_, Ncrs_]:=SWdetq[q, m, Ncrs]=Module[{mlen=Length[m],n,SWtemp},
n=Permutations[Range[mlen]];

(* The following Do loop encodes what the less readable Catch[Fold[...  function that follows it accomplishes.
That formulation runs marginally faster. There, Catch and Throw serve the same role as the Break[] command. You may activiate either implementation. *)

(*SWdetq`k[s_, mlength_]:=Module[{Ki,t=1},
	Do[ t=t**m[[n[[s,Ki]],Ki]];
		If[SameQ[t,0],Break[],t=DuplicateReduction[t,Ncrs,2]]
	,{Ki,1,mlength}];
	t
];*)

SWdetq`k[s_, mlength_]:=Catch[Fold[If[SameQ[#1,0],Throw[#1],DuplicateReduction[#1**m[[n[[s,#2]],#2]],Ncrs,2]]&,1,Range[mlength]]];

(* The below code outlines several parallel implementations. The one that has been found to run fastest is active.
In particular, the need to convert 0's between a number and an NCPoly object introduces a measurable slowdown *)

(*SWtemp=Array[(-q)^MInversions[n[[#]]]**(SWdetq`k[#,mlen])&,Length[n]];
SWtemp=Pick[SWtemp,SWtemp,_NCPoly];*)
(*SWtemp=DeleteCases[Array[(-q)^MInversions[n[[#]]]**(SWdetq`k[#,mlen])&,Length[n]],0];*)
(*SWtemp=Cases[Array[(-q)^MInversions[n[[#]]]**(SWdetq`k[#,mlen])&,Length[n]],Except[0]];*)
SWtemp=Cases[Array[(-q)^MInversions[n[[#]]]**(SWdetq`k[#,mlen])&,Length[n]],_NCPoly];
If[SameQ[SWtemp,{}],
	Return[0],
	(* We use the Merge[ -, Total] function to account for the possibility that the Association has multiple values with the same key *)
	Return[NCPoly@@{SWtemp[[1,1]],Merge[SWtemp[[All,2]],Total]}] 
]

(*Return[Total[Array[(-q)^MInversions[n[[#]]]**(SWdetq`k[#,mlen])&,Length[n]]]]*)
]


(* The function RBrep returns the Reduced Burau representation of a Braid.
It takes in as input the skewcommutative element 'q', the input: 'Braid' and the ambient variables for the representation.
In doing so it assumes 'Braid' is a 2xNcrs list where Ncrs is the number of crossing in the input braid.
The first row of this input matrix contains the data for which crossing is first encountered in the braid.
The second row of this input matrix distinguishes whether it is a positive crossing (and is equal to 1) or negtive (and equal to -1).
Vars represents the variable list of the Braid used by the NCPoly data structure and ensures the Burau representation is populated consistently.
Note that the first Ncrs variables correspond to b_i's, the next Ncrs variables correspond to c_i's and the final Ncrs variables correspond to a_i's.
*)
RBrep[q_, Braid_, vars_]:=Module[{FI=IdentityMatrix[Max[Braid]+1], Ncrs=Length[Braid], M, NCvars, p},
M=ConstantArray[FI,Ncrs];
NCvars=NCToNCPoly[#,vars]&/@ vars;

Do[
	p=Braid[[i,1]];
	If[\!\(TraditionalForm\`Braid\)[[i,2]]==1,
		(* If the braid generator is a positive crossing *)
		M[[i]]=ReplacePart[M[[i]],{
					{p,p}->NCvars[[i+2*Ncrs]],  {p,p+1}->NCvars[[i]],
					{p+1,p}->NCvars[[i+Ncrs]],{p+1,p+1}->0}],
		(* Else the braid generator is a negative crossing *)
		M[[i]]=ReplacePart[M[[i]],{
					{p,p}->0,              {p,p+1}->NCvars[[i+Ncrs]],
					{p+1,p}->NCvars[[i]],{p+1,p+1}->NCvars[[i+2*Ncrs]]}]
	],{i,Ncrs}
];

Return[q**Drop[Fold[NCDot,M],1,1]]]

(*Equivalently: 
Do[FI=NCDot[FI,M[[i]]],{i,1,Ncrs}]; 
Return[q**Drop[FI,1,1]]]*)



(* For a given input matrix, this function outputs a List of submatrices.
 The output, is a list that stores all the symmetric submatrices of the input matrix M.
 It runs over every element of DSU, the power set of the matrix dimension and for every single element it gives a submatrix of M *)
SSubMatrices[M_]:=Module[{DSU=Delete[Subsets[Range[Length[M]]],1]},
	Return[Array[M[[DSU[[#]],DSU[[#]]]]&,Length[DSU]]]
]


(* This is the sum of the simple walks on a Braid Following the description of Armond arXiv:1101.3810v2 
Reinterpreting the function C defined in "On the colored Jones Polynomial and the Kashaev invariant" by V. Huynh and T. Le - page 2.
Input a braid, a knot or the 2 x Ncrs matrix of Braid generators and signs, along with the skewcommutative value 'q', and the list of algebras variables.
The function outputs a sum of all possible simple walks (see definitions in the Armond Paper) on the braid. *)

(* This function uses the quantum determinant which is at worst factorial in run time.
 Load precomputed values if possible *)
<<"walk-model-to-compute-the-colored-jones-polynomial/simplewalks.m";

(* We attempt to ensure compatibility with the KnotTheory` package.
These functions take Object types defined in the KnotTheory Package and convert them for local use *)
SimpleWalkCalculator[Braid_Knot,NCvars_,q_]:=SimpleWalkCalculator[Array[List[Abs[BR[Braid][[2,#]]],Sign[BR[Braid][[2,#]]]]&,Length[BR[Braid][[2]]]],NCvars,q]
SimpleWalkCalculator[Braid_BR,NCvars_,q_]:=SimpleWalkCalculator[Array[List[Abs[Braid[[2,#]]],Sign[Braid[[2,#]]]]&,Length[Braid[[2]]]],NCvars,q]

SimpleWalkCalculator[brd_, NCvars_, q_]:=SimpleWalkCalculator[brd, NCvars, q]=Module[{temp,simpleWalkMatrix=SSubMatrices[RBrep[q, brd, NCvars]],Ncrs=Length[brd]},

(* The below code outlines several parallel implementations. The one that has been found to run fastest is active.
In particular, the need to convert 0's between a number and an NCPoly object introduces a measurable slowdown *)

(*temp=Array[(-1)^((Length[simpleWalkMatrix[[#]]])-1)*SWdetq[q, simpleWalkMatrix[[#]], Ncrs]&,Length[simpleWalkMatrix]];
temp=Pick[temp,temp,_NCPoly];*)
(*temp=DeleteCases[Array[(-1)^((Length[simpleWalkMatrix[[#]]])-1)*SWdetq[q, simpleWalkMatrix[[#]], Ncrs]&,Length[simpleWalkMatrix]],0];*)
(*temp=Cases[Array[(-1)^((Length[simpleWalkMatrix[[#]]])-1)*SWdetq[q, simpleWalkMatrix[[#]], Ncrs]&,Length[simpleWalkMatrix]],Except[0]];*)
temp=Cases[Array[(-1)^((Length[simpleWalkMatrix[[#]]])-1)*SWdetq[q, simpleWalkMatrix[[#]], Ncrs]&,Length[simpleWalkMatrix]],_NCPoly];
If[SameQ[temp,{}],
	Return[0],
	(* We use the Merge[ -, Total] function to account for the possibility that the Association has multiple values with the same key *)
	Return[NCPoly@@{temp[[1,1]],Merge[temp[[All,2]],Total]}]
]
(*Return[Total[Array[(-1)^((Length[simpleWalkMatrix[[#]]])-1)*SWdetq[q, simpleWalkMatrix[[#]], Ncrs]&,Length[simpleWalkMatrix]]]]*)

(* This code will add currently computed values to the stored list, but may also include all other related data as well. Use with great care. *)
(*(SimpleWalkCalculator[brd, NCvars, q]=simpleWalks)>>>"walk-model-to-compute-the-colored-jones-polynomial/simplewalks.m"*)
]


(* This code calculates the Script E function for a single positive generator of a walk-word.
It takes as input the skewcommutative value 'q', the number of colors being used to evaluate the color Jones Polynomial 'n',
and the number of times the generator has either a c-type crossing, 'cr' or an a-crossing 'ad' in the walk-word being evaluated.
This function assumes the walk-word is given is right-quantum form.
Memoization surprisingly speeds up the overall program runtime here. *)
ScriptEPos[q_,n_,cr_,ad_]:=ScriptEPos[q,n,cr,ad]=Block[{SEPval=1},
	If[ad!=0,SEPval*=Product[(1-q^(n-cr-k)),{k,ad}]];
	If[cr!=0,SEPval*=q^(cr*(n-1-ad))];

Return[SEPval]]



(* This code calculates the Script E function for a single negative generator of a walk-word.
It takes as input the skewcommutative value 'q', the number of colors being used to evaluate the color Jones Polynomial 'n',
and the number of times the generator has either a c-type crossing, 'cr' or an a-crossing 'ad' in the walk-word being evaluated.
This function assumes the walk-word is given is right-quantum form.
Memoization surprisingly speeds up the overall program runtime here. *)
ScriptENeg[q_,n_,cr_,ad_]:=ScriptENeg[q,n,cr,ad]=Block[{SENval=1},
	If[ad!=0,SENval*=Product[(1-q^(cr+k-n)),{k,ad}]];
	If[cr!=0,SENval*=q^(-cr*(n-1))];

Return[SENval]]



(* This is the first of two separate implementations of the monomial builder function.
It takes in the number of times a given word had an a, b, or c-type crossing of each generator and rebuilds the word the right-quantum form.
It does this by assembling the list of occurences of each letter crossing in the 'b, c, a' ordering of a right quantum form.
It then builds a base 3*Ncrs integer from this by generating a list for each letter index(-1 due to indexing issues) the length of the number of times it appears.
Flattening this list and converting to the appropriate base completes the process.
It should be used when the faster compiled form doesn't work with your version of Mathematica or your system lacks a C-compiler. *)

(*MonomialBuilder[aList_, bList_, cList_, Ncrs_]:=(*MonomialBuilder[aList, bList, cList, Ncrs]=*)Block[{MBexponents=Join[bList,cList,aList],MBdigits},
MBdigits=Flatten[Array[ConstantArray[#-1,MBexponents[[#]]]&,3*Ncrs]];

Return[Join[Reverse[MBexponents],{FromDigits[MBdigits, 3*Ncrs]}]]
]*)


(* This is the second of two separate implementations of the monomial builder function.
It takes in the number of times a given word had an a, b, or c-type crossing of each generator and rebuilds the word the right-quantum form.
It does this by assembling the list of occurences of each letter crossing in the 'b, c, a' ordering of a right quantum form.
It then builds a base 3*Ncrs integer from this by generating a list with each letter index(-1 due to indexing issues) the number of times it appears.
Flattening this list and converting to the appropriate base completes the process.
It is faster, but may fail if your system does not have a C-compiler or your version of Mathematica is too old *)
MonomialBuilder[aList_, bList_, cList_, Ncrs_]:=(*MonomialBuilder[aList, bList, cList, Ncrs]=*)Block[
{MBexponents=Join[bList,cList,aList],MBdigits},
MBdigits=MBC[MBexponents,Ncrs,Total[MBexponents]];

Return[Join[Reverse[MBexponents],{FromDigits[MBdigits, 3*Ncrs]}]]
]

MBC=Compile[{{MBCexponents,_Integer,1},{Ncrs,_Integer},{MBCdigitsLength,_Integer}},
Block[{MBCdigits=Table[0,MBCdigitsLength],MBi=0,MBj=0,MBposition=1,MBlength=3*Ncrs},
For[MBi=0,MBi<MBlength,MBi++,
	For[MBj=0,MBj<MBCexponents[[MBi+1]],MBj++,MBCdigits[[MBposition]]=MBi;MBposition++];
	];
Return[MBCdigits]],
RuntimeOptions->{"CatchMachineIntegerOverflow"->False},CompilationTarget->"C"
]


(* This is the first of two implementations of a helper function for BMEC, to slow memory loading.
It carries out the majority of algorithm 2 and equation (9.2) from Hajij, Levitt arXiv: 1804.07910 .
It should be used when the faster compiled form doesn't work with your version of Mathematica or your system lacks a C-compiler. *)
(*BraidMonomialHelper[ ncPart_, Ncrs_, Signs_]:=BraidMonomialHelper[ ncPart, Ncrs, Signs]=Block[
(* Initialize the degree count lists *)
{BMHlocalMonomial, BMHword, BMHcrossing, BMHaList=ConstantArray[0,Ncrs], BMHbList=ConstantArray[0,Ncrs], BMHcList=ConstantArray[0,Ncrs], BMHqdegree=0},

BMHlocalMonomial=PadLeft[IntegerDigits[Last[ncPart],3*Ncrs],Total[Most[ncPart]]];

Do[
	BMHword=BMHlocalMonomial[[i]];
	BMHcrossing=Mod[BMHword,Ncrs]+1;
	If[Signs[[BMHcrossing]]>0,
		Switch[Quotient[BMHword,Ncrs],
			2,BMHaList[[BMHcrossing]]++, (* a is ordered last so we don't need to check how many b's or c's have already appeared *)
			0,BMHbList[[BMHcrossing]]++; BMHqdegree-=(2*BMHcList[[BMHcrossing]]), (* b is ordered first, but commutes with a's, so we need to account for c's *)
			1,BMHcList[[BMHcrossing]]++; BMHqdegree+=BMHaList[[BMHcrossing]] (* c is ordered middle, account for all the a's it needs to cross *)
		],
		Switch[Quotient[BMHword,Ncrs],
			2,BMHaList[[BMHcrossing]]++, (* a is ordered last so we don't need to check how many b's or c's have already appeared *)
			0,BMHbList[[BMHcrossing]]++; BMHqdegree+=(2(BMHaList[[BMHcrossing]] + BMHcList[[BMHcrossing]])), (* b is ordered first, so we need to account for a's and c's it will pass *)
			1,BMHcList[[BMHcrossing]]++; BMHqdegree-=BMHaList[[BMHcrossing]] (* c is ordered middle, account for all the a's it needs to cross *)
		]
	]
	,{i,1,Length[BMHlocalMonomial]}
];

List[{BMHqdegree},BMHaList,BMHbList,BMHcList]
]*)


(* This is the second of two implementations of a helper function for BMEC, to slow memory loading.
It carries out the majority of algorithm 2 and equation (9.2) from Hajij, Levitt arXiv: 1804.07910 .
It is not all compiled in the common event that the integer encoding the noncommutative walk-word exceeds C's storage length.
It is faster, but may fail if your system does not have a C-compiler or your version of Mathematica is too old *)
BraidMonomialHelper[ ncPart_, Ncrs_, Signs_]:=BraidMonomialHelper[ ncPart, Ncrs, Signs]=
Block[{BMHlocalMonomial={}},
BMHlocalMonomial=PadLeft[IntegerDigits[Last[ncPart],3*Ncrs],Total[Most[ncPart]]];

Return[BMHC[BMHlocalMonomial,Ncrs,Signs]]
]

BMHC=Compile[{{BMHClocalMonomial,_Integer,1},{Ncrs,_Integer},{Signs,_Integer,1}},
Block[
(* Initialize the degree count lists *)
{BMHword=0, BMHcrossing=1, BMHaList=Table[0,Ncrs], BMHbList=Table[0,Ncrs], BMHcList=Table[0,Ncrs], BMHqdegree=0, Blen=Length[BMHClocalMonomial],Bcount=0},

Do[
	BMHword=BMHClocalMonomial[[Bcount]];
	BMHcrossing=Mod[BMHword,Ncrs]+1;
	If[Signs[[BMHcrossing]]>0,
		Switch[Quotient[BMHword,Ncrs],
			2,BMHaList[[BMHcrossing]]++, (* a is ordered last so we don't need to check how many b's or c's have already appeared *)
			0,BMHbList[[BMHcrossing]]++; BMHqdegree-=(2*BMHcList[[BMHcrossing]]), (* b is ordered first, but commutes with a's, so we need to account for c's *)
			1,BMHcList[[BMHcrossing]]++; BMHqdegree+=BMHaList[[BMHcrossing]], (* c is ordered middle, account for all the a's it needs to cross *)
			_,1
		],
		Switch[Quotient[BMHword,Ncrs],
			2,BMHaList[[BMHcrossing]]++, (* a is ordered last so we don't need to check how many b's or c's have already appeared *)
			0,BMHbList[[BMHcrossing]]++; BMHqdegree+=(2*(BMHaList[[BMHcrossing]] + BMHcList[[BMHcrossing]])), (* b is ordered first, so we need to account for a's and c's it will pass *)
			1,BMHcList[[BMHcrossing]]++; BMHqdegree-=BMHaList[[BMHcrossing]], (* c is ordered middle, account for all the a's it needs to cross *)
			_,1
		]
	]
	,{Bcount,1,Blen}
];

Return[List[Table[BMHqdegree,Ncrs],BMHaList,BMHbList,BMHcList]]],
RuntimeOptions->{"CatchMachineIntegerOverflow"->False},CompilationTarget->"C"]


(* A function for calculating all the relevant information from the exponents without reordering the polynomial *)
BMEC[ monomial_,  Ncrs_, Signs_, q_]:=BraidMonomialExponentCounter[monomial,Ncrs,Signs, q]

(* The function returns a list of 4 elements, with the first being one element and the rest being Lists containing as many elements as the braid has crossings *)
BraidMonomialExponentCounter[ monomialRule_, Ncrs_, Signs_, q_]:=Block[{BMECexponentList},
BMECexponentList=BraidMonomialHelper[ monomialRule[[1]], Ncrs, Signs];

List[monomialRule[[2]]*q^BMECexponentList[[1,1]], BMECexponentList[[2]], BMECexponentList[[3]], BMECexponentList[[4]]]
]


(*  This function implements the Duplicate Reduction Lemma, originally known as Lemma 4 in Armond arXiv:1101.3810v2 .
	We set ncvLen to record an integer controlling access to the NCPoly data structure.
	Specifically, NCPoly stores variable term data in reverse order with an extra data term. *)
DuplicateReduction[0, Ncrs_, numColors_]:=0

(*  The implementation below is the first of two separate implementations.
	It follows the second description of Algorithm 4 in Hajij, Levitt arXiv: 1804.07910 .
	It should be used when the faster compiled form doesn't work with your version of Mathematica or your system lacks a C-compiler. *)

(*DuplicateReduction[walkList_NCPoly, Ncrs_, numColors_]:=(*DuplicateReduction[walkList, Ncrs, numColors]=*)Block[{DRWalkList=Normal[walkList[[2]]], ncvLen=3*Ncrs+1, DRkeys, DRi},
Do[
	DRWalkList=DeleteCases[DRWalkList,
									HoldPattern[DRkeys_List->_]/;
										(DRkeys[[ncvLen-DRi-2*Ncrs]]+Max[DRkeys[[ncvLen-DRi-Ncrs]],DRkeys[[ncvLen-DRi]]])>=numColors];  (* ai+Max[bi,ci] *)
	If[SameQ[DRWalkList,{}],Break[]]
	,{DRi,1,Ncrs}
];
DRWalkList=NCPoly@@{walkList[[1]],Association[DRWalkList]};
Return[DRWalkList]
]*)

(*  The implementation below is the second of two separate implementations.
	It roughly follows the description of Algorithm 4 in Hajij, Levitt arXiv: 1804.07910 .
	It removes the double for loop by running a single (compiled) loop across all the words and recording when any of them has an excess of a's + max(b's, c's).
	The Pick[] function then selects out the words which will not zero N-evaluate and returns them.
	This implementation is faster, but may fail if your system does not have a C-compiler or your version of Mathematica is too old *)

DuplicateReduction[walkList_NCPoly, Ncrs_, numColors_]:=(*DuplicateReduction[walkList, Ncrs, numColors]=*)Block[{DRWalkList=Normal[walkList[[2]]], ncvLen=3*Ncrs+1(*, DRkeys*)},
(* This is an indentical, slower, but more readable version of the actual function call. *)
(*DRkeys=DRC[Most/@DRWalkList[[All,1]],Ncrs,numColors];
DRWalkList=Pick[DRWalkList,DRkeys,0];
DRWalkList=NCPoly@@{walkList[[1]],Association[DRWalkList]};
Return[DRWalkList]*)

Return[NCPoly@@{walkList[[1]],Association[Pick[DRWalkList,DRC[Most/@DRWalkList[[All,1]],Ncrs,numColors],0]]}]
]

DRC=Compile[{{DRCdigits,_Integer,2},{Ncrs,_Integer},{numColors,_Integer}},
Block[{DRnumColors=numColors,DRi,DRlen=Length[DRCdigits]},
Return[Table[Boole[MemberQ[UnitStep[DRCdigits[[DRi,;;Ncrs]]+MapThread[Max,{DRCdigits[[DRi,Ncrs+1;;2*Ncrs]],DRCdigits[[DRi,2*Ncrs+1;;3*Ncrs]]}]-DRnumColors],1]],{DRi,DRlen}]]],
RuntimeOptions->{"CatchMachineIntegerOverflow"->False},CompilationTarget->"C",Parallelization->True
]


(* The below functions are designed to promote compatibility with the KnotTheory Package *)
CJ[q_,NC_,Braid_Knot]:=CJ[q,NC,Array[List[Abs[BR[Braid][[2,#]]],Sign[BR[Braid][[2,#]]]]&,Length[BR[Braid][[2]]]]]
CJ[q_,NC_,Braid_BR]:=CJ[q,NC,Array[List[Abs[Braid[[2,#]]],Sign[Braid[[2,#]]]]&,Length[Braid[[2]]]]]

(*  This is the main Color Jones Function.
	It takes as input the skew-commutative measure or complex number 'q', the number of colors 'NC' being used in calculating the color Jones polynomial,
	and the braid word for the knot or link (links may not be fully supported) whose invariant is being computed. *)
CJ[q_,NC_,Braid_List]:=Module[
{stackHeight=1, loopDone=False, CJP=1, mirror=False, TPW, Ncrs, walks, simpleWalks, mirrorSimpleWalks, numStrands, writhe, LNG, aList, bList, cList, CoeffList, walkWeights, NCvars, i, j, localBraid, mirrorLocalBraid},

(*  Ensure we are using our default type of Braid Word.
    If its a dimension 1 list, we assume its a Braid Word, such as {1,-2,1,-2} for the Figure 8 knot.
    If its a dimension 2 list, we assume it has a {crossing, sign} form, such as {{1,1},{2,-1},{1,1},{2,-1}} for the Figure 8 knot.
    Otherwise, we would like to return an Error.
    Following this, tabulate the number of crossings - 'Ncrs' - as well as the number of strands in the braid representation and the writhe. *)
If[MatrixQ[Braid]!=True,
	localBraid=Array[List[Abs[Braid[[#]]],Sign[Braid[[#]]]]&,Length[Braid]],
	localBraid=Braid
];
Ncrs=Length[localBraid];
numStrands=Max[localBraid]+1;
writhe=Total[localBraid[[All,2]]];

(*  All NonCommutative variables are generated dynamically and kept track of using the NCvars List.
	This accomidates varied knots using a standardized notation.
	Maintaining the order of this List: {CJP`b1, CJP`b2, ... , CJP`c1, ... , CJP`a1, ... , CJP`a'Ncrs'} is critical to the functionality of calls to this List.
	This reflects the choice to speed computation wherever possible by using integer math over calls to symbol name lookups.
	The standard q value 'CJP`q' is set Commutative and the rest NonCommutative.*)
SetCommutative[CJP`q];
NCvars = Flatten[Symbol/@StringJoin/@Tuples[{{"CJP`b","CJP`c","CJP`a"},ToString/@Range[Ncrs]}]]; (* each crossing can either be positive Xor negative *)
SetNonCommutative[NCvars];

(*  The simple walks over a Braid are calculated using the reduced Burau representation.
	These will be calculated dynamically if necessary or pulled from data tables if possible.
	It will be returned with Lemma 4a already applied. *)
mirrorLocalBraid=localBraid;
mirrorLocalBraid[[All,2]]*=-1;
simpleWalks=SimpleWalkCalculator[localBraid, NCvars, CJP`q];
mirrorSimpleWalks=SimpleWalkCalculator[mirrorLocalBraid, NCvars, CJP`q];

If[ Length[simpleWalks[[2]]]>Length[mirrorSimpleWalks[[2]]],
	localBraid=mirrorLocalBraid;
	writhe*=-1;
	simpleWalks=mirrorSimpleWalks;
	mirror=True
];

CJ`ScriptE[cr_,ad_,position_]:=If[localBraid[[position,2]]>0,ScriptEPos[CJP`q,NC,cr,ad],ScriptENeg[CJP`q,NC,cr,ad]];

(*  Useful for batch runs as a way to update the data tables *)
(* Definition[SimpleWalkCalculator]>>"simplewalks.m";*)

While[loopDone!=True,

(*  If we are looping, rebuild TPW *)
	If[stackHeight==1,
		TPW=simpleWalks,

		(* The following code promotes efficiency by removing walk-words that will zero N-evaluate and combines walk-words with different coefficients *)
		walks=Array[MonomialBuilder[aList[[#]],bList[[#]],cList[[#]],Ncrs]->CoeffList[[#]]&,LNG];
		TPW=NCPoly@@{simpleWalks[[1]],Merge[walks,Collect[Total[#],CJP`q]&]};
		TPW=NCPolyProduct[simpleWalks,TPW];
		TPW=DuplicateReduction[TPW,Ncrs,NC] (* Implement lemma 4b (see Armond arXiv:1101.3810v2) *)
	];

	If[!SameQ[TPW,0], (* If we haven't deleted all the walk-words *)

		walks=Normal[TPW[[2]]];
		LNG=Length[walks];
		{CoeffList,aList,bList,cList}=Transpose[Array[BraidMonomialExponentCounter[walks[[#]],Ncrs,localBraid[[All,2]],CJP`q]&,LNG]];

		walkWeights=Total[CoeffList[[All]]*Times@@@MapThread[CJ`ScriptE,{cList,aList,ConstantArray[Range[Ncrs],LNG]},2]];
		If[walkWeights===0,
			loopDone=True,
			
			CJP+=walkWeights;
			stackHeight++],
		
		loopDone=True
	]
];

(* We collect the q terms to ensure usable output.
   This can increase runtime by an order of magnitude, but is much more efficient than ExpandAll[], Simplify[] or Apart[] *)
CJP=ParallelCombine[Collect[#,CJP`q]&,CJP,DistributedContexts->None];
CJP=Collect[CJP*(CJP`q^(((NC-1)*(writhe-numStrands+1))/2)),CJP`q];

(* If you are not interested in collecting the output, comment out the above lines and activiate the below line *)
(*CJP*=(CJP`q^(((NC-1)*(writhe-numStrands+1))/2));*)

If[!NumericQ[q],SetCommutative[q]];
If[mirror,CJP/.CJP`q->(1/q),CJP/.CJP`q->q]
]

End[]

EndPackage[]

