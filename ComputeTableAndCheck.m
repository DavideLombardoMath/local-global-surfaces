SetLogFile("LocalGlobal.out");

load "ArithmeticFunctions.m";
load "GeneralRepresentationTheory.m";
load "HasseSubgroups.m";
load "GroupExtensions.m";
load "GroupExtensions2.m";

/*
Given a list of groups and congruence conditions,
tests each of them for properties (P1) and (P2)
of the Appendix. Each of our groups satisfies
at least one of the two; since (P1) is quicker
to test, we start with that one, and only check
(P2) if needed.
*/
procedure RunTest(AG)
	counter := 0;
	for t in AG do
	counter := counter + 1;
	// "===============";
	"Testing group number", counter, "out of", #AG;
	test1 := TestGroupCannotBeExtended(t[1], t[2], t[3]);	// test for property (P1)
	if not test1 then
		// t;
		test2 := TestViaConstructingDoubleGroups(t[1], Character(t[2]), t[3]);	// test for property (P2)
		assert test2;								// this throws an error if test2 fails
	end if;
	end for;
end procedure;

/*
Compute the information in Table 1; for each group found,
including the non-maximal ones, perform the test described
in the Appendix
*/

/*
Class C_2
*/

/*
Subgroups of the form E \wreath S_2, with E an exceptional
subgroup of SL_2(F_\ell).
*/

load "ExceptionalWreathS2.m";

// ------------------------------------------------------------------------------------------------------------

/*
Class C_3
*/

load "ClassC3.m";

// ------------------------------------------------------------------------------------------------------------

/*
Class C_6
*/

/*
The group of type C_6 isomorphic to 2^{1+4}O_4(2)
*/
S17 := SymplecticGroup(4,17);
ms := MaximalSubgroups(S17);
G := Random( [H`subgroup : H in ms | #H`subgroup eq 3840] );

ct := CharacterTable(G);
chi := ct[5];

"======= 2^{1+4}O_4(2) =======";
"== Character table ==";
ct;
"== Hasse subgroups ==";
AG := PrintInformation(G, chi : CongruenceCondition := [* [1, 7], 8 *] );

RunTest(AG);

/*
The group of type C_6 isomorphic to 2^{1+4} \Omega_4(2)
*/
S11 := SymplecticGroup(4,11);
ms := MaximalSubgroups(S11);
G := Random( [H`subgroup : H in ms | #H`subgroup eq 1920] );
ct := CharacterTable(G);
chi := ct[4];

"======= 2^{1+4} \Omega_4(2) =======";
"== Character table ==";
ct;
"== Hasse subgroups ==";
AG := PrintInformation(G, chi : CongruenceCondition := [* [3, 5], 8 *] );

RunTest(AG);

// ------------------------------------------------------------------------------------------------------------

/*
Class S
*/

/* Group of type 2.A6 */
S5 := SymplecticGroup(4,5);
ms := MaximalSubgroups(S5);
ms := [ H`subgroup : H in ms | #H`subgroup eq Factorial(6) ];
G := Random(ms);
ct := CharacterTable(G);

"======= 2.A_6 =======";
"== Character table ==";
ct;
"== Hasse subgroups, representation ct[2] ==";
AG := PrintInformation(G, ct[2] : CongruenceCondition := [* [5, 7], 12 *] );

RunTest(AG);

"== Hasse subgroups, representation ct[3] ==";
AG := PrintInformation(G, ct[3] : CongruenceCondition := [* [5, 7], 12 *] );

RunTest(AG);

/* Group of type 2.S6 */
S11 := SymplecticGroup(4,11);
ms := MaximalSubgroups(S11);
ms := [ H`subgroup : H in ms | #H`subgroup eq 2*Factorial(6) ];
G := Random(ms);
ct := CharacterTable(G);
chi := ct[5];

"======= 2.S_6 =======";
"== Character table ==";
ct;
"== Hasse subgroups ==";
AG := PrintInformation(G, chi : CongruenceCondition := [* [1, 11], 12 *] );

RunTest(AG);


/*
The groups of type Sym^3(E), with E exceptional in SL_2(F_\ell)
*/

/*
Sym^3 SL_2(3)
*/
G := SL(2,3);
ct := CharacterTable(G);
chi := ct[4];
V := GModule(chi);
V3 := SymmetricPower(V,3);
ch := Character(V3);

"======= Sym^3 SL_2(F_3) =======";
"== Character table ==";
ct;
"== Hasse subgroups ==";
AG := PrintInformationModule(G, V3);

RunTest(AG);

/*
Sym^3 2.S_4^-
*/
S7 := SL(2,7);
ms := MaximalSubgroups(S7);
G := Random( [H`subgroup : H in ms | #H`subgroup eq 48] );

ct := CharacterTable(G);
chi := ct[4];
V := GModule(chi);
V3 := SymmetricPower(V,3);
ch := Character(V3);

"======= Sym^3 2.S_4^- =======";
"== Character table ==";
ct;
"== Hasse subgroups ==";
AG := PrintInformationModule(G, V3 : CongruenceCondition := [* [1, 7] , 8 *] );

RunTest(AG);

/*
Sym^3 SL_2(5)
*/
G := SL(2,5);
ct := CharacterTable(G);
chi := ct[2];
V := GModule(chi);
V3 := SymmetricPower(V,3);
ch := Character(V3);

"======= Sym^3 SL_2(F_5) =======";
"== Character table ==";
ct;
"== Hasse subgroups ==";
AG := PrintInformation(G, ch : CongruenceCondition := [* [1, 9], 10 *] );

RunTest(AG);

quit;