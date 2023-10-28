G0 := SL(2,3);
ct := CharacterTable(G0);
chi := ct[4];

/*
G_0 = SL_2(F_3) acts via a 2-dimensional irreducible representation and
its dual. The representation in question is ct[5]+ct[6]; as a test, we
also consider ct[4] + ct[4].

In the paper, we prove that G is a group with [G:G_0]=2, so we rely on
our functionalities to compute all groups G with this property and all
representations that, restricted to G_0, coincide with the given
representation of G_0
*/

cdr := ConstructDoubleRepresentation(G0, 2*chi, [* {2}, 3 *] : TestEigenvalues := false );

for c in cdr do
	// Conditions for the representation in question to be defined over F_\ell
	CongruenceCondition := SplitPrimesAndConductor(FieldOfTraces(c[2]));
	CongruenceCondition := CombineCongruences( CongruenceCondition, [* {2}, 3 *] );	// In the paper we prove that \ell is 2 mod 3
	V := GModuleFromCharacter(c[2], c[1][1] );
	AG := PrintInformationModule( c[1][1], V : CongruenceCondition := CongruenceCondition ); 
	RunTest(AG);
end for;

cdr := ConstructDoubleRepresentation(G0, ct[5]+ct[6], [* {2}, 3 *] : TestEigenvalues := false );

for c in cdr do
	// Conditions for the representation in question to be defined over F_\ell
	CongruenceCondition := SplitPrimesAndConductor(FieldOfTraces(c[2]));
	CongruenceCondition := CombineCongruences( CongruenceCondition, [* {2}, 3 *] );	// In the paper we prove that \ell is 2 mod 3
	V := GModuleFromCharacter(c[2], c[1][1] );
	AG := PrintInformationModule( c[1][1], V : CongruenceCondition := CongruenceCondition ); 
	RunTest(AG);
end for;
