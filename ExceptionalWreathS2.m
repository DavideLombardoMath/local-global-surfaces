/*
We consider the subgroups of SL_2(F_\ell) \wr C_2
of exceptional type. All such groups are of the form
(G_0 x G_0) semidirect C_2, where G_0 is as in section
3.5 of the paper.
Indeed, let E be an exceptional subgroup of SL_2(F_\ell).
Arguing exactly as in Lemma 3.14, one sees that a
subgroup of SL_2 \wr C_2 which contains E x E and
has nontrivial image in C_2 must be a semi-direct
product (E x E) semidirect C_2.
/*

"=== SL_2(3) \wr S_2 ===";
G0 := SL(2,3);
ct := CharacterTable(G0);
ct;
chi1 := ct[4];
chi2 := ct[4];

*/
Upon restriction to G_0 x G_0, the representation
splits as the direct sum of two irreducible,
symplectic representations of dimension 2. The
only such representation for G_0 are those with
character ct[4].
*/

cdrwp := ConstructDoubleRepresentationWreathProduct(G0, chi1, chi2);

/*
We check that the two configurations found are in fact isomorphic,
so we only need to consider the first of the two
*/
assert #cdrwp eq 2;
G1 := cdrwp[1][1][1];
G2 := cdrwp[2][1][1];
test, isoG1G2 := IsIsomorphic(G1, G2);

chi1 := cdrwp[1][2];
chi2 := cdrwp[2][2];
assert &and[ chi1(g1) eq chi2(isoG1G2(g1)) : g1 in G1 ];

rep := cdrwp[1];
CongruenceCondition := SplitPrimesAndConductor(FieldOfTraces(rep[2]));	// condition for the representation to be defined over F_\ell
AG := PrintInformation( rep[1][1], rep[2] : CongruenceCondition := CongruenceCondition);
RunTest(AG);


"=== \widehat{S_4} \wr S_2 ===";
S := SL(2,7);
ms := MaximalSubgroups(S);
G0 := Random([ H`subgroup : H in ms | #H`subgroup eq 48 ]);

ct := CharacterTable(G0);
ct;

/*
In this case there are 2 symplectic degree-2 characters, listed as
ct[4] and ct[5] in the character table. In principle, we should
consider both the representation of G_0 x G_0 corresponding to 
ct[4] + ct[4], and the representation corresponding to ct[4] + ct[5];
however, both possibilities lead to isomorphic configurations:
*/
cdrwp4 := ConstructDoubleRepresentationWreathProduct(G0, ct[4], ct[4]);
cdrwp5 := ConstructDoubleRepresentationWreathProduct(G0, ct[4], ct[5]);
G4 := cdrwp4[1][1][1];
G5 := cdrwp5[1][1][1];
test, isoG4G5 := IsIsomorphic(G4, G5);
assert test;
chi4 := cdrwp4[1][2];
chi5 := cdrwp5[1][2];
assert &and[ chi4(g4) eq chi5(isoG4G5(g4)) : g4 in G4 ];

/*
Thus we only consider ct[4]+ct[5]
*/
chi1 := ct[4];
chi2 := ct[5];

cdrwp := ConstructDoubleRepresentationWreathProduct(G0, chi1, chi2);
// "Number of representations", #cdrwp;
for rep in cdrwp do
	CongruenceCondition := SplitPrimesAndConductor(FieldOfTraces(rep[2]));	// condition for the representation to be defined over F_\ell
	AG := PrintInformation( rep[1][1], rep[2] : CongruenceCondition := CongruenceCondition);
	RunTest(AG);
end for;



"=== SL_2(F_5) \wr S_2 ===";
G0 := SL(2,5);
ct := CharacterTable(G0);
ct;

/*
In this case there are 2 symplectic degree-2 characters, listed as
ct[2] and ct[3] in the character table. In principle, we should
consider both the representation of G_0 x G_0 corresponding to 
ct[2] + ct[3], and the representation corresponding to ct[2] + ct[3];
however, both possibilities lead to isomorphic configurations (to
find the isomorphism we consider all the automorphisms of G).
*/
cdrwp2 := ConstructDoubleRepresentationWreathProduct(G0, ct[2], ct[2]);
cdrwp3 := ConstructDoubleRepresentationWreathProduct(G0, ct[2], ct[3]);


G2 := cdrwp2[1][1][1];
G3 := cdrwp3[1][1][1];
test, isoG2G3 := IsIsomorphic(G2, G3);
assert test;
chi2 := cdrwp2[1][2];
chi3 := cdrwp3[1][2];

outaut := GetOuterAutomorphisms(G3);

assert &or[ &and[ chi2(g2) eq chi3(o(isoG2G3(g2))) : g2 in G2 ] : o in outaut ];

/*
Thus we only consider ct[2] + ct[3]
*/

chi1 := ct[2];
chi2 := ct[3];

cdrwp := ConstructDoubleRepresentationWreathProduct(G0, chi1, chi2);
// "Number of representations", #cdrwp;
for rep in cdrwp do
	CongruenceCondition := SplitPrimesAndConductor(FieldOfTraces(rep[2]));	// condition for the representation to be defined over F_\ell
	AG := PrintInformation( rep[1][1], rep[2] : CongruenceCondition := CongruenceCondition);
	RunTest(AG);
end for;

