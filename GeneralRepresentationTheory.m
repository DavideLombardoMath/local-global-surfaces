/*
General representation-theoretic functions
*/

/*
Compute the scalar product of the complex
characters chi_1, chi_2 of the finite
group G
*/
function CharactersScalarProduct(chi1, chi2, G)
	cG := Classes(G);
	return 1/#G * &+[ chi1[i]*ComplexConjugate(chi2[i])*cG[i][2] : i in [1..#cG] ];
end function;

/*
Given a complex character ch of the finite
group G, returns a sequence a_i of non-negative
integers such that ch = \sum a_i \chi_i, where
\chi_i are the irreducible complex characters
of G, in the order in which they appear in
the character table of G.
*/
function DecomposeCharacter(ch, G)
	ct := CharacterTable(G);
	return [ CharactersScalarProduct(ch, c, G) : c in ct ];
end function;

/*
Given a complex character chi of a finite group,
compute the minimal field extension of Q that
contains the image of that character. This is
closely related to the minimal field of definition 
of the corresponding representation, see the
on p. 108 of Serre's book Représentations linéaires
des groupes finis.
*/
function FieldOfTraces(chi)
	K := BaseRing(chi);
	L := sub<K | [ K!chi[i] : i in [1..#chi] ]>;
	return L;
end function;

/*
Given a complex character chi of the finite group
G, let V be the corresponding complex representation.
The next function returns the characters of all the
subrepresentations W of V that are different from
{0} and V itself.
*/
function AllProperSubcharacters(chi, G)
	ct := CharacterTable(G);
	IrrepMultiplicities := DecomposeCharacter(chi, G);		// multiplicities of the irreducible characters in V
	assert #ct eq #IrrepMultiplicities;
	CP := CartesianProduct([ [0..i] : i in IrrepMultiplicities ]);	// in every subrep, a character chi appears a number
									// of times that is between 0 and the multiplicity
									// of chi in V
	Subchars := [ &+[ c[j] * ct[j] : j in [1..#IrrepMultiplicities] ] : c in CP ];
	return [ Subchars[i] : i in [2..#Subchars-1] ];	// skip 0 and chi itself
end function;

/*
Let chi be a complex character of the finite group G, and
let V be the corresponding complex representation.
Let W be a subrepresentation of V defined over C, and let
chi_W be its character. Let K be the minimal field containing
the image of chi_W; it is a subfield of a cyclotomic field,
hence in particular an abelian number field.
If the rational prime p splits completely in K, then the
reduction of chi_W modulo p takes values in F_p. Since over
finite fields the minimal field of definition of a
representation coincides with the minimal field containing
the values of the corresponding character (see again p.108
of Serre's book and recall that finite fields have trivial
Brauer group), it follows that W can be defined over F_p,
and conversely, that if W can be defined over F_p, then p
splits (completely, since K/Q is abelian) in K.

On input (chi, G), the next function returns a list of pairs
[ [c_{i,1}, ..., c_{i,k_i}], m_i ] with the following property:
a subrepresentation of the representation corresponding to chi
can be defined over the finite field F_p (p prime) if and
only if p is congruent to c_{ij} modulo m_i, for some
indices i and j. The correctness of the algorithm follows
from the above discussion.
*/
function AllSubfieldsDefinition(chi, G)
	SubChars := AllProperSubcharacters(chi,G);
	FieldsOfDef := [* FieldOfTraces(s) : s in SubChars *];

	return [* SplitPrimesAndConductor(A) : A in FieldsOfDef *];
end function;

/*
Construct the G-module corresponding to a (not necessarily irreducible)
complex character chi of G. Guaranteed to work only if chi is the sum
of at most 2 irreducible characters (this suffices for our applications).
*/
function GModuleFromCharacter(chi, G)
	multiplicities := DecomposeCharacter(chi, G);
	summands := [];
	ct := CharacterTable(G);

	for i in [1..#ct] do
		summands := summands cat [ GModule(ct[i]) : j in [1..multiplicities[i]] ];
	end for;

	Rs := [BaseRing(s) : s in summands];
	if #Rs gt 1 then
		R := Compositum(Rs[1], Rs[2]);
	else
		R := Rs[1];
	end if;

	return DirectSum( [ChangeRing(s, R) : s in summands] );
end function;

/*
Given a complex character chi of the group G,
corresponding to a representation V, computes
the character of \Lambda^2(V). Based on the
formula
2\chi_{\Lambda^2(V)}(g) = \chi(g)^2 - \chi(g^2)
*/
function ExteriorSquareCharacter(chi, G)
	ct := CharacterTable(G);
	mults := [ 1/#G * &+[ 1/2*(chi(g)^2-chi(g^2))*ComplexConjugate(chi2(g)) : g in G ] : chi2 in ct ];
	return &+[ mults[i] * ct[i] : i in [1..#ct] ];
end function;

/*
Given a complex character chi of the group G,
corresponding to a representation V, computes
the character of the dual of V. We achieve
this by computing the scalar product of
\overline{\chi} with all irreducible characters
of G, and then re-summing the relevant
characters with the correct multiplicities.
*/
function DualCharacter(chi, G)
	ct := CharacterTable(G);
	mults := [ 1/#G * &+[ ComplexConjugate(chi(g))*ComplexConjugate(chi2(g)) : g in G ] : chi2 in ct ];
	return &+[ mults[i] * ct[i] : i in [1..#ct] ];
end function;

/*
On input (chi, G), returns true if and only if
the character chi comes from a faithful complex
representation of the group G. The test is
performed by listing the irreducible characters
that intervene in \chi, writing down an irreducible
module for each of them (including the map giving
the action), computing the kernel of the action
for each irreducible submodule, and intersecting
these kernels.
*/
function IsFaithfulCharacter(chi, G)
	mult := DecomposeCharacter(chi, G);	// multiplicities of the irreducible characters of G in chi
	ct := CharacterTable(G);		// list of irreducible characters
	chars := [ct[i] : i in [1..#ct] | mult[i] ne 0];	// irreducible characters that appear in chi
	Gmods := [GModule(c) : c in chars];			// and their corresponding G-modules
	kers := [Kernel(GModuleAction(V)) : V in Gmods];	// Compute the kernels of the irreducible G-module
	GlobalKer := G;
	for k in kers do
		GlobalKer := GlobalKer meet k;			// Take the intersection of the kernels
	end for;
	return #GlobalKer eq 1;					// The representation is injective iff the intersection 
								// of the kernels is trivial
end function;

/*
On input (chi, G), returns true if and only if
the character chi comes from a symplectic complex
representation of the group G. This happens if
and only if Lambda^2(V*) contains a copy of the
trivial representation.
*/
function IsSymplecticCharacter(chi, G)
	chiVStar2 := ExteriorSquareCharacter(DualCharacter(chi, G), G);
	return DecomposeCharacter(chiVStar2, G)[1] ne 0;
end function;

/*
Given a character chi (of a group G) and an element g
of G, compute the characteristic polynomial of \rho(g),
where \rho is the complex representation with character
chi. Based on the fact that, if \lambda_1, .., \lambda_d
are the eigenvalues of \rho(g), then \lambda_i^k are
the eigenvalues of \rho(g^k). Thus, we can compute the
Newton sums of the eigenvalues by simply evaluating
chi(g^k) for k=1, ..., d = degree of \chi, and then use
these to recover the elementary symmetric functions in
the eigenvalues, that is, the coefficients (up to sign)
of the characteristic polynomial.
*/
function CharacteristicPolynomialFromCharacter(chi, g)
	R<x> := PolynomialRing(FieldOfTraces(chi));
	G := Parent(g);
	d := chi(Id(G));
	powersums := [ chi(g^k) : k in [1..d] ];
	return R!PowerSumToCoefficients(powersums);
end function;
