/*
Given a group G, returns a subset of Aut(G) whose elements
represent all classes in Out(G). If the parameter order is
set to a positive value, only return representatives for
those classes that have the given order in Out(G) and such
that, furthermore, the order of the representative is equal
to the order of the outer automorphism it represents.
*/
function GetOuterAutomorphismsRepresentatives(G : order := 0)
	A := AutomorphismGroup(G);
	m, B := PermutationRepresentation(A);
	InnerAutos := [ m(a) : a in InnerGenerators(A) ];
	OuterAutoGroup, pi := B/sub<B | InnerAutos>;
	OuterAut := [];
	for o in OuterAutoGroup do
		if order eq 0 or Order(o) eq order then
			Append(~OuterAut, o);
		end if;
	end for;
	AutRepresentatives := [];
	AlreadyFound := [];
	for b in B do
		if pi(b) in OuterAut and not pi(b) in AlreadyFound then
			if order eq 0 or Order(b) eq order then
				Append(~AlreadyFound, pi(b));
				Append(~AutRepresentatives, Inverse(m)(b));
			end if;
		end if;
	end for;

	return AutRepresentatives;
end function;

/*
Given the list of irreducible characters Partialct and
the non-negative integer degree, recursively construct
all characters of the given degree that can be obtained
as sums of characters in Partialct. The algorithm is
recursive: if the first character has dimension d, then
its multiplicity must be between 0 and [degree/d]. For
each possible multiplicity, we call back the same
function after removing the first element from Partialct
*/
function BuildCombinationsWithGivenDegree(Partialct, degree)
	if #Partialct eq 0 or degree eq 0 then
		return [0];
	end if;
	d := Partialct[1][1];
	Results := [];
	for i in [0..Floor(degree/d)] do
		PartialResults := [ i*Partialct[1] + c : c in BuildCombinationsWithGivenDegree( [ Partialct[j] : j in [2..#Partialct] ] , degree-d*i) ];
		PartialResults := [ c : c in PartialResults | c[1] eq degree ];
		Results := Results cat PartialResults;
	end for;
	return Results;
end function;

/*
On input:
- a positive integer d
- a group G
- a group G_0
- an embedding of G_0 into G
- a character chi of G_0
constructs all d-dimensional representations V of G with
the property that the characters \chi' appearing in V,
when restricted to (the copy inside G of) G_0, appear
as summands of \chi. In particular, the representations
thus found contain all the representation of G that,
when restricted to G_0, coincide with \chi.
*/
function AllCharactersOfDegreeWithGivenRestriction(d, G, G0, embeddingG0, chi)
	ComputedCharacters := [];
	ct := CharacterTable(G);
	Partialct := [ c : c in ct | &+[ c(embeddingG0(g0)) * ComplexConjugate(chi(g0)) : g0 in G0 ] ne 0 ];

	return BuildCombinationsWithGivenDegree(Partialct, d);
end function;

/*
Given a group G_0 and two characters \chi_1, \chi_2 of G_0,
of degree 2, consider G_0 x G_0 as acting on a vector
space of dimension 4 as the direct sum of V_1 and V_2, the
representations corresponding to \chi_1, \chi_2. The next function
return all groups G abstractly isomorphic to some semi-direct product
(G_0 x G_0) semidirect Z/2Z, together with the list of all
representations V of G such that, upon restriction to G_0 x G_0,
V decomposes as V_1 \oplus V_2 as a representation of G_0 x G_0,
and such that elements in the non-trivial coset of G_0 x G_0
inside G act by exchanging the two subspaces V_1, V_2 (in particular,
such elements act with trace 0).
*/
function ConstructDoubleRepresentationWreathProduct(G0, chi1, chi2)
	// Book-keeping: MAGMA can only
	// perform certain group-theoretic
	// computations on permutation groups,
	// as opposed to general abstract groups
	// So we start by finding an isomorphism
	// from G_0 to a permutation group G_2
	G1, c1 := FPGroup(G0);
	G2, c2 := PermutationGroup(G1);
	i1 := Inverse(c1);
	i2 := Inverse(c2);

	Doubles := [* *];		// store the possible groups G
	DoubleCharacters := [* *];	// store the corresponding characters
	C2 := CyclicGroup(2);		// the cyclic group of order 2; will be used to construct the semidirect product
	G, m := DirectProduct(G2, G2);	// the group G_0 x G_0, represented as a permutation group
	m1, m2 := Explode(m);		// the two embeddings of G_0 in G_0 x G_0
	A := AutomorphismGroup( G );	// the automorphism group of G_0 x G_0; will be used to construct the semidirect product
	ct := CharacterTable(G);	// the character table of G_0 x G_0
	time chiGmult := [ 1/#G * &+[ (chi1(g1) + chi2(g2)) * ComplexConjugate( c(m1(c2(i1(g1)))*m2(c2(i1(g2)))) ) : g1 in G0, g2 in G0 ] : c in ct ];
	chiG := &+[ ct[i] * chiGmult[i] : i in [1..#ct] ];
					// compute \chi_1 + \chi_2 as a character of G_0 x G_0
					// This is done by taking the scalar products < \chi_1(g_1) + \chi_2(g_2), \chi( m_1(g_1) * m_2(g_2) )>
					// and then re-summing the characters of G_0 x G_0 with the correct multiplicities.
					// The complicated expression m1(c2(i1(g1)))*m2(c2(i1(g2))) takes charge of converting
					// between the abstract group G_0 x G_0 and the corresponding permutation group.
		
	outaut := GetOuterAutomorphismsRepresentatives(G : order := 2);		// the automorphisms of order 2 used to build the semi-direct product
	outaut := [ o : o in outaut | AutomorphismStabilisesCharacter(G, chiG, o) ];	// if G is of the type we want, then
											// the "external" automorphism becomes conjugation by
											// a certain matrix in the representation V; as a
											// consequence, this automorphism should stabilise the
											// character \chi_1 + \chi_2

	outaut := outaut cat [ outaut[1]^Order(outaut[1]) ];				// we add the "identity" automorphism to the list of the
											// possible automorphisms to consider (even though this
											// should not be necessary)

	for o in outaut do								// we loop over all the order-2 automorphisms of G_0 x G_0,
		f := hom< C2->A | [ o ] >;						
		Gdouble, embeddingG := SemidirectProduct(G, C2, f);			// construct the corresponding semidirect product,
		Append(~Doubles, [* Gdouble, embeddingG *]);				// and add the group G thus constructed (together with the
											// embedding of G_0 x G_0 into G) to the list Doubles.
	end for;



	for Gdouble in Doubles do							// we now loop over all possible groups G
		allreps := AllCharactersOfDegreeWithGivenRestriction(4, Gdouble[1], G, Gdouble[2], chiG);	// and compute all 4-dimensional representations
														// of G that could possibly restrict to \chi_1+\chi_2
														// on G_0 x G_0
		for rep in allreps do										// For each such representation, we test that
			if &and[ rep(Gdouble[2](g)) eq chiG(g) : g in G ] and &and[ rep(g) eq 0 : g in Gdouble[1] | not g in Image(Gdouble[2]) ] then	// the restriction to G_0 x G_0 is indeed the correct one, and the character of the restriction to the non-trivial coset is identically 0
				// "Found one with the correct restriction";
				if IsSymplecticCharacter(rep, Gdouble[1]) and IsFaithfulCharacter(rep, Gdouble[1]) then		// if in addition the 4-dimensional representation is faithful and symplectic,
					Append(~DoubleCharacters, [* Gdouble, rep *]);						// we add it to the list of those to be returned
				end if;
			end if;
		end for;
	end for;
	return DoubleCharacters;
end function;



/*
On input the finite group G1, return the list of (isomorphism classes of)
finite groups G such that G contains a subgroup of index 2 isomorphic to
G1. If the parameter TestEigenvalues is set to true, then it only returns
the groups that satisfy the following additional property: every element
that is in G but not in the subgroup isomorphic to G1 should have order
whose 2-adic valuation is greater than the 2-adic valuation of \ell-1,
where \ell is a prime satisfying the congruence conditions encoded by the
parameter congruence.
The reason why this is meaningful is as follows: elements in G\G_1 are of
the form \sqrt{\delta} * g_1, where g_1 has a rational eigenvalue \mu.
The eigenvalue \sqrt{\delta} * \mu, raised to the power (\ell-1), is equal
to -1. This implies that the 2-adic valuation of such an eigenvalue is
1 more than the 2-adic valuation of (\ell-1).
In particular, at least half the elements of G should have an eigenvalue
the 2-part of whose order is 2^{v_2(\ell-1) + 1}, and this implies that
those same elements have order whose 2-part is divisible by
2^{v_2(\ell-1) + 1}
*/
function ConstructDoubleGroups(G1, congruence : TestEigenvalues := true)
	TwoAdicValuation := Min( [Valuation(congruence[2], 2)] cat [Valuation(k-1, 2) : k in congruence[1]]);	// a lower bound for v_2(\ell-1)

	n := 2*#G1;	// the order of G

	gs := [* SmallGroup(n, i) : i in [1..NumberOfSmallGroups(n)] *];	// the list of all isomorphism classes
										// of groups of order n

	if TestEigenvalues then
		gs := [* g : g in gs | #[ h : h in g | Valuation(Order(h), 2) ge TwoAdicValuation+1 ] ge #G1 *];	// only keep those groups for which
															// the condition on the 2-parts of the
															// orders of the elements is satisfied
	end if;


	Doubles := [* *];	// store the possible groups G

	for Gtilde in gs do	// loop over the possibilities
		ms := MaximalSubgroups(Gtilde);		// Look for subgroups isomorphic to G_1; any subgroup of index 2 is normal
		for m in ms do
			if IsIsomorphic(m`subgroup, G1) then
				_, isom := IsIsomorphic(G1, m`subgroup);
				Append(~Doubles, [* Gtilde, isom *]);
			end if;
		end for;
	end for;
	return Doubles;
end function;



/*
On input
- a group G
- a complex character chi of G
- a congruence condition on the prime \ell
- a parameter TestEigenvalues
construct all pairs (G', chi') such that:
- G' contains G with index 2
- the restriction of chi' to G is chi
- if TestEigenvalues is set to true, G' satisfies the
  condition on eigenvalues in the previous function
*/
function ConstructDoubleRepresentation(G, chi, congruence : TestEigenvalues := true)
	DoubleCharacters := [* *];
	Doubles := ConstructDoubleGroups(G, congruence : TestEigenvalues := TestEigenvalues);	// list the possible groups G'

	for Gdouble in Doubles do	// we now loop over all possible groups G'
		allreps := AllCharactersOfDegreeWithGivenRestriction(4, Gdouble[1], G, Gdouble[2], chi); 	// and compute all 4-dimensional representations of
														// G' that could possibly restrict to \chi on G

		for rep in allreps do		// For each such representation, we test that
			if &and[ rep(Gdouble[2](g)) eq chi(g) : g in G ] then	// the restriction to G is indeed the correct one
				// "Found one with the correct restriction";
				if IsSymplecticCharacter(rep, Gdouble[1]) and IsFaithfulCharacter(rep, Gdouble[1]) then		// if in addition the 4-dimensional representation is faithful and symplectic,
					Append(~DoubleCharacters, [* Gdouble, rep *]);						// we add it to the list of those to be returned

				end if;
			end if;
		end for;
	end for;
	return DoubleCharacters;
end function;

/*
Given
- a group G'
- an embedding of a group G into G', where |G'| = 2|G|
- the character chidouble of a representation of G'
- a congruence condition on the prime \ell
tests property (P2), i.e., checks that G' \ G contains
an element whose eigenvalues (in the mod-\ell representation
afforded by the reduction modulo \ell of \chi_double) have
multiplicative orders whose 2-adic valuations are all
different from v_2(\ell-1)+1.
*/
function TestCannotExtend(Gdouble, embeddingG, chidouble, congruence)
	TwoAdicValuation := Min( [Valuation(congruence[2], 2)] cat [Valuation(k-1, 2) : k in congruence[1]]);
	NontrivialCoset := [g : g in Gdouble | not g in Image(embeddingG)];
	Charpolys := [* CharacteristicPolynomialFromCharacter(chidouble, g) : g in NontrivialCoset *];
	// print Charpolys;
	OrdersRoots := { CongruenceConditionOneRoot(p) : p in Charpolys };
	OrdersRoots;
	for o in OrdersRoots do
		if Max( [Valuation(oRoot, 2) : oRoot in o ] ) le TwoAdicValuation then
			return true;
		end if;
	end for;
	return false;
end function;


/*
Given a group G, the character \chi of a representation of G,
and a congruence condition on the prime \ell, tests if the
group G has property (P2) of the Appendix.
*/
function TestViaConstructingDoubleGroups(G, chi, congruence)
	congruence := [* { congruence[2] }, congruence[1] *];
	drep := ConstructDoubleRepresentation(G, chi, congruence);
	return &and[ TestCannotExtend(d[1][1], d[1][2], d[2], congruence) : d in drep ];	
end function;

