/*
Functions pertaining the study of Hasse groups
*/

/*
Let G be a finite group and V be a complex representation of G.
Let rho : G --> GL(V) be the representation homomorphism. Since
the order of every g in G is finite, the roots of charpoly(\rho(g))
are all roots of unity, say of orders o_1, ..., o_r. In particular, 
charpoly(rho(g)) has a root modulo p if and only if F_p contains
a primitive root of unity whose order lies in the set {o_1, ...,
o_r}. In turn, this happens iff p is congruent to 1 modulo one
of the values o_1, ..., o_r.
On input (G,V), the next function returns a minimal list 
{m_1, ..., m_k} with the property that charpoly(rho(g)) has at
least one F_p-rational eigenvalue iff p is 1 modulo one of the
integers m_1, ..., m_k.

In all our applications, the list of integers returned by
this function consists of a single number.
*/
function CongruenceConditionEigenvalues(G, V)
	rho := GModuleAction(V);

	/*
	Let g_1, ..., g_{|G|} be an enumeration of the elements of G.
	We start by building a list of lists [m_{i,1}, ..., m_{i,l_i}]
	with the property that charpoly(rho(g_i)) has an F_p-rational
	eigenvalue iff p is 1 modulo at least one of the integers 
	m_{i,1}, ..., m_{i, l_i}. To shorten the computation, we
	actually work with conjugacy classes of elements in G.
	*/
	Conds := [];
	
	ConjClass := ConjugacyClasses(G);

	for g in ConjClass do
		p := CharacteristicPolynomial(rho(g[3]));
		Append(~Conds, CongruenceConditionOneRoot(p));
	end for;

	/*
	Next we build a list of integers {m_1, ..., m_k} such that
	every charpoly(rho(g_i)) has an F_p-rational eigenvalue iff
	p is congruent to 1 modulo one of the integers m_i. To this end
	we notice that an integer m should appear in this list iff for
	every i the list [ m_{i,1}, ..., m_{i, l_i} ] contains a divisor
	of m. As a consequence, we may only test integers m up to
	the LCM of all the m_{i,j}.
	*/
	MaxModule := LCM( [ LCM(c) : c in Conds ] );
	GoodConds := [];
	for i in [1..MaxModule] do
		if &and[ #( SequenceToSet(Divisors(i)) meet Conds[j]) ne 0 : j in [1..#Conds] ] then
			Append(~GoodConds, i);
		end if;
	end for;

	/*
	Finally, we purge the list of unnecessary items. Notice that
	if m, m' both appear in the list GoodConds, and m divides m',
	then m' may be omitted (indeed if p is congruent to 1 modulo
	m', then a fortiori it is 1 modulo m, and since m \in GoodConds 
	we know that charpoly(rho(g)) has a root in F_p).
	*/
	FinalConds := [];
	for i in GoodConds do
		if #(SequenceToSet(Divisors(i)) meet SequenceToSet(FinalConds)) eq 0 then
			Append(~FinalConds, i);
		end if;
	end for;

	return FinalConds;
end function;

/*
Let G be a finite group and fix a representation
rho : G --> GL(V) of G.
A "candidate" is a triple (H, cc, FDS), where:
- H is an element of the poset of conjugacy classes of
  subgroups of G;
- cc is a list of positive integers with the property 
  that rho(h) has at least one root in F_p for all h
  in the subgroup H iff the prime p is congruent to 1
  modulo one of the integers in cc;
- FDS is a list of pairs of the form
  [ [m_{i,1}, ..., m_{i, k_i} ], c_i ]
  with the property that the the restriction of V to H
  is reducible over F_p if and only if p is congruent
  to m_{i,j} modulo c_i for some i, j.

On input (G, V), the next function outputs the list of 
all candidates corresponding to subgroups H of G such 
that there exists at least one prime p for which rho(H),
reduced modulo p, is a Hasse subgroup.

We also include a version with input the character of V
instead of V itself.
*/
function ListCandidatesModule(G, V)
	ct := CharacterTable(G);
	lat := SubgroupLattice(G);

	Candidates := [* *];

	for PosetElement in lat do								// loop over conjugacy classes of subgroups of G
		H := Group(PosetElement);							// build a subgroup representing the conjugacy class
		if #H gt 1 then									// the trivial subgroup is never Hasse
			// GroupName(H);								// print a description of the group H
			VH := Restriction(V, H);						// consider the restriction of V to H
			cc := CongruenceConditionEigenvalues(H, VH);				// compute the congruence conditions for the existence of eigenvalues

			// "The eigenvalues are rational if \ell is congruent to 1 modulo", cc;

			cH := Character(VH);
			FDS := AllSubfieldsDefinition(cH, H);					// compute the congruence conditions for the reducibility of V_H modulo p
			
			// "The restriction of V to H becomes reducible if \ell is in one of the following congruence classes", FDS;
			if &or[ &or[i[2] in Divisors(c) : i in FDS] : c in cc ] then
				// "V_H is not irreducible whenever the eigenvalues are rational";
			else
				Append(~Candidates, [* PosetElement, cc, FDS *]);
			end if;
		end if;
	end for;
	return Candidates;
end function;

function ListCandidates(G, chi)
	V := GModule(chi);
	return ListCandidatesModule(G, V);
end function;




/*
The next function is essentially one of bookkeeping: it
rewrites the information in the output of ListCandidates
modulo a single positive integer M.

Given a list of candidates as above, it returns a pair
L, M, where M is a positive integer and L is a list of
pairs of the form [ H_i, {c_{i,1}, ..., c_{i,k_i}} ].
Here the H_i are (conjugacy classes of) subgroups of G,
that are Hasse precisely modulo those primes that are
congruent to one of the integers c_{i,j} modulo M.
*/
function UnifyCongruenceConditions(Candidates)
	RelevantMod := 1;

	/*
	We start by taking the LCM of all the congruence
	conditions in the list Candidates
	*/
	for Candidate in Candidates do
		RelevantMod := LCM(RelevantMod, LCM(Candidate[2]) );
		if #Candidate[3] ne 0 then
			DecompCond := Candidate[3];
			DecompCond := [ DC[2] : DC in DecompCond ];
			RelevantMod := LCM(RelevantMod, LCM(DecompCond));
		end if;
	end for;

	/*
	Build a new list by rewriting all the congruence conditions
	modulo the integer RelevantMod computed above. Note that
	all congruence classes that are not coprime to RelevantMod
	are discarded since they can contain at most one prime number.
	*/
	UpdatedCandidates := [* *];

	for Candidate in Candidates do
		GoodPrimesCandidate := [i : i in [1..RelevantMod] | &or[ i mod MM eq 1 : MM in Candidate[2] ] and GCD(i, RelevantMod) eq 1 ];	// primes that satisfy the
																	// congruence condition that
																	// ensures the existence of
																	// F_p-rational eigenvalues
		DecompCond := Candidate[3];
		GoodPrimesCandidate := [ p : p in GoodPrimesCandidate | &and[ not(p mod DC[2] in DC[1]) : DC in DecompCond ] ];		// filter out the primes that
																	// do not satisfy the
																	// condition for irreducibility
		Append(~UpdatedCandidates, [* Candidate[1], GoodPrimesCandidate *]);
	end for;

	return UpdatedCandidates, RelevantMod;
end function;



/*
The next function takes as input a finite group G, a G-module V 
corresponding to a representation rho : G --> GL(V), and a congruence
condition on primes (given as a pair [{c_1, ..., c_r}, m]), and prints
information on maximal Hasse subgroups of rho(G). In particular, it
outputs an integer M such that the collection of Hasse subgroups of
rho(G) mod p only depends on p mod M, and for each class c mod M, a list
of the maximal Hasse subgroups of rho(G) mod p.

If CongruenceCondition is given, only those primes p that satisfy
p \equiv c_i mod m for some i=1,...,r are listed in the output. It is
assumed that m | M.

We also include a version taking as input the character of V instead of
the module itself.

Finally, even though the function only prints information about the
maximal Hasse subgroups, it returns a complete list of ALL Hasse subgroups,
which can then be fed to the test of Lemma 5.3
*/
function PrintInformationModule(G, V : CongruenceCondition := [* [0], 1 *] )
	AllHasseGroups := [* *];
	Candidates := ListCandidatesModule(G, V);									// compute a full list of candidates

	UpdatedCandidates, RelevantMod := UnifyCongruenceConditions(Candidates);				// compute the integer M
	PrimeCongruenceClasses := [ i : i in [1..RelevantMod] | GCD(i,RelevantMod) eq 1 and i mod CongruenceCondition[2] in CongruenceCondition[1] ];	
														// residue classes prime to M
														// that satisfy the congruence condition

	"The answer depends on p modulo", RelevantMod;
	for p in PrimeCongruenceClasses do
		InterestingGroups := [ cand[1] : cand in UpdatedCandidates | p in cand[2] ];			// loop over subgroups that are of class
														// (L) when reduced modulo p
		GroupsForP := [];
		for H1 in InterestingGroups do
			Append(~AllHasseGroups, [* Group(H1), Restriction(V, Group(H1)), [RelevantMod, p] *] );
			if &and[ not( H1 le H2 ) : H2 in InterestingGroups | H2 ne H1 ] then			// test for maximality
				Append(~GroupsForP, H1 );
			end if;
		end for;

		if #GroupsForP ne 0 and ( p mod CongruenceCondition[2] in CongruenceCondition[1] ) then		// if there are Hasse subgroups
														// and furthermore p satisfies the given
														// congruence conditions
			"p \equiv", p, "mod", RelevantMod;
			[GroupName(Group(H)) : H in GroupsForP];						// print a description, the cardinality and
			"Orders", [#(Group(H)) : H in GroupsForP];						// the exponent of each of the maximal subgroups
			"Exponents", [Exponent(Group(H)) : H in GroupsForP];					
		end if;
	end for;
	return AllHasseGroups;
end function;

function PrintInformation(G, chi : CongruenceCondition := [* [0], 1 *] )
	V := GModule(chi);
	return PrintInformationModule(G, V : CongruenceCondition := CongruenceCondition);
end function;
