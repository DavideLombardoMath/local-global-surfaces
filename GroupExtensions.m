/*
Given a group G, returns a subset of Aut(G) whose elements
represent all classes in Out(G). If the parameter order is
set to a positive value, only return representatives for
those classes that have the given order in Out(G)
*/
function GetOuterAutomorphisms(G : order := 0)
	A := AutomorphismGroup(G);
	m, B := PermutationRepresentation(A);
	// InnerAutos := [ b : b in B | IsInner(Inverse(m)(b)) ];
	InnerAutos := [ m(a) : a in InnerGenerators(A) ];
	OuterAutoGroup, pi := B/sub<B | InnerAutos>;
	OuterReps := [];
	for o in OuterAutoGroup do
		if order eq 0 or Order(o) eq order then
			Append(~OuterReps, Inverse(pi)(o));
		end if;
	end for;

	return [Inverse(m)(b) : b in OuterReps];
end function;



/*
Auxiliary function; see NoEigenvalueRaisesToMinusOne for a description
*/
function TestSingleEigenvalue(order, congruence)

	if order eq 1 then
		return true;
	end if;

	M := congruence[1];
	m := congruence[2];
	// Next we check whether the congruence condition
	// gives us the exact 2-adic valuation of (p-1)
	ExactValuationKnown := false;
	if Valuation(m-1,2) lt Valuation(M,2) then
		ExactValuationKnown := true;
	end if;


	// We ignore the condition that the order
	// divides (p-1) and only check 2-adic
	// valuations

	if ExactValuationKnown then
		return Valuation(order, 2) eq Valuation(m-1, 2);
	else
		// if the 2-valuation of order is strictly
		// less than the 2-valuation of M, then
		// we can be sure that v_2(order) < v_2(p-1)
		return Valuation(order, 2) lt Valuation(M, 2);
	end if;

end function;

/*
Given a G-module V and an element
g of G, returns the list of the
multiplicative orders of the eigenvalues
of g acting on V
*/
function EigenvalueOrders(g, V)
	// first we get the characteristic polynomial of g in the given representation
	rho := GModuleAction(V);
	p := CharacteristicPolynomial(rho(g));	
	// then we return the orders of the roots of unity that are eigenvalues of p
	return CongruenceConditionOneRoot(p);
end function;

/*
Given a G-module V, an element g of G
and a congruence condition [M, m],
returns true if the following holds.
Consider the eigenvalues z_1, ..., z_r
of g acting on V. These will be roots of
unity of respective multiplicative orders
k_1, ..., k_n. This function returns true
if, given that p is congruent to m mod M,
no power z_i^((p-1)/2) is equal to -1.
Note that z_i^((p-1)/2) = -1 is equivalent
to the fact that the order k_i of z_i divides p-1,
together with the fact that v_2(k_i) = v_2(p-1).
*/
function NoEigenvalueRaisesToMinusOne(g, V, congruence)
	evo := EigenvalueOrders(g, V);
	return &and[ TestSingleEigenvalue(ev, congruence) : ev in evo ];
end function;


/*
Given a group H, a complex character chi of H, and an
automorphism phi of H, returns true if and only if
chi(phi(-))=chi(-). Notice that inner automorphisms
preserve all characters, so this is only relevant if
phi represents an outer automorphism.
*/
function AutomorphismStabilisesCharacter(H, chi, phi)
	return &and[ chi(h) - chi(phi(h)) eq 0 : h in H ];
end function;

/*
Given a group H, an H-module V, and a congruence condition
on the prime \ell, the next function test if the representation
of H afforded by V has property (P1), as defined and studied
in the Appendix
*/
function TestGroupCannotBeExtended(H, V, congruence)
	try
		outs := GetOuterAutomorphisms(H : order := 2);		// the outer automorphisms of H of order 2
		chi := Character(V);
		test := true;
		for phi in outs do						// for each outer automorphism of order 2
			if AutomorphismStabilisesCharacter(H, chi, phi) then	// that stabilises the representation V
				_, fp := IsInner(phi^2);			// we obtain an element f_p such that phi^2 is conjugation by f_p
				if fp ne Id(H) then				// if f_p is the identity, we are already done
					test := test and &or[ NoEigenvalueRaisesToMinusOne(x * phi(x) * fp, V, congruence) : x in H ];	// otherwise, we test property (P1)
				end if;
				if not test then
					return false, phi;
				end if;
			end if;
		end for;
		return test;
	catch e
		return false;
	end try;
end function;

