/*
Arithmetic functions
*/

/*
Compute the multiplicative order of a root of unity
*/
function OrderRootUnity(zeta)
	d := Degree(Parent(zeta));
	n := 2*d^2;
	for i in [1..n] do
		if zeta^i eq 1 then
			return i;
		end if;
	end for;
	return 0;
end function;

/*
Given an abelian extension K of Q, compute its conductor c and
the residue classes modulo c which correspond to primes that
split completely in K.
The output is a pair [ [m_1, ..., m_k], c ], where c is the
conductor and m_1, ..., m_k are the residue classes of the
totally split primes.
*/
function SplitPrimesAndConductor(K)
	if Degree(K) eq 1 then		// special case: K = Q
		return [* [0], 1 *];
	end if;

	A := AbelianExtension(K);
	c := Norm(Conductor(A));
	result := [];
	for i in [ j : j in [1..c] | GCD(j,c) eq 1 ] do
		p := i;
		while not IsPrime(p) do				// compute the smallest prime in the residue class
			p := p + c;
		end while;
		if #DecompositionType(A,p) eq Degree(K) then	// check if p is totally split in K
			Append(~result, i);
		end if;
	end for;
	return [* result, c *];
end function;

/*
Given a polynomial p whose roots r_1, ..., r_n
are all roots of unity of some order, returns 
the sequence ord(r_1), ..., ord(r_n). If q is
a prime congruent to 1 modulo any of these
numbers, then one of the roots r_i is defined
over F_q, and therefore p(x) has a root modulo q
*/
function CongruenceConditionOneRoot(p)
	K := SplittingField(p);
	return { OrderRootUnity(r[1]) : r in Roots(ChangeRing(p, K)) };
end function;

/*
Given two pairs ( {c_1, ..., c_m}, M_1 ) and ( {d_1, ..., d_r), M_2 ),
returns a pair ( {e_i}, M ) with M = LCM(M_1, M_2) and e_i the list
of congruence classes modulo M that reduce into {c_1, ..., c_m} mod M_1
and into {d_1, ..., d_r} modulo M_2
*/
function CombineCongruences( Congruence1, Congruence2 )
	M1 := Congruence1[2];
	M2 := Congruence2[2];
	Classes1 := Congruence1[1];
	Classes2 := Congruence2[1];
	CommonModulus := LCM(M1, M2);
	ValidCongruenceClasses := {};
	for p in [ j : j in [1..CommonModulus] | GCD(j,CommonModulus) eq 1 ] do
		if (p mod M1) in Classes1 and (p mod M2) in Classes2 then
			ValidCongruenceClasses := ValidCongruenceClasses join { p };
		end if;
	end for;
	return [* ValidCongruenceClasses , CommonModulus *];
end function;
