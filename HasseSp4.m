/*
Compute a list of Hasse subgroups
of Sp_4(F_\ell) and GSp_4(F_\ell)
for small primes \ell
*/

SetLogFile("HasseSubgroupsSp4-100.out");

/*
Constructs the general symplectic 
group as a subgroup of GL_n(F_ell)
*/
function GSp(n,ell)
	G := Sp(n, ell);
	G1 := GL(n,FiniteField(ell));
	N:=Normaliser(G1,G);

	_, J := SymplecticForm(SymplecticGroup(n, ell));
	J := GL(n,FiniteField(ell))!J;

	return N, J;
end function;

/*
Test whether the subgroup has surjective multiplier
*/
function TestSurjectiveMultiplier(H, ell)
	Sp4 := SymplecticGroup(4, ell);
	ind := #H / #( H meet Sp4 );
	return ind eq (ell-1);
end function;









/*
Test whether a subgroup fixes no line in F_\ell^4
*/
function HasNoCommonEigenvector(H)
	subm := Submodules(GModule(H));
	subm := [s : s in subm | Dimension(s) eq 1];
	return #subm eq 0;
end function;

/*
Test whether every element of a subgroup has
an F_\ell-rational eigenvalue
*/
function IsLocallyReducible(H)
	for h in H do
		if not HasRoot(CharacteristicPolynomial(h)) then
			return false;
		end if;
	end for;
	return true;
end function;

/*
Test whether a subgroup H is Hasse, that is, H acts
irreducibly, but every element of H fixes a line
*/
function HasPropertyL(H)
	return IsIrreducible(H) and IsLocallyReducible(H);
end function;

/*
Check containment of H1 in a
conjugate of H2
*/
function CheckContainment(G, H1, H2)
	if #H1 ge #H2 then
		return false;
	end if;

	if #H2 mod #H1 ne 0 then
		return false;
	end if;
	sbgps := Subgroups(H2);
	sbgps := [H`subgroup : H in sbgps];
	for H in sbgps do
		if IsConjugate(G,H1,H) then
			return true;
		end if;
	end for;
	return false;
end function;

/*
Given a group G and a list of
subgroups of G, test whether
the j-th element of the list
is maximal among the subgroups
in the list
*/
function IsMaximalInList(G, j, FinalList)
	for i in [1..#FinalList] do
		if i ne j then
			if CheckContainment(G, FinalList[j], FinalList[i]) then
				return false;
			end if;
		end if;
	end for;
	return true;
end function;

/*
Remove duplicates up to conjugacy
*/
function PurgeDuplicates(GS, G)
FinalList := [];
for H in GS do
	test := true;
	for H1 in FinalList do
		if IsConjugate(G, H`subgroup, H1`subgroup) then
			test := false;
			break;
		end if;
	end for;
	if test then
		Append(~FinalList, H);
	end if;
end for;
return FinalList;
end function;












/*
List all Hasse subgroups of a given group G,
exploring recursively the lattice of all subgroups
of G by going down from G to its maximal subgroups
*/

function HasseSubgroups(G : SurjectiveMultiplier := false)
	CandidateSubgroups := MaximalSubgroups(G);		// list the maximal subgroups of G
	GoodSubgroups := [];						// keep track of Hasse subgroups
	while #CandidateSubgroups ne 0 do			
		CandidateSubgroups := [H : H in CandidateSubgroups| IsIrreducible(H`subgroup) ];		// a class-L subgroup must be irreducible
		LocalReducibility := [ IsLocallyReducible(H`subgroup) : H in CandidateSubgroups ];	// and every element should have eigenvalues
		LProp := [ CandidateSubgroups[i] : i in [1..#LocalReducibility] | LocalReducibility[i] ];
		RemainingCandidates := [ CandidateSubgroups[i] : i in [1..#LocalReducibility] | not LocalReducibility[i] ];
		RemainingCandidates := PurgeDuplicates(RemainingCandidates, G);					// subgroups of different maximal subgroups of G
																		// might still be conjugated in G

		GoodSubgroups := GoodSubgroups cat LProp;									// those satisfy both 
		CandidateSubgroups := &cat[ MaximalSubgroups(H`subgroup) : H in RemainingCandidates ];
	end while;

	FinalList := PurgeDuplicates(GoodSubgroups, G);
	FinalList := [H`subgroup : H in FinalList];


	i := 1;
	while i le #FinalList do
		if IsMaximalInList(G, i, FinalList) then
			i := i+1;
		else
			Remove(~FinalList, i);
		end if;
	end while;

	if SurjectiveMultiplier then
		ell := Characteristic(BaseRing(G));
		FinalList := [H : H in FinalList | TestSurjectiveMultiplier(H, ell) ];
	end if;
return FinalList;
end function;


function DescribeSubgroup(K, ell)
	if not IsIrreducible(K) then	// type C_1
		return "Type C_1 (a reducible subgroup)";
	end if;

	OrdSL2 := #SL(2, ell);
	OrdGL2 := #GL(2, ell);
	OrdSL22 := #SL(2, ell^2);

	if not IsPrimitive(K) then		// type C_2
		if #K eq OrdSL2^2*2 then
			return "Type C_2, isomorphic to SL_2(\ell)^2 : 2";
		end if;

		if #K eq OrdGL2*2 then
			return "Type C_2, isomorphic to GL_2(\ell).2";
		end if;
	end if;


	try
	if IsSemiLinear(K) then		// type C_3
		if #K eq OrdSL22*2 then
			return "Type C_3, isomorphic to SL_2(\ell^2):2";
		end if;

		return "Type C_3, isomorphic to GU_2(\ell).2";
	end if;
	catch e
		;
	end try;

	if #K eq #SL(2,ell) then	// Class S, isomorphic to SL(2, F_\ell)
		return "Type S, isomorphic to SL_2(\ell)";
	end if;

	try
		if IsExtraSpecialNormaliser(K) then	// type C_6
			return "Type C_6";
		end if;
	catch e
		;
	end try;

	if #K le 5000 then				// other cases
		return GroupName(K);
	end if;


	return "Cannot classify the given subgroup";
end function;


function DescribeSubgroupGSp(K, ell)
	Sp4 := SymplecticGroup(4,FiniteField(ell));
	return "Group of order", #K, ". The intersection with Sp_4 is described as follows:", DescribeSubgroup(K meet Sp4, ell);
end function;






/*
For each prime ell, list the maximal subgroups
of Sp_4(F_\ell) or GSp_4(F_\ell).
For each such M, print a list of maximal Hasse
subgroups of M
*/
procedure AllHasseSubgroups(ell : General := false)
	/*
	Initialise the symplectic group Sp_4(F_\ell)
	and the corresponding bilinear form
	*/
	Sp4 := SymplecticGroup(4,FiniteField(ell));
	if not General then
		G := Sp4;
	else
		G, J := GSp(4, ell);
	end if;

	ms := MaximalSubgroups(G);

	if General then
		ms := [ H : H in ms | not (Sp4 subset H`subgroup) ];
	end if;

	for H in ms do
		if General then
			"==== Maximal subgroup :", DescribeSubgroupGSp(H`subgroup, ell), "====";
		else
			"==== Maximal subgroup :", DescribeSubgroup(H`subgroup, ell), "====";
		end if;
		FinalList := HasseSubgroups(H`subgroup);
		if General then
			FinalList := [ H : H in FinalList | TestSurjectiveMultiplier(H, ell) ];
		end if;
		if #FinalList gt 0 then
			"Number of maximal Hasse subgroups:", #FinalList;
			"Orders:", [#H : H in FinalList];
			"Group structures:", [GroupName(H) : H in FinalList];
			"Exponents:", [Exponent(H) : H in FinalList];
			"Element orders:", [ {Order(h) : h in H} : H in FinalList ];
		else
			"No Hasse subgroups lie inside this maximal subgroup";
		end if;
	end for;
end procedure;


"====== Hasse subgroups of Sp_4(F_\ell) ======";

for ell in [ 2, 3, 5, 7 ] do
"===== Prime ", ell, "=====";
HasseSubgroups(Sp(4,ell));

"==== Hasse subgroups by Aschbacher type ====";
AllHasseSubgroups(ell);
end for;



"====== Hasse subgroups of GSp_4(F_\ell) ======";

for ell in [ 2, 3, 5, 7 ] do
"===== Prime ", ell, "=====";
HasseSubgroups(GSp(4,ell) : SurjectiveMultiplier := true);

"==== Hasse subgroups by Aschbacher type ====";
AllHasseSubgroups(ell : General := true);
end for;






"====== Hasse subgroups of Sp_4(F_\ell) ======";

for ell in [ p : p in [1..100] | IsPrime(p) ] do
	"===== Prime ", ell, "=====";
	AllHasseSubgroups(ell);
end for;
