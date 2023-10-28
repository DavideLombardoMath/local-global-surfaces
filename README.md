This repository contains some MAGMA scripts accompanying the paper 'On the local-global principle for isogenies of abelian surfaces', by Davide Lombardo and Matteo Verzobio.
The main files are HasseSp4.m, which computes a list of Hasse subgroups of Sp_4(\F_\ell) for small primes \ell, and ComputeTableAndCheck.m, which computes the data in Table 1 of the paper and runs the tests described in the Appendix. Output files for these two scripts are provided.

In addition, the repository contains the following files:
- ArithmeticFunctions.m: auxiliary functions related to congruence conditions (e.g., for the existence of certain roots of unity modulo the prime \ell)
- ClassC3.m: constructs all possible Hasse subgroups contained in a maximal subgroup of Sp_4(F_\ell) of class C_3
- ExceptionalWreathS2.m: constructs all possible Hasse subgroups contained in a maximal subgroup of Sp_4(F_\ell) isomorphic to SL_2(\F_\ell) \wr S_2
- GeneralRepresentationTheory.m: an implementation of standard calculations in the representation theory of finite groups
- GroupExtensions.m and GroupExtensions2.m: functions to test properties (P1) and (P2) from the paper
- HasseSubgroups.m: auxiliary functions to determine whether certain subgroups are Hasse or not, giving in particular an implementation of the algorithm sketched in Section 3.2 of the paper
