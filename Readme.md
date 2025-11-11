# Crouziex-Formulisation of Multilinear Orthogonality (MO) for Quadratic Extremals in Crouzeix's Conjecture

## Overview

This repository contains a formal proof in Coq of the Multilinear Orthogonality (MO) assumption from the appendix of the paper on a three-dimensional reduction for Crouzeix's conjecture. Specifically, it verifies MO in the restricted case of quadratic polynomials (degree ≤2, corresponding to N=3) under the assumptions that the matrix A is Hermitian (self-adjoint, A = A\*) and the vector v equals the support eigenvector x.

Crouzeix's conjecture states that for any square matrix A and analytic function f, ||f(A)|| ≤ 2 sup\_{z ∈ W(A)} |f(z)|, where W(A) is the numerical range. The MO assumption is key to making the 3D reduction unconditional in the general case, but remains open for arbitrary degrees and non-normal matrices. This proof handles the "worked example (quadratic case)" described in the appendix, using discrete Cauchy-Riemann conditions, telescoping sums, and projections onto the 3D span span{x, A x, A\* x}.

The code is split into two main files:

- **QuickSplitLast.v**: Specializes to N=3, proves MO under Hermitian assumptions using ordinal arithmetic, sum splitting, and boundary vanishing.
- **FinalOpenLemma.v**: Sets up the general framework for arbitrary N, including matrix definitions (e.g., Gram matrix, projector P3), defect telescoping for powers of A and A\*, and multilinear expansions.

Key result: Theorem `wMO_in_V3` shows the variation vector w_MO lies in the 3D span, confirming the first variation vanishes orthogonally.

This formalization uses the MathComp library for rigorous linear algebra and relies on custom modules for complex matrices and inner products.

## Limitations and Context

- This proves MO only for quadratic extremals and Hermitian A. The general case (non-normal A, arbitrary degree) remains open, as noted in the paper's appendix.
- Assumes specific hypotheses (e.g., `A_herm`, `v_is_x`, `coeff_shift_interior_for_Phi`), which simplify cancellations but limit generality.
- For extensions: Induct on N or relax Hermitian assumption to tackle the full conjecture.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Citations

Paper Coming soon.

Contributions welcome! If you extend to higher degrees or non-Hermitian cases, open a PR.
