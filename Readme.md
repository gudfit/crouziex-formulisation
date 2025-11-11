# Crouziex-Formulisation of Multilinear Orthogonality (MO) for Quadratic Extremals in Crouzeix's Conjecture

This repository contains a formal proof in Coq of the Multilinear Orthogonality (MO) assumption from the appendix of the paper on a three-dimensional reduction for Crouzeix's conjecture. The key innovation is the use of a "leak" mechanism to handle the defect in projections, allowing the proof to work in the 3D span without collapsing to 2D under invariance assumptions. Specifically, it verifies MO in the restricted case of quadratic polynomials (degree ≤2, corresponding to N=3) under the assumptions that the matrix A is Hermitian (self-adjoint, $A = A^*$) and the vector v equals the support eigenvector x.

Crouzeix's conjecture states that for any square matrix A and analytic function f, $\|f(A)\| \leq 2 \sup_{z \in W(A)} |f(z)|$, where $W(A)$ is the numerical range. The MO assumption is key to making the 3D reduction unconditional in the general case, but remains open for arbitrary degrees and non-normal matrices. This proof handles the "worked example (quadratic case)" described in the appendix, using discrete Cauchy-Riemann conditions, telescoping sums, defect decomposition via leaks, and projections onto the 3D span $\\{x, A x, A^* x\\}$.

The code is split into two main files:

- **QuickSplitLast.v**: Specializes to N=3, proves MO under Hermitian assumptions using ordinal arithmetic, sum splitting, boundary vanishing, and leak-based defect telescoping.
- **FinalOpenLemma.v**: Sets up the general framework for arbitrary N, including matrix definitions (e.g., Gram matrix, projector P3), defect telescoping for powers of A and A*, and multilinear expansions.

Key result: Theorem `wMO_in_V3` shows the variation vector w_MO lies in the 3D span, confirming the first variation vanishes orthogonally.

This formalization uses the MathComp library for rigorous linear algebra and relies on custom modules for complex matrices and inner products.

## Mathematical Approach

The proof addresses the challenge of verifying MO in the 3D span without reducing to 2D under invariance or commutativity assumptions. For non-normal matrices, the coupling in $H_{\theta^\*} = \frac{1}{2}(e^{-i\theta^\*} A + e^{i\theta^\*} A^\*)$ requires the full 3D span $\{x_{\theta^\*}, A x_{\theta^\*}, A^\* x_{\theta^\*}\}$, as 2D Krylov spans (e.g., $\{x, A x\}$) capture only 54-60% of the extremal norm in Jordan blocks (per experiments).

The main issue is that direct invariance collapses the 3D span to 2D, but to prove MO without this, we introduce a "leak" mechanism:

- **Leak Definition**: leak $:= (I - P_3) A B$, where $P_3$ is the orthogonal projector onto the 3D span $B$ (columns: $x$, $Ax$, $A^\*x$). This captures the "defect" — the part of $A$ acting on the span that leaks outside.
- **Leak Star for Adjoint**: $\text{leak\\_star} := (I - P_3) A^\* B$, similarly for $A^*$.
- **Defect Telescoping**: Decompose powers: $A^p (B a) = B (A_3^p a) + \sum \texttt{leaks}$, where $A_3$ is the $3\times3$ compression of $A$ onto the span. Similar for $(A^\*)^q$.
  - Lemmas like $\text{fwd\\_defect\\_telescope}$ and $\text{adj\\_defect\\_telescope}$ telescope the sums using recursive decomposition ($\text{step\\_decompose\\_v}$, $\text{step\\_decompose\\_star}$).
  - For mixed terms $((A^\*)^q A^p) (B a)$, $\text{mixed}\_{\text{rectangle}}$  combines both, reducing multilinear traces to compressed $A_3$ / $A_{3,\text{gadj}}$ parts + boundary defects.
- **Cancellations**: When $\xi \perp$ 3D span ($P_3 \xi = 0$), boundary inner products ($\Phi 0 0$, $0 1$, $1 0$) vanish ($\text{phi\\_edge\\_j0}$, $\text{phi\\_edge\\_k0}$), and discrete CR on coefficients telescopes the interior to zero ($\text{rect\\_telescope\\_HCR\\_direct}$).
- **Why 3D is Preserved**: Without leak, noncommutativity $[A, A^\*] \neq 0$ collapses to 2D; leak handles the adjoint direction, proving MO for quadratic/Hermitian while keeping the full 3D structure.
This approach avoids assuming commutativity, making it a step toward general non-normal cases, though limited to quadratic here.

## Limitations and Context

- This proves MO only for quadratic extremals and Hermitian A. The general case (non-normal A, arbitrary degree) remains open, as noted in the paper's appendix.
- Assumes specific hypotheses (e.g., `A_herm`, `v_is_x`, `coeff_shift_interior_for_Phi`), which simplify cancellations but limit generality.
- For extensions: Induct on N or relax Hermitian assumption to tackle the full conjecture.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Citations

Paper Coming soon.

Contributions welcome! If you extend to higher degrees or non-Hermitian cases, open a PR.
