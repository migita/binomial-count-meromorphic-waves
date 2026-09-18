# Exact checks for the two pure subfamilies and for single equations

All scripts use SymPy only and exact rational arithmetic. Saved outputs are the
`.txt` files.

| Script | What it checks |
| --- | --- |
| `reflection_checks.py` | Proposition (Reflection): `S_{iota A}(rho) = -S_A(-rho) - 2A(0)A(-rho)` and `R_{iota A}(rho) = -R_A(-rho)` with symbolic coefficients for d = 1..5; the formula for `P_{iota A}` at p = 2, 3; the six purely dissipative pairs at p = 5; the scaling `u = b_p lambda^p v_A(lambda(x-ct))`, `c = -b_p lambda^p P_A(0)` by substitution in the evolution equation at p = 2, 3. |
| `symmetric_count.py 2 3 4 5 6 7 8` | The length `F_p = C(p-1, floor((p-1)/2))` of the fixed locus of the reflection and its reducedness (Groebner basis; the Jacobian determinant generates the unit ideal together with the equations) for p = 2..8. |
| `elliptic_symmetric.py` | The length `2 F_p` of the elliptic matching scheme of the purely dispersive family on the sample lattice (g2, g3) = (2, 1), for p = 2, 4, 6. |
| `label_checks.py` | What the paper reads off the labels, at the prime indices 5 and 7: the labels of all pairs with real coefficients at p = 3 (and of the two complex pairs, for both choices of i modulo 5) and of the 21 real pairs at p = 4; a pair is a pulse iff its label contains 0; the mirror image has label -L; `P_A(0) != 0` at the pulses; and, with symbolic coefficients for p = 3, 4, 5, the identity `R_0 = -A(0)(A(0) + C_A(0))` and the parity splitting of the Jacobian on the fixed subspace of the reflection. |
| `p6_list.py` | The ten purely dispersive pairs at p = 6: the two remainder equations, the eliminant and its factorization (with the sextic factor in full), the operator `P_A`, and the two real pairs. |

| `elliptic_dissipative.py` | For p = 3, 5, 7 the elliptic matching system of the purely dissipative family has no solution on the sample lattice (g2, g3) = (2, 1) (Groebner basis {1}), hence none on a generic lattice. |
| `modular/symmetric_modular.py 32003 3 4 ... 14` | Finite-field certificates that the `F_p` pairs of the pure subfamily are distinct, for p = 3..14: Singular (quotient dimension `F_p` and unit ideal with the Jacobian determinant) and msolve (degree of the ideal, of the eliminating polynomial and of its squarefree part, all equal to `F_p`) over F_32003. Each simple point modulo 32003 lifts uniquely by Hensel's lemma, and the known length `F_p` shows that the lifts are all the points. Results: `modular/results_q32003_p3-14.json`. Needs Singular and/or msolve (paths through the environment variables `SINGULAR`, `MSOLVE`). |

An independent recomputation of the p = 5 and p = 6 lists was carried out
separately during the review of the manuscript.
