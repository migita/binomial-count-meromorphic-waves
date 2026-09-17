# Exact checks for the two pure subfamilies and for single equations

All scripts use SymPy only and exact rational arithmetic. Saved outputs are the
`.txt` files.

| Script | What it checks |
| --- | --- |
| `reflection_checks.py` | Proposition (Reflection): `S_{iota A}(rho) = -S_A(-rho) - 2A(0)A(-rho)` and `R_{iota A}(rho) = -R_A(-rho)` with symbolic coefficients for d = 1..5; the formula for `P_{iota A}` at p = 2, 3; the six purely dissipative pairs at p = 5; the scaling `u = b_p lambda^p v_A(lambda(x-ct))`, `c = -b_p lambda^p P_A(0)` by substitution in the evolution equation at p = 2, 3. |
| `symmetric_count.py 2 3 4 5 6 7 8` | The length `F_p = C(p-1, floor((p-1)/2))` of the fixed locus of the reflection and its reducedness (Groebner basis; the Jacobian determinant generates the unit ideal together with the equations) for p = 2..8. |
| `elliptic_symmetric.py` | The length `2 F_p` of the elliptic matching scheme of the purely dispersive family on the sample lattice (g2, g3) = (2, 1), for p = 2, 4, 6. |
| `p6_list.py` | The ten purely dispersive pairs at p = 6: the two remainder equations, the eliminant and its factorization (with the sextic factor in full), the operator `P_A`, and the two real pairs. |

An independent recomputation of the p = 5 and p = 6 lists was carried out
separately during the review of the manuscript.
