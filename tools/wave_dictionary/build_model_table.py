#!/usr/bin/env python3
"""Regenerate the exact reduction table from the explicit presets."""

from pathlib import Path

import sympy as s

from core import DT, DX, DY, DZ, RHO, parse, reduce_pde
from dictionary import models


HERE = Path(__file__).resolve().parent

INTRO = r"""# Named models and their profile operators

Every row specifies the equation actually used:

\[
\mathcal L(D_t,D_x,D_y,D_z)u+\mathcal M(D_t,D_x,D_y,D_z)(u^2/2)=0.
\]

Thus the Burgers nonlinearity is \((u^2/2)_x=u u_x\), whereas the Fisher
row has \(\mathcal M=2\), giving \(u^2\). This convention fixes signs
and factors that vary between sources.

For one-dimensional rows use \(\xi=x-ct\); rows marked **plane** use
\(\xi=kx+\ell y-ct\), with \(k\ne0\). The reduction substitutes
\(D_t=-cD\), \(D_x=kD\), \(D_y=\ell D\), and divides by the indicated
power \(D^m\). Its autonomous branch is
\(\widehat L(D)U+qU^2/2+K=0\), with \(K=0\) if \(m=0\).

The displayed monic operator is
\(P_B(D)=(\widehat L(D)+qB)/L_p\), where
\(\widehat L(0)B+qB^2/2+K=0\), and \(v=q(U-B)/L_p\).
The leading coefficient \(L_p\) and \(q\) must be nonzero; parameter
specializations that cancel them require a new reduction.
For \(m\ge2\), nonconstant polynomial forcing from integration is set
to zero. These restrictions are displayed by the CLI as well.

The table is generated from `models.json` by `build_model_table.py`.
Each name denotes the explicit representative below; coefficients and
sign conventions in a different article should be checked against it.

| Model / preset | \(\mathcal L\) | \(\mathcal M\) | \(m\) | \(p\) | \(P_B(D)\) |
|---|---|---|---|---|---|
"""

NOTES = r"""
## Forms needing an additional substitution

Potential equations need the slope specified explicitly. They are not
silently identified with equations for the original dependent variable.
The following reductions explain several commonly grouped names; these
potential forms are not CLI presets.

| Equation | Profile substitution | Monic profile operator |
|---|---|---|
| KS flame-front potential, \(H_t+\nu H_{xx}+\mu H_{xxxx}+H_x^2/2=0\) | \(H=H(\xi)\), \(\xi=x-ct\), \(U=H'\); no integration | \(D^3+(\nu/\mu)D+(B-c)/\mu\), with \(-cB+B^2/2=0\) |
| Two-dimensional KS height equation, \(H_t+\nu\Delta H+\mu\Delta^2H+\lvert\nabla H\rvert^2/2=0\) | \(\xi=kx+\ell y-ct\), \(U=H'\), \(s=k^2+\ell^2\); no integration | \(D^3+\nu D/(\mu s)+(sB-c)/(\mu s^2)\), with \(-cB+sB^2/2=0\) |
| Jimbo–Miwa, \(H_{xxxy}+3H_yH_{xx}+3H_xH_{xy}+2H_{yt}-3H_{xz}=0\) | \(\xi=kx+\ell y+mz-ct\), \(U=H'\), integrate once, \(k\ell\ne0\) | \(D^2+(6k^2\ell B-2\ell c-3km)/(k^3\ell)\) |

For the Jimbo–Miwa row the unnormalized profile is
\(k^3\ell U''+3k^2\ell U^2-(2\ell c+3km)U+K=0\).
For the height forms, a meromorphic slope need not have a meromorphic
primitive: integrating a nonzero pole residue produces a logarithm.

## Choosing the intended variant

The `viscous_boussinesq` row uses \(u_{xxt}\) damping. Ordinary drag
proportional to \(u_t\) generally prevents the displayed double integration.
The `quadratic_swift_hohenberg` row becomes stationary at `--speed 0`;
the usual additional cubic nonlinearity is outside this quadratic class.
The seventh-order KdV-type row specifies a quadratic equation with higher
linear dispersion, rather than the full seventh flow of the integrable
KdV hierarchy with its additional nonlinear derivative terms.

Several Rosenau equations share a name while changing the flux or mixed
derivative terms. The rows here use \((u^2/2)_x\); they do not cover
Rosenau–Hyman nonlinear dispersion. Likewise, a scalar two-dimensional KS
equation for a velocity field and the isotropic height equation above are
different PDEs; the nonlinear coefficient after the phase substitution
must be taken from the form actually supplied.

The names “purely dispersive” and “purely dissipative” in the paper classify
profile operators. For a second-order-in-time, reaction or stationary PDE,
that classification by powers of \(D\) is not a statement about physical
energy dissipation.

## Sources for conventions

The reductions in the table follow directly from its displayed equations.
For literature comparisons, primary sources fixing several easily confused
conventions are:

- [Simbawa, Matthews and Cox, *The Nikolaevskiy equation with dispersion*, equations (1)–(2)](https://arxiv.org/html/1002.3490): the `dispersive_nikolaevskiy` preset uses their signs, with their control parameter renamed `epsilon`.
- [Paliathanasis, *Benney–Lin and Kawahara equations*, equation (1)](https://arxiv.org/html/1907.06918): the Benney–Lin preset uses `eta` and `b` for its two named coefficients.
- [Maypaokha et al., *Monotone travelling waves in the Rosenau–KdV equation*](https://strathprints.strath.ac.uk/93689/1/Maypaokha-etal-NARWA-2025-Monotone-travelling-waves-in-the-Rosenau-KdV.pdf): the mixed fourth-space/first-time derivative belongs to the Rosenau–KdV equation.
- [Cornejo-Pérez and Rosu, *Travelling-wave solutions for Korteweg–de Vries–Burgers equations through factorizations*](https://arxiv.org/abs/math-ph/0604004): the reduction and front normalization can be compared with the exact `kdv_burgers` example.

For the conformable derivative on positive coordinates, the exact identity
\(T_\alpha=t^{1-\alpha}\partial_t=\partial_\tau\),
\(\tau=t^\alpha/\alpha\), is established in
[Abdelhakim, *Precise interpretation of the conformable fractional derivative*](https://arxiv.org/abs/1805.02309).
Spatial conformable derivatives similarly use \(X=x^\beta/\beta\).
Their compositions give the same operator dictionary when the transformed
equation is one of the displayed forms. This statement concerns the
transformed coordinate; it does not assert global meromorphicity across the
branch point in the original complex coordinate or apply to nonlocal
Caputo/Riemann–Liouville derivatives.
"""


def build():
    operators = dict(zip((DT, DX, DY, DZ), s.symbols("D_t D_x D_y D_z")))
    lines = [INTRO]
    for row in models().values():
        L, M = parse(row["linear"]), parse(row["quadratic"])
        direction = tuple(map(parse, row["direction"]))
        red = reduce_pde(L, M, s.Symbol("c"), direction)
        name = "%s (`%s`)" % (row["name"], row["id"])
        if row["direction"] != ["1", "0", "0"]:
            name += " **plane**"
        polynomial = s.Poly(red["P_about_B"], RHO)
        terms = [s.factor_terms(s.cancel(co), sign=False)*s.Symbol("D")**j
                 for (j,), co in polynomial.terms()]
        operator = s.Add(*terms, evaluate=False)
        fields = [name, r"\(%s\)" % s.latex(L.subs(operators)), r"\(%s\)" % s.latex(M.subs(operators)),
                  str(red["integrations"]), str(red["order"]), r"\(%s\)" % s.latex(operator, order="none")]
        lines.append("| " + " | ".join(fields) + " |\n")
    lines.append(NOTES)
    text = "".join(lines).replace(r"\(", "$").replace(r"\)", "$")
    text = text.replace(r"\[", "$$").replace(r"\]", "$$")
    (HERE/"MODELS.md").write_text(text)


if __name__ == "__main__":
    build()
