# Named models and their profile operators

Every row specifies the equation actually used:

$$
\mathcal L(D_t,D_x,D_y,D_z)u+\mathcal M(D_t,D_x,D_y,D_z)(u^2/2)=0.
$$

Thus the Burgers nonlinearity is $(u^2/2)_x=u u_x$, whereas the Fisher
row has $\mathcal M=2$, giving $u^2$. This convention fixes signs
and factors that vary between sources.

For one-dimensional rows use $\xi=x-ct$; rows marked **plane** use
$\xi=kx+\ell y-ct$, with $k\ne0$. The reduction substitutes
$D_t=-cD$, $D_x=kD$, $D_y=\ell D$, and divides by the indicated
power $D^m$. Its autonomous branch is
$\widehat L(D)U+qU^2/2+K=0$, with $K=0$ if $m=0$.

The displayed monic operator is
$P_B(D)=(\widehat L(D)+qB)/L_p$, where
$\widehat L(0)B+qB^2/2+K=0$, and $v=q(U-B)/L_p$.
The leading coefficient $L_p$ and $q$ must be nonzero; parameter
specializations that cancel them require a new reduction.
For $m\ge2$, nonconstant polynomial forcing from integration is set
to zero. These restrictions are displayed by the CLI as well.

The table is generated from `models.json` by `build_model_table.py`.
Each name denotes the explicit representative below; coefficients and
sign conventions in a different article should be checked against it.

| Model / preset | $\mathcal L$ | $\mathcal M$ | $m$ | $p$ | $P_B(D)$ |
|---|---|---|---|---|---|
| Burgers (`burgers`) | $D_{t} - D_{x}^{2} \nu$ | $D_{x}$ | 1 | 1 | $D + \frac{c - B}{\nu}$ |
| Khokhlov-Zabolotskaya-Kuznetsov (plane waves) (`kzk`) **plane** | $D_{x} \left(D_{t} - D_{x}^{2} \nu\right) + D_{y}^{2} \gamma$ | $D_{x}^{2}$ | 2 | 1 | $D + \frac{c k - B k^{2} - \gamma \ell^{2}}{k^{3} \nu}$ |
| Korteweg-de Vries (`kdv`) | $D_{t} + D_{x}^{3} \mu$ | $D_{x}$ | 1 | 2 | $D^{2} + \frac{B - c}{\mu}$ |
| Benjamin-Bona-Mahony / regularized long wave (`bbm`) | $- D_{t} D_{x}^{2} + D_{t} + D_{x}$ | $D_{x}$ | 1 | 2 | $D^{2} + \frac{1 + B - c}{c}$ |
| Boussinesq (sign parameter s) (`boussinesq`) | $D_{t}^{2} + D_{x}^{4} s - D_{x}^{2}$ | $- 2 D_{x}^{2}$ | 2 | 2 | $D^{2} + \frac{-1 + c^{2} - 2 B}{s}$ |
| improved Boussinesq (`improved_boussinesq`) | $- D_{t}^{2} D_{x}^{2} + D_{t}^{2} - D_{x}^{2}$ | $- 2 D_{x}^{2}$ | 2 | 2 | $D^{2} + \frac{1 - c^{2} + 2 B}{c^{2}}$ |
| Kadomtsev-Petviashvili (plane waves) (`kp`) **plane** | $D_{x} \left(D_{t} + D_{x}^{3}\right) + 3 D_{y}^{2} s$ | $D_{x}^{2}$ | 2 | 2 | $D^{2} + \frac{B k^{2} - c k + 3 s \ell^{2}}{k^{4}}$ |
| Zakharov-Kuznetsov (plane waves) (`zk`) **plane** | $D_{t} + D_{x} \left(D_{x}^{2} + D_{y}^{2}\right)$ | $D_{x}$ | 1 | 2 | $D^{2} + \frac{- c + B k}{k \left(\ell^{2} + k^{2}\right)}$ |
| quadratic Klein-Gordon (`quadratic_klein_gordon`) | $D_{t}^{2} - D_{x}^{2} + a$ | $2 b$ | 0 | 2 | $D^{2} + \frac{a + 2 B b}{-1 + c^{2}}$ |
| KdV-Burgers (`kdv_burgers`) | $D_{t} + D_{x}^{3} \mu - D_{x}^{2} \nu$ | $D_{x}$ | 1 | 2 | $D^{2} - \frac{D \nu}{\mu} + \frac{B - c}{\mu}$ |
| BBM-Burgers (`bbm_burgers`) | $- D_{t} D_{x}^{2} + D_{t} - D_{x}^{2} \nu + D_{x}$ | $D_{x}$ | 1 | 2 | $D^{2} - \frac{D \nu}{c} + \frac{1 + B - c}{c}$ |
| KP-Burgers (plane waves) (`kp_burgers`) **plane** | $D_{x} \left(D_{t} + D_{x}^{3} \mu - D_{x}^{2} \nu\right) + D_{y}^{2} \gamma$ | $D_{x}^{2}$ | 2 | 2 | $D^{2} - \frac{D \nu}{k \mu} + \frac{B k^{2} + \gamma \ell^{2} - c k}{k^{4} \mu}$ |
| ZK-Burgers (plane waves) (`zk_burgers`) **plane** | $D_{t} + D_{x} \mu \left(D_{x}^{2} + D_{y}^{2}\right) - \nu \left(D_{x}^{2} + D_{y}^{2}\right)$ | $D_{x}$ | 1 | 2 | $D^{2} - \frac{D \nu}{k \mu} + \frac{- c + B k}{k \mu \left(\ell^{2} + k^{2}\right)}$ |
| Boussinesq with mixed-derivative damping (`viscous_boussinesq`) | $D_{t}^{2} - 2 D_{t} D_{x}^{2} b + D_{x}^{4} \alpha - D_{x}^{2}$ | $- 2 D_{x}^{2} \beta$ | 2 | 2 | $D^{2} + \frac{2 D b c}{\alpha} + \frac{-1 + c^{2} - 2 B \beta}{\alpha}$ |
| Fisher-KPP (`fisher`) | $D_{t} - D_{x}^{2} - 1$ | $2$ | 0 | 2 | $D^{2} + D c - \left(-1 + 2 B\right)$ |
| damped quadratic Klein-Gordon (hyperbolic Fisher) (`damped_klein_gordon`) | $D_{t}^{2} \tau + D_{t} - D_{x}^{2} - 1$ | $2$ | 0 | 2 | $D^{2} - \frac{D c}{-1 + \tau c^{2}} + \frac{-1 + 2 B}{-1 + \tau c^{2}}$ |
| Kuramoto-Sivashinsky (`ks`) | $D_{t} + D_{x}^{4} + D_{x}^{2}$ | $D_{x}$ | 1 | 3 | $D^{3} + D + \left(B - c\right)$ |
| Kuramoto–Sivashinsky with dispersion / Topper–Kawahara form (`dispersive_ks`) | $D_{t} + D_{x}^{4} + D_{x}^{3} \sigma + D_{x}^{2}$ | $D_{x}$ | 1 | 3 | $D^{3} + \sigma D^{2} + D + \left(B - c\right)$ |
| Kawahara (`kawahara`) | $D_{t} + D_{x}^{5} \beta + D_{x}^{3} \alpha$ | $D_{x}$ | 1 | 4 | $D^{4} + \frac{\alpha D^{2}}{\beta} + \frac{B - c}{\beta}$ |
| Rosenau-KdV (`rosenau_kdv`) | $D_{t} D_{x}^{4} + D_{t} + D_{x}^{3} + D_{x}$ | $D_{x}$ | 1 | 4 | $D^{4} - \frac{D^{2}}{c} + \frac{-1 + c - B}{c}$ |
| Rosenau-Kawahara (`rosenau_kawahara`) | $D_{t} D_{x}^{4} + D_{t} - D_{x}^{5} + D_{x}^{3} + D_{x}$ | $D_{x}$ | 1 | 4 | $D^{4} - \frac{D^{2}}{1 + c} + \frac{-1 + c - B}{1 + c}$ |
| Rosenau-RLW (`rosenau_rlw`) | $D_{t} D_{x}^{4} - D_{t} D_{x}^{2} + D_{t} + D_{x}$ | $D_{x}$ | 1 | 4 | $D^{4} - D^{2} + \frac{-1 + c - B}{c}$ |
| Rosenau (`rosenau`) | $D_{t} D_{x}^{4} + D_{t} + D_{x}$ | $D_{x}$ | 1 | 4 | $D^{4} + \frac{-1 + c - B}{c}$ |
| sixth-order Boussinesq (`sixth_order_boussinesq`) | $D_{t}^{2} - D_{x}^{6} \beta - D_{x}^{4} \alpha - D_{x}^{2}$ | $- 2 D_{x}^{2}$ | 2 | 4 | $D^{4} + \frac{\alpha D^{2}}{\beta} + \frac{1 - c^{2} + 2 B}{\beta}$ |
| fifth-order KP (plane waves) (`fifth_order_kp`) **plane** | $D_{x} \left(D_{t} + D_{x}^{5} \beta + D_{x}^{3} \alpha\right) + D_{y}^{2} \gamma$ | $D_{x}^{2}$ | 2 | 4 | $D^{4} + \frac{\alpha D^{2}}{\beta k^{2}} + \frac{B k^{2} + \gamma \ell^{2} - c k}{\beta k^{6}}$ |
| beam equation with quadratic nonlinearity (`quadratic_beam`) | $D_{t}^{2} + D_{x}^{4} + 1$ | $-2$ | 0 | 4 | $D^{4} + D^{2} c^{2} - \left(-1 + 2 B\right)$ |
| Swift-Hohenberg with quadratic nonlinearity (`quadratic_swift_hohenberg`) | $D_{t} - r + \left(D_{x}^{2} + 1\right)^{2}$ | $2$ | 0 | 4 | $D^{4} + 2 D^{2} - D c + \left(1 - r + 2 B\right)$ |
| Benney-Lin (`benney_lin`) | $D_{t} + D_{x}^{5} \eta + D_{x}^{3} + b \left(D_{x}^{4} + D_{x}^{2}\right)$ | $D_{x}$ | 1 | 4 | $D^{4} + \frac{b D^{3}}{\eta} + \frac{D^{2}}{\eta} + \frac{D b}{\eta} + \frac{B - c}{\eta}$ |
| Kawahara-Burgers (`kawahara_burgers`) | $D_{t} + D_{x}^{5} \beta + D_{x}^{3} \alpha - D_{x}^{2} \nu$ | $D_{x}$ | 1 | 4 | $D^{4} + \frac{\alpha D^{2}}{\beta} - \frac{D \nu}{\beta} + \frac{B - c}{\beta}$ |
| fourth-order Fisher (`fourth_order_fisher`) | $D_{t} + D_{x}^{4} \gamma - D_{x}^{2} - 1$ | $2$ | 0 | 4 | $D^{4} - \frac{D^{2}}{\gamma} - \frac{D c}{\gamma} + \frac{-1 + 2 B}{\gamma}$ |
| Fifth-order ZK-type quadratic equation (`fifth_order_zk`) **plane** | $D_{t} + D_{x} \alpha \left(D_{x}^{2} + D_{y}^{2}\right) + D_{x} \beta \left(D_{x}^{2} + D_{y}^{2}\right)^{2}$ | $D_{x}$ | 1 | 4 | $D^{4} + \frac{\alpha D^{2}}{\beta \left(\ell^{2} + k^{2}\right)} + \frac{- c + B k}{\beta k \left(\ell^{4} + k^{4} + 2 \ell^{2} k^{2}\right)}$ |
| Nikolaevskiy (velocity form) (`nikolaevskiy`) | $D_{t} + D_{x}^{2} \left(\epsilon - \left(D_{x}^{2} + 1\right)^{2}\right)$ | $D_{x}$ | 1 | 5 | $D^{5} + 2 D^{3} + D \left(1 - \epsilon\right) - \left(B - c\right)$ |
| Nikolaevskiy with linear dispersion (`dispersive_nikolaevskiy`) | $D_{t} - D_{x}^{5} \beta - D_{x}^{3} \alpha + D_{x}^{2} \left(\epsilon - \left(D_{x}^{2} + 1\right)^{2}\right)$ | $D_{x}$ | 1 | 5 | $D^{5} + \beta D^{4} + 2 D^{3} + \alpha D^{2} + D \left(1 - \epsilon\right) - \left(B - c\right)$ |
| Seventh-order quadratic KdV-type equation (`seventh_order_kdv`) | $D_{t} + D_{x}^{7} \gamma + D_{x}^{5} \beta + D_{x}^{3} \alpha$ | $D_{x}$ | 1 | 6 | $D^{6} + \frac{\beta D^{4}}{\gamma} + \frac{\alpha D^{2}}{\gamma} + \frac{B - c}{\gamma}$ |

## Forms needing an additional substitution

Potential equations need the slope specified explicitly. They are not
silently identified with equations for the original dependent variable.
The following reductions explain several commonly grouped names; these
potential forms are not CLI presets.

| Equation | Profile substitution | Monic profile operator |
|---|---|---|
| KS flame-front potential, $H_t+\nu H_{xx}+\mu H_{xxxx}+H_x^2/2=0$ | $H=H(\xi)$, $\xi=x-ct$, $U=H'$; no integration | $D^3+(\nu/\mu)D+(B-c)/\mu$, with $-cB+B^2/2=0$ |
| Two-dimensional KS height equation, $H_t+\nu\Delta H+\mu\Delta^2H+\lvert\nabla H\rvert^2/2=0$ | $\xi=kx+\ell y-ct$, $U=H'$, $s=k^2+\ell^2$; no integration | $D^3+\nu D/(\mu s)+(sB-c)/(\mu s^2)$, with $-cB+sB^2/2=0$ |
| Jimbo–Miwa, $H_{xxxy}+3H_yH_{xx}+3H_xH_{xy}+2H_{yt}-3H_{xz}=0$ | $\xi=kx+\ell y+mz-ct$, $U=H'$, integrate once, $k\ell\ne0$ | $D^2+(6k^2\ell B-2\ell c-3km)/(k^3\ell)$ |

For the Jimbo–Miwa row the unnormalized profile is
$k^3\ell U''+3k^2\ell U^2-(2\ell c+3km)U+K=0$.
For the height forms, a meromorphic slope need not have a meromorphic
primitive: integrating a nonzero pole residue produces a logarithm.

## Choosing the intended variant

The `viscous_boussinesq` row uses $u_{xxt}$ damping. Ordinary drag
proportional to $u_t$ generally prevents the displayed double integration.
The `quadratic_swift_hohenberg` row becomes stationary at `--speed 0`;
the usual additional cubic nonlinearity is outside this quadratic class.
The seventh-order KdV-type row specifies a quadratic equation with higher
linear dispersion, rather than the full seventh flow of the integrable
KdV hierarchy with its additional nonlinear derivative terms.

Several Rosenau equations share a name while changing the flux or mixed
derivative terms. The rows here use $(u^2/2)_x$; they do not cover
Rosenau–Hyman nonlinear dispersion. Likewise, a scalar two-dimensional KS
equation for a velocity field and the isotropic height equation above are
different PDEs; the nonlinear coefficient after the phase substitution
must be taken from the form actually supplied.

The names “purely dispersive” and “purely dissipative” in the paper classify
profile operators. For a second-order-in-time, reaction or stationary PDE,
that classification by powers of $D$ is not a statement about physical
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
$T_\alpha=t^{1-\alpha}\partial_t=\partial_\tau$,
$\tau=t^\alpha/\alpha$, is established in
[Abdelhakim, *Precise interpretation of the conformable fractional derivative*](https://arxiv.org/abs/1805.02309).
Spatial conformable derivatives similarly use $X=x^\beta/\beta$.
Their compositions give the same operator dictionary when the transformed
equation is one of the displayed forms. This statement concerns the
transformed coordinate; it does not assert global meromorphicity across the
branch point in the original complex coordinate or apply to nonlocal
Caputo/Riemann–Liouville derivatives.
