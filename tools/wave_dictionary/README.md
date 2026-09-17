# Travelling-wave dictionary

Enter a quadratic PDE, obtain its profile operator, and construct its
nonconstant rational, rational-exponential and elliptic **one-pole waves**.
The output gives exact formulas and the necessary and sufficient equations on
their parameters. It also identifies a proposed rational-exponential formula
by its normalized pair, so changes of notation, background, amplitude,
translation and primitive frequency can be checked directly.

The [model table](MODELS.md) specifies 34 representative equations and their
operators. Names are convenient preset labels; the displayed PDE is the input.
The [arithmetic note](ARITHMETIC.md) explains the integer root of every
normalized operator, the low-order denominators and the subset labels.

## Run

Python 3.8 or later; the verified dependency is SymPy 1.13.3:

```sh
python3 -m pip install -r requirements.txt
python3 dictionary.py models
python3 dictionary.py waves --model kdv --set mu=1 --speed 1 --background 0 --kind exponential --solve kappa
python3 dictionary.py waves --model fisher --speed '5/sqrt(6)' --rate '1/sqrt(6)' --kind exponential
python3 dictionary.py waves --model dispersive_ks --set sigma=4 --speed 0 --kind elliptic --g2 '1/12' --g3 0
python3 dictionary.py identify '4*E**2/(1+E**2)**2'
python3 dictionary.py catalogue --order 4
```

Commands work from any directory when `dictionary.py` is given by its path.
Append `--json` for machine-readable results. Quote arithmetic expressions in
the shell; use `**` for powers, `I` for the imaginary unit and `sqrt(...)` for
exact radicals. Decimal literals are converted to exact decimal rationals.

The KdV example gives

$$
U=12Q(1-Q),\qquad Q=\frac{e^{\xi}}{1+e^{\xi}},\qquad \xi=x-t,
$$

after the parameter condition $\kappa^2=1$ is imposed. The two rate signs
give the same expression in the tool's coordinate
$T=(\kappa/2)\tanh(\kappa\xi/2)$. The identification example removes a
frequency multiplier of two and an amplitude multiplier, recovering
$A(\rho)=\rho$, $P_A(\rho)=\rho^2-1$, with label $\{0\}\subset\mathbb F_3$.
This is an algebraic identification; it does not assert that amplitude or
rate changes preserve the coefficients of a fixed PDE.

For custom input, write the equation as

$$
\mathcal L(\partial_t,\partial_x,\partial_y,\partial_z)u+
\mathcal M(\partial_t,\partial_x,\partial_y,\partial_z)(u^2/2)=0.
$$

```sh
python3 dictionary.py waves --linear 'Dt-5*Dx**2+Dx**3' --quadratic Dx --speed=-6 --rate 1 --background 0 --kind exponential
python3 dictionary.py waves --model kp --direction 1 2 0 --speed 13 --set s=1 --rate 1 --background 0 --kind exponential
```

`--set NAME=VALUE` specifies a coefficient and can be repeated. Parameters
left unspecified remain symbolic. The phase is
$\xi=k_xx+k_yy+k_zz-ct$; one-dimensional presets use $(1,0,0)$, and
the plane-wave presets use $(k,\ell,0)$. `--background` means the value
at $e^{\kappa\xi}=0$ for exponential profiles, at infinity for rational
profiles, and a constant equilibrium of the integrated equation for elliptic
profiles. It imposes an additional equation; a background is never assumed to
be a symmetry of an arbitrary input PDE.

## Reading the result

Every listed equality must hold, and every guard must be nonzero.

| Status | Meaning |
|---|---|
| `verified` | The formula satisfies the reduced equation, subject to the displayed nonzero guards. |
| `conditional` | The formula is valid exactly when all the displayed parameter equations and guards hold. |
| `no_match` | This family has an exact contradiction at the supplied parameter values. |
| `unsupported` | The reduction or requested identification lies outside the implemented class. |
| `input_error` | The arithmetic input is invalid. |

`--solve VARIABLE` isolates all roots over $\mathbb C$ when the remaining
equations are univariate with rational coefficients, using their polynomial
gcd and exact algebraic roots. A result marked `implicit` keeps the conditions
and explains why they have not been solved. If several symbolic parameters
remain, this release returns an exact algebraic description of the family,
not an enumerated list of every parameter specialization. A failed or
unsupported solve is never interpreted as an empty list of waves.

No reality filter is applied. Complex normalized pairs and imaginary rates
are included. Reality, poles on a chosen real line, smoothness and boundary
conditions are separate questions. In particular a singular periodic wave
need not be a smooth solitary wave.

## Scope of completeness

After phase substitution, the nonlinear operator must be
$qD^m$, with $q\ne0$, and the linear operator must be divisible by
$D^m$. The tool constructs profiles of the autonomous equation

$$
\widehat L(D)U+\frac q2U^2+K=0.
$$

Here $K=0$ when $m=0$, and is a free integration constant when
$m\ge1$. When $m\ge2$, a general integration also permits polynomial
forcing in $\xi$; this tool selects the autonomous branch by setting the
nonconstant forcing coefficients to zero. This distinction matters for KP
and Boussinesq reductions. Differentiating the reported integrated equation
$m$ times always recovers the specified PDE on its plane-wave ansatz.

The leading coefficient and the nonlinear coefficient must remain nonzero.
Specialize parameters with `--set` before reduction to handle a drop in
order. The default computation limit is profile order eight; `--max-order`
can raise it. It is a practical limit, not a claim about the mathematics.

For each rate or nonsingular elliptic lattice, the construction exhausts the
one-pole sector up to translation. The paper's classification theorem
identifies this sector with **all nonconstant meromorphic profiles of the
autonomous branch** when the profile order is odd or its operator is even.
For a mixed operator of even order, further meromorphic profiles may exist;
the Fisher equation is an example. Constant solutions, cubic nonlinearities,
coupled systems, nonlinear dispersion and potentials that require a slope
substitution are outside the constructor's current input format. The model
table explains the relevant distinctions.

If $B$ is an equilibrium of the integrated equation and $L_p$ its
leading coefficient, the paper's normalization is

$$
v=\frac q{L_p}(U-B),\qquad
P(D)=\frac{\widehat L(D)+qB}{L_p},\qquad
\widehat L(0)B+\frac q2 B^2+K=0.
$$

## Why a large Gröbner basis is unnecessary here

The constructor fixes the PDE coefficients and leaves the rate or lattice
parameters explicit. It does not eliminate all coefficients of all possible
operators at once.

In the exponential case a one-pole profile is a polynomial of degree $p$
in $T=(\kappa/2)\tanh(\kappa\xi/2)$, with
$T'=\kappa^2/4-T^2$. In the rational case use $T=1/\xi$ and
$T'=-T^2$. Write $U=\sum_{j=0}^p b_jT^j$. Dominant balance fixes

$$
b_p=-\frac{2L_p(-1)^p(2p-1)!}{q(p-1)!}.
$$

For $j=p-1,p-2,\ldots,0$, the coefficient of $T^{p+j}$ in the
residual determines $b_j$ linearly. Its multiplier is

$$
L_p(-1)^p j(j+1)\cdots(j+p-1)+qb_p.
$$

It cannot vanish for $0\le j<p$: the product is strictly less than
$(2p-1)!/(p-1)!$, whereas the second term supplies twice that magnitude
with the opposite sign. The remaining residual coefficients are precisely
the parameter conditions returned by the program. This proves necessity as
well as sufficiency within the one-pole sector.

For elliptic profiles, use the complete basis
$1,\wp,\wp',\ldots,\wp^{(p-2)}$, reduce products by
$(\wp')^2=4\wp^3-g_2\wp-g_3$, and successively cancel the highest pole
orders. The same nonzero multipliers determine the principal part and the
constant. The missing simple-pole term is a compatibility condition: the
residue of a one-pole elliptic function must vanish. The remaining equations
and $g_2^3-27g_3^2\ne0$ are necessary and sufficient. In order one an
elliptic profile with one simple pole is impossible.

These are direct exact constructions of specified equations. They do not
replace the separate global counting and simplicity certificates in
[`../../certificates/`](../../certificates/).

## Verification and provenance

The [verification record](VALIDATION.json) gives the checked versions,
counts and scope of the computations on 17 September 2026.

```sh
python3 -m unittest -v
python3 verify_arithmetic.py
python3 verify_catalogue.py
```

The substitution tests include KdV, KdV–Burgers, Fisher, an imaginary-rate
profile, a complex KS pair, elliptic KS, all 33 real reference pairs,
primitive-period normalization, exact root exclusion and unsupported
reductions. The arithmetic verifier replays integer identities and explicit
finite-field witnesses, controlling all primes above the stated threshold.

`verify_catalogue.py` rebuilds the small matching systems over $\mathbb Q$,
computes a graded reverse-lexicographic basis and converts it to lexicographic
order by FGLM, then uses exact real-root counts on every
nonlinear eliminant factor. It recovers all real pairs at $p=1,2,3,4$,
respectively $1,3,8,21$, all rational. The total complex pair counts are
$1,3,10,35$. The real reference file is **not** the input to the wave
constructor. This order conversion avoids the much slower direct lexicographic
calculation; no basis is stored in the repository.

The reference pairs and initial model list were recovered from the author's
`fable_missed_waves_20260917/` calculations. This implementation was written
and checked with Codex on 17 September 2026. The old prototype's swallowed
solver errors and real-only absence statements are not used. Only source,
small exact data and mathematical explanations are committed.
