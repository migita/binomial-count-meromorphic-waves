"""Exact one-pole profiles for constant-coefficient quadratic equations.

Only SymPy is required. All equations in a result must hold simultaneously;
all guards must be nonzero. An unresolved equation is never an absence claim.
"""

import ast
from functools import reduce
from math import gcd

import sympy as s


RHO, T, X, Y = s.symbols("rho T X Y")
DT, DX, DY, DZ = s.symbols("Dt Dx Dy Dz")
OPERATORS = (DT, DX, DY, DZ)


class UnsupportedReduction(ValueError):
    """The input is outside the tool's specified reduction or profile class."""


def parse(text):
    """Parse arithmetic without evaluating Python code or arbitrary functions."""
    def visit(node):
        if isinstance(node, ast.Expression):
            return visit(node.body)
        if isinstance(node, ast.Constant) and type(node.value) in (int, float):
            return s.Rational(str(node.value))
        if isinstance(node, ast.Name):
            return s.I if node.id == "I" else s.Symbol(node.id)
        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.USub):
                return -visit(node.operand)
            if isinstance(node.op, ast.UAdd):
                return visit(node.operand)
        if isinstance(node, ast.BinOp):
            a, b = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add):
                return a + b
            if isinstance(node.op, ast.Sub):
                return a - b
            if isinstance(node.op, ast.Mult):
                return a * b
            if isinstance(node.op, ast.Div):
                return a / b
            if isinstance(node.op, ast.Pow):
                return a ** b
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == "sqrt" and len(node.args) == 1
                and not node.keywords):
            return s.sqrt(visit(node.args[0]))
        raise ValueError("Use numbers, symbols, + - * / **, parentheses and sqrt only.")

    value = visit(ast.parse(text, mode="eval"))
    if value.has(s.zoo, s.nan, s.oo, -s.oo):
        raise ValueError("The expression is not finite.")
    return value


def clean(expression):
    return s.cancel(s.expand(expression))


def unique(expressions, equations=False):
    result = []
    for expression in expressions:
        expression = s.factor(clean(expression))
        if equations:
            expression = s.factor(s.fraction(expression)[0])
            if expression == 0:
                continue
        elif expression.is_zero is False and not expression.free_symbols:
            continue
        if expression not in result and -expression not in result:
            result.append(expression)
    return result


def reduce_pde(linear, quadratic, speed, direction=(1, 0, 0), max_order=8):
    """Reduce L u + M(u**2/2)=0 along xi=kx*x+ky*y+kz*z-speed*t.

    M must become q*rho**m and L must be divisible by rho**m.
    The autonomous integrated branch is Lhat(D)U+q*U**2/2+K=0.
    For m=0, K=0. For m>=2, polynomial forcing is outside this branch.
    """
    linear, quadratic = map(s.sympify, (linear, quadratic))
    direction = tuple(map(s.sympify, direction))
    if len(direction) != 3:
        raise ValueError("direction must contain kx, ky, kz")
    if all(k == 0 for k in direction) and s.sympify(speed) == 0:
        raise UnsupportedReduction("The travelling phase is constant.")
    try:
        s.Poly(linear, *OPERATORS)
        s.Poly(quadratic, *OPERATORS)
        sub = dict(zip(OPERATORS, [-s.sympify(speed)*RHO]
                       + [k*RHO for k in direction]))
        lp, mp = [s.Poly(s.expand(f.subs(sub, simultaneous=True)), RHO)
                  for f in (linear, quadratic)]
    except s.PolynomialError as exc:
        raise UnsupportedReduction("L and M must be polynomials in the derivative symbols.") from exc
    if mp.is_zero or len(mp.terms()) != 1:
        raise UnsupportedReduction("The nonlinear operator must reduce to one nonzero monomial q*rho**m.")
    (m,), q = mp.terms()[0]
    if lp.is_zero or any(j[0] < m for j, coefficient in lp.terms() if coefficient != 0):
        raise UnsupportedReduction("The linear operator is zero or is not divisible by the nonlinear derivative order.")
    phat = s.Poly(clean(lp.as_expr()/RHO**m), RHO)
    p, leading = int(phat.degree()), phat.LC()
    if not 1 <= p <= max_order:
        raise UnsupportedReduction("Profile order %s is outside the configured range 1..%s." % (p, max_order))
    even = p % 2 == 0 and all(phat.nth(j) == 0 for j in range(1, p, 2))
    guards = [leading, q, s.denom(s.together(linear)), s.denom(s.together(quadratic))]
    return {
        "linear_pde": linear, "quadratic_pde": quadratic,
        "speed": s.sympify(speed), "direction": direction,
        "integrations": m, "order": p, "L": phat.as_expr(),
        "q": q, "leading": leading,
        "P_about_B": clean((phat.as_expr()+q*s.Symbol("B"))/leading),
        "background_equation": phat.nth(0)*s.Symbol("B")+q*s.Symbol("B")**2/2
                               + (s.Symbol("K") if m else 0),
        "v_scale": clean(q/leading), "guards": unique(guards),
        "meromorphic_classification_applies": bool(p % 2 or even),
        "scope": "Nonconstant one-pole profiles in the autonomous integrated branch; complex parameters allowed.",
    }


def linear_apply(profile, reduction, derivative):
    polynomial = s.Poly(reduction["L"], RHO)
    value, out = profile, s.S.Zero
    for j in range(reduction["order"] + 1):
        out += polynomial.nth(j)*value
        if j < reduction["order"]:
            value = derivative(value)
    return out


def residual(profile, reduction, derivative, normal=clean):
    return normal(linear_apply(profile, reduction, derivative)
                  + reduction["q"]*profile**2/2)


def finish(reduction, kind, profile, remainder, conditions, guards, coordinates):
    condition_denominators = [s.denom(s.together(e)) for e in conditions]
    conditions = unique(conditions, equations=True)
    guards = unique(reduction["guards"] + guards + condition_denominators
                    + [s.denom(s.together(profile)), s.denom(s.together(remainder))])
    impossible = (any(g == 0 for g in guards)
                  or any(e.is_zero is False and not e.free_symbols for e in conditions))
    status = "no_match" if impossible else ("conditional" if conditions else "verified")
    return {
        "kind": kind, "status": status, "profile": s.factor(profile),
        "coordinates": coordinates, "conditions": conditions, "guards": guards,
        "integrated_residual": s.factor(remainder),
        "integration_constant": (-s.Poly(remainder, *coordinates).coeff_monomial(1)
                                 if reduction["integrations"] else s.S.Zero),
        "scope": "Necessary and sufficient conditions for this one-pole family, subject to the guards.",
    }


def riccati_profile(reduction, kind="exponential", rate=None, background=None):
    """The unique polynomial in T with a pole of the required order.

    Exponential: T=(rate/2)*tanh(rate*xi/2), T'=rate**2/4-T**2.
    Rational: T=1/xi, T'=-T**2. A translation of xi is arbitrary.
    """
    if kind not in ("exponential", "rational"):
        raise ValueError("kind must be exponential or rational")
    rate = s.Symbol("kappa") if rate is None else s.sympify(rate)
    p, q, leading = reduction["order"], reduction["q"], reduction["leading"]
    background_symbols = set() if background is None else s.sympify(background).free_symbols
    if T in (reduction["L"].free_symbols | q.free_symbols | rate.free_symbols | background_symbols):
        raise ValueError("T is reserved for the profile coordinate.")
    h = rate**2/4 if kind == "exponential" else s.S.Zero
    derivative = lambda f: s.expand((h-T**2)*s.diff(f, T))
    bp = -2*leading*(-1)**p*s.factorial(2*p-1)/(s.factorial(p-1)*q)
    profile = bp*T**p
    for j in range(p-1, -1, -1):
        coefficient = s.Poly(residual(profile, reduction, derivative), T).nth(p+j)
        pivot = leading*(-1)**p*s.rf(j, p)+q*bp
        profile += clean(-coefficient/pivot)*T**j
    profile = clean(profile)
    remainder = residual(profile, reduction, derivative)
    conditions = [co for (j,), co in s.Poly(remainder, T).terms()
                  if j or not reduction["integrations"]]
    if background is not None:
        endpoint = -rate/2 if kind == "exponential" else 0
        conditions.append(profile.subs(T, endpoint)-s.sympify(background))
    result = finish(reduction, kind, profile, remainder, conditions,
                    [rate] if kind == "exponential" else [], [T])
    result["coordinate_definition"] = ("T = (kappa/2)*tanh(kappa*xi/2)"
                                       if kind == "exponential" else "T = 1/xi")
    if kind == "exponential":
        result["rate"] = rate
        result["profile_in_Q"] = s.factor(profile.subs(T, rate*(s.Symbol("Q")-s.Rational(1, 2))))
        result["Q_definition"] = "Q = exp(kappa*xi)/(1+exp(kappa*xi))"
    return result


def elliptic_arithmetic(g2, g3):
    cubic = 4*X**3-g2*X-g3

    def normal(expression):
        polynomial = s.Poly(s.expand(expression), Y)
        return clean(sum(co*Y**(j % 2)*cubic**(j//2)
                         for (j,), co in polynomial.terms()))

    def derivative(expression):
        return normal(Y*s.diff(expression, X)+(6*X**2-g2/2)*s.diff(expression, Y))

    return normal, derivative


def pole_coefficient(expression, order):
    """At each pole order >=2 there is one monomial X**a*Y**b, b<2."""
    b = order % 2
    a = (order-3*b)//2
    if a < 0:
        return s.S.Zero
    return s.Poly(expression, X, Y).coeff_monomial(X**a*Y**b)


def elliptic_profile(reduction, g2=None, g3=None, background=None):
    g2 = s.Symbol("g2") if g2 is None else s.sympify(g2)
    g3 = s.Symbol("g3") if g3 is None else s.sympify(g3)
    p, q, leading = reduction["order"], reduction["q"], reduction["leading"]
    background_symbols = set() if background is None else s.sympify(background).free_symbols
    if {X, Y} & (reduction["L"].free_symbols | q.free_symbols | g2.free_symbols | g3.free_symbols | background_symbols):
        raise ValueError("X and Y are reserved for the elliptic coordinates.")
    if p == 1:
        return {"kind": "elliptic", "status": "no_match", "conditions": [], "guards": [],
                "reason": "An elliptic function cannot have a single simple pole in a fundamental parallelogram."}
    normal, derivative = elliptic_arithmetic(g2, g3)
    basis = [X]
    for j in range(1, p-1):
        basis.append(derivative(basis[-1]))
    sp = 2*s.factorial(2*p-1)/s.factorial(p-1)**2
    profile = -sp*leading/q*basis[p-2]
    for j in range(p-3, -1, -1):
        order = p+j+2
        remainder = residual(profile, reduction, derivative, normal)
        pivot = pole_coefficient(normal(linear_apply(basis[j], reduction, derivative)
                                        + q*profile*basis[j]), order)
        profile = normal(profile-pole_coefficient(remainder, order)/pivot*basis[j])
    remainder = residual(profile, reduction, derivative, normal)
    profile = normal(profile-pole_coefficient(remainder, p)/(q*pole_coefficient(profile, p)))
    remainder = residual(profile, reduction, derivative, normal)
    conditions = [co for powers, co in s.Poly(remainder, X, Y).terms()
                  if any(powers) or not reduction["integrations"]]
    if background is not None:
        b = s.sympify(background)
        equilibrium = reduction["L"].subs(RHO, 0)*b+q*b**2/2
        conditions.append(remainder.subs({X: 0, Y: 0})-equilibrium)
    result = finish(reduction, "elliptic", profile, remainder, conditions,
                    [g2**3-27*g3**2], [X, Y])
    result.update({"g2": g2, "g3": g3,
                   "coordinate_definition": "X = wp(xi;g2,g3), Y = wp'(xi;g2,g3), Y**2 = 4*X**3-g2*X-g3"})
    return result


def solve_univariate(result, variable):
    """Solve all remaining equalities over C when they are univariate over Q.

    Symbolic parameters or unsupported coefficient fields leave exact conditions
    visible. No general-purpose solve() call is interpreted as a completeness proof.
    """
    variable = s.sympify(variable)
    if not isinstance(variable, s.Symbol):
        raise ValueError("The solve variable must be a symbol.")
    if result["status"] == "no_match":
        return {"status": "solved", "variable": variable, "roots": []}
    equations = result["conditions"]
    if not equations:
        return {"status": "free", "variable": variable, "guards": result["guards"]}
    if any(e.free_symbols - {variable} for e in equations):
        return {"status": "implicit", "reason": "Other parameters remain in the exact conditions."}
    try:
        polynomials = [s.Poly(e, variable, domain=s.QQ) for e in equations]
        common = reduce(s.gcd, polynomials).sqf_part()
        for guard in result["guards"]:
            if not guard.free_symbols - {variable}:
                try:
                    forbidden = s.Poly(s.fraction(s.cancel(guard))[0], variable, domain=s.QQ)
                    common = common.exquo(s.gcd(common, forbidden))
                except (s.PolynomialError, s.polys.polyerrors.CoercionFailed):
                    pass  # The original guard remains an explicit condition on each root.
        roots = common.all_roots(radicals=False)
        return {"status": "solved", "variable": variable, "polynomial": common.as_expr(),
                "roots": roots, "guards": result["guards"]}
    except (s.PolynomialError, s.polys.polyerrors.CoercionFailed, NotImplementedError) as exc:
        return {"status": "implicit", "reason": "Exact univariate isolation is unavailable: " + str(exc)}


def identify(expression, variable=None):
    """Identify a rational function of exp(z), modulo background/scale/translation.

    A common integral frequency multiplier is removed before checking the
    single-pole condition. Algebraic coefficients are allowed; finite-field
    subset labels are emitted only for rational coefficients integral there.
    """
    variable = s.Symbol("E") if variable is None else s.sympify(variable)
    expression = s.cancel(expression)
    if expression.free_symbols - {variable}:
        raise UnsupportedReduction("Identification requires specified coefficients; substitute any parameters first.")
    try:
        numerator, denominator = [s.Poly(f, variable, extension=True)
                                  for f in s.fraction(expression)]
    except s.PolynomialError as exc:
        raise UnsupportedReduction("Input must be rational in E=exp(z).") from exc
    if denominator.nth(0) == 0 or numerator.degree() > denominator.degree():
        raise UnsupportedReduction("The profile must be finite at E=0 and E=infinity.")
    background = numerator.nth(0)/denominator.nth(0)
    numerator = s.Poly(numerator.as_expr()-background*denominator.as_expr(), variable, extension=True)
    if numerator.is_zero:
        raise UnsupportedReduction("The profile is constant.")
    exponents = [j for polynomial in (numerator, denominator)
                 for (j,), coefficient in polynomial.terms() if j and coefficient != 0]
    frequency = reduce(gcd, exponents)
    def divide_frequency(poly):
        return s.Poly(sum(co*variable**(j//frequency) for (j,), co in poly.terms()), variable, extension=True)
    numerator, denominator = map(divide_frequency, (numerator, denominator))
    if denominator.sqf_part().degree() != 1:
        raise UnsupportedReduction("More than one pole remains per primitive exponential period.")
    p = int(denominator.degree())
    pole = clean(-denominator.nth(p-1)/(p*denominator.LC()))
    Q = s.Symbol("Q")
    translated = clean((numerator.as_expr()/denominator.as_expr()).subs(variable, -pole*Q/(1-Q)))
    try:
        polynomial = s.Poly(translated, Q)
    except s.PolynomialError as exc:
        raise UnsupportedReduction("The normalized profile is not a polynomial in Q.") from exc
    sp = 2*s.factorial(2*p-1)/s.factorial(p-1)**2
    scale = clean((-1)**(p-1)*sp*s.factorial(p-1)/polynomial.LC())
    v = s.expand(scale*translated)
    derivative = lambda f: s.expand(Q*(1-Q)*s.diff(f, Q))
    basis = [Q]
    for j in range(1, p):
        basis.append(derivative(basis[-1]))
    rest, A = v/sp, s.S.Zero
    for j in range(p-1, -1, -1):
        coefficient = clean(s.Poly(rest, Q).nth(j+1)/s.Poly(basis[j], Q).nth(j+1))
        A += coefficient*RHO**j
        rest = clean(rest-coefficient*basis[j])
    derivatives = [v]
    for j in range(p):
        derivatives.append(derivative(derivatives[-1]))
    remainder, P = s.expand(derivatives[p]+v**2/2), RHO**p
    for j in range(p-1, -1, -1):
        coefficient = clean(-s.Poly(remainder, Q).nth(p+j)/s.Poly(derivatives[j], Q).nth(p+j))
        P += coefficient*RHO**j
        remainder = clean(remainder+coefficient*derivatives[j])
    result = {"status": "verified" if remainder == 0 else "no_match", "order": p,
              "primitive_frequency_multiplier": frequency, "background": background,
              "pole_in_primitive_exponential": pole, "amplitude_normalization": scale,
              "A": s.factor(A), "mirror_A": s.factor((-1)**(p-1)*A.subs(RHO, -RHO)),
              "P": s.factor(P), "profile_in_Q": s.factor(v), "residual": remainder}
    if remainder == 0:
        result["integer_root"] = next(n for n in range(1, p+1) if s.simplify(A.subs(RHO, n)) != 0)
        ell = 2*p-1
        coefficients = s.Poly(A, RHO).all_coeffs()
        if s.isprime(ell) and all(a.is_Rational and s.denom(a) % ell != 0 for a in coefficients):
            roots = [n for n in range(ell) if sum(int(s.numer(a))*pow(int(s.denom(a)), -1, ell)
                     *pow(n, p-1-j, ell) for j, a in enumerate(coefficients)) % ell == 0]
            result["prime_index_label"] = {"prime": ell, "subset": roots}
    return result


def serializable(value):
    if isinstance(value, dict):
        return {str(k): serializable(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [serializable(v) for v in value]
    if isinstance(value, s.Basic):
        return str(value)
    return value
