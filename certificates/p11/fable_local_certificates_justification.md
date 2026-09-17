# Why the local certificates prove what they claim

Date: September 2, 2026. Fable (Claude). This note supplies the arguments behind the two certification procedures used for the
collision points of the special fibre at a gap-two prime (`/tmp/fable/coll/separator.py`, `corank2_certify.py`, `lfield.py`),
so that their outputs can be read as proofs and not as heuristics. Nothing here is new mathematics; it is the bookkeeping of
Newton polygons, Weierstrass preparation and Hensel's lemma with explicit error terms. Codex's reproducers
(`codex_false_positive_notice.md`, the finite-algebra counterexamples, the raw-key precision bug) and its proof review
(`codex_local_certificate_review.md`, five repairs, all adopted here) are the reason the error terms are made explicit.

## 0. Setting

Let \(\ell\) be the structured prime (13 for p=8, 19 for p=11), \(G=(G_0,\dots,G_{d-1})\) the exact equations \(G_r=\ell F_r\in
\mathbb Z_{(\ell)}[a]\), and \(a_0\in\mathbb F_\ell^d\) a singular special point of corank \(c\in\{1,2\}\). Choose pivot equations
\(I\) and pivot coordinates \(T\) (|I|=|T|=d-c) with the block \(\partial G_I/\partial a_T\) invertible modulo \(\ell\), and free
coordinates \(F\), |F|=c. By the implicit function theorem over \(\mathbb Z_\ell\) there are unique series
\(y(\varepsilon)\in\mathbb Z_\ell[[\varepsilon_1,\dots,\varepsilon_c]]^{d-c}\) with \(G_I(a_0+\varepsilon e_F+y(\varepsilon))=0\),
and the local scheme at \(a_0\) is
\[
 Z=\operatorname{Spec}\ \mathbb Z_\ell[[\varepsilon]]/(\tilde g_1,\dots,\tilde g_c),\qquad
 \tilde g_i(\varepsilon)=G_{\mathrm{dep}_i}(a_0+\varepsilon e_F+y(\varepsilon)),
\]
finite flat over \(\mathbb Z_\ell\) of rank the local length \(L\). Its generic fibre consists of the characteristic-zero points
above \(a_0\), counted with multiplicity; the claim to be certified is that there are \(L\) distinct ones.

**What the computation knows.** The simplified Newton iteration computes \(y\) modulo the ideal \(\mathcal I=(\ell^K,\varepsilon^E)\)
(square truncation in the free variables). Uniqueness of the implicit function modulo \(\mathcal I\) gives \(y\equiv y^\ast\) and
hence \(g_i\equiv\tilde g_i\pmod{\mathcal I}\): the computed jets are the true germs modulo \(\mathcal I\), nothing more.

**Local length.** \(L=\dim_{\mathbb F_\ell}\mathbb F_\ell[[\varepsilon]]/(\bar g)\). The computation sees the jets modulo
\(\mathfrak m^E\) and measures \(L_E=\dim\mathbb F_\ell[[\varepsilon]]/(\bar g,\mathfrak m^E)\). If \(L_E<E\), then
\(\mathfrak m^{L_E}\subseteq(\bar g)+\mathfrak m^E\) (Artinian quotient of length \(L_E\)), so \(\mathfrak m^E\subseteq(\bar g)+\mathfrak m\cdot\mathfrak m^E\)
and Nakayama gives \(\mathfrak m^E\subseteq(\bar g)\); hence \(L=L_E\) (this noncircular form is Codex's, `codex_local_certificate_review.md`).
Independently, the sum of the computed local lengths over all singular special points equals the total length minus the number of
simple special points (352716 − 119781 − 87372 = 145563 at p=11), which is forced by flatness of the model; the computed lengths
also equal the presentation counts point by point. Both checks passed at p=8 and p=11.

## 1. Corank one: the tail-aware Newton polygon

Here \(g(\varepsilon)\in\mathbb Z_\ell[[\varepsilon]]\) is known modulo \((\ell^K,\varepsilon^E)\), and \(L\) is the order of
\(\bar g\). Write \(v_i=v(g_i)\) for the known coefficients (\(v_i\ge K\) when \(g_i\equiv0\)).

**Lemma 1 (Newton polygon of the germ).** The roots of \(\tilde g\) with positive valuation correspond to the segments of negative
slope of the lower convex hull of \(\{(i,v(\tilde g_i))\}_{0\le i\le L}\); a segment from \((i_0,v_0)\) to \((i_1,v_1)\) carries
exactly \(i_1-i_0\) roots of valuation \(s=(v_0-v_1)/(i_1-i_0)\). The omitted coefficients \(i\ge E>L\) have valuation \(\ge0\) and
lie on or above the horizontal line through \((L,0)\), so they do not affect this part of the hull. The known coefficients agree
with the true ones modulo \(\ell^K\); a vertex with \(v_i<K\) is exact, a vertex with \(v_i\ge K\) is only a lower bound.

*Proof.* Weierstrass preparation and the classical Newton polygon theorem for power series over a complete discretely valued
field; see any text on local fields. \(\square\)

**Lemma 2 (edge polynomials and separation).** Let a segment have slope \(s=a/b\) in lowest terms, left vertex \((i_0,v_0)\) with
\(v_0<K\), and let \(\varphi(T)=\sum(g_i/\ell^{v_i}\bmod\ell)\,T^{(i-i_0)/b}\) over the lattice points on the segment. Substituting
\(\varepsilon=\ell^{a/b}\tau\) and dividing by \(\ell^{v_0}\) gives a series \(\Phi(\tau)\) in \(\mathbb Z_\ell[\ell^{1/b}][[\tau]]\)
whose reduction is \(\varphi(\tau^b)\) provided every omitted term \(\tilde g_i\varepsilon^i\), \(i\ge E\), contributes a
multiple of \(\ell\): this holds when \(sE>v_0\). If \(\varphi\) is squarefree over \(\overline{\mathbb F_\ell}\), the roots of
\(\tilde g\) on that segment are pairwise distinct.

*Proof.* The roots of valuation exactly \(s\) are the unit roots of \(\Phi\). \(\Phi\) converges on the closed unit disc; by
Weierstrass preparation its number of zeros there is the degree of its reduction, and by Hensel's lemma each simple root of the
reduction lifts to a unique zero. Simple roots of \(\varphi(T)\) in \(T=\tau^b\) give \(b\) distinct \(\tau\), one per \(b\)-th
root, all distinct. The condition \(sE>v_0\) is what guarantees that the reduction is computed from known coefficients only: an
omitted term has valuation at least \(si-v_0\ge sE-v_0\ge1\) after the substitution. \(\square\)

**Lemma 3 (refinement).** If \(\varphi\) has a repeated root \(\theta\in\mathbb F_\ell\) of multiplicity \(\mu\) on a segment of
integral slope \(s\) with left vertex \((i_0,v_0)\), put \(H=v_0+s\,i_0\) (the common valuation of the edge terms after the
substitution; Codex's correction of the first version, which used \(v_0\) and could only miss refinements, never certify falsely).
The \(\mu\) roots near \(\theta\) are the small roots of \(h(\tau)=\tilde g(\ell^s(\theta+\tau))/\ell^{H}\), and
\(h\) is known modulo \(\ell^{K'}\) with
\[
 K'=\min(K-H,\ sE-H),
\]
now as an exact polynomial representative (no further \(\tau\)-truncation): the arithmetic error \(\ell^K\) contributes
\(\ell^{K-H}\), and the omitted tail contributes \(\ell^{si-H}\), \(i\ge E\). Lemma 1 and 2 then apply to \(h\) with
\(E=\infty\). Fractional slopes with repeated roots, or repeated roots outside \(\mathbb F_\ell\), are not refined; the point is
reported as not certified.

*Proof.* Direct substitution; this is the bound stated in Codex's notice. \(\square\)

**Lemma 4 (unknown left vertex).** If the left vertex of a segment has \(v_0\ge K\) (coefficient zero to precision), the segment's
true slope is at least \(K-v_1\) over its length. If the segment has length one, it carries a single root; it is distinct from
every root of every other segment whenever \(K-v_1\) exceeds all other slopes, because roots on different segments have different
valuations. Segments of length \(\ge2\) with an unknown left vertex certify nothing.

**Theorem (corank one).** If every segment of the polygon of \(g\) up to \(L\) is certified by Lemma 2, Lemma 3 (recursively) or
Lemma 4, then the \(L\) points of the generic fibre of \(Z\) are distinct. Conversely the procedure never certifies a multiple
root: Lemma 2 needs squarefree reductions, Lemma 3 propagates the error, Lemma 4 needs distinct valuations.

Regression: the exact germ \((t-13)^2(1+t+\dots+t^7)\), whose degree-<8 jet is \([169,143,\dots]\), is refused at \(K=6\) and
\(K=14\) (Codex's reproducer); \((T-13)^2(1+T)\) as an exact polynomial is refused; \((T-13)(T-26)(1+T+T^2)\) and \((T^2-13)(1+T)\)
are certified. Codex's independent suite of 243 exact repeated-root germs produced no false certificate.

## 2. Corank two: exact certification per branch

For \(c=2\) no truncation bound is used at all. The truncated analysis (resultant, descent, second coordinate) serves only to
produce, for each branch, a local field \(K\) and an approximate point \(a^\ast\in O_K^d\). The certificate is then:

**Lemma 5 (fields).** For a *leaf* branch (simple edge root after all refinements; initial repeated-edge data do not determine the
final field, e.g. \((x^2-13)^2-2\cdot13^3\) has slope 1/2 with edge \((T-1)^2\) but needs residue degree 2 as well) with slope
\(a/b\), \(\gcd(a,b)=1\), \(\ell\nmid b\), and edge root \(T_0\in\mathbb F_{\ell^f}\),
let \(W=\mathbb Z_\ell[\zeta]/(m)\) be the unramified extension with residue field \(\mathbb F_{\ell^f}\), \(\tilde T_0\in W\) a lift
of \(T_0\), and \(s,t\) with \(as+bt=1\). Put \(\varpi^b=\ell\,\tilde T_0^{\,s}\). Then \(O_K=W[\varpi]\) is the full ring of integers
of \(K=W[1/\ell](\varpi)\), a totally ramified extension of degree \(b\) of \(\mathbb Q_\ell(\zeta)\), and every root of the
branch with those data lies in a field isomorphic to \(K\): the unit \(\tilde T^\ast/\tilde T_0\equiv1\) between the exact and
approximate values is a \(b\)-th power because \(\ell\nmid b\). (Eisenstein basis, Codex's correction of my first version, which
used \(\pi^b=\ell^a u\) and fails to be maximal for \(a>1\).)

**Lemma 6 (Newton–Kantorovich in a DVR).** Let \(F=G\) restricted to \(O_K^d\), \(J\) its Jacobian, \(a\in O_K^d\), \(\delta=\det
J(a)\ne0\). If \(v(F(a))>2v(\delta)\) componentwise (valuation of \(K\), \(v(\varpi)=1\)), then there is a unique \(a^\dagger\in
O_K^d\) with \(F(a^\dagger)=0\) and \(v(a^\dagger-a)\ge v(F(a))-v(\delta)\) componentwise.

*Proof.* Standard multivariate Hensel lemma over a complete DVR, using the adjugate: the map \(x\mapsto x-J(a)^{-1}F(x)\) is a
contraction on the ball of radius \(v(F(a))-v(\delta)\) around \(a\) because \(J(a)^{-1}=\operatorname{adj}J(a)/\delta\) has
denominator valuation \(v(\delta)\) and the quadratic remainder of \(F\) is bounded by the square of the displacement. \(\square\)

The point \(a^\dagger\) has coordinates in \(O_K\); its \([K:\mathbb Q_\ell]=fb\) embeddings into \(\overline{\mathbb Q}_\ell\) are
points of \(\mathscr X_p\), and they are pairwise distinct as soon as one coordinate generates \(K\) (Lemma 7).

**Lemma 7 (orbit identification and separation, replacing the first version).** Let \(x=\sum_j w_ja_j^\dagger\) be a fixed
linear form of the certified point (the same weights for every branch), viewed as an element of \(K\), and let \(\chi_x\) be the
characteristic polynomial of multiplication by \(x\) on \(K\) as a \(\mathbb Q_\ell\)-vector space (degree \(n=[K:\mathbb Q_\ell]\)),
computed from the refined \(a\) and hence known modulo \(\ell^{\lfloor\rho/b\rfloor}\) where \(\rho=v(F(a))-v(\delta)\).
(i) If \(\operatorname{disc}\chi_x\not\equiv0\) modulo that precision, the \(n\) embeddings of \(a^\dagger\) are pairwise distinct
points, i.e. the orbit has exactly \(n\) elements. (ii) Two certified records of the same degree represent provably different
orbits if their \(\chi_x\) differ modulo \(\ell^{\min(\text{prec}_1,\text{prec}_2)}\); if they agree at the common precision they are
counted once (conservative). Different degrees are different orbits. No branch label, shift, slope or residue enters the count
(Codex showed that distinct shifts do not prove disjointness and that a reduction at each record's own precision can split one
orbit into two keys). \(\square\)

**Theorem (corank two).** If the certified orbits, identified and separated by Lemma 7, have degrees summing to \(L\),
then the generic fibre of \(Z\) consists of exactly \(L\) distinct points. No assumption on the truncated series enters: the
candidates could be arbitrary; the conclusion rests on Lemmas 5–7 applied to the exact equations, and on the local length \(L\),
which is exact by Section 0. If the degrees sum to less than \(L\), nothing is concluded about the remaining points.

**Exact pulses.** When the free coordinate is the endpoint jump \(a_d\), pulses have \(\varepsilon_2=0\) exactly and the jet \(g_1\)
is divisible by \(\varepsilon_2\). The local scheme then splits as \(\{\varepsilon_2=0,\ g_2=0\}\cup\{g_1/\varepsilon_2=0,\ g_2=0\}\);
the first component is a univariate problem in \(t\) handled by the descent, and its branches are certified with \(\varepsilon_2=0\)
as the candidate second coordinate. A vanishing jet column is only evidence to precision, so the split is candidate generation, not
a proof of an exact factorization (Codex's point (3)); the resulting candidates are certified by Lemma 6 on the exact equations,
and completeness is still judged by the degree sum against \(L\).

## 3. Status of the certified sets

- p=8, ℓ=13 (known reduced, the test bed): 942 corank-1 points certified with the height-corrected separator; all 234 corank-2
  points complete, 223 with the first-generation driver and 11 with the second-generation one (Codex's descent over local fields for
  repeated edge roots in residue extensions or on fractional slopes; orbit identification by the characteristic polynomial of a
  common linear form; second coordinate from the union of the local finder and the descent). Total 6435, as the Gröbner certificate.
- p=11, ℓ=19: all 47801 corank-1 points certified (97971 points); first-generation corank-2 batch 11145 of 11592 points complete,
  none over-certified; the 447 incomplete points are in the second-generation pass (update at the end of this note).

## 4. Known limitations, honestly

- The descent refines only over \(\mathbb Q_\ell\) with \(\mathbb F_\ell\)-rational repeated roots; branches needing an extension are
  left uncertified. Codex is writing the general descent over local fields; until then those points remain open, not wrong.
- Lemma 6 is applied with the computed \(a\), and the Newton iteration in \(O_K\) loses \(a\) digits of precision per division by
  \(\varpi\); the working precision \(M=24\) is far above the valuations encountered (\(v(\delta)\le3\), \(v(F)\le7\)).
- The linear change \(c\) is tried from a short list; a point that certifies for one \(c\) is certified, a point that fails for all
  is reported incomplete. Any \(c\) gives a valid certificate when complete; the choice affects only candidate quality.

## 5. Reflection-fixed points (added September 2, evening)

The reflection \(\iota\) acts on \(\mathscr X_p\); at \(p=8\) it negates the odd coefficients \(a_1,a_3,a_5,a_7\) and fixes
\(a_2,a_4,a_6\). A special point fixed by \(\iota\) (odd coefficients zero mod \(\ell\)) is where the generic route is least
natural: the eliminant in the odd direction is even, its low coefficients vanish identically, and the two-variable jets must be read
with care. The generic driver did certify the one such corank-2 point of \(p=8\), \(A_0=x^7+4x^5+12x^3+9x\), after a linear change
\(c=7\): four \(\mathbb Q_{13}\)-rational points, two of them reflection-fixed and one reflection pair. Codex then resolved the same
point by a symmetry-preserving construction (`codex_reflection_p8.py`, `codex_reflection_p8.md`): in the exact chart
\(a_5=t,\ a_1=tb_1,\ a_3=tb_3,\ a_7=tb_7,\ T=t^2\), dividing the odd equations by \(t\) gives seven polynomial equations in
\((T,b_1,b_3,b_7,a_2,a_4,a_6)\) whose Jacobian is a unit at the quotient point (determinant \(3\) mod 13), so the off-fixed pair is an
ordinary Hensel lift; the fixed sector is \(E(0,u)=0\). The two computations agree modulo \(13^6\) coordinate by coordinate, and the
off-fixed lift has \(v_{13}(T)=4\), so \(v(t)=2\).

The structure behind this is the following lemma, due to Codex, which we record because it gives the exact obstruction and a
local-length proof that does not use presentation counts.

**Lemma 8 (equivariant local algebra).** Let \(O\) be a complete discrete valuation ring of residue characteristic \(\neq2\) with
fraction field \(K\), and let the local equations at an \(\iota\)-fixed point be, after equivariant implicit elimination,
\(g_1=E(t^2,u)\), \(g_2=t\,H(t^2,u)\) with \(E,H\in O[[T,u]]\). Assume the quotient Jacobian \(\partial(E,H)/\partial(T,u)\) is a
unit at the residue point and that \(E(0,u)\) is distinguished of degree \(m\) in \(u\), with Weierstrass polynomial \(W(u)\). Let
\((\tau,\eta)\in O^2\) be the unique Hensel lift of the quotient system \(E=H=0\). Then \(A=O[[t,u]]/(E,tH)\) is finite and free of
rank \(m+2\) over \(O\), and \(A\otimes K\) is reduced if and only if \(\tau\neq0\) and \(W\) is squarefree.

*Proof.* Since \(E(0,u)\) is distinguished, \(O[[t,u]]/(E)\) is free over \(O[[t]]\) and \(t\) is a nonzerodivisor on it. If
\(ta\in(E,tH)\), write \(ta=eE+tHh\); then \(t(a-Hh)\in(E)\), so \(a\in(E,H)\). Hence multiplication by \(t\) gives the exact
sequence \(0\to C\to A\to B\to0\) with \(C=O[[t,u]]/(E,H)\cong O[t]/(t^2-\tau)\), free of rank 2 by the unit quotient Jacobian, and
\(B=A/tA=O[[u]]/(E(0,u))\cong O[u]/(W)\), free of rank \(m\). An extension of free \(O\)-modules splits, so \(A\) is free of rank
\(m+2\). Over \(K\): if \(\tau\neq0\), the ideals \((t)\) and \((H)\) become comaximal modulo \(E\) once the uniformizer is inverted
(on \(H=0\) one has \(t^2=\tau\), a unit of \(K\)), and the Chinese remainder theorem gives \(A_K\cong B_K\times K[t]/(t^2-\tau)\),
reduced exactly when \(W\) is squarefree. Conversely, if \(\tau=0\) or \(W\) is not squarefree, \(A_K\) has the non-reduced quotient
\(C_K\) or \(B_K\), and a finite reduced \(K\)-algebra has no non-reduced quotient. \(\square\)

Two remarks. First, the unit quotient Jacobian places \(\tau\) in \(O\), not in \(O^2\): whether the pair \(t=\pm\sqrt\tau\) is
rational or a quadratic orbit is a separate outcome, and at the \(p=8\) point it happens to be rational. The obstructions to
reducedness are \(\tau=0\) and \(\operatorname{disc}W=0\), nothing else. Second, the lemma proves the local length \(m+2\) and local
flatness directly, so at these points the accounting does not depend on the flatness total. At \(A_0\) above, \(m=2\), \(W\) has two
distinct rational roots and \(v(\tau)=4\), so \(L=4\) and the point is reduced by two independent routes. At \(p=11\) there are 36
reflection-fixed corank-2 special points, all of length 4; all of them were completed by the first-generation driver (Codex checked
the inventory), so the lemma is a cross-check there rather than a necessity.
