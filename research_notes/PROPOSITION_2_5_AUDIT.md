# Audit of Proposition 2.5: interior \(L^2\) Hessian estimate on products of cones

**Project:** `MdeBorbon/LeanConicalKahler`  
**Authors of the paper:** Martin de Borbon and Gregory Edwards  
**Paper:** *Schauder estimates on products of cones*, *Commentarii Mathematici Helvetici* **96** (2021), 113–148; DOI: `10.4171/CMH/509`  
**Version inspected:** [arXiv:2002.07668v1](https://arxiv.org/pdf/2002.07668), 18 February 2020, especially printed pp. 8–9 (§2.4 and Proposition 2.5).  
**Audit date:** 5 November 2026  
**Purpose:** Preserve mathematical findings, counterexamples, and proof obligations for future research and Lean formalisation. **This file is not a Lean proof and is not an erratum for the published journal version.** The published article's full text has not been compared with this arXiv version.

## Summary and confidence levels

1. **Confirmed error — omitted outer boundary term.** The integration of the Bochner identity in Proposition 2.5 misses a boundary term from \(\partial B_1\). Its displayed global equality between the \(L^2\) Hessian and \(L^2\) Laplacian norms is false, even for a smooth radial Dirichlet eigenfunction on a genuine cone with \(0<\beta<1\).
2. **Confirmed favourable sign in the smooth calculation.** On a geodesic ball centred at the cone vertex, the omitted boundary term is non-positive. Under sufficient regularity to justify integration up to the boundary and passage across the singular strata, the *inequality* required for the spectral argument survives. This does **not**, by itself, resolve all regularity and trace issues.
3. **Confirmed error — purported equivalence of second-order Sobolev norms.** The sentence preceding Proposition 2.5 that the intrinsic Riemannian Hessian and Euclidean Hessian are uniformly equivalent is false. Equality of the resulting \(W^{2,2}\) spaces cannot be inferred from uniform equivalence of metric tensors. A concrete counterexample is below.
4. **Promising repair, not yet completely verified.** A *localized* Bochner estimate avoids the outer boundary and can be applied to finite eigenfunction sums. It requires explicit control of singular-set cutoffs, eigenfunction regularity, weak Hessian identification, and uniformity in ball centres before it becomes a complete proof of the proposition as used later in the paper.
5. **Scope of conclusion.** The audit does not disprove Proposition 2.5 or Theorem 1.1. It identifies a false step in the arXiv proof and a plausible route to repair the required interior estimate. Do not mark the proposition as formally established on the basis of this note.

## 1. Statement and normalisation

Work on

\[
M=\prod_{a=1}^n C(S^1_{2\pi\beta_a})\times\mathbb R^{m-2n},\qquad 0<\beta_a<1,
\]

with the paper's Riemannian metric

\[
g=\sum_{a=1}^n(dr_a^2+\beta_a^2r_a^2d\theta_a^2)+ds^2,
\]

and \(\Delta_g=\operatorname{div}_g\nabla_g\), so that the eigenvalue equation is \(-\Delta_g v=\lambda v\) for \(\lambda>0\). The singular set is \(S=\bigcup_a\{r_a=0\}\). Let \(B_1\) be the ball centred at the common cone vertex.

Proposition 2.5 states, for a weak solution \(-\Delta_g u=f\) on \(B_1\) with \(u\in W^{1,2}\) and \(f\in L^2\), that \(u\in W^{2,2}(B_{1/2})\) and

\[
\|\nabla_g^2u\|_{L^2(B_{1/2})}\le C\bigl(\|f\|_{L^2(B_1)}+\|u\|_{L^2(B_1)}\bigr).
\tag{P2.5}
\]

The meaning of \(W^{2,2}\) must be fixed: the intrinsic \(L^2\) Hessian and the Euclidean distributional second derivatives are **not** interchangeable by metric comparison alone. For comparison with the current Lean project, its upstream Kähler Laplacian for \(g_{\mathrm{Lean}}=2q\) is \(\tfrac12\Delta_g\) when \(q\) is the paper's model metric.

## 2. The missing outer-boundary contribution

The arXiv proof, printed p. 8, uses the pointwise Bochner identity on the regular locus,

\[
\frac12\Delta_g|\nabla v|^2=|\nabla_g^2v|^2-\lambda|\nabla v|^2,
\qquad -\Delta_gv=\lambda v.
\]

It multiplies this identity by a cutoff \(\chi_\varepsilon\) excluding \(S\) and writes an integral formula with only \(\tfrac12\int_{B_1}(\Delta\chi_\varepsilon)|\nabla v|^2\). Since \(\chi_\varepsilon\) does **not** vanish at the *outer boundary* of \(B_1\), integration by parts also produces an outer boundary term. The proof subsequently asserts

\[
\int_{B_1}|\nabla^2_gv|^2
=\lambda\int_{B_1}|\nabla v|^2
=\lambda^2\int_{B_1}v^2.
\tag{Incorrect equality}
\]

Even in the nonsingular smooth case, the correct identity is

\[
\int_{B_1}|\nabla^2_gv|^2
=\lambda\int_{B_1}|\nabla v|^2
+\frac12\int_{\partial B_1}\partial_\nu|\nabla v|^2.
\tag{2.1}
\]

Here \(\nu\) denotes the outward unit normal. Because \(v=0\) on \(\partial B_1\) and \(\Delta v=0\) there by the eigenvalue equation, at a smooth boundary point

\[
\nabla v=(\partial_\nu v)\nu,
\qquad \nabla_g^2v(\nu,\nu)=-H\,\partial_\nu v,
\]

where \(H\) is the outward mean curvature (trace of the second fundamental form). Hence

\[
\frac12\partial_\nu|\nabla v|^2
=\nabla_g^2v(\nu,\nu)\,\partial_\nu v
=-H(\partial_\nu v)^2.
\]

The smooth part of the radius-one sphere centred at the vertex of an \(m\)-dimensional metric cone has \(H=m-1\). Thus, *provided the boundary and singular-stratum limits are justified*,

\[
\boxed{
\int_{B_1}|\nabla_g^2v|^2
=\lambda^2\int_{B_1}v^2
-(m-1)\int_{\partial B_1}(\partial_\nu v)^2.
}
\tag{2.2}
\]

The missing term is non-positive. This gives the desired estimate

\[
\|\nabla_g^2v\|_{L^2(B_1)}\le\lambda\|v\|_{L^2(B_1)}
\]

**if** (2.2) has been rigorously extended across the singular set and the boundary intersections. In a formal proof, do not assume either of these extensions without establishing the necessary regularity/traces.

### Finite eigenfunction sums

For \(v_N=\sum_{j=1}^N\lambda_j^{-1}f_j\), where the \(f_j\)'s are \(L^2\)-orthogonal Dirichlet eigenfunctions,

\[
F_N:=-\Delta v_N=\sum_{j=1}^N f_j.
\]

Under the same boundary hypotheses, an analogous identity gives

\[
\boxed{
\int_{B_1}|\nabla^2_gv_N|^2
=\int_{B_1}F_N^2
-(m-1)\int_{\partial B_1}(\partial_\nu v_N)^2
\le\int_{B_1}F_N^2.
}
\tag{2.3}
\]

Thus the corresponding arXiv *equality* for finite sums should be replaced by \(\le\); orthogonality still controls the right-hand side. Do not infer orthogonality of the individual Hessians themselves.

## 3. Concrete counterexample on a genuine cone (within \(m\ge3\), \(0<\beta<1\))

Let

\[
M=C(S^1_{2\pi\beta})\times\mathbb R,
\quad g=dr^2+\beta^2r^2d\theta^2+ds^2,
\quad 0<\beta<1.
\]

Set \(R=\sqrt{r^2+s^2}\) and \(B_1=\{R<1\}\). The radial function

\[
v(R)=\frac{\sin(\pi R)}{R},\qquad v(0)=\pi,
\]

is a Dirichlet eigenfunction satisfying \(-\Delta_g v=\pi^2v\). The radial Laplacian is \(v''+2R^{-1}v'\), and the conical volume measure integrates radial functions exactly as \(\beta\) times Euclidean \(\mathbb R^3\) volume.

A direct calculation yields

\[
\int_{B_1}v^2\,dV_g=2\pi\beta,
\qquad
\int_{B_1}(\Delta_gv)^2\,dV_g=2\pi^5\beta.
\]

Since \(v'(1)=-\pi\), the boundary term is

\[
(m-1)\int_{\partial B_1}(\partial_\nu v)^2\,dA_g
=2(4\pi\beta)\pi^2=8\pi^3\beta.
\]

Consequently,

\[
\boxed{
\int_{B_1}|\nabla_g^2v|^2\,dV_g
=2\pi^3\beta(\pi^2-4)
<2\pi^5\beta
=\int_{B_1}(\Delta_gv)^2\,dV_g.
}
\tag{3.1}
\]

In particular, the claimed equality fails for \(\beta=1/2\), not just for a Euclidean limiting example. The function is smooth enough at the cone vertex to make the radial calculation unproblematic; it is also a weak solution across the singular axis.

## 4. Second issue: intrinsic Hessian \(\ne\) Euclidean Hessian

The opening of §2.4 (printed p. 8) says the intrinsic Hessian is uniformly equivalent to the Euclidean Hessian and that it is immaterial which metric defines \(W^{2,2}\). That claim is **false as written**. Uniform ellipticity of the tensors only compares first-derivative norms; the Levi-Civita connections differ by singular coefficients.

Take the same space \(C(S^1_{2\pi\beta})\times\mathbb R\) and let \(x=r\cos\theta\) be the first Cartesian coordinate of the underlying topological \(\mathbb R^2\) cone factor. Let \(u=x\), independent of \(s\). Then

\[
D^2_{\mathrm{Euc}}u=0,
\]

so \(u\in W^{2,2}_{\mathrm{Euc}}(B_1)\). On the regular locus the orthonormal angular vector is \(e_\theta=(\beta r)^{-1}\partial_\theta\), and a direct Christoffel-symbol calculation gives

\[
\boxed{
\nabla_g^2u(e_\theta,e_\theta)
=\frac{\beta^2-1}{\beta^2r}\cos\theta.
}
\tag{4.1}
\]

As \(r\downarrow0\), \(|\nabla_g^2u|^2\) has a non-integrable \(r^{-2}\) contribution. Since \(dV_g=\beta r\,dr\,d\theta\,ds\),

\[
\int_{B_{1/2}}|\nabla_g^2u|^2\,dV_g=\infty.
\tag{4.2}
\]

Thus ordinary Euclidean \(W^{2,2}\) does **not** imply an \(L^2\) intrinsic Hessian, and the norms are not equivalent. This is a valid counterexample in the paper's dimension range \(m\ge3\).

**Important qualification:** this particular \(u\) has \(\Delta_gu\notin L^2\) near the axis. Thus it does **not** contradict Proposition 2.5 under its PDE hypothesis. It invalidates the blanket *space-identification argument* preceding the proposition. The relation between intrinsic Hessian regularity and Euclidean weak second derivatives **for solutions of \(\Delta_gu\in L^2\)** remains to be proved or reformulated.

## 5. Proposed local Bochner repair (promising; proof obligations remain)

The target is an **interior** estimate, so one can avoid \(\partial B_1\) by introducing a second cutoff supported strictly inside the ball.

**Step A: reduce to the Dirichlet problem.** Choose \(\eta_0\in C_c^\infty(B_1)\), radial around the cone vertex, with \(\eta_0\equiv1\) on \(B_{3/4}\) and bounded \(\nabla\eta_0,\Delta\eta_0\). Put

\[
\widetilde u=\eta_0u,\qquad
\widetilde f=-\Delta_g\widetilde u
=\eta_0 f-2\langle\nabla\eta_0,\nabla u\rangle-u\Delta_g\eta_0.
\]

Using a Caccioppoli estimate on the support of \(\nabla\eta_0\), obtain

\[
\|\widetilde f\|_{L^2(B_1)}\le C\bigl(\|f\|_{L^2(B_1)}+\|u\|_{L^2(B_1)}\bigr).
\]

**Step B: finite spectral sums.** Expand \(\widetilde f=\sum_j f_j\) in an \(L^2\)-orthogonal basis of Dirichlet eigenfunctions, and let

\[
v_N=\sum_{j=1}^N\lambda_j^{-1}f_j,
\qquad F_N=-\Delta_gv_N=\sum_{j=1}^Nf_j.
\]

Select \(\eta_1\in C_c^\infty(B_{3/4})\), radial about the vertex, \(\eta_1\equiv1\) on \(B_{1/2}\), with bounded gradient and Laplacian.

**Step C: localized Bochner identity.** On the regular locus, for \(\Delta_gv_N=-F_N\),

\[
\frac12\Delta_g|\nabla v_N|^2
=|\nabla_g^2v_N|^2-\langle\nabla v_N,\nabla F_N\rangle.
\]

Formally multiplying by \(\eta_1^2\), integrating by parts *without any outer boundary contribution*, and using \(\Delta_gv_N=-F_N\), gives

\[
\boxed{
\begin{aligned}
\int\eta_1^2|\nabla_g^2v_N|^2
={}&\int\eta_1^2F_N^2
-2\int\eta_1F_N\langle\nabla\eta_1,\nabla v_N\rangle\\
&+\frac12\int\Delta_g(\eta_1^2)|\nabla v_N|^2.
\end{aligned}}
\tag{5.1}
\]

To justify (5.1) across the singular set, first replace \(\eta_1^2\) by \(\eta_1^2\chi_\varepsilon\), where \(\chi_\varepsilon\) vanishes near \(S\) and tends to 1 away from it. It is important to control **both** the \(\Delta\chi_\varepsilon\) terms from the first integration by parts **and** the \(\nabla\chi_\varepsilon\) terms arising when moving the derivative off \(F_N\). A logarithmic construction in each codimension-two factor is a candidate satisfying, locally,

\[
\int|\nabla\chi_\varepsilon|\to0,
\qquad \int|\Delta\chi_\varepsilon|\to0.
\]

For each fixed \(N\), the cited Lipschitz estimates for Dirichlet eigenfunctions would bound \(v_N\), \(F_N\), and \(\nabla v_N\); these are the ingredients needed to pass the cutoff terms to zero. **Verify the precise regularity result and its applicability to these cone balls rather than assuming it.**

**Step D: uniform estimate.** Provided the limit is justified, Cauchy–Schwarz and the bounded cutoffs imply

\[
\int_{B_{1/2}}|\nabla_g^2v_N|^2
\le C\left(\int_{B_1}F_N^2+\int_{B_1}|\nabla v_N|^2\right).
\tag{5.2}
\]

Spectral orthogonality gives

\[
\int_{B_1}|\nabla v_N|^2
=\sum_{j=1}^N\lambda_j^{-1}\|f_j\|_{L^2}^2
\le\lambda_1^{-1}\|F_N\|_{L^2}^2.
\]

Therefore

\[
\boxed{
\|\nabla_g^2v_N\|_{L^2(B_{1/2})}
\le C\|F_N\|_{L^2(B_1)}\le C\|\widetilde f\|_{L^2(B_1)},
}
\tag{5.3}
\]

uniformly in \(N\). One may then seek a weakly convergent subsequence of the intrinsic Hessians, identify the limit with the Hessian of the weak Dirichlet solution, and use uniqueness to conclude the desired **intrinsic** interior estimate for \(u\).

**What this does not automatically prove:** (a) equivalence with the Euclidean distributional \(W^{2,2}\) space; (b) a bound for every operator in \(\mathcal D_2\), since those are explicit coordinate differential operators and need separate comparison with intrinsic derivatives; or (c) estimates with constants uniform in the centre of an arbitrary ball \(B_1(p)\). The latter issue matters for §2.5.1 and the Schauder iteration.

## 6. Proof obligations for an agent (in priority order)

1. **Version check:** obtain and read the final published *Commentarii Mathematici Helvetici* version if accessible; record whether the argument or \(W^{2,2}\) terminology was changed. Do not claim that the journal version contains these errors until verified.
2. **Boundary check:** independently establish (2.2) on \(C(S^1_{2\pi\beta})\times\mathbb R\) for the explicit radial eigenfunction and, if pursuing the global strategy, justify the boundary traces and singular-stratum cutoff limit for general eigenfunctions. A smooth-domain Reilly/Miranda–Talenti argument is useful, but boundary regularity is nontrivial at \(\partial B_1\cap S\).
3. **Localized cutoff lemma:** construct \(\chi_\varepsilon\) near all SNC strata and prove the required \(L^1\) bounds for \(\nabla\chi_\varepsilon\) and \(\Delta\chi_\varepsilon\) on compact subsets; list the precise boundedness requirements on \(v_N,F_N,\nabla v_N\).
4. **Eigenfunction regularity:** verify exact statements and hypotheses of [Mon17] and [BKMR18, Proposition 5.4], including whether their Lipschitz estimates cover the Dirichlet eigenfunctions on the cone ball, how boundary intersections are treated, and whether uniform-in-\(N\) regularity is needed (it should not be for the fixed-\(N\) cutoff limit).
5. **Weak Hessian:** define intrinsic \(W^{2,2}\) or an \(L^2\) weak covariant Hessian on the regular locus, with a satisfactory extension/distributional interpretation across \(S\). Make the weak-compactness and identification step explicit.
6. **Comparison with the target operators:** decide precisely how the intrinsic Hessian bound gives the estimates needed for every \(D\in\mathcal D_2\), especially the pure conical operators when \(\beta<1/2\). The paper's \(\mathcal D_2\) is a list of **coordinate operators**, not covariant Hessian components.
7. **Uniformity in centres:** derive the corresponding estimate on \(B_1(p)\subset B_2(p)\), with a constant independent of \(p\), as used in §2.5.1. A cutoff radial about the common vertex need not remain suitable after translating the ball centre; this needs its own geometric construction or reduction.
8. **Lean interface:** keep this audit separate from `ROADMAP.md`'s proved results. No use of `sorry`, `axiom`, or any assumption encoding the desired Hessian bound as a theorem. State the repaired lemma with explicit hypotheses, including the metric normalisation.

## 7. Suggested project handling

- Place this note in the repository, for example at `research_notes/PROPOSITION_2_5_AUDIT.md`.
- Add a short pointer in `ROADMAP.md` under **Proposition 2.5**, labelled *audit / possible repair, not proved*.
- Keep the actual theorem statement as the analytic goal. Do **not** reproduce the false global Hessian equality or assert that Euclidean \(W^{2,2}\) and intrinsic \(W^{2,2}\) are automatically equivalent.
- Prioritise the **localized** Bochner estimate over global boundary regularity, unless a reliable conical Reilly identity with all boundary terms is already available.
- Report unresolved assumptions, gaps, and mathematical alternatives explicitly to Martin before claiming the analytic milestone complete.

## Sources

- de Borbon–Edwards, [arXiv:2002.07668v1 PDF](https://arxiv.org/pdf/2002.07668), printed pp. 8–9, §2.4, Proposition 2.5 (the exact proof reviewed here).
- [Published article record (EMS Press)](https://ems.press/journals/cmh/articles/323504), *Commentarii Mathematici Helvetici* 96 (2021), 113–148. The article PDF is subscription-restricted at the time of this audit; **the published proof was not checked**.

---

**Agent status:** Research audit only. Sections 2–4 contain explicit mathematical counterchecks. Section 5 is a candidate proof strategy with outstanding regularity, cutoff and weak-limit obligations. Nothing in this note should be represented as kernel-checked Lean mathematics.
