# ConicalKahlerLean

A Lean 4 formalisation of Kähler metrics with cone singularities along complex divisors,
built on top of the formal proof of the Calabi conjecture
[`wxkj99/calabi-yau`](https://github.com/wxkj99/calabi-yau).

The design document is [`CONICAL_KAHLER_LEAN_API.md`](CONICAL_KAHLER_LEAN_API.md); progress,
open proof obligations and blockers are tracked in [`STATUS.md`](STATUS.md). The plan towards the
Schauder estimates of de Borbon–Edwards is in [`ROADMAP.md`](ROADMAP.md). Issues found in that
paper are recorded in [`PAPER_REVIEW.md`](PAPER_REVIEW.md), with verified errors kept separate from
suspected gaps.

## Main result so far

For every `β > 0`, the standard cone metric with cone angle `2πβ` along `{z₀ = 0}`

```
ω_β = i β² |z₀|^(2β-2) dz₀ ∧ dz̄₀ + i ∑_{j ≥ 1} dz_j ∧ dz̄_j
```

is an (upstream) `KahlerForm` on the open complex manifold `{z₀ ≠ 0} ⊆ ℂⁿ`, and it is Ricci-flat
there:

```lean
ConicalKahler.standardConeForm (β : ConeAngle) :
  KahlerForm n (modelDomain (singleConeWeights β))
ConicalKahler.standardConeForm_coeffMatrix   -- g_{jk̄} = diag(β² |z₀|^(2β-2), 1, …, 1)
ConicalKahler.standardConeForm_ricciFlat     -- (standardConeForm β).IsRicciFlat
```

More generally `ModelConeForm θ` is the normal-crossings model with an independent cone angle
(or none) in each coordinate direction. Coordinates are 0-indexed (`Fin n`), so the singular
coordinate written `z₁` in the usual notation is `z 0` in Lean.

Along an arbitrary smooth divisor `D ⊆ X` (`SmoothDivisor`, given by adapted holomorphic charts),
a Kähler form on `X \ D` has *quasi-isometric* cone angle `2πβ` (`IsConeAlong D β ω₀`) if, in
some adapted chart near each point of `D`, its Hermitian quadratic form is uniformly equivalent to
that of `ω_β`. The form is pulled back to an arbitrary adapted chart by `metricInAdaptedChart`.

* For `0 < β ≤ 1` the condition does not depend on the adapted chart
  (`IsQuasiIsometricCone.forall_chart_of_le_one`).
* For `β > 1` it does: under the shear `(z₀, z₁) ↦ (z₀, z₁ + z₀)` the standard cone metric fails
  the comparison on every neighbourhood (`not_coneComparableIn_shear`). For `β > 1`,
  `IsConeAlong` is therefore an existence-of-compatible-chart condition.
* `IsConeAlong` asserts quasi-isometry only: no tangent-cone uniqueness, asymptotic expansion
  or weighted regularity.

### The model is exactly a flat cone

Transversally, the metric tensor of `ω_β` is *exactly* that of the flat cone of angle `2πβ`, in
covering coordinates. This is an identity, not merely a quasi-isometry.
Write `z₀ = r e^{iθ}` and change variables radially, `ρ = r^β`, `φ = βθ`. Then the transverse
metric becomes `dρ² + ρ² dφ²` with `φ ~ φ + 2πβ` (`transverseConeMetric_polar`). The same holds
for the Riemannian metric `ω_β(·, J·)` of the upstream Kähler form with `ρ = √2 r^β`
(`standardConeForm_polar_riemannian`). The holonomy is the rotation by `2πβ`, and the
circumference is `2πβ` × radius (`coneCircleLength_eq_two_pi_mul_radialLength`).

**What exactly is proved.** These results are *tensor identities* plus *equivariance on covering
coordinates*. The metric tensor of `ω_β`, pulled back by the polar map `(r, θ) ↦ r e^{iθ}`
on `(0, ∞) × ℝ`, is equal to the flat cone tensor `dρ² + ρ² dφ²` pulled back by the radial
change of variables. That change of variables is a diffeomorphism of `(0, ∞) × ℝ` that turns the
deck translation `θ ↦ θ + 2π` into `φ ↦ φ + 2πβ`. The lengths are integrals along explicit curves.
Not formalised:

* the quotient `((0, ∞) × ℝ)/(φ ~ φ + 2πβ)` as a manifold or metric space;
* the induced path-length distance, or the minimality of radial segments;
* the metric completion of `(ℂ \ {0}, g_β)` or the cone vertex.

So there is no independently constructed metric-space isometry, and nothing is stated at the
vertex. Those statements are listed as outstanding in `STATUS.md`.

`perturbedConeForm_isConeAlong` and `perturbedConeForm_not_ricciFlat` give, for every `β`, a form
with quasi-isometric cone angle `2πβ` that is not Ricci-flat, so it is not locally isometric to
the model. Model geometry, strong asymptotic conditions (spec §3.5, not defined) and
quasi-isometry are kept as three separate levels.

### Agreement with upstream `metricInChart`

`metricInAdaptedChart` is the pullback along an arbitrary holomorphic chart. When the adapted
chart is the selected chart it equals the upstream `KahlerForm.metricInChart`
(`metricInAdaptedChart_eq_metricInChart`). In general the two are related by
`metricInChart x z = Aᵀ g^χ Ā` (`metricInChart_eq_metricInAdaptedChart_change`).

### SNC divisors

`SNCDivisor n X ι` has labelled components and SNC charts as in spec §4, and each component is a
`SmoothDivisor` (`SNCDivisor.component`). `IsSNCConeAlong Δ angle ω₀` assigns an arbitrary angle
`angle i > 0` to each label and compares with the *same* `ModelConeForm`, using the chart's local
weights. The smooth case is the one-label case (`isConeAlong_iff_isSNCConeAlong`).

**Chart invariance for `0 < β_i ≤ 1`.** If all cone angles satisfy `β_i ≤ 1`, the SNC condition
does not depend on the SNC charts used: a comparison in one SNC chart at `p` gives a comparison in
any other SNC chart at `p` after shrinking (`SNCConeComparableIn.exists_restrOpen_of_le_one`,
`IsQuasiIsometricSNCCone.forall_chart_of_le_one`).

* The two charts may list the components through `p` in different orders, and the matching goes
  by label (`SNCChart.weightsMatch`).
* The analytic core is one weighted comparison for arbitrary `ConeWeights`
  (`exists_weighted_model_comparison`). The smooth-divisor invariance theorems are now its
  one-label case.

### The Laplacian of the cone models

`laplaceBeltrami ω₀ f` is the Laplace–Beltrami operator of the Riemannian metric `g = ω₀(·, J·)`.
It is the upstream `CalabiYau.Riemannian.ΔG`, reused rather than redefined. For any product of
cones and Euclidean factors,

```
Δ_g f = ∑_j Δ_{z_j} f / (2 w_j),     Δ_{z_j} = ∂²_{x_j} + ∂²_{y_j}
```

(`laplaceBeltrami_modelConeFormOn`). On a cone factor in the coordinates `ρ = |z_j|^β`, `θ`,
the `j`-th term is `½ (F_ρρ + ρ⁻¹ F_ρ + (βρ)⁻² F_θθ)`
(`coordLaplacian_div_modelWeight_conePolar`, `laplaceBeltrami_standardCone_polar`). The factor `½`
is the normalisation `g = 2q`.

The following are harmonic:
- `ρ^{k/β} cos kθ` and `ρ^{k/β} sin kθ` (`coneHarmonicCos_polar_eq_zero`). These are `Re z^k`
  and `Im z^k`, which are harmonic for every Kähler form (`laplaceBeltrami_re_pow_eq_zero`).
- Differences of the squared radial coordinates `ρ_a² − ρ_b²` (`laplaceBeltrami_potentialTerm_sub`).
- `log |z_j|²` (`laplaceBeltrami_log_coordNormSq_eq_zero`).

Homogeneity, cone dilations and derivative estimates are in `ConicalKahler/Laplacian/ConeHarmonic`
and `ConicalKahler/Cone/Dilation`.

### Real cone models and the operators `𝒟₂`

The Schauder estimates are formulated in the paper's **real coordinates**. A cone factor point
is `w = r e^{iθ} ∈ ℝ²`, with `θ ∈ ℝ/2πℤ` the same angle as on the Kähler side. These coordinates
are globally defined, unlike the flat developing coordinates `r e^{iβθ}`
(`developing_add_two_pi_ne`).

* `RealConeModel κ ι = ℝ^{(Fin 2 × κ) ⊕ ι}`: cone factors indexed by `κ`, Euclidean coordinates by
  `ι`. Its dimension is `2#κ + #ι`, which can be odd.
* The model metric `g = ∑_a (dr_a² + β_a² r_a² dθ_a²) + ds²` (`productConeMetric`) satisfies
  `b²|v|² ≤ g(v) ≤ |v|²` when `b ≤ β_a ≤ 1`. Its Gram matrix has determinant `∏ β_a²`, and the
  Riemannian volume is `(∏ β_a)` times Lebesgue measure (`productConeVolume_eq`).
* **Cone distance.** `coneDist β` is the distance of the Euclidean cone over a circle of length
  `2πβ`: `d² = r² + s² − 2rs cos(min(β∠, π))`. `ConeTwo β` and `ConeProduct β ι` (the `L²`
  product, via Mathlib's `PiLp`) are metric spaces. We prove:
  - the comparison `b|p − q| ≤ d(p, q) ≤ |p − q|`, and ball inclusions;
  - that balls centred at the vertex are Euclidean balls;
  - that dilations scale `d`;
  - that `d` induces the Euclidean topology;
  - that locally `d` is the flat distance in developing coordinates.

  **This distance is formally defined.** It is not yet proved to be the length distance of `g`.
* **Bridge.** `ConeWeights.realChart` (`z ↦ |z|^{β-1} z` on cone directions) maps the Kähler
  model to the real model. Under this map the Hermitian form of the Kähler model is the pull-back
  of `g`. The Riemannian metric `ω(·, J·)` is **twice** that pull-back, and
  `laplaceBeltrami = ½ Δ_β` (`ConeWeights.modelConeForm_apply_I_smul_eq_two_mul`,
  `laplaceBeltrami_eq_half_coneLaplacian`).
* **`𝒟₂`** (`D2Op`) lists exactly the coordinate operators of the paper (p. 2). The pure conical
  ones are included only when `β_a < 1/2`.
  - For `β_a ≥ 1/2` every `D ∈ 𝒟₂` annihilates the harmonic functions of one factor
    (`D2Op.apply_factor_eq_zero`).
  - The examples on p. 3 are sharp (`sharp_holderExponent`). For `α` above `1/β − 1`
    (`β ≥ 1/2`) or `1/β − 2` (`β < 1/2`), some `D ∈ 𝒟₂` maps a harmonic function to a function
    that is not `α`-Hölder near the vertex.

### Sobolev spaces and weak solutions

`ConicalKahler/Sobolev/` sets up the `L²` theory that the Schauder estimates start from.
- `W^{1,2}(Ω)` and `W^{1,2}_0(Ω)` are Hilbert spaces of pairs `(u, ∇u)` (`W12`, `H01`).
- The Friedrichs–Poincaré inequality is `norm_fst_le_of_mem_H01`.
- For any symmetric, measurable, uniformly elliptic coefficient field (`CoeffField`):
  - weak solutions of `-div(A∇u) = f` exist and are unique in `W^{1,2}_0` (Lax–Milgram,
    `existsUnique_H01_isWeakSolution`);
  - the Caccioppoli inequality holds (`caccioppoli`).
- The cone Laplacian in the paper's real coordinates is the case `A = g⁻¹` (`coneCoeff`). In real
  coordinates `g⁻¹` is the paper's metric with angles `1/β_a`.
- The codimension-two singular set has zero capacity: test functions supported off it are dense
  in `W^{1,2}_0` (`dense_testSubmodule_regular`).

### Compactness, harmonic approximation, scaling and spectral theory

- **Bridges** with the geometric theory:
  - `div(g⁻¹∇u)` is the paper's Laplacian at regular points (`divergence_coneInvOp_gradient`);
  - the intrinsic `W^{1,2}` norm defined by `g` and `dV_g` is equivalent to the Euclidean one
    (`intrinsicNormSq_bounds`).
- **Rellich**: `W^{1,2}_0(Ω) ↪ L²(Ω)` is compact (`isCompactOperator_H01_fst`). This reuses
  upstream's Rellich–Kondrachov theorem through the bridge `memW01p_of_mem_H01`.
- **Harmonic approximation** (the paper's Lemma 2.4):
  - harmonic replacement gives an explicit `δ`, uniform in the centre, also on cone balls
    (`harmonic_approximation`, `cone_harmonic_approximation`);
  - the paper's compactness argument is `exists_tendsto_of_approx_solutions` and
    `harmonic_approximation_of_compactness`.
- **Scaling**:
  - dilations of weak solutions (`CoeffField.IsWeakSolution.dilate`);
  - the dilation invariance of `g⁻¹` and of the scaled norms;
  - the scaled Caccioppoli inequality (`exists_caccioppoli_ball_scaled`).
- **The spectral theorem for the Dirichlet problem**: the solution operator is compact, symmetric,
  positive and injective, and its eigenspaces span `L²(Ω)` (`CoeffField.dirichletG_eigenspaces_dense`).

### Weak harmonic functions on the models

- **Classical and weak solutions.**
  - A function that is `C²` off the singular set `S`, with `u, ∇u ∈ L²`, and solves `-Δu = f`
    classically there is a weak solution on all of `Ω`, including near `S`
    (`cone_isWeakSolution_of_classical`).
  - Conversely, such a weak solution satisfies the equation pointwise
    (`cone_classical_of_isWeakSolution`).
  - `S` is removable for `W^{1,2}` (`mem_W12_of_regular`, `classicalPair_mem_W12`).
- **The explicit harmonic functions are weakly harmonic** on every bounded open set:
  - `r^{k/β} cos kθ` and `r^{k/β} sin kθ` (for `β ≤ k`), the coordinates `s_i`, and the harmonic
    quadratics (`IsClassicalHarmonic.isWeakSolution`);
  - in particular the span of the paper's list of `𝓗_{≤2}` (`explicitH2`).
- **Corollary 3.5** for the span of the paper's list: every `D ∈ 𝒟₂` maps it to constants `τ`
  with `|τ| ≤ C ‖P‖_{L²(B_1)}` (`corollary_3_5`). That this span is all of `𝓗_{≤2}` (Prop. 3.4) is
  not proved.
- **Energy uniqueness**, which replaces the maximum principle in Lemma 3.3: a weakly harmonic
  function in `W^{1,2}_0` vanishes (`eq_zero_of_isWeakSolution_zero_of_mem_H01`).
- **Rotations of the cone factors**:
  - they preserve the weak formulation (`cone_isWeakSolution_rot`);
  - the Dirichlet problem is rotation-symmetric (`cone_dirichlet_rot_invariant`);
  - the Dirichlet solution operator commutes with them (`dirichletG_isoLp`).
- **Fourier modes in `θ_a`**:
  - the modes of a weak solution are weak solutions (`isWeakSolution_angMode`);
  - they transform like `cos kθ` and `sin kθ` (`rotLp_cosCoeff`);
  - a function is determined by its modes (`eq_zero_of_modes_eq_zero`).

### The link and Lemma 3.3

These results hold for every **conical** coefficient field on `ℝ^d` (`A(tx) = A(x)`,
`A(x) x = x`; `CoeffField.IsConical`), and in particular for the cone Laplacian
(`coneCoeff_isConical`).

- **Polar coordinates** on `ℝ^d` (`integral_polar_iter`), from Mathlib's
  `homeomorphUnitSphereProd`.
- **Lemma 3.1** (`link_spectral`, `cone_link_spectral`). `L²` of the link has a Hilbert basis of
  eigenfunctions of `-Δ_ḡ`, with eigenvalues `λ_i ≥ 0` and finitely many below any bound. The link
  is the unit sphere. Its Sobolev space `linkW12` is defined by homogeneous extension to shells,
  and it embeds compactly into `L²` (`isCompactOperator_linkFst`).
- **Homogeneous harmonic functions** (§3.2):
  - if `φ` is a link eigenfunction with `λ = δ(δ + d − 2)`, then `ρ^δ φ` is weakly harmonic off
    the vertex (`homogeneous_harmonic`);
  - for `δ ≥ 0` and `d ≥ 2` it is weakly harmonic on balls through the vertex
    (`homPair_isWeakSolution`, by vertex removability `isWeakSolution_of_punctured`).
- **Lemma 3.3** (`expansion`, `cone_expansion`). For `d ≥ 2`, every weakly harmonic
  `u ∈ W^{1,2}(B_1)` is the `L²(B_1)`-sum `∑ a_i ρ^{δ_i} φ_i` of mutually orthogonal, weakly
  harmonic, homogeneous functions of degrees `δ_i ≥ 0`.
  - The proof uses neither the maximum principle (`PAPER_REVIEW.md` S2) nor Frobenius theory.
  - Instead, the Wronskian identity (`wronskian`) tested with radial functions gives the radial
    ODE `u_φ(r) = C r^δ` (`rayCoeff_eq`), and Parseval on spheres gives convergence.
- **Not proved:**
  - the completeness of `𝓗_{≤2+α}` (Prop. 3.4);
  - multiplicity one of `λ = 0`;
  - `L²` convergence of the Fourier modes in `θ_a`.

## Normalisation conventions

We use the upstream conventions without change.

* A real `(1,1)`-form is written `ω = i ∑_{j,k} g_{jk̄} dz_j ∧ dz̄_k`, and
  `ContinuousAlternatingMap.coeffMatrix` returns the Hermitian matrix `(g_{jk̄})`.
  For example the Euclidean form `i ∑ dz_j ∧ dz̄_j = 2 ∑ dx_j ∧ dy_j` has coefficient matrix `1`
  (`complexHessian_normSq`).
* The Riemannian metric is `g(u, v) = ω(u, Jv)` with `J v = i v`. Hence
  (`IsOneOne.apply_I_smul`)

  ```
  g(v, v) = ω(v, Jv) = 2 ∑_{j,k} g_{jk̄} v_j v̄_k .
  ```

  The **Riemannian quadratic form is twice the Hermitian coefficient quadratic form.** The model
  quantity `modelConeQuadratic θ z v = ∑_j w_j(z) |v_j|²` is the *Hermitian* one, and
  `modelConeForm_apply_I_smul` states `ω_θ(v, Jv) = 2 · modelConeQuadratic θ z v`. All cone
  comparison conditions are formulated with the Hermitian quadratic forms on both sides, so the
  factor `2` cancels; mixing a Hermitian and a Riemannian quantity would be a factor-two error.
* `i∂∂̄|z|^(2β) = β² |z|^(2β-2) i dz ∧ dz̄` on `ℂ*` (`radialCoeff_rpow`). This is why the potential
  `|z₀|^(2β) + ∑_{j≥1} |z_j|²` produces exactly `ω_β`.

## Layout

| File | Content |
|---|---|
| `ConicalKahler/Analysis/DDBarLocal.lean` | germ locality and additivity of `ddbar` |
| `ConicalKahler/Analysis/RadialHessian.lean` | complex Hessian of `∑_j g_j(|z_j|²)` |
| `ConicalKahler/Manifold/OpenSubset.lean` | charts and `i∂∂̄` on open subsets of `ℂⁿ` |
| `ConicalKahler/Cone/Weights.lean` | `ConeAngle`, `ConeWeights`, model domain, weights, quadratic form, matrix |
| `ConicalKahler/Cone/Model.lean` | `ModelConeForm` and its coefficient matrix |
| `ConicalKahler/Cone/ModelRicci.lean` | Ricci-flatness of the model |
| `ConicalKahler/Cone/Standard.lean` | the standard cone metric `ω_β` along `{z₀ = 0}` |
| `ConicalKahler/Divisors/AdaptedChart.lean` | `DivisorChart`, `SmoothDivisor`, complement, coordinate hyperplane |
| `ConicalKahler/Cone/ChartMetric.lean` | metric in an arbitrary adapted chart; positivity; chart-change law |
| `ConicalKahler/Cone/Comparison.lean` | `IsQuasiIsometricCone` / `IsConeAlong`; shrinking; the model is conical |
| `ConicalKahler/Analysis/HyperplaneMaps.lean` | estimates for holomorphic maps sending `{ζ_a = 0}` into `{z_b = 0}` |
| `ConicalKahler/Cone/WeightedComparison.lean` | comparison of cone models under hyperplane-matching coordinate changes (angles `≤ 1`) |
| `ConicalKahler/Cone/SNCChartInvariance.lean` | SNC chart invariance for `0 < β_i ≤ 1`, with permuted components |
| `ConicalKahler/Cone/ChartInvariance.lean` | smooth-divisor chart invariance for `0 < β ≤ 1` (one-label case) |
| `ConicalKahler/Cone/AngleRestriction.lean` | the shear test: failure for `β > 1`, success for `β ≤ 1` |
| `ConicalKahler/Cone/Kahler.lean` | `ConeKahlerForm`, Kähler–Einstein equation on `X \ D` |
| `ConicalKahler/Cone/FlatCone.lean` | polar coordinates, radial change, isometry with the flat cone, holonomy, lengths |
| `ConicalKahler/Analysis/RadialCalculus.lean` | rules for computing `g' + s g''` |
| `ConicalKahler/Cone/Separable.lean` | Kähler forms `i∂∂̄ ∑ g_j(|z_j|²)` and their Ricci forms |
| `ConicalKahler/Cone/QuasiIsometricExample.lean` | a quasi-isometric cone metric that is not Ricci-flat |
| `ConicalKahler/Manifold/HolomorphicChart.lean` | `HolChart`: holomorphic charts outside the selected atlas |
| `ConicalKahler/Cone/SelectedChart.lean` | agreement with upstream `metricInChart`; transformation law |
| `ConicalKahler/Divisors/SNC.lean` | `SNCChart`, `SNCDivisor`, components, local weights, coordinate SNC |
| `ConicalKahler/Cone/SNCComparison.lean` | SNC cone condition, SNC model, smooth case as specialization |
| `ConicalKahler/Cone/Dilation.lean` | cone dilations; homothety `q ↦ λ² q` of every product of cones |
| `ConicalKahler/Laplacian/Polar.lean` | `Δ_{z_j}` in polar and cone coordinates; second-order chain rule |
| `ConicalKahler/Laplacian/Model.lean` | `laplaceBeltrami`; Laplacian of products of cones; harmonic functions |
| `ConicalKahler/Laplacian/ConeHarmonic.lean` | `ρ^{k/β} cos kθ`, `ρ^{k/β} sin kθ`: harmonicity, homogeneity, derivative bounds |
| `ConicalKahler/Real/ConeFactor.lean` | one cone factor in the paper's real coordinates: metric, Gram determinant, `realConeChart` bridge |
| `ConicalKahler/Real/ConeDistance.lean` | hinges, the cone distance, `ConeTwo` metric space, Euclidean comparison |
| `ConicalKahler/Real/Product.lean` | `RealConeModel`, product metric, volume, `ConeProduct` metric space, balls |
| `ConicalKahler/Real/D2.lean` | polar coordinates, `pd`, `Δ_β`, `D2Op` (`𝒟₂`), harmonic examples, Hölder sharpness |
| `ConicalKahler/Real/Bridge.lean` | Kähler model → real model; `ω(v, Jv) = 2 g_paper` |
| `ConicalKahler/Real/Normalisation.lean` | `laplaceBeltrami = ½ Δ_β` in the paper's coordinates |
| `ConicalKahler/Sobolev/H1.lean` | test functions, `W^{1,2}`, `W^{1,2}_0` as Hilbert spaces of pairs, Friedrichs–Poincaré |
| `ConicalKahler/Sobolev/Elliptic.lean` | coefficient fields, Dirichlet form, weak solutions, Lax–Milgram existence and uniqueness |
| `ConicalKahler/Sobolev/Caccioppoli.lean` | cut-offs in `W^{1,2}_0` (upstream mollification), Caccioppoli inequality |
| `ConicalKahler/Sobolev/ConeLaplacian.lean` | `g⁻¹` of the real cone models as a coefficient field; cone versions of the estimates |
| `ConicalKahler/Sobolev/Capacity.lean` | logarithmic cut-offs, zero capacity of the singular set, density |
| `ConicalKahler/Sobolev/Restrict.lean` | restriction to subdomains, smooth cut-off functions |
| `ConicalKahler/Sobolev/Rellich.lean` | bridge to upstream `MemW01p`, Rellich compactness, compact embedding |
| `ConicalKahler/Sobolev/Intrinsic.lean` | metric gradient, `dV_g` on `ℝ^d`, intrinsic `W^{1,2}` norm and its equivalence |
| `ConicalKahler/Sobolev/HarmonicApprox.lean` | harmonic replacement, Lemma 2.4, compactness of approximate solutions |
| `ConicalKahler/Sobolev/ConeApprox.lean` | cone balls in `ℝ^d`, Lemma 2.4 uniformly in the centre |
| `ConicalKahler/Sobolev/Divergence.lean` | `div(g⁻¹∇u)` equals the paper's Laplacian at regular points |
| `ConicalKahler/Sobolev/Scaling.lean` | dilations, scaled norms, scaled Caccioppoli |
| `ConicalKahler/Sobolev/Spectral.lean` | Dirichlet solution operator, spectral theorem |
| `ConicalKahler/Real/D2Linear.lean` | locality and linearity of `pd` and `𝒟₂`; quadratic monomials |
| `ConicalKahler/Sobolev/Classical.lean` | integration by parts off `S`, removability of `S`, classical ⇔ weak solutions, energy uniqueness |
| `ConicalKahler/Sobolev/ExplicitHarmonic.lean` | `IsClassicalHarmonic`; the explicit harmonic functions are weakly harmonic |
| `ConicalKahler/Sobolev/Corollary35.lean` | the paper's list of `𝓗_{≤2}`, Corollary 3.5 for its span |
| `ConicalKahler/Sobolev/Rotation.lean` | isometries and weak solutions, rotations of the cone factors, symmetric Dirichlet problem |
| `ConicalKahler/Sobolev/FourierModes.lean` | continuity of the rotation action, Fourier modes in `θ_a`, Fourier uniqueness |
| `ConicalKahler/Sobolev/Polar.lean` | polar coordinates on `ℝ^d`, the radial projection, homogeneous extensions |
| `ConicalKahler/Sobolev/FormSpectral.lean` | spectral theorem for coercive symmetric forms with compact dense embedding |
| `ConicalKahler/Sobolev/Link.lean` | conical coefficient fields, the link Sobolev space, the link form, Rellich on the link |
| `ConicalKahler/Sobolev/LinkSpectral.lean` | tangential gradients, density, link eigenfunctions, Lemma 3.1 |
| `ConicalKahler/Sobolev/Homogeneous.lean` | radial averages, tangentiality, product rule, `ρ^δ φ` weakly harmonic off the vertex |
| `ConicalKahler/Sobolev/Expansion.lean` | vertex removability, `ρ^δ φ` on balls, Wronskian identity, radial test functions, key identity |
| `ConicalKahler/Sobolev/HarmonicExpansion.lean` | ray coefficients, radial ODE, Parseval on spheres, Lemma 3.3 |
| `ConicalKahler/Sobolev/ConeLink.lean` | the cone Laplacian is conical; Lemmas 3.1 and 3.3 for products of cones |
| `ConicalKahlerTest/Model.lean` | the specification's concrete tests (`n = 1`, `β = 1`, `n = 2`, SNC) |
| `ConicalKahlerTest/Divisor.lean` | divisor and cone-condition tests; `z₀ ↦ z₀²` is not an adapted chart |
| `ConicalKahlerTest/Geometry.lean` | flat-cone isometry, angles `π`, `4π`, holonomy, QI ≠ model |
| `ConicalKahlerTest/SelectedChart.lean` | agreement with `metricInChart`, shear transformation law |
| `ConicalKahlerTest/SNC.lean` | two axes with angles `π`, `6π`; components; smooth case |
| `ConicalKahlerTest/Laplacian.lean` | polar formula, harmonic functions, cross-check of the two routes, dilation |
| `ConicalKahlerTest/SNCInvariance.lean` | crossing components with angles `π` and `2π/3`; swapped and mixed charts |
| `ConicalKahlerTest/RealCone.lean` | cone distances, area `πβρ²` of a cone disk, odd dimension, `𝒟₂` membership, sharpness |
| `ConicalKahlerTest/Sobolev.lean` | constants, existence, Poincaré, Caccioppoli and density on `C(S¹_π) × ℝ` |
| `ConicalKahlerTest/Compactness.lean` | Rellich, Lemma 2.4, divergence identity, scaling and the spectral theorem on `C(S¹_π) × ℝ` |
| `ConicalKahlerTest/WeakHarmonic.lean` | classical ⇔ weak, explicit harmonic functions, Corollary 3.5, rotations and Fourier modes on `C(S¹_{4π/3}) × ℝ` |
| `ConicalKahlerTest/LinkExpansion.lean` | polar coordinates, Lemma 3.1, indicial roots, homogeneous harmonic functions, radial ODE, Lemma 3.3 on `C(S¹_{4π/3}) × ℝ` |
| `ConicalKahlerTest/PaperChecks.lean` | Lean checks of the verified items of `PAPER_REVIEW.md` |
| `scripts/AxiomAudit.lean` | fails unless every declaration uses only the standard axioms |

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean `v4.34.1`), Mathlib
(`v4.34.1`) and the upstream commit
(`91b1ddf000c7028bc42ae6102eba0e2042eb37ff`) are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`. These are the same Lean and Mathlib versions as the upstream project.

```sh
lake exe cache get        # Mathlib build cache
lake build                # library and tests
lake env lean scripts/AxiomAudit.lean
```

CI (`.github/workflows/ci.yml`) runs all three steps on every push and also rejects `sorry`,
`admit`, `axiom` and `opaque` in the sources.
