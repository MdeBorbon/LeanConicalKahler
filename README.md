# ConicalKahlerLean

A Lean 4 formalisation of Kähler metrics with cone singularities along complex divisors,
built on top of the formal proof of the Calabi conjecture
[`wxkj99/calabi-yau`](https://github.com/wxkj99/calabi-yau).

The design document is [`CONICAL_KAHLER_LEAN_API.md`](CONICAL_KAHLER_LEAN_API.md); progress,
open proof obligations and blockers are tracked in [`STATUS.md`](STATUS.md). The plan towards the
Schauder estimates of de Borbon–Edwards is in [`ROADMAP.md`](ROADMAP.md).

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
| `ConicalKahlerTest/Model.lean` | the specification's concrete tests (`n = 1`, `β = 1`, `n = 2`, SNC) |
| `ConicalKahlerTest/Divisor.lean` | divisor and cone-condition tests; `z₀ ↦ z₀²` is not an adapted chart |
| `ConicalKahlerTest/Geometry.lean` | flat-cone isometry, angles `π`, `4π`, holonomy, QI ≠ model |
| `ConicalKahlerTest/SelectedChart.lean` | agreement with `metricInChart`, shear transformation law |
| `ConicalKahlerTest/SNC.lean` | two axes with angles `π`, `6π`; components; smooth case |
| `ConicalKahlerTest/Laplacian.lean` | polar formula, harmonic functions, cross-check of the two routes, dilation |
| `ConicalKahlerTest/SNCInvariance.lean` | crossing components with angles `π` and `2π/3`; swapped and mixed charts |
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
