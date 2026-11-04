# STATUS

Last updated: 2026-11-04.

Pins: Lean `v4.34.1`, Mathlib `v4.34.1` (`d13f23b7`), `calabiyau` at
`91b1ddf000c7028bc42ae6102eba0e2042eb37ff`. Upstream is used unmodified.

Every completed result below is kernel-checked. `scripts/AxiomAudit.lean` confirms that all 515
`ConicalKahler.*` declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.
The sources contain no `sorry`, `admit`, `axiom` or `opaque`, and the build has no warnings.

## Milestone 1: local model (spec items 2–4): COMPLETE

| Spec item | Lean declaration | File |
|---|---|---|
| `ConeAngle`, `ConeWeights`, `singleConeWeights` | `ConeAngle`, `ConeWeights`, `singleConeWeights`, `ConeWeights.smooth` | `Cone/Weights` |
| model domain is open | `modelDomain θ : TopologicalSpace.Opens (E n)` (openness: `isOpen_modelDomainSet`) | `Cone/Weights` |
| single-cone domain is `{z₀ ≠ 0}` | `mem_modelDomain_single` | `Cone/Weights` |
| weights positive off the divisor | `modelWeight_pos` | `Cone/Weights` |
| model quadratic form and matrix | `modelConeQuadratic`, `modelConeMatrix`, `modelConeQuadratic_pos`, `modelConeMatrix_posDef`, `modelConeQuadratic_eq_sum`, `det_modelConeMatrix` | `Cone/Weights` |
| `∂∂̄|z|^{2β} = β²|z|^{2β-2}` | `radialCoeff_rpow`, `coeffMatrix_ddbar_separable`, `complexHessian_modelPotential` | `Analysis/RadialHessian`, `Cone/Model` |
| model form as a `KahlerForm` | `modelConeFormOn θ U hU` (any open `U ⊆ modelDomain θ`), `ModelConeForm θ` | `Cone/Model` |
| computed Hermitian diagonal | `modelConeMatrix_eq_coeffMatrix`, `modelConeFormOn_metricInChart`, `modelConeForm_apply_eq`, `modelConeFormOn_apply_I_smul` | `Cone/Model`, `Cone/Standard` |
| smooth, closed, positive | `KahlerForm` fields; restated as `standardConeForm_isSmooth`, `_isClosed`, `_isPositive` | `Cone/Standard` |
| Ricci-flat on the complement | `modelConeFormOn_ricciFlat`, `modelConeForm_ricciFlat`, `standardConeForm_ricciFlat` | `Cone/ModelRicci`, `Cone/Standard` |
| standard `ω_β` with explicit formula | `standardConeForm`, `standardConeForm_apply`, `standardConeForm_coeffMatrix` | `Cone/Standard` |
| `β = 1` is Euclidean | `standardConeForm_one` | `Cone/Standard` |
| tests `n = 1`, `n = 2`, volume factor, SNC `k = 2` | | `ConicalKahlerTest/Model` |

## Milestone 2: divisors, adapted charts, cone conditions (spec items 1, 5–7): COMPLETE

| Spec item | Lean declaration | File |
|---|---|---|
| adapted holomorphic chart | `DivisorChart n X D p` (fields as in the spec), `DivisorChart.restrOpen`, `symm_notMem`, `coord_ne_zero` | `Divisors/AdaptedChart` |
| smooth divisor and complement | `SmoothDivisor n X`, `SmoothDivisor.complement : Opens X`; `KahlerForm n D.complement` is well-typed (test) | `Divisors/AdaptedChart` |
| coordinate hyperplane | `coordHyperplane n`, `coordHyperplaneChart`, `coordHyperplane_complement` (= `modelDomain (singleConeWeights β)`) | `Divisors/AdaptedChart` |
| metric in an arbitrary adapted chart | `formInAdaptedChart`, `metricInAdaptedChart`, `metricQuadraticInAdaptedChart` (`= g^χ(v,v)/2`) | `Cone/ChartMetric` |
| positivity | `formInAdaptedChart_isPositive`, `metricInAdaptedChart_posDef`, `metricQuadraticInAdaptedChart_pos` | `Cone/ChartMetric` |
| chart-change law | `formInAdaptedChart_change`, `metricQuadraticInAdaptedChart_change` (`q₁(z₁;v) = q₂(z₂; DΦ v)`), `metricInAdaptedChart_change` (`g₁ = Aᵀ g₂ Ā`, upstream convention) | `Cone/ChartMetric` |
| the model in its own chart | `metricQuadraticInAdaptedChart_model` | `Cone/ChartMetric` |
| `IsConeAlong` (quasi-isometric only) | `ConeComparableIn`, `IsQuasiIsometricCone`, `IsConeAlong` (abbrev), `isQuasiIsometricCone_iff` (spec's literal form) | `Cone/Comparison` |
| shrinking, constants, localization | `ConeComparableIn.restrOpen`, `ConeComparableIn.mono`, `IsQuasiIsometricCone.exists_chart_subset`, `coneComparableIn_iff_riemannian` | `Cone/Comparison` |
| model satisfies the condition | `modelOnHyperplane`, `modelOnHyperplane_isConeAlong` (`C = 1`) | `Cone/Comparison` |
| **chart invariance, `0 < β ≤ 1`** | `ConeComparableIn.exists_restrOpen_of_le_one`, `IsQuasiIsometricCone.forall_chart_of_le_one` | `Cone/ChartInvariance` |
| analytic inputs | `exists_hyperplane_estimates`, `fderiv_apply_zero_eq_zero_of_tangent`, `modelConeQuadratic_le_of_le_one`, `exists_model_comparison` | `Analysis/HyperplaneMaps`, `Cone/ChartInvariance` |
| **counterexample, `β > 1`** | `shearChart`, `not_coneComparableIn_shear` (fails for every neighbourhood and constant) | `Cone/AngleRestriction` |
| shear is admissible for `β ≤ 1` | `coneComparableIn_shear_of_le_one` (`C = 2 + 2/β²`) | `Cone/AngleRestriction` |
| `ConeKahlerForm`, KE equation | `ConeKahlerForm`, `ConeKahlerForm.IsKahlerEinstein`, `isKahlerEinstein_zero_iff`, `ofEq`, `ext` | `Cone/Kahler` |
| standard example | `standardConeKahlerForm β`, `standardConeKahlerForm_isKahlerEinstein` (`λ = 0`) | `Cone/Kahler` |
| `z₀ ↦ z₀²` is not adapted | test in `ConicalKahlerTest/Divisor` | tests |

With this the spec's v0.1 "definition of done" is met for the smooth-divisor case. The model and the
smooth-divisor quasi-isometry are defined, the model identities and chart independence for
`0 < β ≤ 1` are proved, and `β > 1` is supported as a model and as an existential compatible-chart
condition, with an explicit counterexample to unrestricted invariance. The SNC generalisation is
outstanding (see below). The model construction already accepts arbitrary `ConeWeights`, so SNC
will not require changing it.

## Milestone 3: metric geometry of the model (review priority 1): COMPLETE

The standard cone metric is *exactly* a flat cone transversally. All statements below are
equalities of metric tensors, and they are properties of the model only.

| Statement | Lean declaration | File |
|---|---|---|
| product structure: `q_β = q_transverse(z_0) + |dz'|²` | `modelConeQuadratic_single_eq_transverse`, `transverseConeMetric` | `Cone/FlatCone` |
| flat cone of angle `2πβ`: metric `dρ² + ρ² dφ²` on `(0,∞) × ℝ`, `φ ~ φ + 2πβ`; it is flat (pullback of `|dw|²` by `ρe^{iφ}`) | `flatConeMetric`, `flatConeMetric_eq_normSq_fderiv_polarMap`, `flatConeMetric_add_snd`, `polarMap_add_snd` | `Cone/FlatCone` |
| polar coordinates on `ℂ \ {0}` and deck group `θ ↦ θ + 2π` | `polarMap`, `fderiv_polarMap`, `normSq_fderiv_polarMap`, `polarMap_add_two_pi`, `exists_polarMap_eq` | `Cone/FlatCone` |
| radial change `ρ = c r^β`, `φ = βθ` is a diffeomorphism of `(0,∞) × ℝ` conjugating `θ ↦ θ + 2π` to `φ ↦ φ + 2πβ` | `coneRadialChange`, `coneRadialChangeHomeomorph`, `contDiffOn_coneRadialChange`, `contDiffOn_coneRadialChangeInv`, `coneRadialChange_add_two_pi` | `Cone/FlatCone` |
| **isometry, Hermitian form**: `β²|z_0|^(2β-2)|dz_0|² = dρ² + ρ²dφ²`, `ρ = r^β` | `transverseConeMetric_polar`, `modelConeQuadratic_polar_slice` | `Cone/FlatCone` |
| **isometry, Riemannian metric of the upstream form**: `ω_β(v, Jv)` on a transverse slice `= dρ² + ρ²dφ²`, `ρ = √2 r^β` | `standardConeForm_polar_riemannian`, `transverseSlice`, `fderiv_transverseSlice_polarMap` | `Cone/FlatCone` |
| developing map `ζ ↦ e^{βζ}` on the universal cover; holonomy = rotation by `2πβ`, trivial iff `β ∈ ℤ` | `transverseConeMetric_exp`, `exp_mul_add_two_pi_I`, `exp_two_pi_mul_I_eq_one_iff` | `Cone/FlatCone` |
| circumference `2πβ r^β`, radial length `r^β`, ratio `2πβ` | `coneCircleLength_eq`, `coneRadialLength_eq`, `coneCircleLength_eq_two_pi_mul_radialLength` | `Cone/FlatCone` |
| radial-coefficient calculus | `radialCoeff_congr`, `radialCoeff_add`, `radialCoeff_eq_deriv`, `radialCoeff_rpow_add_rpow_two_mul`, `radialCoeff_log_one_add_mul_rpow` | `Analysis/RadialCalculus` |
| separable Kähler forms `i∂∂̄ ∑ g_j(|z_j|²)` and their Ricci forms | `SeparableProfile`, `SeparableProfile.kahlerForm`, `kahlerForm_metricInChart`, `ricciForm_coeffMatrix` | `Cone/Separable` |
| **QI is strictly weaker than the model**: a form with `IsConeAlong` (`C = 5`) that is not Ricci-flat, for every `β > 0` | `perturbedConeForm`, `perturbedConeForm_isConeAlong`, `perturbedConeForm_ricciForm_coeffMatrix_zero` (`Ric_{00̄} = -4β²s^(β-1)/(1+4s^β)²`), `perturbedConeForm_not_ricciFlat`, `exists_isConeAlong_not_ricciFlat`, `perturbedConeKahlerForm_not_isKahlerEinstein_zero` | `Cone/QuasiIsometricExample` |
| tests (`β = 1/2`, `β = 2`, `β = 1`, holonomy, `n = 2`) | | `ConicalKahlerTest/Geometry` |

**Three levels, kept separate.**
1. *Model geometry* (this milestone): `ω_β` is transversally isometric to the flat cone of angle
   `2πβ`, and Ricci-flat.
2. *Strong asymptotic cone conditions* (spec §3.5; not defined): the metric is asymptotic to the
   model at the divisor.
3. *Quasi-isometric cone condition* `IsConeAlong`: two-sided bounds only.

The perturbed example `i∂∂̄(|z_0|^(2β) + |z_0|^(4β) + |z'|²)` satisfies 3. Its ratio to the model
tends to `1`, so it would also satisfy 2. It is not Ricci-flat, so it fails 1. Hence 1 is strictly
stronger than 3.

## Milestone 4: compatibility with upstream `metricInChart` (review priority 2): COMPLETE

| Statement | Lean declaration | File |
|---|---|---|
| holomorphic charts outside the selected atlas; the selected chart is one | `HolChart`, `HolChart.toChartAt`, `HolChart.contDiffAt_transition`, `HolChart.ofChartAt`, `DivisorChart.toHolChart` | `Manifold/HolomorphicChart`, `Divisors/AdaptedChart` |
| pullback along any holomorphic chart, on any open `U ⊆ X` | `formInHolChart`, `metricInHolChart`, `metricQuadraticInHolChart`, `formInHolChart_isPositive`, `metricInHolChart_posDef`, `formInHolChart_change`, `metricInHolChart_change`, `metricQuadraticInHolChart_change` | `Cone/ChartMetric` |
| the adapted-chart pullback is the special case `U = X \ D` (by `rfl`) | `formInAdaptedChart_eq_formInHolChart`, `metricInAdaptedChart_eq_metricInHolChart`, `metricQuadraticInAdaptedChart_eq_metricQuadraticInHolChart` | `Cone/ChartMetric` |
| charts of an open subset are restrictions of ambient charts | `extChartAt_opens_apply'`, `mem_extChartAt_opens_target`, `extChartAt_opens_symm_coe` | `Cone/SelectedChart` |
| **selected chart = upstream**: `chartRep x z = formInHolChart … (ofChartAt x) z`, so `metricInChart x z = metricInHolChart … (ofChartAt x) z` on the whole chart target | `chartRep_eq_formInHolChart`, `metricInChart_eq_metricInHolChart` | `Cone/SelectedChart` |
| **agreement**: if `χ.coord = chartAt x` then `metricInAdaptedChart D ω₀ χ z = ω₀.metricInChart x z` (and the quadratic forms agree) | `metricInAdaptedChart_eq_metricInChart`, `metricQuadraticInAdaptedChart_eq_chartRep` | `Cone/SelectedChart` |
| **transformation law** for an arbitrary adapted chart: `metricInChart x z = Aᵀ g^χ(w) Ā`, `A = D(χ ∘ (chartAt x)⁻¹)(z)`, `w = χ((chartAt x)⁻¹ z)`; quadratic form `ω(v,Jv)/2 = q^χ(w; Av)` | `metricInChart_eq_metricInHolChart_change`, `metricInChart_eq_metricInAdaptedChart_change`, `chartRep_apply_I_smul_eq_metricQuadraticInAdaptedChart` | `Cone/SelectedChart` |
| coordinate hyperplane: agreement for every Kähler form | `metricInAdaptedChart_coordHyperplane_eq_metricInChart` | `Cone/SelectedChart` |
| tests (model; shear chart transformation law) | | `ConicalKahlerTest/SelectedChart` |

The adapted-chart API was refactored to be a thin layer over `formInHolChart`. Every Milestone 2
declaration keeps its name, statement and definition. Only the proofs now go through the generic
lemmas. `formInAdaptedChart_coordHyperplaneChart` and
`metricQuadraticInAdaptedChart_coordHyperplaneChart` (any Kähler form, identity chart) are new.

## Decisions affecting definitions

* **Coordinates are 0-indexed.** The singular coordinate of the single-divisor model is `z 0`
  (the spec's and the task's `z₁`), and `DivisorChart.cutsOut` uses `coord x 0 = 0`.
* `modelWeight` is defined by cases (`none ↦ 1`, `some β ↦ β² ‖z_j‖^(2β-2)`) exactly as in the
  spec. Since `Real.rpow` is used, for `β < 1` the weight at `z_j = 0` takes Mathlib's junk value
  `0`. This does not matter, because every statement is restricted to `modelDomain θ` or to
  `z 0 ≠ 0`.
* `ModelConeForm θ` is *defined* as `i∂∂̄ Φ_θ` restricted to `modelDomain θ`, with
  `Φ_θ = ∑_{cone} |z_j|^(2β_j) + ∑_{smooth} |z_j|²`. Its coefficient matrix is then proved equal to
  the spec's `modelConeMatrix`.
* `metricQuadraticInAdaptedChart` is defined as `ω_χ(v, Jv)/2`, where `ω_χ = (ω y) ∘ Dτ(z)` and
  `τ = extChartAt y ∘ χ⁻¹`. The derivative is the real Fréchet derivative, i.e. the honest
  pullback; it is proved equal to the restriction of scalars of the complex derivative.
* `IsQuasiIsometricCone` is stated through the auxiliary predicate `ConeComparableIn`. The literal
  spec form is the theorem `isQuasiIsometricCone_iff`, which is proved by `Iff.rfl`.
* The chart-invariance theorem compares two adapted charts **at the same base point `p`**, and
  shrinks the second chart (`restrOpen`) to a neighbourhood of `p` chosen in the proof.
* `ConeKahlerForm.IsKahlerEinstein` is the equation on `X \ D` only, not the current equation on
  `X` (spec §6).
* **Flat cone.** The flat cone of angle `2πβ` is represented by its polar coordinates
  `(ρ, φ) ∈ (0, ∞) × ℝ` with the metric `dρ² + ρ²dφ²` and the deck translation `φ ↦ φ + 2πβ`.
  The quotient manifold is not constructed. Isometry statements are pullback identities between
  coverings that intertwine the deck groups. Lengths (`coneRadialLength`, `coneCircleLength`)
  are lengths of explicit curves. They are not distances: minimality of radial segments is not
  proved.
* **Normalisation in the isometry.** With the Hermitian form `q` the radial variable is
  `ρ = r^β`. With the upstream Riemannian metric `g = ω(·, J·) = 2q` it is `ρ = √2 r^β`.

Supporting lemmas re-proved locally because the upstream versions are `private`:
`ConicalKahler.ddbar_congr` (upstream `KahlerForm.ddbar_eq_of_eventuallyEq`) and
`ConicalKahler.mddbar_opens` (upstream `KahlerForm.mddbar_restrict_open`).

## Outstanding proof obligations

1. ~~Agreement with `metricInChart`~~: done in Milestone 4.
2. **General restriction and transport of Kähler forms** to open subsets (`KahlerForm n M →
   KahlerForm n U`), and restriction of `ConeKahlerForm` to neighbourhoods. The model already has
   this via `modelConeFormOn`.
3. **`Divisors/SNC`** (spec item 8): `SNCChart`, labelled components, the comparison condition
   with weights `some (angle (active j))`, and the smooth-divisor case as a special case.
   `ModelConeForm` and its Ricci-flatness already handle arbitrary `ConeWeights`.
4. **Cone-admissible atlases for `β > 1`** (spec §4.1): a `ConeAdmissibleChartChange` interface
   with bounded weighted Jacobians, and invariance within such an atlas.
5. **Stronger regularity** (spec §3.5): `IsAsymptoticCone`, weighted Hölder, conormal and
   polyhomogeneous interfaces. Deliberately not started; none of these is implied by
   `IsConeAlong`.
6. **Bridge** `smoothDivisor_of_regularHolomorphicSection` (holomorphic implicit function theorem).

## Blockers

None blocking. Technical notes:

* In this Mathlib, `ContinuousAt.norm` does not elaborate for maps into the nested space
  `E →L[ℂ] (E →L[ℂ] E)`. The norm-instance unification fails (reproduced outside the module
  system). `Analysis/HyperplaneMaps` therefore gets its second-order bounds from
  `ContDiffAt.exists_lipschitzOnWith` applied to `fderiv`, instead of bounding the norm of the
  second derivative.
* `ω` cannot be used as a variable name in files that `open scoped ContDiff` (it is analyticity
  notation). Kähler forms are named `ω₀`, as upstream does.
