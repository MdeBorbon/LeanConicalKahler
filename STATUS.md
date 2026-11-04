# STATUS

Last updated: 2026-11-04.

Pins: Lean `v4.34.1`, Mathlib `v4.34.1` (`d13f23b7`), `calabiyau` at
`91b1ddf000c7028bc42ae6102eba0e2042eb37ff`. Upstream is used unmodified.

Every completed result below is kernel-checked. `scripts/AxiomAudit.lean` confirms that all 315
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

Supporting lemmas re-proved locally because the upstream versions are `private`:
`ConicalKahler.ddbar_congr` (upstream `KahlerForm.ddbar_eq_of_eventuallyEq`) and
`ConicalKahler.mddbar_opens` (upstream `KahlerForm.mddbar_restrict_open`).

## Outstanding proof obligations

1. **Agreement with `metricInChart`**: if `χ.coord = chartAt (E n) x` for `x : D.complement`, then
   `metricInAdaptedChart D ω₀ χ z _ _ = ω₀.metricInChart x z` on the chart target. This needs
   lemmas identifying `extChartAt` and `tangentCoordChange` of an `Opens` subtype with those of the
   ambient manifold. They are straightforward but were not needed for any result above.
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
