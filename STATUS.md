# STATUS

Last updated: 2026-11-04.

Pins: Lean `v4.34.1`, Mathlib `v4.34.1` (`d13f23b7`), `calabiyau` at
`91b1ddf000c7028bc42ae6102eba0e2042eb37ff`. Upstream is used unmodified.

Every completed result below is kernel-checked. `scripts/AxiomAudit.lean` confirms that all 680
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
| **chart invariance, `0 < β ≤ 1`** | `ConeComparableIn.exists_restrOpen_of_le_one`, `IsQuasiIsometricCone.forall_chart_of_le_one` (since Milestone 6: the one-label case of the SNC theorem) | `Cone/ChartInvariance` |
| analytic inputs | `exists_hyperplane_estimates`, `fderiv_apply_zero_eq_zero_of_tangent`, `modelConeQuadratic_le_of_le_one`, `exists_model_comparison` (since Milestone 6: special cases of the general lemmas below) | `Analysis/HyperplaneMaps`, `Cone/ChartInvariance` |
| **counterexample, `β > 1`** | `shearChart`, `not_coneComparableIn_shear` (fails for every neighbourhood and constant) | `Cone/AngleRestriction` |
| shear is admissible for `β ≤ 1` | `coneComparableIn_shear_of_le_one` (`C = 2 + 2/β²`) | `Cone/AngleRestriction` |
| `ConeKahlerForm`, KE equation | `ConeKahlerForm`, `ConeKahlerForm.IsKahlerEinstein`, `isKahlerEinstein_zero_iff`, `ofEq`, `ext` | `Cone/Kahler` |
| standard example | `standardConeKahlerForm β`, `standardConeKahlerForm_isKahlerEinstein` (`λ = 0`) | `Cone/Kahler` |
| `z₀ ↦ z₀²` is not adapted | test in `ConicalKahlerTest/Divisor` | tests |

With this the spec's v0.1 "definition of done" is met for the smooth-divisor case. The model and the
smooth-divisor quasi-isometry are defined, the model identities and chart independence for
`0 < β ≤ 1` are proved, and `β > 1` is supported as a model and as an existential compatible-chart
condition, with an explicit counterexample to unrestricted invariance. The SNC generalisation
(Milestone 5) did not change the model construction.

## Milestone 3: metric geometry of the model (review priority 1): COMPLETE

Transversally, the standard cone metric is *exactly* a flat cone, in the following sense. All
statements below are equalities of metric tensors on covering coordinates, together with
equivariance under the deck groups and lengths of explicit curves. They are properties of the
model only. No metric-space isometry with the quotient cone, and nothing at the vertex, is
claimed (see outstanding item 4).

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

## Milestone 5: SNC divisors with labelled cone angles (review priority 3, spec item 8): COMPLETE

| Statement | Lean declaration | File |
|---|---|---|
| SNC chart (spec §4 fields verbatim) | `SNCChart n X ι components p`, `SNCChart.slot`, `SNCChart.Away`, `SNCChart.toHolChart`, `SNCChart.restrOpen` | `Divisors/SNC` |
| support/complement in a chart | `SNCChart.mem_iUnion_iff`, `symm_notMem_iUnion`, `away_coord`, `SNCChart.symmComplement` | `Divisors/SNC` |
| SNC divisor with labelled components; complement is open | `SNCDivisor n X ι` (`components`, `isClosed`, `locallyFinite`, `exists_chart`), `support`, `isClosed_support`, `complement`, `mem_complement_iff_forall` | `Divisors/SNC` |
| **each labelled component is a smooth divisor** | `SNCChart.toDivisorChart` (swap the slot to coordinate `0`), `SNCDivisor.component`, `swapCoord`, `HolChart.transCLE` | `Divisors/SNC`, `Manifold/HolomorphicChart` |
| local weights `some (angle (active j))` / `none`; **same `ConeWeights` and `ModelConeForm`** | `SNCChart.localWeights`, `localWeights_angle_slot`, `mem_modelDomain_localWeights` (model domain = `Away`), `modelWeight_localWeights_slot` | `Divisors/SNC` |
| coordinate SNC divisor `{z_0 ⋯ z_{k-1} = 0}` | `coordSNC n k hk`, `coordSNCChart`, `coordSNCWeights`, `coordSNC_complement` (= model domain) | `Divisors/SNC` |
| metric in an SNC chart | `metricInSNCChart`, `metricQuadraticInSNCChart`, `metricInSNCChart_posDef`, `metricQuadraticInSNCChart_pos`, `metricQuadraticInSNCChart_change` | `Cone/SNCComparison` |
| SNC quasi-isometric cone condition, arbitrary angles `β_i > 0` | `SNCConeComparableIn`, `IsQuasiIsometricSNCCone`, `IsSNCConeAlong` (abbrev), `.restrOpen`, `.mono`, `exists_chart_subset` | `Cone/SNCComparison` |
| SNC model is SNC-conical (`C = 1`), Ricci-flat, KE | `modelOnCoordSNC`, `modelOnCoordSNC_coeffMatrix`, `modelOnCoordSNC_isSNCConeAlong`, `modelOnCoordSNC_ricciFlat`, `SNCConeKahlerForm`, `standardSNCConeKahlerForm_isKahlerEinstein` | `Cone/SNCComparison` |
| **smooth case is a specialization** | `SmoothDivisor.toSNC`, `DivisorChart.toSNCChart`, `toSNC_complement`, `toSNC_chart_k`, `localWeights_eq_singleConeWeights`, `SmoothDivisor.toSNCForm`, `isConeAlong_iff_isSNCConeAlong` | `Divisors/SNC`, `Cone/SNCComparison` |
| tests (`n = k = 2` with angles `π` and `6π`; components; `k = 1`; smooth ⇒ SNC) | | `ConicalKahlerTest/SNC` |

`ConeWeights`, `modelDomain`, `modelWeight`, `modelConeQuadratic` and `modelConeFormOn` are
reused unchanged. The SNC model *is* `modelConeFormOn (coordSNCWeights hk angle)`.

## Milestone 6: chart invariance of SNC conical metrics (second review): COMPLETE

**Theorem.** Let `Δ` be an SNC divisor with labelled components and cone angles
`angle : ι → ConeAngle` with `0 < β_i ≤ 1` for all labels. Suppose `ω₀` on `X \ ⋃ᵢ Dᵢ` is
comparable to the local SNC model in one SNC chart at `p`. Then it is comparable to the local SNC
model in every SNC chart at `p`, after shrinking that chart around `p`. So
`IsQuasiIsometricSNCCone` does not depend on the charts used.

| Statement | Lean declaration | File |
|---|---|---|
| **SNC chart invariance, all `β_i ≤ 1`** | `SNCConeComparableIn.exists_restrOpen_of_le_one`, `IsQuasiIsometricSNCCone.forall_chart_of_le_one` | `Cone/SNCChartInvariance` |
| matching of active components **by label** (permutations allowed); local angles `≤ 1` | `SNCChart.weightsMatch`, `SNCChart.localWeights_le_one` | `Cone/SNCChartInvariance` |
| analytic core: two-sided comparison of arbitrary cone models under a hyperplane-matching biholomorphism, all angles `≤ 1` | `WeightsMatch`, `exists_weighted_term_bound`, `exists_weighted_upper_bound`, `exists_weighted_model_comparison` | `Cone/WeightedComparison` |
| where `β ≤ 1` enters | `cone_term_le` (one-term inequality), `norm_sq_le_modelConeQuadratic` (the model controls `‖v‖²`), `invWeightBound` | `Cone/WeightedComparison` |
| estimates for maps sending `{ζ_a = 0}` into `{z_b = 0}` (`a ≠ b` allowed) | `exists_coordHyperplane_estimates`, `fderiv_apply_eq_zero_of_tangent`, `coordHypProj` | `Analysis/HyperplaneMaps` |
| two charts around a common point | `HolChart.eventually_transition`, `transition_apply_center`, `eventually_transition_left_inv`, `contDiffAt_transition_center` | `Manifold/HolomorphicChart` |
| smooth and one-label SNC comparisons agree | `coneComparableIn_iff_sncConeComparableIn` | `Cone/SNCComparison` |
| tests: crossing components with angles `π` and `2π/3` in `ℂ²` (swapped chart) and in `ℂ³` (swap plus shear into the smooth direction); local weights follow labels, not slots | | `ConicalKahlerTest/SNCInvariance` |

**No duplicated argument.** The analytic estimate is proved once, for arbitrary `ConeWeights`, and
the smooth-divisor results are now corollaries:

* `exists_model_upper_bound` and `exists_model_comparison` are the single-hyperplane case of the
  weighted lemmas (`weightsMatch_single`, `singleConeWeights_le_one`).
* `ConeComparableIn.exists_restrOpen_of_le_one` is the one-label case of the SNC theorem, through
  `coneComparableIn_iff_sncConeComparableIn`.
* `exists_hyperplane_estimates` is the `a = b = 0` case of `exists_coordHyperplane_estimates`.
* `modelConeQuadratic_le_of_le_one` keeps its statement and constant. It is now proved from
  `cone_term_le`.

All Milestone 2 statements are unchanged and the existing tests (including the shear chart)
still pass.

**Not covered.** For `β_i > 1` the condition remains an existence-of-compatible-chart condition.
The shear counterexample embeds through `isConeAlong_iff_isSNCConeAlong`.

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
* **Generic chart layer.** The pullback is defined once for a `HolChart` on an arbitrary open
  `U ⊆ X` (`formInHolChart`). `formInAdaptedChart` keeps its original definition, which is
  definitionally the `U = X \ D` case.
* **SNC divisors.** `SNCChart` has exactly the spec's fields. `SNCDivisor` asks for a
  `LocallyFinite` family of closed components rather than `[Fintype ι]`. This is implied by
  `[Finite ι]` (`locallyFinite_of_finite`) and is what makes the support closed. Components are
  labelled, not required to be irreducible or connected: a label is what carries a cone angle.
  The angle function is `ι → ConeAngle`, so every component has a cone angle (use `β = 1` for an
  uncharged component). The "away" condition in an SNC chart is `χ.Away z` (all active
  coordinates nonzero), which is equivalent to `z ∈ modelDomain (χ.localWeights angle)`.
  Charts are not required to have `p` on all of their active components (as in the spec). The
  components through the centre are always active (`mem_range_active_of_mem`).
* **Chart invariance by labels.** In the SNC invariance theorem the coordinate change is matched
  component-by-component *by label*. The slot of a label may differ between the two charts.
  Active components of a chart that do not pass through `p` need no matching: their weights are
  bounded near `p`.
* **Helper renames (Milestone 6).** The projection `hypProj` onto `{z_0 = 0}` and its lemmas were
  generalised to `coordHypProj a` (any coordinate) with the same lemma names otherwise
  (`coordHypProj_apply`, `coordHypProj_apply_self`, …). The `0`-specific theorems
  `exists_hyperplane_estimates`, `fderiv_apply_zero_eq_zero_of_tangent` and `norm_apply_zero_le`
  are kept. The hypothesis `p ∈ D` of `ConeComparableIn.exists_restrOpen_of_le_one` is no longer
  needed. It is kept, named `_hp`, so that existing calls are unchanged.
* **Transport of forms** along an equality of open sets (`kahlerCast`) is used to compare
  `KahlerForm n D.complement` with `KahlerForm n D.toSNC.complement`. The two open sets are
  equal but not definitionally so.

Supporting lemmas re-proved locally because the upstream versions are `private`:
`ConicalKahler.ddbar_congr` (upstream `KahlerForm.ddbar_eq_of_eventuallyEq`) and
`ConicalKahler.mddbar_opens` (upstream `KahlerForm.mddbar_restrict_open`).

## Outstanding proof obligations

Done since the first review: agreement with `metricInChart` (Milestone 4), `Divisors/SNC`
(Milestone 5), and SNC chart invariance for `β_i ≤ 1` (Milestone 6).

1. **General restriction and transport of Kähler forms** to open subsets (`KahlerForm n M →
   KahlerForm n U`), and restriction of `ConeKahlerForm` to neighbourhoods. The model has this via
   `modelConeFormOn`. Transport along *equal* open sets is `kahlerCast`.
2. **Cone-admissible atlases when some angle exceeds `2π`** (spec §4.1), for smooth and SNC
   divisors: a `ConeAdmissibleChartChange` interface with bounded weighted Jacobians, and
   invariance within such an atlas. The invariance theorem of Milestone 6 needs *all* `β_i ≤ 1`.
   With a single `β_i > 1` it fails for arbitrary charts (shear counterexample).
3. **Stronger regularity** (spec §3.5): `IsAsymptoticCone`, weighted Hölder, conormal and
   polyhomogeneous interfaces. Deliberately not started, as requested. None of these is implied by
   `IsConeAlong`. Milestone 3 gives a form with `IsConeAlong` that is not Ricci-flat.
4. **Metric-space statements for the flat cone.** The Milestone 3 results are tensor identities
   and deck-group equivariance on covering coordinates (see the README). Still missing: the
   quotient cone as a metric space, the path-length distance, minimality of radial segments, and
   the metric completion of `(ℂ \ {0}, g_β)` with its vertex.
5. **Bridge** `smoothDivisor_of_regularHolomorphicSection` (holomorphic implicit function theorem).

## Blockers

None blocking. Technical notes:

* In this Mathlib, `ContinuousAt.norm` does not elaborate for maps into the nested space
  `E →L[ℂ] (E →L[ℂ] E)`. The norm-instance unification fails (reproduced outside the module
  system). `Analysis/HyperplaneMaps` therefore gets its second-order bounds from
  `ContDiffAt.exists_lipschitzOnWith` applied to `fderiv`, instead of bounding the norm of the
  second derivative.
* `ω` cannot be used as a variable name in files that `open scoped ContDiff` (it is analyticity
  notation). Kähler forms are named `ω₀`, as upstream does.
