# STATUS

Last updated: 2026-11-06.

Pins: Lean `v4.34.1`, Mathlib `v4.34.1` (`d13f23b7`), `calabiyau` at
`91b1ddf000c7028bc42ae6102eba0e2042eb37ff`. Upstream is used unmodified.

Every completed result below is kernel-checked. `scripts/AxiomAudit.lean` confirms that all 2124
`ConicalKahler.*` declarations (library and tests) depend only on `propext`, `Classical.choice` and
`Quot.sound`.
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

## Milestone 7: the Laplacian and elementary harmonic analysis of the models (third review): COMPLETE

All entries are kernel-checked. The Schauder theory itself is **not** started; see `ROADMAP.md`.

| Statement | Lean declaration | File |
|---|---|---|
| **Laplace–Beltrami operator** of the Riemannian metric `g = ω(·, J·)`, reusing upstream `ΔG`; `Δ_g = 2 tr_ω(i∂∂̄)` | `laplaceBeltrami`, `laplaceBeltrami_eq_two_mul_laplacian` | `Laplacian/Model` |
| complex-trace Laplacian on `U ⊆ ℂⁿ`; `Re ∂_j∂̄_j f = ¼ Δ_{z_j} f` | `laplacian_opens`, `re_complexHessian_diag`, `coordLaplacian` | `Laplacian/Model`, `Laplacian/Polar` |
| **products of cones and Euclidean factors**: `Δ_g f = ∑_j Δ_{z_j} f / (2 w_j)` | `laplaceBeltrami_modelConeFormOn`, `laplaceBeltrami_modelConeFormOn_split`, `laplacian_modelConeFormOn` | `Laplacian/Model` |
| second-order chain rule along curves; Euclidean Laplacian in polar coordinates | `deriv_deriv_comp_curve`, `coordLaplacian_polar`, `coordLaplacian_eq_rotate` | `Laplacian/Polar` |
| **polar formula for the cone**: `F_ρρ + ρ⁻¹F_ρ + (βρ)⁻²F_θθ = β⁻² ρ^{2/β-2} Δ_{z_j} f`; for the model, the `j`-th term is `½(F_ρρ + ρ⁻¹F_ρ + (βρ)⁻²F_θθ)`; for the standard 2D cone this is all of `Δ_g` | `coordLaplacian_conePolar`, `coordLaplacian_div_modelWeight_conePolar`, `laplaceBeltrami_standardCone_polar` | `Laplacian/Polar`, `Laplacian/Model` |
| **`ρ^{k/β} cos kθ`, `ρ^{k/β} sin kθ` harmonic**, polar form | `coneHarmonicCos`, `coneHarmonicSin`, `coneHarmonicCos_polar_eq_zero`, `coneHarmonicSin_polar_eq_zero` | `Laplacian/ConeHarmonic` |
| … and as `Re z_j^k`, `Im z_j^k`, for the actual Laplace–Beltrami operator of every model (indeed every Kähler form) | `re_pow_coordSlice_conePolar`, `laplaceBeltrami_re_pow_eq_zero`, `laplaceBeltrami_im_pow_eq_zero` | `Laplacian/ConeHarmonic`, `Laplacian/Model` |
| pluriharmonic ⇒ harmonic for every Kähler form; `i∂∂̄ Re P = 0` | `laplaceBeltrami_eq_zero_of_ddbar_eq_zero`, `ddbar_re_eq_zero`, `ddbar_im_eq_zero`, `laplaceBeltrami_re_eq_zero` | `Laplacian/Model` |
| homogeneity of degree `k/β`; cone dilations are homotheties `q ↦ λ² q` of every product of cones | `coneHarmonicCos_homogeneous`, `re_pow_coneDilate`, `coneDilation`, `modelConeQuadratic_coneDilation`, `coneDilation_mul` | `Laplacian/ConeHarmonic`, `Cone/Dilation` |
| derivatives and estimates: explicit `∂_ρ`, `∂_θ`, `∂²_ρ`, `∂²_θ`; exact gradient norm `(k/β)² ρ^{2k/β-2}`; scale-invariant bounds | `deriv_coneHarmonicCos_rho`, …, `coneHarmonicCos_gradNormSq`, `coneHarmonicCos_bounds`, `coneHarmonicSin_bounds` | `Laplacian/ConeHarmonic` |
| degree-two functions: `Δ_g ρ_j² = 2`; `ρ_a² − ρ_b²` harmonic | `potentialTerm`, `laplaceBeltrami_potentialTerm`, `laplaceBeltrami_potentialTerm_sub` | `Laplacian/Model` |
| logarithmic barrier `log |z_j|²` harmonic | `ddbar_log_coordNormSq_eq_zero`, `laplaceBeltrami_log_coordNormSq_eq_zero` | `Laplacian/Model` |
| tests (`β = 1`; angle `π`; two cones `π`, `2π/3`; cross-check of polar and Kähler routes) | | `ConicalKahlerTest/Laplacian` |
| **roadmap** to de Borbon–Edwards Thm 1.1: dictionary of normalisations, exact statement, ingredient list with status, reuse survey (calabi-yau, EllipticPDE) | | `ROADMAP.md` |

**Normalisation (checked against the paper).** The paper's metric `dr² + β²r²dθ²` is our Hermitian
form `q`, with `r = ρ = |z|^β`. Our Riemannian metric is `g = 2q`. So
`laplaceBeltrami = ½ Δ_paper`, and `Δ_g ρ² = 2` corresponds to the paper's `Δ_β r² = 4`.

**What is not claimed.**
- Harmonicity is proved pointwise on the regular part, for smooth functions.
- No weak or `W^{1,2}` statement is made.
- Nothing is said at the cone locus beyond what the explicit formulas show.
- The completeness of the list of homogeneous harmonic functions (paper Prop. 3.4) is not proved.

## Milestone 8: real cone geometry and the operators `𝒟₂` (fourth review): COMPLETE

All entries are kernel-checked. Paper references are to de Borbon–Edwards. The two requested
corrections to `ROADMAP.md` are made:
1. `𝒟₂` consists of the coordinate operators of p. 2, not covariant Hessian components.
2. The paper's real coordinates (which keep `θ` and are globally defined) are distinguished from
   the flat developing coordinates (which use `βθ` and are local or on a cover).

**One cone factor** (`Real/ConeFactor`, `Real/ConeDistance`)

| Statement | Lean declaration |
|---|---|
| the paper's metric `dr² + β²r²dθ²` at `w ∈ ℂ ≅ ℝ²`; polar form | `paperConeMetric`, `paperConeMetric_polar` |
| uniform equivalence: `β²|v|² ≤ g ≤ |v|²` (`β ≤ 1`); `min(1,β²)`, `max(1,β²)` in general | `le_paperConeMetric_of_le_one`, `paperConeMetric_le_of_le_one`, `paperConeMetric_bounds` |
| Gram determinant `β²`, volume density `β` | `paperConeGram`, `det_paperConeGram`, `sqrt_det_paperConeGram` |
| real coordinates keep `θ` and are global; developing coordinates are not single-valued for `β ∉ ℤ` | `realConeChart`, `realConeChart_polarMap`, `realConeChartHomeomorph`, `polarMap_paperCoords_add_two_pi`, `developing_add_two_pi_ne` |
| bridge: `β²|z|^{2β-2}|v|² = g_paper(Φ_β z; DΦ_β(z) v)` | `hasFDerivAt_realConeChart`, `fderiv_realConeChart_apply`, `transverseConeMetric_eq_paperConeMetric` |
| planar hinges and the hinge comparison (triangle inequality of the Euclidean cone) | `hingeDist`, `hingeDist_eq_norm_sub`, `hingeDist_triangle` |
| **cone distance** `d² = r² + s² − 2rs cos(min(β∠, π))`, a metric space | `coneVertexAngle`, `coneDist`, `ConeTwo` (`MetricSpace`), `coneDist_triangle`, `eq_of_coneDist_eq_zero` |
| formula in the paper's polar coordinates with `θ ∈ ℝ/2πℤ` | `angle_polarMap_eq_abs_toReal`, `coneDist_polarMap` |
| locally the flat distance in developing coordinates | `coneDist_polarMap_eq_developing` |
| distance to the vertex is `r`; along rays `|t − s||p|`; dilations and rotations; `β = 1` is Euclidean | `coneDist_vertex`, `coneDist_radial`, `coneDist_mul_left`, `coneDist_one` |
| Euclidean comparison: `β|p−q| ≤ d ≤ |p−q|` (`β ≤ 1`); `|p−q| ≤ d ≤ (πβ/2)|p−q|` (`β ≥ 1`) | `mul_norm_sub_le_coneDist`, `coneDist_le_norm_sub`, `norm_sub_le_coneDist`, `coneDist_le_mul_norm_sub`, `coneDist_bounds` |
| balls: `B_E(w,ρ) ⊆ B_d(w,ρ) ⊆ B_E(w,ρ/β)`; vertex balls are Euclidean; same topology | `ConeTwo.ball_subset_of_le_one`, `ConeTwo.ball_vertex`, `ConeTwo.homeomorph` |

**Products of cones and a Euclidean factor** (`Real/Product`), cone factors indexed by a finite type
`κ`, Euclidean coordinates by `ι`

| Statement | Lean declaration |
|---|---|
| real coordinate space of dimension `2#κ + #ι` (odd allowed) | `RealConeIndex`, `RealConeModel`, `RealConeModel.cone`, `.eucl`, `.ofCones`, `.norm_sq_eq` |
| product metric, uniform equivalence (eq. (2.1)) | `productConeMetric`, `productConeMetric_bounds`, `productConeMetric_bounds_of_le_one` |
| Gram matrix block diagonal; `det g = ∏ β_a²` | `productConeBilin`, `productConeGram`, `productConeGram_eq`, `det_productConeGram` |
| **Riemannian volume `= (∏ β_a) · Lebesgue`**; singular set null; statement in coordinates | `ae_cone_ne_zero`, `productConeVolume`, `productConeVolume_eq`, `map_ofLp_productConeVolume` |
| **product distance** as the `L²` product (`PiLp 2`) of the factor metric spaces | `ConeFactor`, `toFactors`, `ConeProduct` (`MetricSpace`), `ConeProduct.dist_mk` |
| comparison with the Euclidean distance (`β_a ≤ 1`; arbitrary angles with explicit constants) | `ConeProduct.dist_bounds`, `.dist_bounds_of_le_one`, `.dist_bounds_uniform`, `.lowerConst`, `.upperConst` |
| ball inclusions; balls centred on the vertex stratum are Euclidean; dilations; topology | `ConeProduct.ball_subset`, `.ball_subset_of_le_one`, `.dist_of_cone_eq_zero`, `.ball_of_cone_eq_zero`, `.dist_smul`, `.homeomorph` |

**The operators `𝒟₂` and the examples** (`Real/D2`)

| Statement | Lean declaration |
|---|---|
| polar coordinates `(r_a, θ_a, s_i)` with lifted angles; the real point; `2π`-periodicity | `ConeVar`, `PolarPoint`, `PolarPoint.toModel`, `PolarPoint.toModel_update_theta_add_two_pi` |
| coordinate partial derivatives, `Δ_β`, `Δ = ∑ Δ_{β_a} + Δ_{ℝ^ι}` | `pd`, `coneLaplacian`, `paperLaplacian` |
| **`𝒟₂` exactly as on p. 2**, pure conical operators only for `β_a < 1/2` | `D2Op`, `D2Op.apply` |
| `r^{k/β} cos kθ`, `r^{k/β} sin kθ`, `r^{1/β} s cos θ` harmonic | `coneLaplacian_harmonicCos`, `coneLaplacian_harmonicSin`, `paperLaplacian_harmonicCos`, `paperLaplacian_mixedExample` |
| for `β_a ≥ 1/2`, every `D ∈ 𝒟₂` annihilates the `Δ_{β_a}`-harmonic functions of `(r_a, θ_a)` | `D2Op.apply_factor_eq_zero` |
| `∂²_r(r^{1/β} cos θ) = β⁻¹(β⁻¹−1) r^{1/β−2} cos θ`; `∂²_{rs}(r^{1/β} s cos θ) = β⁻¹ r^{1/β−1} cos θ` | `pd_r_pd_r_harmonicCos_one`, `rs_apply_mixedExample` |
| `C r^γ cos θ` is `γ`-Hölder at the vertex and not `α`-Hölder near it for `α > γ` (cone distance) | `radialCosFn`, `abs_radialCosFn_le`, `HolderNearVertex`, `not_holderNearVertex_radialCosFn` |
| **sharpness of the exponent bounds in `μ`** (p. 3 items 1–2) | `holderExponentBound`, `sharp_holderExponent` |
| pure conical operators must be excluded for `β ≥ 1/2`, including `β = 1/2` | `not_holderNearVertex_pure_of_half_le` |

**Bridge and normalisations** (`Real/Bridge`, `Real/Normalisation`)

| Statement | Lean declaration |
|---|---|
| Kähler model `ℂ^N` (weights `θ`) → real model with one cone per cone direction and two Euclidean coordinates per smooth direction | `ConeWeights.ConeIdx`, `.SmoothIdx`, `.coneAngleOf`, `.RealModel`, `.realChart`, `.realChartDeriv`, `.fderiv_realChart_cone` |
| `q_θ(z; v) = g_paper(Φ z; DΦ v)`; **`ω_θ(v, Jv) = 2 g_paper(Φ z; DΦ v)`** (the factor 2) | `ConeWeights.modelConeQuadratic_eq_productConeMetric`, `ConeWeights.modelConeForm_apply_I_smul_eq_two_mul` |
| **`laplaceBeltrami(ω_β) = ½ Δ_β`** in the paper's coordinates | `laplaceBeltrami_eq_half_coneLaplacian` |

**Tests and paper checks.**
- `ConicalKahlerTest/RealCone`:
  - opposite points at distance `√2` on the cone of angle `π`, and `2` (through the vertex) for
    `β = 3`;
  - **area `πβρ²` of the metric disk of radius `ρ` about the vertex**, which checks the distance
    and volume normalisations against each other;
  - dimension `5` for `C(S¹_π) × C(S¹_{2π/3}) × ℝ`, with volume factor `1/6`;
  - `𝒟₂` membership for `β = 1/3` but not `2/3`;
  - the exponent bounds;
  - `∂²_r(r² cos θ) = 2 cos θ` at `β = 1/2`;
  - an instance of `sharp_holderExponent`.
- `ConicalKahlerTest/PaperChecks`: Lean checks of the verified items of `PAPER_REVIEW.md`.

**Paper review.** `PAPER_REVIEW.md` separates verified items from suspected gaps.
- Verified items (V1–V8): the eigenvalue typo `k²β²` (should be `k²/β²`); the complex-coordinate
  normalisation and the placement of the factor `4`; the sign in `L_{0,0}`; `(m−3)⁻¹ → (m−2)⁻¹`;
  `> 1/2` versus `≥ 1/2` in `𝒟₂`; `c_β`; `√d → √n`; `λ^j r_a(x)^{−1}`.
- Suspected gaps (S1–S7): Prop. 2.5 boundary terms, Lemma 3.3, uniformity, Lemma 4.3, `β = 1/2`
  in the proof, Lemma 3.1, Lemma 2.7.

The target theorem is unchanged.

**Addendum: Proposition 2.5 audit (after Milestone 8).** The audit
`research_notes/PROPOSITION_2_5_AUDIT.md` was checked independently. The symbolic checks are in
`research_notes/prop_2_5_checks.py` (sympy, not kernel-checked).
- Confirmed errors in the arXiv proof (`PAPER_REVIEW.md`):
  - V9: an outer boundary term is missing from the Bochner argument; counterexample
    `sin(πR)/R` on `C(S¹_{2πβ}) × ℝ`;
  - V10: the intrinsic and Euclidean `W^{2,2}` are not equivalent; counterexample `r cos θ`.
- Remaining gaps: S1. The localised Bochner repair (§C) is proposed but not established.
- Proposition 2.5 and Theorem 1.1 are not claimed false.
- The journal version (paywalled) has not been compared. arXiv has only v1.

**What is not claimed.**
- `coneDist`, `ConeTwo` and `ConeProduct` carry a **formally defined** distance (the standard
  formula for Euclidean cones). It is not proved to be the length distance of `g`. Consistent
  facts are proved: the distance to the vertex, distances along rays, and flatness in developing
  coordinates on sectors.
- `𝒟₂` acts on functions of the lifted polar coordinates. Derivatives are one-variable `deriv`s,
  which take the value `0` where the slice is not differentiable, and the weight `r⁻¹` uses Lean's
  `0⁻¹ = 0`. Statements are made for `r_a > 0`.
- The Hölder statements concern explicit functions on one cone factor near the vertex, with respect
  to the cone distance. For `C r^γ cos θ` only the estimate at the vertex is proved, not full
  `γ`-Hölder continuity.
- The Laplacian normalisation in real coordinates is stated for one cone (`ℂ¹`). For products it
  follows from `laplaceBeltrami_modelConeFormOn_split`, but it is not restated in real
  coordinates. `fderiv` of `ConeWeights.realChart` is proved componentwise only.
- No Sobolev spaces, weak solutions or Schauder estimates yet. The classification of homogeneous
  harmonic functions is not attempted.

## Milestone 9: Sobolev spaces and weak solutions on the real cone models (fifth review): COMPLETE

All entries are kernel-checked. The Hilbert-space framework (`Sobolev/H1`, `Sobolev/Elliptic`) works
on any finite-dimensional real inner product space with an additive Haar measure. The Caccioppoli
inequality and density work on `ℝ^d` (Lebesgue measure), where upstream's Sobolev library applies.
The cone models enter through `coneCoeff` (`Sobolev/ConeLaplacian`).

| Statement | Lean declaration | File |
|---|---|---|
| test functions; the Hilbert space `L²(Ω) × L²(Ω; F)` of pairs; graphs `(φ, ∇φ)` | `IsTestFn`, `L2Pair`, `graph`, `testSubmodule` | `Sobolev/H1` |
| **`W^{1,2}_0(Ω)`** (closure of the graphs; complete) and **`W^{1,2}(Ω)`** (pairs with `G` the weak gradient of `u`; closed); `W^{1,2}_0 ⊆ W^{1,2}` | `H01`, `W12`, `IsWeakGradPair`, `H01_le_W12` | `Sobolev/H1` |
| integration by parts for test functions | `integral_mul_fderiv_eq_neg` | `Sobolev/H1` |
| **Friedrichs–Poincaré** for `Ω ⊆ B̄(x₀, R)` (any centre, since Milestone 10): `‖u‖ ≤ 2R ‖∇u‖` on `W^{1,2}_0(Ω)` | `norm_graph_fst_le`, `norm_fst_le_of_mem_H01`, `norm_sq_le_of_mem_H01` | `Sobolev/H1` |
| symmetric uniformly elliptic measurable coefficient fields; Cauchy–Schwarz and the norm bound for symmetric non-negative operators | `CoeffField`, `inner_sq_le_of_symm`, `norm_apply_le_of_symm`, `stronglyMeasurable_of_inner` | `Sobolev/Elliptic` |
| multiplication by `A` on `L²`; the Dirichlet form `∫ ⟨A G, H⟩`; coercivity on `W^{1,2}_0` | `CoeffField.mulOp`, `.dirichletForm`, `.lam_mul_norm_sq_le`, `.isCoercive_dirichletForm₀` | `Sobolev/Elliptic` |
| **weak solutions** of `-div(A ∇u) = f`; testing against all of `W^{1,2}_0(Ω)` | `CoeffField.IsWeakSolution`, `.isWeakSolution_iff`, `IsWeakSolution.forall_H01` | `Sobolev/Elliptic` |
| **existence and uniqueness** in `W^{1,2}_0(Ω)` for bounded `Ω` and `f ∈ L²(Ω)` (Lax–Milgram) | `CoeffField.existsUnique_H01_isWeakSolution` | `Sobolev/Elliptic` |
| cut-offs of `W^{1,2}(Ω)` functions lie in `W^{1,2}_0(Ω)` (via upstream mollification) | `cutPair`, `hasWeakPartialDeriv_cutFst`, `cutPair_mem_H01` | `Sobolev/Caccioppoli` |
| **Caccioppoli** (paper, Lemma 2.3): `∫ η² ⟨A ∇u, ∇u⟩ ≤ ∫ η² f² + ∫ (η² + 4Λ |∇η|²) u²` | `caccioppoli` | `Sobolev/Caccioppoli` |
| the inverse metric `g⁻¹` of one factor is the paper's metric with angle `1/β`; `G(β) G(1/β) = 1` | `coneInvFactor`, `inner_coneInvFactor`, `paperConeGram_mul_inv`, `productConeGram_mul_inv` | `Sobolev/ConeLaplacian` |
| **the cone Laplacian as a coefficient field** `A = g⁻¹` on `ℝ^d` (`λ = (1+∑β_a²)⁻¹`, `Λ = 1+∑β_a⁻²`; `λ = 1` if `β_a ≤ 1`) | `coneInvOp`, `coordIso`, `coneCoeffA`, `coneCoeff`, `coneCoeff_coercive_of_le_one` | `Sobolev/ConeLaplacian` |
| existence/uniqueness and Caccioppoli for the cone Laplacian | `cone_existsUnique_H01`, `cone_caccioppoli` | `Sobolev/ConeLaplacian` |
| logarithmic cut-offs `h_n(t) = S(log t / n + 2)`; `|h_n'| ≤ C/(nt)` | `logCut`, `contDiff_logCut`, `abs_deriv_logCut_le` | `Sobolev/Capacity` |
| energy in a plane `∫_{ℝ²} 4|y|² h_n'(|y|²)² ≤ 4πC²/n`; Fubini over the plane of `(x_{i₀}, x_{i₁})`; `∫_{B̄_R} |∇χ_n|² ≤ (4πC²/n) V_R` | `integral_cutEnergy_plane_le`, `integral_closedBall_le_plane`, `integral_closedBall_norm_gradient_planeCut_le` | `Sobolev/Capacity` |
| **density** (paper, §2.1): test functions on `Ω \ S` are dense in `W^{1,2}_0(Ω)`; the weak equation need only be tested on the regular part | `graph_mem_closure_testSubmodule_diff`, `dense_testSubmodule_regular`, `isWeakSolution_iff_regular` | `Sobolev/Capacity` |
| tests on `C(S¹_π) × ℝ ⊆ ℝ³` | | `ConicalKahlerTest/Sobolev` |

**Normalisation.** The paper's weak equation `∫ ⟨∇u, ∇φ⟩_g dV_g = ∫ f φ dV_g` becomes, in real
coordinates, `∫ ⟨g⁻¹ ∇u, ∇φ⟩ dx = ∫ f φ dx`: the constant `∏ β_a` in `dV_g = (∏ β_a) dx` cancels
(`productConeVolume_eq`). We therefore use Lebesgue measure and `A = g⁻¹`.

**What is not claimed.**
- The `W^{1,2}` spaces are those of `ℝ^d` with Lebesgue measure. The paper defines them through
  `g` and `dV_g`; the norms are equivalent (bounds `λ, Λ` and the constant `∏ β_a`), but that is
  stated here only through the coercivity and upper bounds of `coneCoeff`.
- The paper tests the weak equation against compactly supported **Lipschitz** functions; we use
  smooth ones. Ours is implied by the paper's, and conversely holds for every test pair in
  `W^{1,2}_0(Ω)` (`IsWeakSolution.forall_H01`). That compactly supported Lipschitz functions lie in
  `W^{1,2}_0` (Rademacher) is not formalised.
- The Friedrichs constant `2R` is not optimal. The mean-value Poincaré inequality on balls is not
  restated here (upstream has it on the unit ball).
- Rellich compactness, harmonic approximation (Lemma 2.4), regularity and the Hessian estimate
  (Prop. 2.5) are not started. (Rellich and Lemma 2.4 are done in Milestone 10.)

## Milestone 10: compactness, harmonic approximation, scaling, spectral theory (sixth review): COMPLETE

All entries are kernel-checked. Files `Sobolev/Restrict`, `Sobolev/Rellich`, `Sobolev/Intrinsic`,
`Sobolev/HarmonicApprox`, `Sobolev/ConeApprox`, `Sobolev/Divergence`, `Sobolev/Scaling`,
`Sobolev/Spectral`; tests in `ConicalKahlerTest/Compactness`.

**1. Bridges with the geometric theory.**

| Statement | Lean declaration | File |
|---|---|---|
| `g⁻¹ ξ` is the **metric gradient**: `g(g⁻¹ξ, w) = ⟨ξ, w⟩`; `|∇_g u|²_g = ⟨g⁻¹ξ, ξ⟩` | `productConeBilin_coneInvOp`, `productConeMetric_coneInvOp`, `coneGradNormSq_eq` | `Sobolev/Intrinsic` |
| `dV_g`, transported to `ℝ^d`, is `(∏ β_a) dx` (reusing `productConeVolume_eq`) | `coneVolume`, `coneVolume_eq` | `Sobolev/Intrinsic` |
| the **intrinsic norm** `∫_Ω (u² + |∇_g u|²_g) dV_g = (∏ β_a)(‖u‖² + ∫ ⟨g⁻¹G, G⟩)` | `intrinsicNormSq`, `intrinsicNormSq_eq` | `Sobolev/Intrinsic` |
| **norm equivalence** (paper, §2.1): `(∏β) λ ‖(u,G)‖² ≤ ‖u‖²_{W^{1,2}_g} ≤ (∏β) Λ ‖(u,G)‖²`; lower constant `∏β` for `β_a ≤ 1` | `intrinsicNormSq_bounds`, `intrinsicNormSq_lower_of_le_one` | `Sobolev/Intrinsic` |
| `g⁻¹ = I + ∑_a (β_a⁻² − 1) P_a` on the regular part (`P_a`: projection onto the rotation field `J_a y`; `J_a` skew) | `coneInvOp_eq_add_sum`, `rotJ`, `inner_rotJ_self` | `Sobolev/Divergence` |
| second derivatives along curves; polar second derivatives `∂²_r`, `∂²_θ = r²D²u(e_θ,e_θ) − r Du(e_r)`, `∂²_s` | `deriv_deriv_comp_curve`, `pd_r_pd_r_eq`, `pd_θ_pd_θ_eq`, `pd_s_pd_s_eq` | `Sobolev/Divergence` |
| **`div(g⁻¹ ∇u) = paperLaplacian β (u ∘ toModel)`** at every regular point, for `u` of class `C²` there (with `laplaceBeltrami_eq_half_coneLaplacian`, this is `2 Δ_g` for one factor) | `divergence`, `divergence_coneInvOp_gradient` | `Sobolev/Divergence` |

**2. Rellich compactness.**

| Statement | Lean declaration | File |
|---|---|---|
| our weak gradients are upstream weak partial derivatives; `H01 ⊆` upstream `MemW01p`; upstream witnesses agree with ours a.e. | `hasWeakPartialDeriv_of_mem_W12`, `memW01p_of_mem_H01`, `ae_eq_snd_of_witness` | `Sobolev/Rellich` |
| **Rellich**: bounded sequences in `W^{1,2}_0(Ω)` (`Ω` bounded open) have `L²`-convergent subsequences (reusing upstream `rellich_kondrachov_W01p_seq`) | `rellich_H01` | `Sobolev/Rellich` |
| **the embedding `W^{1,2}_0(Ω) ↪ L²(Ω)` is a compact operator** | `H01.fstL`, `isCompactOperator_H01_fst` | `Sobolev/Rellich` |
| restriction to subdomains: `L²(Ω) → L²(U)`, pairs, `W^{1,2}` and weak solutions restrict | `restrictLp`, `L2Pair.restrict`, `restrict_mem_W12`, `IsWeakSolution.restrict` | `Sobolev/Restrict` |
| smooth cut-offs `0 ≤ η ≤ 1`, `η = 1` on a compact `K ⊆ Ω` | `exists_cutoff` | `Sobolev/Restrict` |

**3. Harmonic approximation (paper, Lemma 2.4).**

| Statement | Lean declaration | File |
|---|---|---|
| energy estimates for the Dirichlet problem: `λ‖∇w‖ ≤ 2R‖f‖`, `λ‖w‖ ≤ 4R²‖f‖` (`Ω ⊆ B̄(x₀, R)`) | `lam_mul_norm_snd_le`, `lam_mul_norm_fst_le` | `Sobolev/HarmonicApprox` |
| **harmonic replacement**: `u = h + w` with `h` weakly `A`-harmonic on `Ω`, `w ∈ W^{1,2}_0(Ω)`, `λ‖u − h‖ ≤ 4R²‖f‖` | `exists_harmonic_replacement` | `Sobolev/HarmonicApprox` |
| **Lemma 2.4 with explicit `δ = λε/(4R²+1)`**, independent of the centre and shape of `Ω`, without the hypothesis `‖u‖ ≤ 1`; the paper's form with `U ⊆ Ω` | `harmonic_approximation`, `harmonic_approximation_restrict` | `Sobolev/HarmonicApprox` |
| **Lemma 2.4 on cone balls `B(p, ρ)` with `δ` independent of `p`** (`B(p,ρ) ⊆ B̄_E(p, ρ/lowerConst β)`) | `coneBall`, `coneBall_subset_closedBall`, `ball_subset_coneBall`, `isOpen_coneBall`, `cone_harmonic_approximation` | `Sobolev/ConeApprox` |
| Caccioppoli in gradient form; bounds for cut-off pairs | `caccioppoli_norm`, `norm_cutPair_sq_le` | `Sobolev/HarmonicApprox` |
| **compactness of approximate solutions**: weak solutions with `‖u_n‖ ≤ M`, `f_n → f` have a subsequence converging **in `W^{1,2}(U)`** (`U` open, `closure U ⊆ Ω` compact) to a weak solution with right-hand side `f` | `norm_restrict_sq_le_of_cutoff`, `exists_tendsto_of_approx_solutions` | `Sobolev/HarmonicApprox` |
| Lemma 2.4 by the **paper's contradiction argument** | `harmonic_approximation_of_compactness` | `Sobolev/HarmonicApprox` |

**4. Scaling.**

| Statement | Lean declaration | File |
|---|---|---|
| `∫_{t⁻¹Ω} F(tx) dx = t^{-d} ∫_Ω F`; `‖u(t·)‖² = t^{-d}‖u‖²` | `dilDom`, `setIntegral_comp_smul_dilDom`, `dilLp`, `norm_dilLp_sq` | `Sobolev/Scaling` |
| `(u, G) ↦ (u(t·), t G(t·))` preserves `W^{1,2}`; the Dirichlet energy scales by `t^{2−d}` | `dilate`, `dilate_mem_W12`, `norm_dilate_snd_sq` | `Sobolev/Scaling` |
| **scaling of weak solutions**: `-div(A∇(u(t·))) = t² f(t·)` for dilation-invariant `A` | `CoeffField.IsWeakSolution.dilate` | `Sobolev/Scaling` |
| `g⁻¹` is dilation invariant; cone balls dilate to cone balls; **scaled norms `‖u‖_{B(x,ρ)}` are dilation invariant** | `coneCoeffA_smul`, `dilDom_coneBall`, `scaledNormSq`, `scaledNormSq_dilate` | `Sobolev/Scaling` |
| Caccioppoli on `B(p,1) ⊂ B(p,2)` with a constant independent of `p` | `exists_caccioppoli_ball` | `Sobolev/Scaling` |
| **scaled Caccioppoli** (§2.5.1): `λ∫_{B(p,ρ)}|∇u|² ≤ ρ²∫_{B(p,2ρ)} f² + (1+4ΛΓ²)ρ⁻²∫_{B(p,2ρ)} u²` (by dilation from unit scale) | `exists_caccioppoli_ball_scaled` | `Sobolev/Scaling` |

**5. The spectral theorem for the Dirichlet problem** (the feasibility study turned into a proof:
Mathlib already has the spectral theorem for compact symmetric operators).

| Statement | Lean declaration | File |
|---|---|---|
| the solution operator `f ↦ u ∈ W^{1,2}_0(Ω)` is bounded linear; `G = fst ∘ solution` | `CoeffField.solution`, `.solutionL`, `.dirichletG` | `Sobolev/Spectral` |
| `G` is **compact**, **symmetric**, **positive** and **injective** | `.isCompactOperator_dirichletG`, `.isSymmetric_dirichletG`, `.inner_dirichletG_self_nonneg`, `.injective_dirichletG` | `Sobolev/Spectral` |
| **the eigenspaces of `G` span a dense subspace of `L²(Ω)`; nonzero eigenspaces are finite-dimensional** | `.dirichletG_eigenspaces_dense`, `.finiteDimensional_eigenspace_dirichletG` | `Sobolev/Spectral` |
| eigenvectors are **Dirichlet eigenfunctions** `-div(A∇u) = μ⁻¹ u`, `u ∈ W^{1,2}_0`, with `0 < μ ≤ 4R²/λ` | `.dirichletG_eigen` | `Sobolev/Spectral` |

**What is not claimed.**
- **Proposition 2.5 is not proved**, and nothing here uses the incorrect equalities of its arXiv
  proof (`PAPER_REVIEW.md` V9). The spectral theorem is an input to the localised Bochner argument
  (`PAPER_REVIEW.md` §C), whose obligations (i)–(v) remain open.
- The eigenvalues of `G` are not arranged into a sequence `λ_j → ∞` with an orthonormal basis.
  The statements are density of the span of the eigenspaces, finite multiplicity and the lower
  bound `λ/(4R²)`.
- The divergence identity is pointwise, for `C²` functions at regular points. The converse (a
  classical solution on the regular part that lies in `W^{1,2}` is a weak solution) is not
  formalised. It needs integration by parts against test functions supported in the regular set
  (`dense_testSubmodule_regular` reduces to those).
- The scaled Caccioppoli inequality is stated on **Euclidean** balls of the real coordinates, with
  arbitrary centre and radius. Geodesic balls are comparable (`coneBall_subset_closedBall`,
  `ball_subset_coneBall`), which gives the estimate between `B(p, ρ)` and `B(p, Kρ)` for a fixed
  `K = K(β)`, but the ratio `2` between geodesic balls is not proved. It would need cut-offs that
  are Lipschitz for `d_g`.
- The scaled Hessian estimate of §2.5.1 is not proved (it depends on Proposition 2.5).
- `𝒟₂` operators are not touched in this milestone. They remain coordinate operators, distinct
  from covariant Hessian components.

## Milestone 11: weak harmonic functions on the models (seventh review): COMPLETE

All entries are kernel-checked. Files `Real/D2Linear`, `Sobolev/Classical`,
`Sobolev/ExplicitHarmonic`, `Sobolev/Corollary35`, `Sobolev/Rotation`, `Sobolev/FourierModes`;
tests in `ConicalKahlerTest/WeakHarmonic` (model `C(S¹_{4π/3}) × ℝ`, `β = 2/3`).

**1. Classical and weak solutions.** `S = ⋃_a {r_a = 0}` is the singular set (`coneSingular`).

| Statement | Lean declaration | File |
|---|---|---|
| integration by parts `∫ u ∂_w φ = -∫ (∂_w u) φ` for `u ∈ C¹(U)`, `U` open, `supp φ ⊆ U` | `integral_mul_fderiv_eq_neg_of_contDiffOn` | `Sobolev/Classical` |
| **removability of `S` for `W^{1,2}`**: the weak-gradient identity against test functions supported in `Ω \ S` implies it on `Ω` (reuses `dense_testSubmodule_regular`) | `mem_W12_of_regular` | `Sobolev/Classical` |
| `u ∈ C¹(Ω \ S)`, `u, ∇u ∈ L²(Ω)` ⇒ `(u, ∇u) ∈ W^{1,2}(Ω)` | `classicalPair`, `classicalPair_mem_W12` | `Sobolev/Classical` |
| `∫ ⟨A∇u, ∇φ⟩ = -∫ div(A∇u) φ` for test functions off `S` | `dirichletForm_classicalPair_graph` | `Sobolev/Classical` |
| **classical ⇒ weak**, any coefficient field: flux `C¹` off `S` and `-div(A∇u) = f` there | `isWeakSolution_of_classical` | `Sobolev/Classical` |
| **weak ⇒ classical** for `u` with `C¹` flux off `S` and `f` continuous there (fundamental lemma) | `classical_of_isWeakSolution` | `Sobolev/Classical` |
| the flux `g⁻¹∇u` on `ℝ^d`; it is `C¹` off `S` for `u ∈ C²`; its divergence is `paperLaplacian` | `coneFlux`, `contDiffOn_coneFlux`, `divergence_coneFlux`, `divergence_coordIso` | `Sobolev/Classical` |
| **for the cone Laplacian**: `u ∈ C²(Ω \ S)`, `u, ∇u ∈ L²(Ω)`: `-Δu = f` classically on the regular part ⇔ `-div(g⁻¹∇u) = f` weakly on `Ω` | `cone_isWeakSolution_of_classical`, `cone_classical_of_isWeakSolution` | `Sobolev/Classical` |
| **energy uniqueness** (replaces the maximum principle of Lemma 3.2 in Lemma 3.3, `PAPER_REVIEW.md` S2) | `eq_of_isWeakSolution_of_sub_mem_H01`, `eq_zero_of_isWeakSolution_zero_of_mem_H01` | `Sobolev/Classical` |

**2. The explicit harmonic functions are weakly harmonic.**

| Statement | Lean declaration | File |
|---|---|---|
| locality and linearity of `pd`, `coneLaplacian`, `paperLaplacian`, `D2Op.apply` on `C²` germs; `pd = DU(e_k)`, `pd∘pd = D²U(e_k, e_l)`; smoothness of `toModel` | `pd_congr`, `D2Op.apply_congr`, `pd_eq_fderiv`, `pd_pd_eq_fderiv`, `D2Op.apply_add`, `paperLaplacian_sum`, `PolarPoint.contDiff_toModel` | `Real/D2Linear` |
| `Δ(r_b²) = 4`, `Δ(s_i s_j) = 2δ_ij` (paper's normalisation); `r^{k/β} sin kθ` harmonic | `paperLaplacian_r_sq`, `paperLaplacian_s_mul`, `paperLaplacian_harmonicSin` | `Real/D2Linear` |
| homogeneous functions: `Df(tw) = t^{γ-1} Df(w)` and `|Df(w)| ≤ M |w|^{γ-1}` | `fderiv_smul_of_homogeneous`, `exists_norm_fderiv_le_of_homogeneous` | `Sobolev/ExplicitHarmonic` |
| `r^{k/b} cos kθ = |w|^{k/b-k} Re(w^k)` in the real coordinate `w`: polar form, homogeneity, smoothness off `0`, bound | `harmCosC`, `harmSinC`, `harmCosC_polarMap`, `harmCosC_smul`, `abs_harmCosC_le` | `Sobolev/ExplicitHarmonic` |
| `IsClassicalHarmonic β P`: `C²` and harmonic on the regular part, bounded with bounded gradient on bounded sets; a subspace | `IsClassicalHarmonic`, `classicalHarmonic` | `Sobolev/ExplicitHarmonic` |
| **every `IsClassicalHarmonic` function is weakly harmonic on every bounded open `Ω`**, which may meet `S` | `IsClassicalHarmonic.isWeakSolution` (with `memLp`, `memLp_gradient`) | `Sobolev/ExplicitHarmonic` |
| members: constants, `s_i`, `r_a^{k/β_a} cos kθ_a`, `r_a^{k/β_a} sin kθ_a` (for `β_a ≤ k`), `∑ c_a r_a² + ∑ Q_{ij} s_i s_j` with `2∑c_a + tr Q = 0` | `isClassicalHarmonic_const`, `_eucl`, `_harmCos`, `_harmSin`, `_quadFn` | `Sobolev/ExplicitHarmonic` |

**3. The paper's list of `𝓗_{≤2}` and Corollary 3.5.**

| Statement | Lean declaration | File |
|---|---|---|
| the span of the paper's list (Prop. 3.4): `1`, `s_i`, `r_a^{1/β_a} cos θ_a`, `r_a^{1/β_a} sin θ_a` (`β_a ≥ 1/2`), `𝓗_2(ℝ^{m−2n})`, `r_a² − r_b²`, `r_a² − 2s_i²` | `h2Generators`, `explicitH2`, `quadS_mem_explicitH2`, `rsq_sub_rsq_mem_explicitH2`, `rsq_sub_two_ssq_mem_explicitH2` | `Sobolev/Corollary35` |
| finite-dimensional; weakly harmonic on bounded open sets (`β_a ≤ 1`) | `finiteDimensional_explicitH2`, `isWeakSolution_of_mem_explicitH2` | `Sobolev/Corollary35` |
| **Corollary 3.5 (constancy)**: `D P` is constant on the regular part for all `D ∈ 𝒟₂` | `corollary_3_5_const` | `Sobolev/Corollary35` |
| **Corollary 3.5 (eq. (3.3))**: `|τ| ≤ C ‖P‖_{L²(B_1)}` with `C = C(D, β)` (`β_a ≤ 1`) | `corollary_3_5` | `Sobolev/Corollary35` |

**4. Rotations and Fourier modes in the angles `θ_a`.**

| Statement | Lean declaration | File |
|---|---|---|
| linear isometries `L` of `ℝ^d` transport `L²`, `W^{1,2}`, `W^{1,2}_0` (`∇(u∘L) = L⁻¹(∇u∘L)`) and the weak solutions of `L`-equivariant coefficient fields | `isoLp`, `isoPair`, `isoPair_mem_W12`, `isoPair_mem_H01`, `CoeffField.IsWeakSolution.isoPair` | `Sobolev/Rotation` |
| the rotations `θ_a ↦ θ_a + t` (`coneRot`, `rotE`); **`g⁻¹` is equivariant**; vertex balls are invariant | `coneInvOp_coneRot`, `coneCoeffA_rotE`, `rotE_preimage_ball` | `Sobolev/Rotation` |
| rotations map weak solutions to weak solutions; **symmetric Dirichlet problem**: invariant `Ω`, `f` ⇒ invariant solution | `cone_isWeakSolution_rot`, `cone_dirichlet_rot_invariant`, `cone_dirichlet_rot_invariant_ae` | `Sobolev/Rotation` |
| the Dirichlet operator `G` commutes with the rotations; its eigenspaces are invariant | `dirichletG_isoLp`, `isoLp_mem_eigenspace_dirichletG` | `Sobolev/Rotation` |
| the rotations act **continuously** on `L²(Ω)` and on pairs (Mathlib `Lp.compMeasurePreserving_continuous`) | `rotLp`, `rotPair`, `continuous_rotLp`, `continuous_rotPair` | `Sobolev/FourierModes` |
| **the Fourier modes `C_k u = ∫_0^{2π} cos(kt) u∘R_t`, `S_k u` of a weak solution are weak solutions** (with the modes of `f`); modes of weakly harmonic functions are weakly harmonic | `cosCoeff`, `sinCoeff`, `isWeakSolution_angMode`, `isWeakSolution_cosMode`, `isWeakSolution_zero_angMode` | `Sobolev/FourierModes` |
| **the modes transform like `cos kθ`, `sin kθ`**: `C_k u ∘ R_s = cos(ks) C_k u + sin(ks) S_k u` | `rotLp_cosCoeff`, `rotLp_sinCoeff` | `Sobolev/FourierModes` |
| **Fourier uniqueness**: `u` is determined by its modes (Mathlib's Parseval identity on `[0, 2π]`) | `eq_zero_of_fourier_real`, `eq_zero_of_modes_eq_zero`, `eq_zero_of_harmonic_modes_eq_zero` | `Sobolev/FourierModes` |

**What is not claimed.**
- **Proposition 3.4 (completeness) is not proved.** `explicitH2` is the span of the paper's list;
  that it contains every homogeneous harmonic function of degree `≤ 2`, and that there is none of
  degree in `(2, 2 + μ)`, remains open. Corollary 3.5 is proved for `explicitH2`, so it becomes
  the paper's Corollary 3.5 once completeness is known.
- **Lemma 3.3 is not proved.** Its uniqueness step is now available in energy form, and the
  decomposition of weak solutions into Fourier modes in one angle `θ_a` is proved. Still missing:
  the radial/spherical part (the link eigenfunctions, Lemma 3.1) and the convergence of the
  expansion. The Fourier modes are not shown to be orthogonal or to sum to `u` in `L²`; what is
  proved is that `u` is determined by them.
- **Interior regularity off `S` is not proved.** `cone_classical_of_isWeakSolution` assumes that
  `u` is `C²` off `S`; there is no Weyl lemma or Schauder theory for weak solutions yet.
- The weak harmonicity of `r^{k/β} cos kθ` is proved for `β ≤ k` (bounded gradient); this covers the
  paper's range `β < 1` for all `k ≥ 1`.
- Corollary 3.5's bound uses Lebesgue measure on `B_1`; `dV_g = (∏β_a) dx` changes only `C`.

(Lemma 3.3 was proved in Milestone 12, below.)

## Milestone 12: the link and Lemma 3.3: COMPLETE (Fourier-mode convergence deferred)

All entries are kernel-checked. Files `Sobolev/Polar`, `Sobolev/FormSpectral`, `Sobolev/Link`,
`Sobolev/LinkSpectral`, `Sobolev/Homogeneous`, `Sobolev/Expansion`, `Sobolev/HarmonicExpansion`,
`Sobolev/ConeLink`; tests in `ConicalKahlerTest/LinkExpansion` (model `C(S¹_{4π/3}) × ℝ`).

The results are proved for an arbitrary **conical** coefficient field on `ℝ^d`
(`CoeffField.IsConical`: `A(tx) = A(x)` for `t > 0` and `A(x) x = x`), then specialised to the
cone Laplacian `A = g⁻¹` (`coneCoeff_isConical`). The link is the unit sphere `S^{d−1}` with the
metric induced by `g`. Its functions are realised as functions on the Euclidean sphere, with the
surface measure `σ` (`sphMeasure`); see "Decisions" below.

**1. Polar coordinates and homogeneous extensions.**

| Statement | Lean declaration | File |
|---|---|---|
| polar coordinates `∫_{ℝ^d} g = ∫_S ∫_0^∞ r^{d−1} g(rw) dr dσ(w)`, for integrals, lintegrals, integrability, both orders (Mathlib `homeomorphUnitSphereProd`) | `integral_polar`, `lintegral_polar`, `integrable_polar_iff`, `integral_polar_iter`, `integral_polar_iter_symm` | `Sobolev/Polar` |
| the radial projection `x ↦ x/|x|` is quasi-measure-preserving; `σ`-null sets ⇔ cone-null sets | `sphProj`, `quasiMeasurePreserving_sphProj`, `ae_of_ae_sphere`, `ae_sphere_of_ae` | `Sobolev/Polar` |
| homogeneous extension `|x|^k Ψ(x/|x|)`: `L²` on shells (and balls when `2k + d > 0`), as a CLM `L²(S) → L²(shell)` | `homFun`, `memLp_homFun`, `homL`, `memLp_homFun_ball` | `Sobolev/Polar`, `Sobolev/Expansion` |

**2. Lemma 3.1 (spectral decomposition on the link).**

| Statement | Lean declaration | File |
|---|---|---|
| abstract spectral theorem for a coercive symmetric form `b` on `V ↪ H` with compact dense embedding: `K = (B⁻¹)ᵀ` compact, symmetric, injective; Hilbert basis of eigenvectors | `formSol`, `formK`, `isCompactOperator_formK`, `isSymmetric_formK`, `injective_formK`, `formK_eigen`, `exists_hilbertBasis_eigenvectors` | `Sobolev/FormSpectral` |
| conical fields: `A` restricted to `S` gives a bounded, symmetric, coercive multiplication operator on `L²(S; ℝ^d)` | `CoeffField.IsConical`, `CoeffField.sphMulOp`, `inner_sphMulOp_comm`, `lam_mul_norm_sq_le_sphMulOp` | `Sobolev/Link` |
| **link Sobolev space** `W^{1,2}(S)`: pairs `(φ, Γ) ∈ L²(S) × L²(S; ℝ^d)` with `|x|^{-1}Γ(x̂)` the weak gradient of `φ(x̂)` on every shell; closed | `LinkPair`, `linkW12`, `mem_linkW12`, `isClosed_linkW12` | `Sobolev/Link` |
| the link form `∫_S ⟨AΓ, Θ⟩ + ∫_S φψ` is coercive | `linkForm`, `linkForm₀`, `isCoercive_linkForm₀` | `Sobolev/Link` |
| **Rellich on the link**: `W^{1,2}(S) → L²(S)` is compact (via Rellich on the shell `{1 < |x| < 4}` and a radial cut-off) | `isCompactOperator_linkFst` | `Sobolev/Link` |
| **density**: smooth functions restricted to `S` are dense in `L²(S)` (Stone–Weierstrass); their tangential gradients give link pairs | `tangGrad`, `smoothLinkPair_mem`, `denseRange_linkFst` | `Sobolev/LinkSpectral` |
| link eigenfunctions `-Δ_ḡ φ = λφ` (weak form); `λ ≥ 0`; constants have `λ = 0` | `IsLinkEigen`, `IsLinkEigen.nonneg`, `linkEigen_const` | `Sobolev/LinkSpectral` |
| **Lemma 3.1**: a Hilbert basis `{φ_i}` of `L²(S)` of link eigenfunctions, `λ_i ≥ 0`, finitely many below any `Λ` | `link_spectral`, `cone_link_spectral` | `Sobolev/LinkSpectral`, `Sobolev/ConeLink` |

**3. Homogeneous harmonic functions (§3.2, indicial roots).**

| Statement | Lean declaration | File |
|---|---|---|
| the tangential part of a link gradient: `⟨Γ(w), w⟩ = 0` for `σ`-a.e. `w` | `ae_inner_linkSnd_eq_zero` | `Sobolev/Homogeneous` |
| radial averages of test functions are smooth; integration by parts along rays | `radAvg`, `contDiff_radAvg`, `integral_ray_deriv` | `Sobolev/Homogeneous` |
| `P = |x|^δ φ(x̂)` has weak gradient `|x|^{δ−1}(δφ(x̂)x̂ + Γ(x̂))` off `0` (product rule) | `homP`, `homG`, `homP_integral` | `Sobolev/Homogeneous` |
| **`(φ, Γ)` link eigenfunction with `λ = δ(δ + d − 2)` ⇒ `ρ^δ φ` weakly harmonic on `ℝ^d \ {0}`** | `homogeneous_harmonic`, `cone_homogeneous_harmonic` | `Sobolev/Homogeneous`, `Sobolev/ConeLink` |
| **vertex removability** (`d ≥ 2`): `W^{1,2}` and weak harmonicity extend across `{0}` | `mem_W12_of_punctured`, `isWeakSolution_of_punctured` | `Sobolev/Expansion` |
| `ρ^δ φ ∈ W^{1,2}(B_R)` and is weakly harmonic on `B_R` (`δ ≥ 0`, `d ≥ 2`) | `homPair`, `homPair_mem_W12`, `homPair_isWeakSolution` | `Sobolev/Expansion` |
| the nonnegative indicial root `δ = (−(d−2) + √((d−2)² + 4λ))/2` | `indicialRoot`, `indicialRoot_nonneg`, `indicialRoot_spec` | `Sobolev/HarmonicExpansion` |

**4. Lemma 3.3 (expansion of harmonic functions).**

| Statement | Lean declaration | File |
|---|---|---|
| products with test functions stay in `W^{1,2}_0`; **Wronskian identity** `∫ P⟨A∇u, ∇η⟩ = ∫ u⟨A∇P, ∇η⟩` for weakly harmonic `u, P` | `exists_smulPair_mem_H01`, `wronskian` | `Sobolev/Expansion` |
| radial test functions `F(|x|)` with `F' = f`, and the field `f(|x|) x̂`; `div` formula | `radPrim`, `radField`, `isTestFn_radField`, `div_radField` | `Sobolev/Expansion` |
| **key identity** `∫_{B_1} u P (f'(|x|) + (2δ + d − 1) f(|x|)/|x|) = 0` | `key_identity` | `Sobolev/Expansion` |
| ray coefficients `u_φ(r) = ∫_S u(rw) φ(w) dσ`; du Bois-Reymond lemma on `(0, 1)` | `rayCoeff`, `ae_eq_const_of_integral_mul_deriv_eq_zero` | `Sobolev/HarmonicExpansion` |
| **radial ODE**: `u_φ(r) = C r^δ` for a.e. `r ∈ (0, 1)` | `rayCoeff_eq` | `Sobolev/HarmonicExpansion` |
| Parseval on each sphere and `∫_{B_1} u² = ∑_i ∫_0^1 r^{d−1} u_{φ_i}(r)² dr` | `lintegral_slice_eq_tsum`, `lintegral_ball_eq_tsum` | `Sobolev/HarmonicExpansion` |
| `∫_{B_1} ρ^δ φ ρ^{δ'} ψ = ⟪φ, ψ⟫/(δ + δ' + d)`; a Parseval criterion for orthogonal series | `integral_ball_homP_mul_homP`, `integral_ball_mul_homP_of_rayCoeff`, `hasSum_of_parseval` | `Sobolev/HarmonicExpansion` |
| **Lemma 3.3**: weakly harmonic `u ∈ W^{1,2}(B_1)` (`d ≥ 2`, conical `A`) is `u = ∑_i a_i ρ^{δ_i} φ_i` in `L²(B_1)` (unconditional `HasSum`); each term weakly harmonic, `δ_i ≥ 0`, `λ_i = δ_i(δ_i + d − 2)`, mutually orthogonal | `expansion`, `cone_expansion` | `Sobolev/HarmonicExpansion`, `Sobolev/ConeLink` |
| the cone Laplacian is conical: `g⁻¹(tx) = g⁻¹(x)`, `g⁻¹(x) x = x` | `coneCoeffA_self`, `coneCoeff_isConical` | `Sobolev/ConeLink` |

The proof of Lemma 3.3 does **not** use the maximum principle (Lemma 3.2); see `PAPER_REVIEW.md`
S2. Separation of variables is done in weak form. The Wronskian identity with `P = ρ^δ φ` is
tested against radial functions `η = F(|x|)` that vanish near `|x| = 1` but are only *constant*
near the vertex, so the equation for `u` across the vertex is used. This gives
`∫_0^1 r^{−δ} u_φ(r) k'(r) dr = 0` for all test functions `k` on `(0, 1)`, so `r^{−δ}u_φ` is
constant (du Bois-Reymond). The second root `r^{2−d−δ}` never appears, because the Wronskian with
`r^δ` is first order. The coefficients and convergence then follow from Parseval on each sphere.

**What is not claimed.**
- **Orthogonality and `L²` convergence of the Fourier modes in `θ_a`** (Milestone 11) are not
  proved. They are no longer needed for Lemma 3.3, which is proved by expanding in link
  eigenfunctions directly.
- **Multiplicity one of `λ = 0`** (connectedness of the link, `PAPER_REVIEW.md` S6) is not proved.
  Lemma 3.3 does not need it.
- **Proposition 3.4 (completeness of `𝓗_{≤2+α}`) is not proved.** Lemma 3.3 reduces it to the
  identification of the link eigenfunctions with `λ ≤ (2 + μ)(2 + μ + d − 2)`. That needs the
  separation of variables on the join `S¹_{β_1} * ⋯ * S^{k−1}`, which is not formalised.
- The eigenvalues are indexed by the Hilbert basis set `s ⊆ L²(S)`, not by `ℕ` in increasing
  order. "Finitely many below any `Λ`" is the content of `λ_i → ∞`.
- Lemma 3.3 is stated on the unit ball `B_1` with Lebesgue measure. Other radii follow by the
  scaling of Milestone 10, which is not restated here. Convergence in `W^{1,2}` and locally uniform
  convergence are not proved.
- `d ≥ 2` is assumed for vertex removability. The paper's models have `d = 2n + k ≥ 2`, except
  `ℝ¹`.

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
* **The Laplacian is upstream's.** `laplaceBeltrami ω₀ f` abbreviates
  `CalabiYau.Riemannian.ΔG ω₀.toRiemannianMetric f` (divergence of the Riemannian gradient, for
  bundled smooth functions). This adds a dependency on upstream's
  `CalabiYau.Geometry.Kahler.Riemannian.Laplacian`, which takes about 4 minutes to build from
  source. `restrictSmooth U hf` bundles a function smooth on `U ⊆ ℂⁿ`.
* **Partial derivatives in polar or cone coordinates** are one-variable `deriv`s of slices,
  for example `deriv (fun s => f (coordSlice j w (polarMap (s ^ β⁻¹, θ)))) ρ`.
* **Holomorphic inputs** are stated as `ContDiffOn ℂ ∞ P U`. Mathlib's "holomorphic ⇒ smooth" is
  only available in one variable.
* **Transport of forms** along an equality of open sets (`kahlerCast`) is used to compare
  `KahlerForm n D.complement` with `KahlerForm n D.toSNC.complement`. The two open sets are
  equal but not definitionally so.

* **Real models (Milestone 8).**
  - `RealConeModel κ ι := EuclideanSpace ℝ ((Fin 2 × κ) ⊕ ι)`. Cone factors are indexed by an
    arbitrary finite type `κ`, so the Kähler bridge can use the subtype of cone directions. The
    paper's case is `κ = Fin n`, `ι = Fin (m − 2n)`.
  - `ConeTwo β` and `ConeProduct β ι` are type synonyms of `ℂ` and `RealConeModel κ ι`. They carry
    the cone distance without a diamond with the Euclidean metric. `ConeProduct` gets its metric by
    `MetricSpace.induced` from `PiLp 2` of the factors.
* **The cone distance is defined by a formula**, `hingeDist |p| |q| (min(β ∠(p,q), π))`, where `∠`
  is Mathlib's unoriented angle `InnerProductGeometry.angle`. Its triangle inequality uses
  Mathlib's `angle_le_angle_add_angle`. Identification with the length distance is an outstanding
  obligation.
* **The paper's metric on one factor** is `paperConeMetric β w v = (Re(w̄v)² + β² Im(w̄v)²)/|w|²`.
  At `w = 0` it takes the junk value `0`, so statements are made on the regular part. The Gram
  matrix is defined entrywise as `g(e_k, e_l)`, and the Riemannian volume as Lebesgue measure with
  density `√det g`. The singular set is null, so the junk values do not matter.
* **`𝒟₂` follows the paper's definition**: pure conical operators only for `β_a < 1/2`. The
  introduction's "`β_a > 1/2`" is not followed (`PAPER_REVIEW.md` V5). `∂²/∂x∂y` means
  `∂_x(∂_y ·)`.
* **Smooth directions of the Kähler model** become two Euclidean real coordinates in
  `ConeWeights.realChart`, not cones of angle `2π`. At `w = 0` the formula `paperConeMetric 1` is
  degenerate.

* **Sobolev spaces as Hilbert spaces of pairs (Milestone 9).** `W^{1,2}(Ω)` and `W^{1,2}_0(Ω)`
  are subspaces of `L2Pair μ Ω = L²(Ω) × L²(Ω; F)`: pairs `(u, G)` with `G` the weak gradient of
  `u`, respectively the closure of the graphs `(φ, ∇φ)` of test functions. This gives completeness
  and Lax–Milgram directly. Upstream's predicates `MemW1p`, `MemW01p` are used through a bridge
  (`cutPair_mem_H01`) where their mollification lemma is needed.
* **Test functions** are smooth with compact support (upstream's convention), not Lipschitz as in
  the paper (see "What is not claimed" under Milestone 9).
* **Coefficients** (`CoeffField`) are operator fields `A : F → (F →L[ℝ] F)`, symmetric, with
  measurable matrix coefficients and the bounds `λ, Λ` almost everywhere. For the cone the bounds
  fail only on the null singular set.
* **Friedrichs–Poincaré with a centre (Milestone 10).** `norm_graph_fst_le`,
  `norm_fst_le_of_mem_H01`, `norm_sq_le_of_mem_H01`, `isCoercive_dirichletForm₀`,
  `existsUnique_H01_isWeakSolution` and `cone_existsUnique_H01` now take `Ω ⊆ B̄(x₀, R)` with an
  implicit centre. Existing calls with `B̄(0, R)` are unchanged.
* **Lemma 2.4 by harmonic replacement (Milestone 10).** The main statement uses the direct argument
  (Lax–Milgram plus the energy estimate), which gives an explicit `δ` that is uniform in the centre.
  The paper's compactness argument is also formalised, as a separate theorem.
* **Divergence** is defined classically as `∑_k ∂_k V_k`, using one-variable partial derivatives of
  components (`divergence`). It does not use the trace of a Fréchet derivative of the operator
  field `g⁻¹`, which is not differentiable at the singular set.
* **Dilations** act on the domain by preimage (`dilDom t Ω = {x | t x ∈ Ω}`), not by pointwise
  scaling of sets.
* **The intrinsic norm** `intrinsicNormSq` uses only the existing `productConeMetric`,
  `coneInvOp` and `productConeVolume`, transported by `coordIso`. No new metric is introduced.
* **`set_option linter.unusedSectionVars false`** is set in the `Sobolev/` files. Many small lemmas
  share one typeclass context, and not every lemma uses all of it. It disables a style lint only.

* **Classical solutions (Milestone 11).** `classicalPair hu hg = (u, ∇u)` uses the classical
  gradient `gradient u`, which takes junk values on the null set `S`. Classical hypotheses are
  stated on `Ω \ S` in the coordinates of `ℝ^d`, and the Laplacian condition in polar coordinates
  (`paperLaplacian`) at all regular polar points `c` with `coordIso e c.toModel ∈ Ω`.
* **`IsClassicalHarmonic`** asks for `C²` on the regular part, measurability, and bounds for `P` and
  `DP` on bounded sets. It is a sufficient condition for weak harmonicity designed for the explicit
  functions; it is not a definition of harmonicity.
* **The paper's list of `𝓗_{≤2}`** (`explicitH2`) is a span of explicit functions on the real model.
  Item 3 is encoded as the quadratics `∑ c_a r_a² + ∑ Q_{ij} s_i s_j` with `2∑c_a + tr Q = 0`, whose
  span equals that of `𝓗_2(ℝ^{m−2n})`, `r_a² − r_b²`, `r_a² − 2s_i²` (the latter three are proved
  members).
* **Rotations** act by `u ↦ u ∘ R_t` on `L²(Ω)` (`isoLp`), for domains with `R_t⁻¹(Ω) = Ω`. Fourier
  modes are `L²`-valued interval integrals over `[0, 2π]` (Bochner), without normalising factors.

* **The link (Milestone 12).** The link of the cone is realised as the Euclidean unit sphere
  `S^{d−1} ⊆ ℝ^d` with Mathlib's surface measure `σ` (`sphMeasure d = volume.toSphere`), not as a
  Riemannian manifold. The link metric `ḡ` enters only through the restriction of `A = g⁻¹` to
  `S`. For the cone, `dV_ḡ` and `σ` differ by the constant `∏β_a`, so eigenfunctions and
  eigenvalues are unchanged.
* **Link Sobolev space by homogeneous extension.** `W^{1,2}(S)` (`linkW12`) is not defined via
  charts on `S`. A pair `(φ, Γ)` is in it when `(φ(x̂), |x|^{−1}Γ(x̂))` lies in `W^{1,2}` of every
  shell `{1/(n+1) < |x| < n+1}`. `Γ` plays the role of the tangential gradient, and is proved
  tangential (`ae_inner_linkSnd_eq_zero`). `linkW12` is marked `irreducible`, because unfolding the
  `iInf` makes elaboration very slow.
* **Conical coefficient fields** (`CoeffField.IsConical`): `A(tx) = A(x)` for `t > 0` and
  `A(x) x = x`. The second condition says that the radial vector is `g`-orthogonal to the link and
  `g`-unit; it makes the Laplacian split as `∂_r² + (d−1)/r ∂_r + r^{−2}Δ_ḡ`. Lemmas 3.1 and 3.3 are
  proved for this class.
* **Lemma 3.3's output** is a `HasSum` in `L²(B_1)` over the Hilbert-basis index set (unconditional
  convergence). Each `P_i` is given as an `L²` class together with a weak solution `Q` with
  `Q.fst = P_i` and the formula `P_i = ρ^{δ_i} φ_i` almost everywhere.

Supporting lemmas re-proved locally because the upstream versions are `private`:
`ConicalKahler.ddbar_congr` (upstream `KahlerForm.ddbar_eq_of_eventuallyEq`) and
`ConicalKahler.mddbar_opens` (upstream `KahlerForm.mddbar_restrict_open`).

## Outstanding proof obligations

Done since the first review: agreement with `metricInChart` (Milestone 4), `Divisors/SNC`
(Milestone 5), SNC chart invariance for `β_i ≤ 1` (Milestone 6), the Laplacian (Milestone 7), and
the real cone geometry with `𝒟₂` (Milestone 8), Sobolev spaces and weak solutions
(Milestone 9), compactness, harmonic approximation, scaling and the Dirichlet spectral
theorem (Milestone 10), and weak harmonic functions on the models with Corollary 3.5 for the
paper's list (Milestone 11), and the link spectral theory with Lemma 3.3 (Milestone 12).

1. **General restriction and transport of Kähler forms** to open subsets (`KahlerForm n M →
   KahlerForm n U`), and restriction of `ConeKahlerForm` to neighbourhoods. The model has this via
   `modelConeFormOn`. Transport along *equal* open sets is `kahlerCast`.
2. **Cone-admissible atlases when some angle exceeds `2π`** (spec §4.1), for smooth and SNC
   divisors: a `ConeAdmissibleChartChange` interface with bounded weighted Jacobians, and
   invariance within such an atlas. The invariance theorem of Milestone 6 needs *all* `β_i ≤ 1`.
   With a single `β_i > 1` it fails for arbitrary charts (shear counterexample).
3. **Stronger regularity** (spec §3.5): `IsAsymptoticCone`, weighted Hölder, conormal and
   polyhomogeneous interfaces. None of these is implied by `IsConeAlong`. Milestone 3 gives a form
   with `IsConeAlong` that is not Ricci-flat. The plan for the Schauder estimates of de
   Borbon–Edwards, including the function spaces they use, is in `ROADMAP.md` §5.
4. **The cone distance as a length distance.** Milestone 8 constructs the cone (with its vertex)
   as a metric space in the paper's real coordinates (`ConeTwo`, `ConeProduct`), with a formally
   defined distance. Still missing:
   - that this distance is the infimum of `g`-lengths of curves;
   - minimality of radial segments (their length equals the distance, `coneDist_radial`);
   - the identification with the metric completion of `(ℂ \ {0}, g_β)`.
5. **Bridge** `smoothDivisor_of_regularHolomorphicSection` (holomorphic implicit function theorem).
6. **Schauder theory** (`ROADMAP.md`). Done: the real models, the formal cone distance, `dV_g`
   and `𝒟₂` (Milestone 8); `W^{1,2}`, `W^{1,2}_0`, weak solutions, Friedrichs–Poincaré,
   existence and uniqueness, Caccioppoli and density (Milestone 9); Rellich, Lemma 2.4 (uniform in
   the centre), scaling, the bridges with `g`, `dV_g` and `paperLaplacian`, and the Dirichlet
   spectral theorem (Milestone 10); classical ⇔ weak solutions, the explicit harmonic functions,
   Corollary 3.5 for the paper's list, energy uniqueness, rotations and Fourier modes in `θ_a`
   (Milestone 11); polar coordinates, the link Sobolev space and Lemma 3.1, homogeneous harmonic
   functions, vertex removability and Lemma 3.3 (Milestone 12). Next: the completeness of
   `𝓗_{≤2+α}` (Prop. 3.4) by separation of variables on the join link, the `L²` Hessian bound (by
   the localised Bochner argument, `PAPER_REVIEW.md` §C), and the Campanato iteration.
   Smaller items:
   - interior regularity of weak solutions off `S` (Weyl lemma / Schauder for weak solutions);
   - orthogonality and `L²` convergence of the Fourier modes in `θ_a` (Parseval for `u`); not
     needed for Lemma 3.3 any more;
   - multiplicity one of the link eigenvalue `0` (connectedness of the link);
   - Caccioppoli with cut-offs that are Lipschitz for `d_g`, which gives the ratio `2` between
     geodesic balls;
   - eigenvalues of `G` as a sequence, with an orthonormal basis of eigenfunctions.
7. **Smaller items from Milestone 8.**
   - Full `γ`-Hölder continuity of `r^γ cos θ` for the cone distance (only the estimate at the
     vertex is proved).
   - The Laplacian normalisation for products, restated in real coordinates.
   - `fderiv` of `ConeWeights.realChart` as a whole.

## Blockers

None blocking. Technical notes:

* In this Mathlib, `ContinuousAt.norm` does not elaborate for maps into the nested space
  `E →L[ℂ] (E →L[ℂ] E)`. The norm-instance unification fails (reproduced outside the module
  system). `Analysis/HyperplaneMaps` therefore gets its second-order bounds from
  `ContDiffAt.exists_lipschitzOnWith` applied to `fderiv`, instead of bounding the norm of the
  second derivative.
* `ω` cannot be used as a variable name in files that `open scoped ContDiff` (it is analyticity
  notation). Kähler forms are named `ω₀`, as upstream does.
* Instance search for `SecondCountableTopology (Lp ℝ 2 (sphMeasure d))` exceeds the default
  `maxSize` of 128, so the separability of `L²(S)` is built by hand (`separableSpace_sph`).
