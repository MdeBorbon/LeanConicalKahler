# STATUS

Last updated: 2026-11-05.

Pins: Lean `v4.34.1`, Mathlib `v4.34.1` (`d13f23b7`), `calabiyau` at
`91b1ddf000c7028bc42ae6102eba0e2042eb37ff`. Upstream is used unmodified.

Every completed result below is kernel-checked. `scripts/AxiomAudit.lean` confirms that all 1137
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

Supporting lemmas re-proved locally because the upstream versions are `private`:
`ConicalKahler.ddbar_congr` (upstream `KahlerForm.ddbar_eq_of_eventuallyEq`) and
`ConicalKahler.mddbar_opens` (upstream `KahlerForm.mddbar_restrict_open`).

## Outstanding proof obligations

Done since the first review: agreement with `metricInChart` (Milestone 4), `Divisors/SNC`
(Milestone 5), SNC chart invariance for `β_i ≤ 1` (Milestone 6), the Laplacian (Milestone 7), and
the real cone geometry with `𝒟₂` (Milestone 8).

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
   and `𝒟₂` (Milestone 8). Next (Milestone 9): Sobolev spaces `W^{1,2}` on the real models, weak
   solutions of `Δu = f` and the first elliptic estimates. Then: completeness of `𝓗_{≤2+α}`, the
   `L²` Hessian bound, and the Campanato iteration.
7. **Smaller items from Milestone 8.**
   - Full `γ`-Hölder continuity of `r^γ cos θ` for the cone distance (only the estimate at the
     vertex is proved).
   - The rest of Corollary 3.5 (`D P` constant for the remaining functions of `𝓗_{≤2}`).
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
