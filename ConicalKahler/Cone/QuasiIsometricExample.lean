module

public import ConicalKahler.Cone.Separable
public import ConicalKahler.Cone.Kahler
public import ConicalKahler.Cone.Standard

/-!
# The quasi-isometric cone condition does not imply the model geometry

`ConicalKahler.Cone.FlatCone` shows that the model `ω_β` is *exactly* a flat cone of angle `2πβ`
transversally, and the model is Ricci-flat (`modelConeForm_ricciFlat`). The cone condition
`IsConeAlong` is much weaker: it only asks for two-sided bounds against the model. This file gives
an explicit Kähler form on `ℂⁿ \ {z_0 = 0}` that satisfies `IsConeAlong (coordHyperplane n) β` for
every `β > 0` but is **not** Ricci-flat, so it is not locally isometric to the model.

The example is

  `ω = i∂∂̄ (|z_0|^(2β) + |z_0|^(4β) + ∑_{j ≥ 1} |z_j|²)`,

the pullback of `i∂∂̄(|w|² + |w|⁴)` by the developing coordinate `w = z_0^β`. Its transverse
coefficient is `β² |z_0|^(2β-2) (1 + 4|z_0|^(2β))` (`perturbedConeSeparable_weight_zero`), between
`1` and `5` times the model on `|z_0| < 1`. Its Ricci form has

  `Ric_{00̄} = -4β² |z_0|^(2β-2) / (1 + 4|z_0|^(2β))² < 0`

(`perturbedConeForm_ricciForm_coeffMatrix_zero`). The ratio to the model tends to `1` at the
divisor, so this metric would even satisfy a leading-order asymptotic cone condition (spec §3.5,
not formalised here). This shows that exact model geometry is strictly stronger than the asymptotic
condition, which in turn is stronger than quasi-isometry.

## Main results

* `perturbedConeForm β : KahlerForm n (coordHyperplane n).complement`.
* `perturbedConeForm_isConeAlong`: it has quasi-isometric cone angle `2πβ` (with `C = 5`).
* `perturbedConeForm_not_ricciFlat`, `perturbedConeKahlerForm_not_isKahlerEinstein_zero`.
* `exists_isConeAlong_not_ricciFlat`: `IsConeAlong` does not imply Ricci-flatness.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set Filter ContinuousAlternatingMap

namespace ConicalKahler

variable {n : ℕ} [NeZero n] (β : ConeAngle)

/-- The profiles of `|z_0|^(2β) + |z_0|^(4β) + ∑_{j ≥ 1} |z_j|²`. -/
noncomputable def perturbedConeProfile (j : Fin n) : ℝ → ℝ :=
  if j = 0 then fun s => s ^ β.beta + s ^ (2 * β.beta) else fun s => s

theorem perturbedConeProfile_zero :
    perturbedConeProfile (n := n) β 0 = fun s => s ^ β.beta + s ^ (2 * β.beta) := by
  simp [perturbedConeProfile]

theorem perturbedConeProfile_of_ne {j : Fin n} (hj : j ≠ 0) :
    perturbedConeProfile β j = fun s => s := by
  simp [perturbedConeProfile, hj]

theorem radialCoeff_perturbedConeProfile_zero {s : ℝ} (hs : 0 < s) :
    radialCoeff (perturbedConeProfile (n := n) β 0) s =
      β.beta ^ 2 * s ^ (β.beta - 1) * (1 + 4 * s ^ β.beta) := by
  rw [perturbedConeProfile_zero, radialCoeff_rpow_add_rpow_two_mul hs]

theorem radialCoeff_perturbedConeProfile_of_ne {j : Fin n} (hj : j ≠ 0) (s : ℝ) :
    radialCoeff (perturbedConeProfile β j) s = 1 := by
  rw [perturbedConeProfile_of_ne β hj, radialCoeff_id]

/-- The profiles define a Kähler form on `{z_0 ≠ 0}`. -/
noncomputable def perturbedConeSeparable : SeparableProfile n (coordHyperplane n).complement where
  g := perturbedConeProfile β
  smooth z hz j := by
    by_cases hj : j = 0
    · subst hj
      have hs : coordNormSq 0 z ≠ 0 := (coordNormSq_pos (z := z) (j := 0) hz).ne'
      rw [perturbedConeProfile_zero]
      exact (Real.contDiffAt_rpow_const_of_ne hs).add (Real.contDiffAt_rpow_const_of_ne hs)
    · rw [perturbedConeProfile_of_ne β hj]
      exact contDiffAt_id
  pos z hz j := by
    by_cases hj : j = 0
    · subst hj
      have hs : 0 < coordNormSq 0 z := coordNormSq_pos (z := z) (j := 0) hz
      rw [radialCoeff_perturbedConeProfile_zero β hs]
      have := β.pos
      positivity
    · rw [radialCoeff_perturbedConeProfile_of_ne β hj]
      exact one_pos

/-- **The perturbed cone form** `i∂∂̄(|z_0|^(2β) + |z_0|^(4β) + ∑_{j≥1} |z_j|²)` on `{z_0 ≠ 0}`. -/
noncomputable def perturbedConeForm : KahlerForm n (coordHyperplane n).complement :=
  (perturbedConeSeparable β).kahlerForm

/-- The transverse coefficient is the model coefficient times `1 + 4|z_0|^(2β)`. -/
theorem perturbedConeSeparable_weight_zero {z : E n} (hz : z 0 ≠ 0) :
    (perturbedConeSeparable β).weight z 0 =
      modelWeight (singleConeWeights β) z 0 * (1 + 4 * ‖z 0‖ ^ (2 * β.beta)) := by
  have hs : 0 < coordNormSq (0 : Fin n) z := coordNormSq_pos hz
  change radialCoeff (perturbedConeProfile β (0 : Fin n)) (coordNormSq (0 : Fin n) z) = _
  rw [radialCoeff_perturbedConeProfile_zero β hs, modelWeight_single_zero, coordNormSq]
  have hz0 : 0 ≤ ‖z 0‖ := norm_nonneg _
  have h1 : (‖z 0‖ ^ 2) ^ (β.beta - 1) = ‖z 0‖ ^ (2 * β.beta - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz0]
    ring_nf
  have h2 : (‖z 0‖ ^ 2) ^ β.beta = ‖z 0‖ ^ (2 * β.beta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz0]
    norm_num
  rw [h1, h2]

theorem perturbedConeSeparable_weight_of_ne (z : E n) {j : Fin n} (hj : j ≠ 0) :
    (perturbedConeSeparable β).weight z j = 1 :=
  radialCoeff_perturbedConeProfile_of_ne β hj _

/-- The Hermitian quadratic form of the perturbed form is the model one plus the extra term
`4 |z_0|^(2β) w_0 |v_0|²`. -/
theorem perturbedCone_quadratic_eq {z : E n} (hz : z 0 ≠ 0) (v : E n) :
    ∑ j, (perturbedConeSeparable β).weight z j * Complex.normSq (v j) =
      modelConeQuadratic (singleConeWeights β) z v +
        4 * ‖z 0‖ ^ (2 * β.beta) *
          (modelWeight (singleConeWeights β) z 0 * Complex.normSq (v 0)) := by
  rw [modelConeQuadratic, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0),
    ← Finset.add_sum_erase _ (fun j => modelWeight (singleConeWeights β) z j * _)
      (Finset.mem_univ 0),
    perturbedConeSeparable_weight_zero β hz]
  have hrest : ∑ j ∈ Finset.univ.erase 0,
      (perturbedConeSeparable β).weight z j * Complex.normSq (v j) =
        ∑ j ∈ Finset.univ.erase 0,
          modelWeight (singleConeWeights β) z j * Complex.normSq (v j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [perturbedConeSeparable_weight_of_ne β z (Finset.ne_of_mem_erase hj),
        modelWeight_single_of_ne β z (Finset.ne_of_mem_erase hj)]
  rw [hrest]
  ring

/-! ### The cone condition -/

/-- The slab `{|z_0| < 1}`, an open neighbourhood of every point of `{z_0 = 0}`. -/
def coordSlab (n : ℕ) [NeZero n] : Set (E n) :=
  {z | ‖z 0‖ < 1}

theorem isOpen_coordSlab : IsOpen (coordSlab n) :=
  isOpen_lt ((EuclideanSpace.proj (0 : Fin n) : E n →L[ℂ] ℂ).continuous.norm) continuous_const

theorem mem_coordSlab_of_apply_zero {p : E n} (hp : p 0 = 0) : p ∈ coordSlab n := by
  simp [coordSlab, hp]

/-- **The perturbed form is comparable to the model** with `C = 5` in the identity chart restricted
to the slab `{|z_0| < 1}`. -/
theorem perturbedConeForm_coneComparableIn {p : E n} (hp : p 0 = 0) :
    ConeComparableIn (coordHyperplane n) β (perturbedConeForm β)
      ((coordHyperplaneChart n p).restrOpen (coordSlab n) isOpen_coordSlab
        (mem_coordSlab_of_apply_zero hp)) 5 := by
  intro z hz haway v
  have hzs : ‖z 0‖ < 1 := hz.2
  rw [metricQuadraticInAdaptedChart_restrOpen, metricQuadraticInAdaptedChart_coordHyperplaneChart,
    perturbedConeForm, SeparableProfile.kahlerForm_apply_I_smul]
  change 5⁻¹ * _ ≤ (2 * ∑ j, (perturbedConeSeparable β).weight z j * Complex.normSq (v j)) / 2 ∧
    (2 * ∑ j, (perturbedConeSeparable β).weight z j * Complex.normSq (v j)) / 2 ≤ _
  rw [mul_div_cancel_left₀ _ two_ne_zero, perturbedCone_quadratic_eq β haway]
  set q := modelConeQuadratic (singleConeWeights β) z v
  set a := modelWeight (singleConeWeights β) z 0 * Complex.normSq (v 0)
  have hq : 0 ≤ q := modelConeQuadratic_nonneg _ _ _
  have ha : 0 ≤ a := mul_nonneg (modelWeight_nonneg _ _ _) (Complex.normSq_nonneg _)
  have haq : a ≤ q :=
    Finset.single_le_sum (f := fun j => modelWeight (singleConeWeights β) z j *
      Complex.normSq (v j)) (fun j _ => mul_nonneg (modelWeight_nonneg _ _ _)
        (Complex.normSq_nonneg _)) (Finset.mem_univ 0)
  have hr0 : 0 ≤ ‖z 0‖ ^ (2 * β.beta) := Real.rpow_nonneg (norm_nonneg _) _
  have hr1 : ‖z 0‖ ^ (2 * β.beta) ≤ 1 :=
    Real.rpow_le_one (norm_nonneg _) hzs.le (by linarith [β.pos])
  constructor
  · have : 0 ≤ 4 * ‖z 0‖ ^ (2 * β.beta) * a := by positivity
    nlinarith
  · nlinarith [mul_le_mul hr1 haq ha zero_le_one]

/-- **The perturbed form has quasi-isometric cone angle `2πβ`** along `{z_0 = 0}`, for every
`β > 0`. -/
theorem perturbedConeForm_isConeAlong : IsConeAlong (coordHyperplane n) β (perturbedConeForm β) :=
  fun p hp => ⟨_, 5, by norm_num, perturbedConeForm_coneComparableIn β hp⟩

/-- The perturbed form as a conical Kähler form. -/
noncomputable def perturbedConeKahlerForm : ConeKahlerForm (coordHyperplane n) β where
  form := perturbedConeForm β
  cone_condition := perturbedConeForm_isConeAlong β

/-! ### The Ricci form -/

/-- `log w_0` near `s > 0`: `log β² + (β - 1) log s + log(1 + 4 s^β)`. -/
theorem log_radialCoeff_perturbedConeProfile_zero_eventuallyEq {s : ℝ} (hs : 0 < s) :
    (fun t => Real.log (radialCoeff (perturbedConeProfile (n := n) β 0) t)) =ᶠ[𝓝 s]
      fun t => (Real.log (β.beta ^ 2) + (β.beta - 1) * Real.log t) +
        Real.log (1 + 4 * t ^ β.beta) := by
  filter_upwards [lt_mem_nhds hs] with t ht
  have hβ : β.beta ^ 2 ≠ 0 := pow_ne_zero 2 β.pos.ne'
  have h1 : t ^ (β.beta - 1) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have h2 : 1 + 4 * t ^ β.beta ≠ 0 := by
    have := Real.rpow_pos_of_pos ht β.beta
    linarith
  rw [radialCoeff_perturbedConeProfile_zero β ht, Real.log_mul (mul_ne_zero hβ h1) h2,
    Real.log_mul hβ h1, Real.log_rpow ht]

theorem contDiffAt_log_radialCoeff_perturbedConeProfile_zero {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ 2 (fun t => Real.log (radialCoeff (perturbedConeProfile (n := n) β 0) t)) s := by
  refine ContDiffAt.congr_of_eventuallyEq ?_
    (log_radialCoeff_perturbedConeProfile_zero_eventuallyEq β hs)
  have hpos : 0 < 1 + 4 * s ^ β.beta := by
    have := Real.rpow_pos_of_pos hs β.beta
    linarith
  exact (contDiffAt_const.add (contDiffAt_const.mul (Real.contDiffAt_log.mpr hs.ne'))).add
    ((contDiffAt_const.add (contDiffAt_const.mul
      (Real.contDiffAt_rpow_const_of_ne hs.ne'))).log hpos.ne')

theorem contDiffAt_log_radialCoeff_perturbedConeProfile_of_ne {j : Fin n} (hj : j ≠ 0) (s : ℝ) :
    ContDiffAt ℝ 2 (fun t => Real.log (radialCoeff (perturbedConeProfile β j) t)) s := by
  simp_rw [radialCoeff_perturbedConeProfile_of_ne β hj, Real.log_one]
  exact contDiffAt_const

/-- `radialCoeff (log w_0)(s) = 4β² s^(β-1) / (1 + 4 s^β)²`. -/
theorem radialCoeff_log_radialCoeff_perturbedConeProfile_zero {s : ℝ} (hs : 0 < s) :
    radialCoeff (fun t => Real.log (radialCoeff (perturbedConeProfile (n := n) β 0) t)) s =
      4 * β.beta ^ 2 * s ^ (β.beta - 1) / (1 + 4 * s ^ β.beta) ^ 2 := by
  rw [radialCoeff_congr (log_radialCoeff_perturbedConeProfile_zero_eventuallyEq β hs)]
  have hpos : 0 < 1 + 4 * s ^ β.beta := by
    have := Real.rpow_pos_of_pos hs β.beta
    linarith
  rw [radialCoeff_add
      (contDiffAt_const.add (contDiffAt_const.mul (Real.contDiffAt_log.mpr hs.ne')))
      ((contDiffAt_const.add (contDiffAt_const.mul
        (Real.contDiffAt_rpow_const_of_ne hs.ne'))).log hpos.ne'),
    radialCoeff_const_add_mul_log _ _ hs, radialCoeff_log_one_add_mul_rpow (by norm_num) hs,
    zero_add]

/-- **The Ricci form of the perturbed cone form** has
`Ric_{00̄} = -4β² |z_0|^(2β-2) / (1 + 4|z_0|^(2β))²` (with `s = |z_0|²`), which is negative. -/
theorem perturbedConeForm_ricciForm_coeffMatrix_zero (x : (coordHyperplane n).complement) :
    ((perturbedConeForm (n := n) β).ricciForm x).coeffMatrix 0 0 =
      -((4 * β.beta ^ 2 * coordNormSq (0 : Fin n) (x : E n) ^ (β.beta - 1) /
        (1 + 4 * coordNormSq (0 : Fin n) (x : E n) ^ β.beta) ^ 2 : ℝ) : ℂ) := by
  have hs : 0 < coordNormSq (0 : Fin n) (x : E n) := coordNormSq_pos (z := (x : E n)) (j := 0) x.2
  have hlog : ∀ j, ContDiffAt ℝ 2
      (fun t => Real.log (radialCoeff ((perturbedConeSeparable β).g j) t))
      (coordNormSq j (x : E n)) := fun j => by
    by_cases hj : j = 0
    · subst hj
      exact contDiffAt_log_radialCoeff_perturbedConeProfile_zero (n := n) β hs
    · exact contDiffAt_log_radialCoeff_perturbedConeProfile_of_ne (n := n) β hj _
  change ((perturbedConeSeparable (n := n) β).kahlerForm.ricciForm x).coeffMatrix 0 0 = _
  rw [SeparableProfile.ricciForm_coeffMatrix _ x hlog]
  simp only [Matrix.neg_apply, Matrix.diagonal_apply_eq]
  change -(((radialCoeff (fun t => Real.log (radialCoeff (perturbedConeProfile (n := n) β 0) t))
    (coordNormSq (0 : Fin n) (x : E n))) : ℝ) : ℂ) = _
  rw [radialCoeff_log_radialCoeff_perturbedConeProfile_zero β hs]

/-- **The perturbed cone form is not Ricci-flat**, so it is not locally isometric to the model
`ω_β`, although it has quasi-isometric cone angle `2πβ`. -/
theorem perturbedConeForm_not_ricciFlat : ¬ (perturbedConeForm (n := n) β).IsRicciFlat := by
  intro h
  have hmem : EuclideanSpace.single (0 : Fin n) (1 : ℂ) ∈ (coordHyperplane n).complement := by
    change EuclideanSpace.single (0 : Fin n) (1 : ℂ) 0 ≠ 0
    simp
  let x : (coordHyperplane n).complement := ⟨EuclideanSpace.single 0 1, hmem⟩
  have h0 := perturbedConeForm_ricciForm_coeffMatrix_zero β x
  have h' : (perturbedConeForm (n := n) β).ricciForm = 0 := h
  have hRic : (perturbedConeForm (n := n) β).ricciForm x = 0 := by
    rw [h']
    rfl
  rw [hRic, coeffMatrix_zero] at h0
  have hs : 0 < coordNormSq (0 : Fin n) (x : E n) :=
    coordNormSq_pos (z := (x : E n)) (j := 0) x.2
  have hpos : 0 < 4 * β.beta ^ 2 * coordNormSq (0 : Fin n) (x : E n) ^ (β.beta - 1) /
      (1 + 4 * coordNormSq (0 : Fin n) (x : E n) ^ β.beta) ^ 2 := by
    have := β.pos
    have := Real.rpow_pos_of_pos hs (β.beta - 1)
    have := Real.rpow_pos_of_pos hs β.beta
    positivity
  have h0' := congrArg Complex.re h0
  simp only [Matrix.zero_apply, Complex.zero_re, Complex.neg_re, Complex.ofReal_re] at h0'
  linarith

/-- The perturbed cone form is not Kähler–Einstein with `λ = 0` on the complement. -/
theorem perturbedConeKahlerForm_not_isKahlerEinstein_zero :
    ¬ (perturbedConeKahlerForm (n := n) β).IsKahlerEinstein 0 := by
  rw [ConeKahlerForm.isKahlerEinstein_zero_iff]
  exact perturbedConeForm_not_ricciFlat β

/-- **Quasi-isometric cone control is strictly weaker than the model geometry.** For every
`β > 0` there is a Kähler form on `ℂⁿ \ {z_0 = 0}` with quasi-isometric cone angle `2πβ` that is
not Ricci-flat, whereas the model `ω_β` is Ricci-flat and transversally a flat cone. -/
theorem exists_isConeAlong_not_ricciFlat :
    ∃ ω₀ : KahlerForm n (coordHyperplane n).complement,
      IsConeAlong (coordHyperplane n) β ω₀ ∧ ¬ ω₀.IsRicciFlat :=
  ⟨perturbedConeForm β, perturbedConeForm_isConeAlong β, perturbedConeForm_not_ricciFlat β⟩

end ConicalKahler
