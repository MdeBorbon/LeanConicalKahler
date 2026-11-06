module

public import ConicalKahler.Sobolev.Rotation
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier modes in the angle of a cone factor

Let `Ω ⊆ ℝ^d` be invariant under all rotations `R_t` of the cone factor `a` (for example a ball
centred at the vertex). The rotations act on `L²(Ω)` by `u ↦ u ∘ R_t` (`rotLp`), and on pairs
(`rotPair`). The **Fourier modes** of `u` in the angle `θ_a` are

  `C_k u = ∫_0^{2π} cos(kt) (u ∘ R_t) dt`,   `S_k u = ∫_0^{2π} sin(kt) (u ∘ R_t) dt`

(`cosCoeff`, `sinCoeff`; Bochner integrals in `L²(Ω)`). This is the separation of variables in
`θ_a` used in §3.3 of the paper, carried out for weak solutions.

## Results

* `continuous_rotLp`, `continuous_rotPair`: **the rotations act continuously** on `L²(Ω)` and on
  `L²(Ω) × L²(Ω; ℝ^d)` (Mathlib's `Lp.compMeasurePreserving_continuous`).
* `isWeakSolution_cosMode`, `isWeakSolution_sinMode`: **the Fourier modes of a weak solution of
  `-div(g⁻¹ ∇u) = f` are weak solutions** with the corresponding modes of `f`. In particular the
  modes of a weakly harmonic function are weakly harmonic.
* `rotLp_cosCoeff`, `rotLp_sinCoeff`: **the modes transform like `cos kθ_a` and `sin kθ_a`**:
  `C_k u ∘ R_s = cos(ks) C_k u + sin(ks) S_k u` and `S_k u ∘ R_s = cos(ks) S_k u − sin(ks) C_k u`.
* `eq_zero_of_modes_eq_zero`: **a function is determined by its Fourier modes**: if all `C_k u` and
  `S_k u` vanish then `u = 0`. The proof is Fourier uniqueness for the continuous periodic function
  `t ↦ ⟨u ∘ R_t, u⟩` (Mathlib's Parseval identity).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set
open scoped ContDiff ENNReal Real

namespace ConicalKahler.Sobolev

open RealConeModel

/-! ### The rotations as explicit operators -/

section Rot

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- The rotation of the cone factor `a` as an explicit operator:
`R_t = I + (cos t − 1) P_a + sin t J_a`, with `P_a` the projection onto the factor `a`. -/
def coneRotL (a : κ) (t : ℝ) : RealConeModel κ ι →L[ℝ] RealConeModel κ ι :=
  ContinuousLinearMap.id ℝ _ + (Real.cos t - 1) • (coneIncl a).comp (coneProj a) +
    Real.sin t • rotJ a

theorem coneRot_eq_coneRotL (a : κ) (t : ℝ) (y : RealConeModel κ ι) :
    coneRot a t y = coneRotL a t y := by
  refine ext_cone_eucl (fun b => ?_) fun i => ?_
  · simp only [coneRot_apply, cone_coneRotₗ, coneRotL, _root_.add_apply,
      ContinuousLinearMap.id_apply, _root_.smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, coneProj_apply, cone_add, cone_smul, cone_coneIncl, cone_rotJ]
    by_cases h : b = a
    · subst h
      simp only [↓reduceIte]
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
    · simp [h]
  · simp [coneRot_apply, coneRotL]

theorem continuous_coneRotL (a : κ) : Continuous (coneRotL (κ := κ) (ι := ι) a) := by
  unfold coneRotL
  exact (continuous_const.add ((Real.continuous_cos.sub continuous_const).smul continuous_const)).add
    (Real.continuous_sin.smul continuous_const)

theorem coneRot_add (a : κ) (s t : ℝ) (y : RealConeModel κ ι) :
    coneRot a s (coneRot a t y) = coneRot a (s + t) y :=
  coneRotₗ_coneRotₗ a s t y

theorem coneRot_add_two_pi (a : κ) (t : ℝ) (y : RealConeModel κ ι) :
    coneRot a (t + 2 * π) y = coneRot a t y := by
  rw [coneRot_eq_coneRotL, coneRot_eq_coneRotL]
  simp [coneRotL, Real.cos_add_two_pi, Real.sin_add_two_pi]

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

theorem rotE_add (e : RealConeIndex κ ι ≃ Fin d) (a : κ) (s t : ℝ) (x : 𝔼) :
    rotE e a s (rotE e a t x) = rotE e a (s + t) x := by
  simp only [rotE_apply, LinearIsometryEquiv.symm_apply_apply, coneRot_add]

theorem rotE_add_two_pi (e : RealConeIndex κ ι ≃ Fin d) (a : κ) (t : ℝ) (x : 𝔼) :
    rotE e a (t + 2 * π) x = rotE e a t x := by
  simp only [rotE_apply, coneRot_add_two_pi]

theorem rotE_zero (e : RealConeIndex κ ι ≃ Fin d) (a : κ) (x : 𝔼) : rotE e a 0 x = x := by
  rw [rotE_apply, coneRot_apply, coneRotₗ_zero, LinearIsometryEquiv.apply_symm_apply]

theorem rotE_symm (e : RealConeIndex κ ι ≃ Fin d) (a : κ) (t : ℝ) (x : 𝔼) :
    (rotE e a t).symm x = rotE e a (-t) x := by
  rw [LinearIsometryEquiv.symm_apply_eq, rotE_add, add_neg_cancel, rotE_zero]

theorem rotE_eq_clm (e : RealConeIndex κ ι ≃ Fin d) (a : κ) (t : ℝ) :
    ((rotE e a t).toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼) =
      ((coordIso e).toContinuousLinearEquiv : RealConeModel κ ι →L[ℝ] 𝔼).comp
        ((coneRotL a t).comp ((coordIso e).symm.toContinuousLinearEquiv :
          𝔼 →L[ℝ] RealConeModel κ ι)) := by
  ext1 x
  simp [rotE_apply, coneRot_eq_coneRotL]

theorem continuous_rotE_clm (e : RealConeIndex κ ι ≃ Fin d) (a : κ) :
    Continuous fun t => ((rotE e a t).toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼) := by
  simp_rw [rotE_eq_clm]
  exact continuous_const.clm_comp ((continuous_coneRotL a).clm_comp continuous_const)

theorem continuous_rotE_uncurry (e : RealConeIndex κ ι ≃ Fin d) (a : κ) :
    Continuous fun p : ℝ × 𝔼 => rotE e a p.1 p.2 := by
  have h : (fun p : ℝ × 𝔼 => rotE e a p.1 p.2) = fun p =>
      ((rotE e a p.1).toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼) p.2 := rfl
  rw [h]
  exact ((continuous_rotE_clm e a).comp continuous_fst).clm_apply continuous_snd

end Rot

/-! ### Continuity of `(L, g) ↦ L ∘ g` on `L²` -/

theorem continuous_compLp_of_continuous {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : ℝ → E →L[ℝ] F} {g : ℝ → Lp E 2 μ} (hL : Continuous L) (hg : Continuous g) :
    Continuous fun t => (L t).compLp (g t) := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ t, ‖(L t).compLp (g t) - (L s).compLp (g s)‖ ≤
      ‖L t‖ * ‖g t - g s‖ + ‖L t - L s‖ * ‖g s‖ := fun t => by
    have e1 : (L t).compLp (g t) - (L s).compLp (g s) =
        (L t).compLp (g t - g s) + (L t - L s).compLp (g s) := by
      have h1 : (L t).compLp (g t - g s) = (L t).compLp (g t) - (L t).compLp (g s) :=
        map_sub ((L t).compLpL 2 μ) _ _
      have h2 : (L t - L s + L s).compLp (g s) = (L t - L s).compLp (g s) + (L s).compLp (g s) :=
        ContinuousLinearMap.add_compLp _ _ _
      rw [sub_add_cancel] at h2
      rw [h1, h2]
      abel
    rw [e1]
    exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.norm_compLp_le _ _)
      (ContinuousLinearMap.norm_compLp_le _ _))
  refine squeeze_zero (fun t => norm_nonneg _) hbound ?_
  have h1 : Tendsto (fun t => ‖g t - g s‖) (𝓝 s) (𝓝 0) := by
    rw [← tendsto_iff_norm_sub_tendsto_zero]
    exact hg.continuousAt
  have h2 : Tendsto (fun t => ‖L t - L s‖) (𝓝 s) (𝓝 0) := by
    rw [← tendsto_iff_norm_sub_tendsto_zero]
    exact hL.continuousAt
  have := ((hL.norm.tendsto s).mul h1).add (h2.mul_const ‖g s‖)
  simpa using this

/-! ### The rotation action on `L²` of an invariant domain -/

section Action

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
variable {d : ℕ} [NeZero d]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

variable (e : RealConeIndex κ ι ≃ Fin d) (a : κ) {Ω : Set (EuclideanSpace ℝ (Fin d))}
  (hΩ : MeasurableSet Ω) (hinv : ∀ t, rotE e a t ⁻¹' Ω = Ω)

/-- **The rotation action on `L²(Ω)`**: `u ↦ u ∘ R_t`. -/
def rotLp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) :
    Lp E 2 (volume.restrict Ω) →ₗᵢ[ℝ] Lp E 2 (volume.restrict Ω) :=
  isoLp (rotE e a t) E hΩ (hinv t)

/-- The rotation action on pairs `(u, G) ↦ (u ∘ R_t, R_t⁻¹ (G ∘ R_t))`. -/
def rotPair (t : ℝ) (v : L2Pair volume Ω) : L2Pair volume Ω :=
  isoPair (rotE e a t) hΩ (hinv t) v

include hΩ hinv in
theorem measurePreserving_rotE (t : ℝ) :
    MeasurePreserving (rotE e a t) (volume.restrict Ω) (volume.restrict Ω) :=
  measurePreserving_restrict_preimage _ hΩ (hinv t)

/-- **The rotations act continuously on `L²(Ω)`.** -/
theorem continuous_rotLp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 (volume.restrict Ω)) : Continuous fun t => rotLp e a hΩ hinv E t f := by
  let F : C(ℝ × 𝔼, 𝔼) := ⟨fun p => rotE e a p.1 p.2, continuous_rotE_uncurry e a⟩
  let γ : ℝ → {g : C(𝔼, 𝔼) // MeasurePreserving g (volume.restrict Ω) (volume.restrict Ω)} :=
    fun t => ⟨F.curry t, measurePreserving_rotE e a hΩ hinv t⟩
  have hγ : Continuous γ := F.curry.continuous.subtype_mk _
  have hc := Lp.compMeasurePreserving_continuous (volume.restrict Ω) (volume.restrict Ω) E
    (p := 2) (by norm_num)
  exact hc.comp (continuous_const.prodMk hγ)

theorem rotPair_fst (t : ℝ) (v : L2Pair volume Ω) :
    (rotPair e a hΩ hinv t v).fst = rotLp e a hΩ hinv ℝ t v.fst := rfl

theorem rotPair_snd (t : ℝ) (v : L2Pair volume Ω) :
    (rotPair e a hΩ hinv t v).snd = ((rotE e a t).symm.toContinuousLinearEquiv :
      𝔼 →L[ℝ] 𝔼).compLp (rotLp e a hΩ hinv _ t v.snd) := rfl

/-- **The rotations act continuously on pairs.** -/
theorem continuous_rotPair (v : L2Pair volume Ω) :
    Continuous fun t => rotPair e a hΩ hinv t v := by
  have hsymm : (fun t => ((rotE e a t).symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼)) =
      fun t => ((rotE e a (-t)).toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼) := by
    funext t
    ext1 x
    simp [rotE_symm]
  have h2 : Continuous fun t => ((rotE e a t).symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼) := by
    rw [hsymm]
    exact (continuous_rotE_clm e a).comp continuous_neg
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.comp
    ((continuous_rotLp e a hΩ hinv ℝ v.fst).prodMk
      (continuous_compLp_of_continuous h2 (continuous_rotLp e a hΩ hinv _ v.snd)))

end Action

/-! ### Angular Fourier coefficients of continuous paths -/

section Coeff

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- `∫_0^{2π} w(t) γ(t) dt` for a weight `w`. -/
def angCoeff (w : ℝ → ℝ) (γ : ℝ → X) : X := ∫ t in (0 : ℝ)..2 * π, w t • γ t

/-- The cosine coefficient `∫_0^{2π} cos(kt) γ(t) dt`. -/
abbrev cosCoeff (k : ℕ) (γ : ℝ → X) : X := angCoeff (fun t => Real.cos (k * t)) γ

/-- The sine coefficient `∫_0^{2π} sin(kt) γ(t) dt`. -/
abbrev sinCoeff (k : ℕ) (γ : ℝ → X) : X := angCoeff (fun t => Real.sin (k * t)) γ

theorem continuous_cos_mul (k : ℕ) : Continuous fun t : ℝ => Real.cos (k * t) :=
  Real.continuous_cos.comp (continuous_const.mul continuous_id)

theorem continuous_sin_mul (k : ℕ) : Continuous fun t : ℝ => Real.sin (k * t) :=
  Real.continuous_sin.comp (continuous_const.mul continuous_id)

theorem intervalIntegrable_smul {w : ℝ → ℝ} (hw : Continuous w) {γ : ℝ → X} (hγ : Continuous γ)
    (a b : ℝ) : IntervalIntegrable (fun t => w t • γ t) volume a b :=
  (hw.smul hγ).intervalIntegrable _ _

/-- Bounded linear maps commute with the coefficients. -/
theorem clm_angCoeff {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (Λ : X →L[ℝ] Y) {w : ℝ → ℝ} (hw : Continuous w) {γ : ℝ → X} (hγ : Continuous γ) :
    Λ (angCoeff w γ) = angCoeff w fun t => Λ (γ t) := by
  rw [angCoeff, angCoeff, ← Λ.intervalIntegral_comp_comm (intervalIntegrable_smul hw hγ _ _)]
  simp only [map_smul]

theorem angCoeff_zero (w : ℝ → ℝ) : angCoeff w (fun _ => (0 : X)) = 0 := by
  simp [angCoeff]

end Coeff

/-! ### The Fourier modes of weak solutions are weak solutions -/

section Modes

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
variable {d : ℕ} [NeZero d]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

variable (e : RealConeIndex κ ι ≃ Fin d) (a : κ) {Ω : Set (EuclideanSpace ℝ (Fin d))}
  (hΩ : MeasurableSet Ω) (hinv : ∀ t, rotE e a t ⁻¹' Ω = Ω)

/-- **The angular modes of a weak solution are weak solutions.** For any continuous weight `w`,
`∫ w(t) (u ∘ R_t) dt` solves `-div(g⁻¹ ∇ ·) = ∫ w(t) (f ∘ R_t) dt` weakly on `Ω`. -/
theorem isWeakSolution_angMode (β : κ → ConeAngle) {w : ℝ → ℝ} (hw : Continuous w)
    {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω}
    (hv : (coneCoeff β e).IsWeakSolution f v) :
    (coneCoeff β e).IsWeakSolution (angCoeff w fun t => rotLp e a hΩ hinv ℝ t f)
      (angCoeff w fun t => rotPair e a hΩ hinv t v) := by
  have hrot : ∀ t, (coneCoeff β e).IsWeakSolution (rotLp e a hΩ hinv ℝ t f)
      (rotPair e a hΩ hinv t v) := fun t => cone_isWeakSolution_rot β e a t hΩ (hinv t) hv
  have hcf := continuous_rotLp e a hΩ hinv ℝ f
  have hcv := continuous_rotPair e a hΩ hinv v
  refine ⟨fun φ hφ w' => ?_, fun φ hφ => ?_⟩
  · -- the weak gradient identity
    set A := (hφ.memLp_fderiv_apply (μ := volume) w' 2 Ω).toLp fun x => fderiv ℝ φ x w'
    set B := (hφ.memLp_smul_vec (μ := volume) w' 2 Ω).toLp fun x => φ x • w'
    let Λ : L2Pair volume Ω →L[ℝ] ℝ := (innerSL ℝ A).comp (WithLp.fstL 2 ℝ _ _) +
      (innerSL ℝ B).comp (WithLp.sndL 2 ℝ _ _)
    have hΛ : ∀ x : L2Pair volume Ω, Λ x = ⟪x.fst, A⟫_ℝ + ⟪x.snd, B⟫_ℝ := fun x => by
      simp only [Λ, _root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
        innerSL_apply_apply, real_inner_comm A, real_inner_comm B]
      rfl
    have h := clm_angCoeff Λ hw hcv
    have h0 : (fun t => Λ (rotPair e a hΩ hinv t v)) = fun _ => 0 := funext fun t => by
      rw [hΛ, (hrot t).1 φ hφ w', neg_add_cancel]
    rw [h0, angCoeff_zero, hΛ] at h
    linarith
  · -- the equation
    let Λ₁ : L2Pair volume Ω →L[ℝ] ℝ := ((coneCoeff β e).dirichletForm Ω).flip (graph volume Ω hφ)
    let Λ₂ : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] ℝ := innerSL ℝ (graph volume Ω hφ).fst
    have h1 := clm_angCoeff Λ₁ hw hcv
    have h2 := clm_angCoeff Λ₂ hw hcf
    have h12 : (fun t => Λ₁ (rotPair e a hΩ hinv t v)) =
        fun t => Λ₂ (rotLp e a hΩ hinv ℝ t f) := funext fun t => by
      simp only [Λ₁, Λ₂, ContinuousLinearMap.flip_apply, innerSL_apply_apply]
      rw [(hrot t).2 φ hφ, real_inner_comm]
    rw [h12, ← h2] at h1
    simp only [Λ₁, Λ₂, ContinuousLinearMap.flip_apply, innerSL_apply_apply] at h1
    rw [h1, real_inner_comm]

theorem isWeakSolution_cosMode (β : κ → ConeAngle) (k : ℕ) {f : Lp ℝ 2 (volume.restrict Ω)}
    {v : L2Pair volume Ω} (hv : (coneCoeff β e).IsWeakSolution f v) :
    (coneCoeff β e).IsWeakSolution (cosCoeff k fun t => rotLp e a hΩ hinv ℝ t f)
      (cosCoeff k fun t => rotPair e a hΩ hinv t v) :=
  isWeakSolution_angMode e a hΩ hinv β (continuous_cos_mul k) hv

theorem isWeakSolution_sinMode (β : κ → ConeAngle) (k : ℕ) {f : Lp ℝ 2 (volume.restrict Ω)}
    {v : L2Pair volume Ω} (hv : (coneCoeff β e).IsWeakSolution f v) :
    (coneCoeff β e).IsWeakSolution (sinCoeff k fun t => rotLp e a hΩ hinv ℝ t f)
      (sinCoeff k fun t => rotPair e a hΩ hinv t v) :=
  isWeakSolution_angMode e a hΩ hinv β (continuous_sin_mul k) hv

/-- The first component of the mode of a pair is the mode of the first component. -/
theorem angCoeff_rotPair_fst {w : ℝ → ℝ} (hw : Continuous w) (v : L2Pair volume Ω) :
    (angCoeff w fun t => rotPair e a hΩ hinv t v).fst =
      angCoeff w fun t => rotLp e a hΩ hinv ℝ t v.fst :=
  clm_angCoeff (WithLp.fstL 2 ℝ _ _) hw (continuous_rotPair e a hΩ hinv v)

/-- **The modes of a weakly harmonic function are weakly harmonic.** -/
theorem isWeakSolution_zero_angMode (β : κ → ConeAngle) {w : ℝ → ℝ} (hw : Continuous w)
    {v : L2Pair volume Ω} (hv : (coneCoeff β e).IsWeakSolution 0 v) :
    (coneCoeff β e).IsWeakSolution 0 (angCoeff w fun t => rotPair e a hΩ hinv t v) := by
  have h := isWeakSolution_angMode e a hΩ hinv β hw hv
  simp only [map_zero] at h
  rwa [angCoeff_zero] at h

/-! ### The modes transform like `cos kθ` and `sin kθ` -/

theorem rotLp_rotLp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (s t : ℝ)
    (f : Lp E 2 (volume.restrict Ω)) :
    rotLp e a hΩ hinv E s (rotLp e a hΩ hinv E t f) = rotLp e a hΩ hinv E (t + s) f := by
  refine Lp.ext ?_
  have hq := (measurePreserving_rotE e a hΩ hinv s).quasiMeasurePreserving
  filter_upwards [isoLp_ae (rotE e a s) hΩ (hinv s) (rotLp e a hΩ hinv E t f),
    hq.ae_eq_comp (isoLp_ae (rotE e a t) hΩ (hinv t) f),
    isoLp_ae (rotE e a (t + s)) hΩ (hinv (t + s)) f] with x h1 h2 h3
  simp only [Function.comp_apply] at h2
  change (isoLp (rotE e a s) E hΩ (hinv s) (rotLp e a hΩ hinv E t f)) x =
    (isoLp (rotE e a (t + s)) E hΩ (hinv (t + s)) f) x
  rw [h1, h3]
  change (isoLp (rotE e a t) E hΩ (hinv t) f) (rotE e a s x) = _
  rw [h2, rotE_add]

theorem rotLp_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 (volume.restrict Ω)) : rotLp e a hΩ hinv E 0 f = f := by
  refine Lp.ext ?_
  filter_upwards [isoLp_ae (rotE e a 0) hΩ (hinv 0) f] with x hx
  change (isoLp (rotE e a 0) E hΩ (hinv 0) f) x = f x
  rw [hx, rotE_zero]

theorem rotLp_add_two_pi (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ)
    (f : Lp E 2 (volume.restrict Ω)) :
    rotLp e a hΩ hinv E (t + 2 * π) f = rotLp e a hΩ hinv E t f := by
  refine Lp.ext ?_
  filter_upwards [isoLp_ae (rotE e a (t + 2 * π)) hΩ (hinv (t + 2 * π)) f,
    isoLp_ae (rotE e a t) hΩ (hinv t) f] with x h1 h2
  change (isoLp (rotE e a (t + 2 * π)) E hΩ (hinv _) f) x = (isoLp (rotE e a t) E hΩ (hinv t) f) x
  rw [h1, h2, rotE_add_two_pi]

/-- Shifting the angle in a coefficient: `∫_0^{2π} W(t) γ(t + s) dt = ∫_0^{2π} W(u − s) γ(u) du`
for a `2π`-periodic `W` and `γ`. -/
theorem integral_shift {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {W : ℝ → ℝ} (hW : Function.Periodic W (2 * π)) {γ : ℝ → X}
    (hγ : Function.Periodic γ (2 * π)) (s : ℝ) :
    ∫ t in (0 : ℝ)..2 * π, W t • γ (t + s) = ∫ u in (0 : ℝ)..2 * π, W (u - s) • γ u := by
  have hG : (fun t => W t • γ (t + s)) = fun t => (fun u => W (u - s) • γ u) (t + s) := by
    funext t
    simp only [add_sub_cancel_right]
  have hper : Function.Periodic (fun u => W (u - s) • γ u) (2 * π) := fun u => by
    simp only
    rw [show u + 2 * π - s = (u - s) + 2 * π by ring, hW, hγ]
  rw [hG, intervalIntegral.integral_comp_add_right (fun u => W (u - s) • γ u) s, zero_add,
    show 2 * π + s = s + 2 * π by ring, hper.intervalIntegral_add_eq s 0, zero_add]

/-- **`C_k u ∘ R_s = cos(ks) C_k u + sin(ks) S_k u`.** -/
theorem rotLp_cosCoeff (k : ℕ) (s : ℝ) (f : Lp ℝ 2 (volume.restrict Ω)) :
    rotLp e a hΩ hinv ℝ s (cosCoeff k fun t => rotLp e a hΩ hinv ℝ t f) =
      Real.cos (k * s) • cosCoeff k (fun t => rotLp e a hΩ hinv ℝ t f) +
        Real.sin (k * s) • sinCoeff k (fun t => rotLp e a hΩ hinv ℝ t f) := by
  have hγ := continuous_rotLp e a hΩ hinv ℝ f
  have hc := clm_angCoeff (rotLp e a hΩ hinv ℝ s).toContinuousLinearMap (continuous_cos_mul k) hγ
  simp only [LinearIsometry.coe_toContinuousLinearMap] at hc
  rw [hc]
  simp only [rotLp_rotLp]
  have hsh := integral_shift (W := fun t => Real.cos (k * t))
    (γ := fun t => rotLp e a hΩ hinv ℝ t f)
    (fun t => by simp only; rw [mul_add, show (k : ℝ) * (2 * π) = k * (2 * π) from rfl,
      Real.cos_add_nat_mul_two_pi])
    (fun t => rotLp_add_two_pi e a hΩ hinv ℝ t f) s
  rw [angCoeff, hsh]
  have h : (fun u => Real.cos (k * (u - s)) • rotLp e a hΩ hinv ℝ u f) = fun u =>
      Real.cos (k * s) • (Real.cos (k * u) • rotLp e a hΩ hinv ℝ u f) +
        Real.sin (k * s) • (Real.sin (k * u) • rotLp e a hΩ hinv ℝ u f) := by
    funext u
    rw [show (k : ℝ) * (u - s) = k * u - k * s by ring, Real.cos_sub, smul_smul, smul_smul,
      ← add_smul]
    ring_nf
  have hi1 : IntervalIntegrable (fun u => Real.cos (k * s) •
      (Real.cos (k * u) • rotLp e a hΩ hinv ℝ u f)) volume 0 (2 * π) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hi2 : IntervalIntegrable (fun u => Real.sin (k * s) •
      (Real.sin (k * u) • rotLp e a hΩ hinv ℝ u f)) volume 0 (2 * π) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [h, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_smul, intervalIntegral.integral_smul]
  rfl

/-- **`S_k u ∘ R_s = cos(ks) S_k u − sin(ks) C_k u`.** -/
theorem rotLp_sinCoeff (k : ℕ) (s : ℝ) (f : Lp ℝ 2 (volume.restrict Ω)) :
    rotLp e a hΩ hinv ℝ s (sinCoeff k fun t => rotLp e a hΩ hinv ℝ t f) =
      Real.cos (k * s) • sinCoeff k (fun t => rotLp e a hΩ hinv ℝ t f) -
        Real.sin (k * s) • cosCoeff k (fun t => rotLp e a hΩ hinv ℝ t f) := by
  have hγ := continuous_rotLp e a hΩ hinv ℝ f
  have hc := clm_angCoeff (rotLp e a hΩ hinv ℝ s).toContinuousLinearMap (continuous_sin_mul k) hγ
  simp only [LinearIsometry.coe_toContinuousLinearMap] at hc
  rw [hc]
  simp only [rotLp_rotLp]
  have hsh := integral_shift (W := fun t => Real.sin (k * t))
    (γ := fun t => rotLp e a hΩ hinv ℝ t f)
    (fun t => by simp only; rw [mul_add, show (k : ℝ) * (2 * π) = k * (2 * π) from rfl,
      Real.sin_add_nat_mul_two_pi])
    (fun t => rotLp_add_two_pi e a hΩ hinv ℝ t f) s
  rw [angCoeff, hsh]
  have h : (fun u => Real.sin (k * (u - s)) • rotLp e a hΩ hinv ℝ u f) = fun u =>
      Real.cos (k * s) • (Real.sin (k * u) • rotLp e a hΩ hinv ℝ u f) -
        Real.sin (k * s) • (Real.cos (k * u) • rotLp e a hΩ hinv ℝ u f) := by
    funext u
    rw [show (k : ℝ) * (u - s) = k * u - k * s by ring, Real.sin_sub, smul_smul, smul_smul,
      ← sub_smul]
    ring_nf
  have hi1 : IntervalIntegrable (fun u => Real.cos (k * s) •
      (Real.sin (k * u) • rotLp e a hΩ hinv ℝ u f)) volume 0 (2 * π) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hi2 : IntervalIntegrable (fun u => Real.sin (k * s) •
      (Real.cos (k * u) • rotLp e a hΩ hinv ℝ u f)) volume 0 (2 * π) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [h, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_smul, intervalIntegral.integral_smul]
  rfl

end Modes

/-! ### Fourier uniqueness -/

/-- **Fourier uniqueness for a continuous function on `[0, 2π]`**: if all its cosine and sine
coefficients vanish, it vanishes at `0`. (Parseval's identity, `tsum_sq_fourierCoeffOn`.) -/
theorem eq_zero_of_fourier_real {g : ℝ → ℝ} (hg : Continuous g)
    (hc : ∀ k : ℕ, ∫ t in (0 : ℝ)..2 * π, Real.cos (k * t) * g t = 0)
    (hs : ∀ k : ℕ, ∫ t in (0 : ℝ)..2 * π, Real.sin (k * t) * g t = 0) : g 0 = 0 := by
  have hπ : (0 : ℝ) < 2 * π := Real.two_pi_pos
  set G : ℝ → ℂ := fun t => (g t : ℂ)
  have hcI : ∀ n : ℤ, ∫ t in (0 : ℝ)..2 * π, Real.cos (n * t) * g t = 0 := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa only [Int.cast_natCast] using hc m
    · simp only [Int.cast_neg, Int.cast_natCast, neg_mul, Real.cos_neg]
      exact hc m
  have hsI : ∀ n : ℤ, ∫ t in (0 : ℝ)..2 * π, Real.sin (n * t) * g t = 0 := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa only [Int.cast_natCast] using hs m
    · simp only [Int.cast_neg, Int.cast_natCast, neg_mul, Real.sin_neg,
        intervalIntegral.integral_neg, neg_eq_zero]
      exact hs m
  have hcoef : ∀ n : ℤ, fourierCoeffOn hπ G n = 0 := by
    intro n
    rw [fourierCoeffOn_eq_integral]
    have hint : (fun t : ℝ => (fourier (-n) (t : AddCircle (2 * π - 0))) • G t) = fun t =>
        ((Real.cos (n * t) * g t : ℝ) : ℂ) - ((Real.sin (n * t) * g t : ℝ) : ℂ) * Complex.I := by
      funext t
      rw [fourier_coe_apply, smul_eq_mul]
      have hπc : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have : 2 * (π : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * (t : ℂ) / ((2 * π - 0 : ℝ) : ℂ) =
          ((-(n * t) : ℝ) : ℂ) * Complex.I := by
        push_cast
        field_simp
        ring
      rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
        Real.sin_neg]
      push_cast
      ring
    have hi1 : IntervalIntegrable (fun t : ℝ => ((Real.cos (n * t) * g t : ℝ) : ℂ)) volume 0
        (2 * π) :=
      (Complex.continuous_ofReal.comp ((Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).mul hg)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t : ℝ => ((Real.sin (n * t) * g t : ℝ) : ℂ) * Complex.I)
        volume 0 (2 * π) :=
      ((Complex.continuous_ofReal.comp ((Real.continuous_sin.comp
        (continuous_const.mul continuous_id)).mul hg)).mul continuous_const).intervalIntegrable _ _
    rw [hint, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, hcI n, hsI n]
    simp
  -- Parseval
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    (Complex.continuous_ofReal.comp hg).continuousOn
  have hL2 : MemLp G 2 (volume.restrict (Ioc 0 (2 * π))) := by
    have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
      isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
    refine MemLp.of_bound (Complex.continuous_ofReal.comp hg).aestronglyMeasurable M ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hM t (Ioc_subset_Icc_self ht)
  have hP := tsum_sq_fourierCoeffOn hπ hL2
  simp only [hcoef, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    tsum_zero, sub_zero, smul_eq_mul] at hP
  have hI : ∫ t in (0 : ℝ)..2 * π, g t ^ 2 = 0 := by
    have h1 : (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖G t‖ ^ 2 = 0 := hP.symm
    have h2 : ∫ t in (0 : ℝ)..2 * π, ‖G t‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h (inv_ne_zero hπ.ne')
      · exact h
    simpa [G, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h2
  have hg2 : Continuous fun t => g t ^ 2 := hg.pow 2
  have hae := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun t => sq_nonneg (g t)) (hg2.intervalIntegrable _ _)).mp hI
  rw [Ioc_eq_empty (not_lt.mpr hπ.le), union_empty] at hae
  have heq : EqOn (fun t => g t ^ 2) 0 (Ioo 0 (2 * π)) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hae)
      isOpen_Ioo hg2.continuousOn continuousOn_const
  have heq' := heq.of_subset_closure hg2.continuousOn continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hπ.ne])
  have h0 := heq' (left_mem_Icc.mpr hπ.le)
  simpa using h0

section Uniqueness

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
variable {d : ℕ} [NeZero d]
variable (e : RealConeIndex κ ι ≃ Fin d) (a : κ) {Ω : Set (EuclideanSpace ℝ (Fin d))}
  (hΩ : MeasurableSet Ω) (hinv : ∀ t, rotE e a t ⁻¹' Ω = Ω)

/-- **A function on `Ω` is determined by its Fourier modes in `θ_a`**: if all its modes `C_k u`
and `S_k u` vanish, then `u = 0`. -/
theorem eq_zero_of_modes_eq_zero {f : Lp ℝ 2 (volume.restrict Ω)}
    (hc : ∀ k : ℕ, cosCoeff k (fun t => rotLp e a hΩ hinv ℝ t f) = 0)
    (hs : ∀ k : ℕ, sinCoeff k (fun t => rotLp e a hΩ hinv ℝ t f) = 0) : f = 0 := by
  have hγ := continuous_rotLp e a hΩ hinv ℝ f
  set g : ℝ → ℝ := fun t => ⟪rotLp e a hΩ hinv ℝ t f, f⟫_ℝ
  have hg : Continuous g := hγ.inner continuous_const
  have key : ∀ {w : ℝ → ℝ}, Continuous w →
      angCoeff w (fun t => rotLp e a hΩ hinv ℝ t f) = 0 →
        ∫ t in (0 : ℝ)..2 * π, w t * g t = 0 := fun {w} hw h0 => by
    have h := clm_angCoeff (innerSL ℝ f) hw hγ
    rw [h0, map_zero] at h
    have hcomm : ∀ t, ⟪f, rotLp e a hΩ hinv ℝ t f⟫_ℝ = g t := fun t => real_inner_comm _ _
    simp only [angCoeff, innerSL_apply_apply, smul_eq_mul, hcomm] at h
    exact h.symm
  have h0 := eq_zero_of_fourier_real hg (fun k => key (continuous_cos_mul k) (hc k))
    (fun k => key (continuous_sin_mul k) (hs k))
  simp only [g, rotLp_zero] at h0
  exact inner_self_eq_zero.mp h0

/-- **A weakly harmonic function is determined by its (weakly harmonic) Fourier modes.** -/
theorem eq_zero_of_harmonic_modes_eq_zero {v : L2Pair volume Ω}
    (hc : ∀ k : ℕ, (cosCoeff k fun t => rotPair e a hΩ hinv t v).fst = 0)
    (hs : ∀ k : ℕ, (sinCoeff k fun t => rotPair e a hΩ hinv t v).fst = 0) : v.fst = 0 :=
  eq_zero_of_modes_eq_zero e a hΩ hinv
    (fun k => (angCoeff_rotPair_fst e a hΩ hinv (continuous_cos_mul k) v).symm.trans (hc k))
    (fun k => (angCoeff_rotPair_fst e a hΩ hinv (continuous_sin_mul k) v).symm.trans (hs k))

end Uniqueness

end ConicalKahler.Sobolev
