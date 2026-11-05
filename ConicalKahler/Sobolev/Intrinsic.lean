module

public import ConicalKahler.Sobolev.ConeLaplacian

/-!
# The intrinsic `W^{1,2}` norm of the cone metric

The paper (§2.1) asserts that the `W^{1,2}` norms defined by `g` and by the Euclidean metric of the
real coordinates are equivalent. Here this is proved for the pairs `(u, G) ∈ L²(Ω) × L²(Ω; ℝ^d)`
used throughout, reusing the existing definitions:

* the metric `g = productConeMetric β` and its bilinear form `productConeBilin β`;
* the operator `g⁻¹ = coneInvOp β` (`Sobolev.ConeLaplacian`);
* the Riemannian volume `dV_g = productConeVolume β` (`Real.Product`).

## Results

* `productConeBilin_coneInvOp`: `g(g⁻¹ ξ, w) = ⟨ξ, w⟩` on the regular part. So `g⁻¹ ∇u` is the
  **metric gradient** `∇_g u` of `u` (`g(∇_g u, w) = du(w)`).
* `productConeMetric_coneInvOp`: `|∇_g u|²_g = g(g⁻¹ ξ, g⁻¹ ξ) = ⟨g⁻¹ ξ, ξ⟩`.
* `coneVolume_eq`: `dV_g`, transported to `ℝ^d` by the coordinate isometry, is `(∏ β_a) dx`.
* `intrinsicNormSq_eq`: the intrinsic norm
  `‖u‖²_{W^{1,2}_g(Ω)} = ∫_Ω (u² + |∇_g u|²_g) dV_g` equals `(∏ β_a)(‖u‖² + ∫_Ω ⟨A G, G⟩)` with
  `A = g⁻¹ = coneCoeff`.
* `intrinsicNormSq_bounds`: **norm equivalence**
  `(∏ β_a) λ ‖(u, G)‖² ≤ ‖u‖²_{W^{1,2}_g} ≤ (∏ β_a) Λ ‖(u, G)‖²` with `λ = coneLam β`,
  `Λ = coneΛ β`. For `β_a ≤ 1` the lower constant is `∏ β_a` (`intrinsicNormSq_lower_of_le_one`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff ENNReal ComplexConjugate

namespace ConicalKahler.Sobolev

open RealConeModel

/-! ### The metric gradient -/

theorem conj_mul_coneInvFactor (b : ℝ) {w : ℂ} (hw : w ≠ 0) (z : ℂ) :
    conj w * coneInvFactor b w z =
      ((conj w * z).re : ℂ) + ((b⁻¹ ^ 2 * (conj w * z).im : ℝ) : ℂ) * Complex.I := by
  have hn : (Complex.normSq w : ℂ) ≠ 0 := by exact_mod_cast Complex.normSq_eq_zero.not.mpr hw
  have hww : conj w * w = (Complex.normSq w : ℂ) := (Complex.normSq_eq_conj_mul_self).symm
  rw [coneInvFactor, Complex.real_smul, Complex.real_smul, Complex.real_smul]
  calc conj w * (((Complex.normSq w)⁻¹ : ℝ) * (((conj w * z).re : ℝ) * w +
        ((b⁻¹ ^ 2 * (conj w * z).im : ℝ) : ℂ) * (Complex.I * w)))
      = ((Complex.normSq w)⁻¹ : ℝ) * (conj w * w) * (((conj w * z).re : ℝ) +
          ((b⁻¹ ^ 2 * (conj w * z).im : ℝ) : ℂ) * Complex.I) := by ring
    _ = _ := by rw [hww, Complex.ofReal_inv, inv_mul_cancel₀ hn, one_mul]

/-- **`g(g⁻¹ z, y) = ⟨z, y⟩`** on one cone factor at `w ≠ 0`. -/
theorem paperConeBilin_coneInvFactor {b : ℝ} (hb : b ≠ 0) {w : ℂ} (hw : w ≠ 0) (z y : ℂ) :
    paperConeBilin b w (coneInvFactor b w z) y = ⟪z, y⟫_ℝ := by
  have hn : Complex.normSq w ≠ 0 := Complex.normSq_eq_zero.not.mpr hw
  rw [paperConeBilin, conj_mul_coneInvFactor b hw, Complex.inner]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  rw [Complex.normSq_apply] at hn ⊢
  have hn' : w.re ^ 2 + w.im ^ 2 ≠ 0 := by rwa [sq, sq]
  field_simp
  ring

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- **`g⁻¹ ξ` is the metric gradient:** `g(g⁻¹ ξ, w) = ⟨ξ, w⟩` at regular points. -/
theorem productConeBilin_coneInvOp (β : κ → ConeAngle) {p : RealConeModel κ ι}
    (hp : ∀ a, p.cone a ≠ 0) (ξ w : RealConeModel κ ι) :
    productConeBilin β p (coneInvOp β p ξ) w = ⟪ξ, w⟫_ℝ := by
  rw [inner_eq_cone_eucl, productConeBilin]
  simp only [coneInvOp, LinearMap.coe_toContinuousLinearMap', coneInvOpₗ, LinearMap.coe_mk,
    AddHom.coe_mk, cone_ofCones, eucl_ofCones]
  congr 1
  exact Finset.sum_congr rfl fun a _ =>
    paperConeBilin_coneInvFactor (β a).pos.ne' (hp a) _ _

/-- **`|∇_g u|²_g = ⟨g⁻¹ ξ, ξ⟩`** for the metric gradient `g⁻¹ ξ` of the covector `⟨ξ, ·⟩`. -/
theorem productConeMetric_coneInvOp (β : κ → ConeAngle) {p : RealConeModel κ ι}
    (hp : ∀ a, p.cone a ≠ 0) (ξ : RealConeModel κ ι) :
    productConeMetric β p (coneInvOp β p ξ) = ⟪coneInvOp β p ξ, ξ⟫_ℝ := by
  rw [← productConeBilin_self, productConeBilin_coneInvOp β hp, real_inner_comm]

/-! ### The Riemannian volume on `ℝ^d` -/

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The Riemannian volume `dV_g` transported to `ℝ^d` by the coordinates `e`. -/
def coneVolume (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) : Measure 𝔼 :=
  (productConeVolume (ι := ι) β).map (coordIso e)

/-- **`dV_g = (∏ β_a) dx`** in the coordinates of `ℝ^d`. -/
theorem coneVolume_eq (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) :
    coneVolume β e = ENNReal.ofReal (∏ a, (β a).beta) • (volume : Measure 𝔼) := by
  rw [coneVolume, productConeVolume_eq, Measure.map_smul,
    (coordIso e).measurePreserving.map_eq]
  exact (coordIso e).continuous.measurable.aemeasurable

/-- The pointwise intrinsic energy `|∇_g u|²_g` of a Euclidean gradient `G` at `x ∈ ℝ^d`. -/
def coneGradNormSq (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (x G : 𝔼) : ℝ :=
  productConeMetric β ((coordIso e).symm x)
    (coneInvOp β ((coordIso e).symm x) ((coordIso e).symm G))

theorem coneGradNormSq_eq (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) {x : 𝔼}
    (hx : ∀ a, ((coordIso e).symm x).cone a ≠ 0) (G : 𝔼) :
    coneGradNormSq β e x G = ⟪coneCoeffA β e x G, G⟫_ℝ := by
  rw [coneGradNormSq, productConeMetric_coneInvOp β hx]
  simp only [coneCoeffA, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  conv_rhs => rw [← (coordIso e).symm.inner_map_map, LinearIsometryEquiv.symm_apply_apply]

/-- The intrinsic `W^{1,2}` norm squared `∫_Ω (u² + |∇_g u|²_g) dV_g` of `(u, G)`. -/
def intrinsicNormSq (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼}
    (v : L2Pair volume Ω) : ℝ :=
  ∫ x in Ω, (v.fst x ^ 2 + coneGradNormSq β e x (v.snd x)) ∂(coneVolume β e)

variable [NeZero d]

theorem inner_mulOp_le {Ω : Set 𝔼} (c : CoeffField 𝔼 volume) (G : Lp 𝔼 2 (volume.restrict Ω)) :
    ⟪c.mulOp Ω G, G⟫_ℝ ≤ c.Λ * ‖G‖ ^ 2 := by
  rw [CoeffField.norm_sq_eq_integral Ω G, ← integral_const_mul, c.inner_mulOp]
  refine integral_mono_ae ?_ ?_ ?_
  · exact (L2.integrable_inner (c.mulOp Ω G) G).congr (by
      filter_upwards [c.mulOp_ae Ω G] with x hx
      rw [hx])
  · exact ((L2.integrable_inner G G).congr (Eventually.of_forall fun x =>
      real_inner_self_eq_norm_sq (G x))).const_mul _
  · filter_upwards [ae_restrict_of_ae c.bounded] with x hx
    exact hx _

/-- **The intrinsic norm in Euclidean terms:**
`∫_Ω (u² + |∇_g u|²_g) dV_g = (∏ β_a) (‖u‖² + ∫_Ω ⟨g⁻¹ G, G⟩)`. -/
theorem intrinsicNormSq_eq (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼}
    (v : L2Pair volume Ω) :
    intrinsicNormSq β e v =
      (∏ a, (β a).beta) * (‖v.fst‖ ^ 2 + ⟪(coneCoeff β e).mulOp Ω v.snd, v.snd⟫_ℝ) := by
  have hprod : 0 ≤ ∏ a, (β a).beta := Finset.prod_nonneg fun a _ => (β a).pos.le
  rw [intrinsicNormSq, coneVolume_eq, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal hprod, smul_eq_mul]
  congr 1
  have hu : Integrable (fun x => v.fst x ^ 2) (volume.restrict Ω) := (Lp.memLp v.fst).integrable_sq
  have hq : (fun x => coneGradNormSq β e x (v.snd x)) =ᵐ[volume.restrict Ω]
      fun x => ⟪(coneCoeff β e).mulOp Ω v.snd x, v.snd x⟫_ℝ := by
    filter_upwards [ae_restrict_of_ae (ae_regular (ι := ι) e),
      (coneCoeff β e).mulOp_ae Ω v.snd] with x hx h2
    rw [coneGradNormSq_eq β e hx, h2]
    rfl
  have hqi : Integrable (fun x => coneGradNormSq β e x (v.snd x)) (volume.restrict Ω) :=
    (L2.integrable_inner ((coneCoeff β e).mulOp Ω v.snd) v.snd).congr hq.symm
  rw [integral_add hu hqi, integral_congr_ae hq, ← L2.inner_def]
  congr 1
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp [sq])

/-- **Equivalence of the intrinsic and Euclidean `W^{1,2}` norms** (paper, §2.1), with explicit
constants: `(∏ β_a) λ ‖(u, G)‖² ≤ ∫_Ω (u² + |∇_g u|²_g) dV_g ≤ (∏ β_a) Λ ‖(u, G)‖²`. -/
theorem intrinsicNormSq_bounds (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼}
    (v : L2Pair volume Ω) :
    (∏ a, (β a).beta) * coneLam β * ‖v‖ ^ 2 ≤ intrinsicNormSq β e v ∧
      intrinsicNormSq β e v ≤ (∏ a, (β a).beta) * coneΛ β * ‖v‖ ^ 2 := by
  have hprod : 0 ≤ ∏ a, (β a).beta := Finset.prod_nonneg fun a _ => (β a).pos.le
  have hlo := (coneCoeff β e).lam_mul_norm_sq_le Ω v.snd
  have hhi := inner_mulOp_le (coneCoeff β e) v.snd
  have hl1 := coneLam_le_one β
  have hΛ1 := one_le_coneΛ β
  have hl0 := (coneLam_pos β).le
  change coneLam β * ‖v.snd‖ ^ 2 ≤ _ at hlo
  change _ ≤ coneΛ β * ‖v.snd‖ ^ 2 at hhi
  rw [intrinsicNormSq_eq, norm_sq_L2Pair]
  have h1 : 0 ≤ ‖v.fst‖ ^ 2 := sq_nonneg _
  constructor
  · rw [mul_assoc]
    gcongr
    nlinarith
  · rw [mul_assoc]
    gcongr
    nlinarith

/-- For `β_a ≤ 1` (the paper's setting) the lower constant is `∏ β_a`:
`(∏ β_a) ‖(u, G)‖² ≤ ∫_Ω (u² + |∇_g u|²_g) dV_g`. -/
theorem intrinsicNormSq_lower_of_le_one {β : κ → ConeAngle} (hβ : ∀ a, (β a).beta ≤ 1)
    (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼} (v : L2Pair volume Ω) :
    (∏ a, (β a).beta) * ‖v‖ ^ 2 ≤ intrinsicNormSq β e v := by
  have hprod : 0 ≤ ∏ a, (β a).beta := Finset.prod_nonneg fun a _ => (β a).pos.le
  have hlo : ‖v.snd‖ ^ 2 ≤ ⟪(coneCoeff β e).mulOp Ω v.snd, v.snd⟫_ℝ := by
    rw [CoeffField.norm_sq_eq_integral Ω v.snd, (coneCoeff β e).inner_mulOp]
    refine integral_mono_ae ?_ ?_ ?_
    · exact (L2.integrable_inner v.snd v.snd).congr (Eventually.of_forall fun x =>
        real_inner_self_eq_norm_sq (v.snd x))
    · exact (L2.integrable_inner ((coneCoeff β e).mulOp Ω v.snd) v.snd).congr (by
        filter_upwards [(coneCoeff β e).mulOp_ae Ω v.snd] with x hx
        rw [hx])
    · filter_upwards [ae_restrict_of_ae (coneCoeff_coercive_of_le_one hβ e)] with x hx
      exact hx _
  rw [intrinsicNormSq_eq, norm_sq_L2Pair]
  gcongr

end ConicalKahler.Sobolev
