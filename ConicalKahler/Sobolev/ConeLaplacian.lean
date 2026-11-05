module

public import ConicalKahler.Sobolev.Caccioppoli
public import ConicalKahler.Real.Product

/-!
# The Laplacian of the real cone models in divergence form

In the paper's real coordinates the model metric `g = ∑_a (dr_a² + β_a² r_a² dθ_a²) + ds²` is
bounded and measurable. So the cone Laplacian is the divergence-form operator `div(g⁻¹ ∇ ·)`, and
`dV_g = (∏ β_a) dx` is a constant multiple of Lebesgue measure (`productConeVolume_eq`). The weak
equation `∫ ⟨∇u, ∇φ⟩_g dV_g = ∫ f φ dV_g` of the paper (§2.2) is, after dividing by `∏ β_a`,

  `∫ ⟨g⁻¹ ∇u, ∇φ⟩ dx = ∫ f φ dx`,

i.e. `-div(A ∇u) = f` with `A = g⁻¹` (`coneCoeff`).

## Results

* `coneInvFactor`, `inner_coneInvFactor`: on one factor `g⁻¹` is the paper's metric with `β`
  replaced by `1/β` (`paperConeBilin β⁻¹`). `paperConeGram_mul_inv`, `productConeGram_mul_inv`: the
  Gram matrices with angles `β` and `1/β` are inverse to each other.
* `coneInvOp β p`: the operator of `g⁻¹_p` on the real model, with
  `⟨coneInvOp β p v, w⟩ = productConeBilin β⁻¹ p v w`.
* `coneCoeff β e`: the corresponding `CoeffField` on `ℝ^d`, where `e` numbers the real
  coordinates. Ellipticity constants: `λ = (1 + ∑ β_a²)⁻¹`, `Λ = 1 + ∑ β_a⁻²`. For `β_a ≤ 1` one
  can take `λ = 1` (`coneCoeff_coercive_of_le_one`).
* For the cone Laplacian: existence and uniqueness of weak solutions in `W^{1,2}_0(Ω)`
  (`cone_existsUnique_H01`), the Caccioppoli inequality (`cone_caccioppoli`) and the
  Friedrichs–Poincaré inequality (`norm_fst_le_of_mem_H01`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff ENNReal ComplexConjugate

namespace ConicalKahler.Sobolev

open RealConeModel

/-! ### One factor -/

/-- The inverse metric of one cone factor at `w`, as an operator on `ℂ ≅ ℝ²`:
`z ↦ |w|⁻² (Re(w̄ z) w + β⁻² Im(w̄ z) i w)`. -/
def coneInvFactor (b : ℝ) (w z : ℂ) : ℂ :=
  (Complex.normSq w)⁻¹ • ((conj w * z).re • w + (b⁻¹ ^ 2 * (conj w * z).im) • (Complex.I * w))

theorem coneInvFactor_add (b : ℝ) (w z₁ z₂ : ℂ) :
    coneInvFactor b w (z₁ + z₂) = coneInvFactor b w z₁ + coneInvFactor b w z₂ := by
  apply Complex.ext <;> simp [coneInvFactor, mul_add] <;> ring

theorem coneInvFactor_smul (b : ℝ) (w : ℂ) (r : ℝ) (z : ℂ) :
    coneInvFactor b w (r • z) = r • coneInvFactor b w z := by
  apply Complex.ext <;> simp [coneInvFactor] <;> ring

/-- **`g⁻¹` is the paper's metric with angle `1/β`.** -/
theorem inner_coneInvFactor (b : ℝ) (w z y : ℂ) :
    ⟪coneInvFactor b w z, y⟫_ℝ = paperConeBilin b⁻¹ w z y := by
  have h1 : ⟪w, y⟫_ℝ = (conj w * y).re := by rw [Complex.inner]; simp [mul_comm]
  have h2 : ⟪Complex.I * w, y⟫_ℝ = (conj w * y).im := by
    rw [Complex.inner]
    simp only [map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [coneInvFactor, real_inner_smul_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, h1, h2, paperConeBilin, inv_pow, div_eq_inv_mul]
  ring

theorem paperConeBilin_comm (b : ℝ) (w u v : ℂ) : paperConeBilin b w u v = paperConeBilin b w v u := by
  unfold paperConeBilin
  ring

/-- **The Gram matrices of `β` and `1/β` are inverse to each other** at `w ≠ 0`. -/
theorem paperConeGram_mul_inv {b : ℝ} (hb : b ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    paperConeGram b w * paperConeGram b⁻¹ w = 1 := by
  have hn : Complex.normSq w ≠ 0 := Complex.normSq_eq_zero.not.mpr hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [paperConeGram, Matrix.mul_apply, Fin.sum_univ_two, paperConeBilin] <;>
    field_simp <;> rw [Complex.normSq_apply] <;> ring

/-! ### The operator `g⁻¹` on the real model -/

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- The angles `1/β_a`. -/
def invAngles (β : κ → ConeAngle) : κ → ConeAngle :=
  fun a => ⟨(β a).beta⁻¹, inv_pos.mpr (β a).pos⟩

/-- **The inverse metric is the metric with angles `1/β`:** `G(β) G(1/β) = 1` on the regular part. -/
theorem productConeGram_mul_inv (β : κ → ConeAngle) {p : RealConeModel κ ι}
    (hp : ∀ a, p.cone a ≠ 0) : productConeGram β p * productConeGram (invAngles β) p = 1 := by
  rw [productConeGram_eq, productConeGram_eq, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    ← Matrix.blockDiagonal_mul]
  have h : (fun a => paperConeGram (β a).beta (p.cone a) *
      paperConeGram (invAngles β a).beta (p.cone a)) = fun _ => 1 :=
    funext fun a => paperConeGram_mul_inv (β a).pos.ne' (hp a)
  rw [h, show (fun _ : κ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 1 from rfl,
    Matrix.blockDiagonal_one, Matrix.fromBlocks_one]

/-- The real inner product of the model, factor by factor. -/
theorem inner_eq_cone_eucl (p q : RealConeModel κ ι) :
    ⟪p, q⟫_ℝ = ∑ a, ⟪p.cone a, q.cone a⟫_ℝ + ∑ i, p.eucl i * q.eucl i := by
  rw [PiLp.inner_apply, Fintype.sum_sum_type, Fintype.sum_prod_type_right]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_two, Complex.inner]
    simp [cone, mul_comm]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [eucl, mul_comm]

/-- The inverse metric `g⁻¹_p` as a linear map of the real model. -/
def coneInvOpₗ (β : κ → ConeAngle) (p : RealConeModel κ ι) :
    RealConeModel κ ι →ₗ[ℝ] RealConeModel κ ι where
  toFun v := ofCones (fun a => coneInvFactor (β a).beta (p.cone a) (v.cone a)) v.eucl
  map_add' v w := ext_cone_eucl (fun a => by simp [coneInvFactor_add]) fun i => by simp
  map_smul' r v := ext_cone_eucl (fun a => by
      simp only [cone_ofCones, cone_smul, RingHom.id_apply]
      rw [← Complex.real_smul, coneInvFactor_smul, Complex.real_smul]) fun i => by simp

/-- **The inverse metric `g⁻¹_p`** as an operator on the real model. -/
def coneInvOp (β : κ → ConeAngle) (p : RealConeModel κ ι) :
    RealConeModel κ ι →L[ℝ] RealConeModel κ ι :=
  LinearMap.toContinuousLinearMap (coneInvOpₗ β p)

theorem inner_coneInvOp (β : κ → ConeAngle) (p v w : RealConeModel κ ι) :
    ⟪coneInvOp β p v, w⟫_ℝ = productConeBilin (invAngles β) p v w := by
  rw [inner_eq_cone_eucl, productConeBilin]
  simp only [coneInvOp, LinearMap.coe_toContinuousLinearMap', coneInvOpₗ, LinearMap.coe_mk,
    AddHom.coe_mk, cone_ofCones, eucl_ofCones, inner_coneInvFactor]
  rfl

/-! ### The coefficient field on `ℝ^d` -/

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The real coordinates of the model, numbered by `e`, as `ℝ^d`. -/
def coordIso (e : RealConeIndex κ ι ≃ Fin d) : RealConeModel κ ι ≃ₗᵢ[ℝ] 𝔼 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

/-- `g⁻¹` transported to `ℝ^d`. -/
def coneCoeffA (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (x : 𝔼) : 𝔼 →L[ℝ] 𝔼 :=
  (coordIso e).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    coneInvOp β ((coordIso e).symm x) ∘L
      (coordIso e).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem inner_coneCoeffA (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (x v w : 𝔼) :
    ⟪coneCoeffA β e x v, w⟫_ℝ =
      productConeBilin (invAngles β) ((coordIso e).symm x) ((coordIso e).symm v)
        ((coordIso e).symm w) := by
  simp only [coneCoeffA, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  conv_lhs => rw [← (coordIso e).apply_symm_apply w]
  rw [LinearIsometryEquiv.inner_map_map, inner_coneInvOp]

theorem measurable_paperConeBilin_comp {f : 𝔼 → ℂ} (hf : Continuous f) (b : ℝ) (u v : ℂ) :
    Measurable fun x => paperConeBilin b (f x) u v := by
  unfold paperConeBilin
  refine Measurable.div ?_ ?_
  · exact (((Complex.continuous_re.comp ((Complex.continuous_conj.comp hf).mul continuous_const)).mul
      (Complex.continuous_re.comp ((Complex.continuous_conj.comp hf).mul continuous_const))).add
      (continuous_const.mul ((Complex.continuous_im.comp ((Complex.continuous_conj.comp hf).mul
        continuous_const)).mul (Complex.continuous_im.comp ((Complex.continuous_conj.comp hf).mul
          continuous_const))))).measurable
  · exact (Complex.continuous_normSq.comp hf).measurable

theorem measurable_inner_coneCoeffA (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)
    (v w : 𝔼) : Measurable fun x => ⟪coneCoeffA β e x v, w⟫_ℝ := by
  simp only [inner_coneCoeffA, productConeBilin]
  refine (Finset.measurable_sum _ fun a _ => ?_).add measurable_const
  exact measurable_paperConeBilin_comp
    ((continuous_cone a).comp (coordIso e).symm.continuous) _ _ _

theorem coneCoeffA_symm (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (x v w : 𝔼) :
    ⟪coneCoeffA β e x v, w⟫_ℝ = ⟪v, coneCoeffA β e x w⟫_ℝ := by
  rw [real_inner_comm (coneCoeffA β e x w) v, inner_coneCoeffA, inner_coneCoeffA, productConeBilin,
    productConeBilin]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => paperConeBilin_comm _ _ _ _
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The singular set is null in `ℝ^d` as well. -/
theorem ae_regular (e : RealConeIndex κ ι ≃ Fin d) :
    ∀ᵐ x : 𝔼, ∀ a, ((coordIso e).symm x).cone a ≠ 0 :=
  ((coordIso e).symm.measurePreserving).quasiMeasurePreserving.ae
    (ae_all_iff.mpr (ae_cone_ne_zero (ι := ι)))

theorem quadratic_coneCoeffA (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (x v : 𝔼) :
    ⟪coneCoeffA β e x v, v⟫_ℝ =
      productConeMetric (invAngles β) ((coordIso e).symm x) ((coordIso e).symm v) := by
  rw [inner_coneCoeffA, productConeBilin_self]

/-- The ellipticity constant `(1 + ∑ β_a²)⁻¹`. -/
def coneLam (β : κ → ConeAngle) : ℝ := (1 + ∑ a, (β a).beta ^ 2)⁻¹

/-- The upper constant `1 + ∑ β_a⁻²`. -/
def coneΛ (β : κ → ConeAngle) : ℝ := 1 + ∑ a, (β a).beta⁻¹ ^ 2

theorem coneLam_pos (β : κ → ConeAngle) : 0 < coneLam β :=
  inv_pos.mpr (by positivity)

theorem coneLam_le_one (β : κ → ConeAngle) : coneLam β ≤ 1 :=
  inv_le_one_of_one_le₀ (by
    have : 0 ≤ ∑ a, (β a).beta ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
    linarith)

theorem one_le_coneΛ (β : κ → ConeAngle) : 1 ≤ coneΛ β := by
  have : 0 ≤ ∑ a, (β a).beta⁻¹ ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  unfold coneΛ
  linarith

theorem coneLam_le (β : κ → ConeAngle) (a : κ) :
    coneLam β ≤ min 1 ((invAngles β a).beta ^ 2) := by
  refine le_min (coneLam_le_one β) ?_
  have hb := (β a).pos
  have hsum : (β a).beta ^ 2 ≤ 1 + ∑ c, (β c).beta ^ 2 := by
    have := Finset.single_le_sum (f := fun c => (β c).beta ^ 2) (fun c _ => sq_nonneg _)
      (Finset.mem_univ a)
    linarith
  calc coneLam β ≤ ((β a).beta ^ 2)⁻¹ := inv_anti₀ (by positivity) hsum
    _ = (invAngles β a).beta ^ 2 := by simp [invAngles, inv_pow]

theorem le_coneΛ (β : κ → ConeAngle) (a : κ) :
    max 1 ((invAngles β a).beta ^ 2) ≤ coneΛ β := by
  refine max_le (one_le_coneΛ β) ?_
  have := Finset.single_le_sum (f := fun c => (β c).beta⁻¹ ^ 2) (fun c _ => sq_nonneg _)
    (Finset.mem_univ a)
  simp only [invAngles, coneΛ]
  linarith

/-- **The cone Laplacian as a coefficient field**: `A = g⁻¹` in the real coordinates numbered by
`e`, with `λ = (1 + ∑ β_a²)⁻¹` and `Λ = 1 + ∑ β_a⁻²`. -/
def coneCoeff (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) : CoeffField 𝔼 volume where
  A := coneCoeffA β e
  measurable_inner := measurable_inner_coneCoeffA β e
  symm := coneCoeffA_symm β e
  lam := coneLam β
  Λ := coneΛ β
  lam_pos := coneLam_pos β
  lam_le := (coneLam_le_one β).trans (one_le_coneΛ β)
  coercive := by
    filter_upwards [ae_regular (ι := ι) e] with x hx v
    rw [quadratic_coneCoeffA, ← (coordIso e).symm.norm_map v]
    exact (productConeMetric_bounds (coneLam_le_one β) (coneLam_le β) (one_le_coneΛ β)
      (le_coneΛ β) hx _).1
  bounded := by
    filter_upwards [ae_regular (ι := ι) e] with x hx v
    rw [quadratic_coneCoeffA, ← (coordIso e).symm.norm_map v]
    exact (productConeMetric_bounds (coneLam_le_one β) (coneLam_le β) (one_le_coneΛ β)
      (le_coneΛ β) hx _).2

/-- **The paper's setting `β_a ≤ 1`: `⟨g⁻¹ v, v⟩ ≥ |v|²`** almost everywhere. -/
theorem coneCoeff_coercive_of_le_one {β : κ → ConeAngle} (hβ : ∀ a, (β a).beta ≤ 1)
    (e : RealConeIndex κ ι ≃ Fin d) :
    ∀ᵐ x : 𝔼, ∀ v, ‖v‖ ^ 2 ≤ ⟪(coneCoeff β e).A x v, v⟫_ℝ := by
  filter_upwards [ae_regular (ι := ι) e] with x hx v
  rw [show (coneCoeff β e).A = coneCoeffA β e from rfl, quadratic_coneCoeffA,
    ← (coordIso e).symm.norm_map v]
  have h := (productConeMetric_bounds (β := invAngles β) (b := 1) (B := coneΛ β) le_rfl
    (fun a => le_min le_rfl ?_) (one_le_coneΛ β) (le_coneΛ β) hx ((coordIso e).symm v)).1
  · simpa using h
  · have hb := (β a).pos
    simp only [invAngles]
    rw [inv_pow]
    exact one_le_inv₀ (by positivity) |>.mpr (by nlinarith [hβ a])

/-! ### The cone Laplacian: existence, uniqueness and Caccioppoli -/

/-- **Existence and uniqueness for the cone Laplacian.** On a bounded `Ω ⊆ ℝ^d` and for every
`f ∈ L²(Ω)`, there is exactly one `u ∈ W^{1,2}_0(Ω)` with `∫ ⟨g⁻¹ ∇u, ∇φ⟩ = ∫ f φ` for all test
functions `φ`. -/
theorem cone_existsUnique_H01 [NeZero d] (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)
    {Ω : Set 𝔼} {x₀ : 𝔼} {R : ℝ} (hR : 0 ≤ R) (hΩ : Ω ⊆ Metric.closedBall x₀ R)
    (f : Lp ℝ 2 (volume.restrict Ω)) :
    ∃! v : H01 volume Ω, (coneCoeff β e).IsWeakSolution f v :=
  (coneCoeff β e).existsUnique_H01_isWeakSolution hR hΩ f

/-- **Caccioppoli inequality for the cone Laplacian** (paper, Lemma 2.3):
`∫ η² |∇u|²_g ≤ ∫ η² f² + ∫ (η² + 4Λ |∇η|²) u²`, where `|∇u|²_g = ⟨g⁻¹ ∇u, ∇u⟩`. -/
theorem cone_caccioppoli [NeZero d] (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)
    {Ω : Set 𝔼} (hΩ : IsOpen Ω) {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω}
    (hv : (coneCoeff β e).IsWeakSolution f v) {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) :
    ∫ x in Ω, η x ^ 2 * ⟪coneCoeffA β e x (v.snd x), v.snd x⟫_ℝ ≤
      (∫ x in Ω, η x ^ 2 * f x ^ 2) +
        ∫ x in Ω, (η x ^ 2 + 4 * coneΛ β * ‖gradient η x‖ ^ 2) * v.fst x ^ 2 :=
  caccioppoli (coneCoeff β e) hΩ hv hη

end ConicalKahler.Sobolev
