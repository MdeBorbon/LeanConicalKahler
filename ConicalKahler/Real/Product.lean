module

public import ConicalKahler.Real.ConeDistance
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Products of two-dimensional cones and a Euclidean factor, in real coordinates

The paper's model space is `C(S¹_{2πβ_1}) × ⋯ × C(S¹_{2πβ_n}) × ℝ^{m-2n}` with metric

  `g = ∑_a (dr_a² + β_a² r_a² dθ_a²) + ds²`.

We index the cone factors by a finite type `κ` (the paper's `Fin n`) and the Euclidean coordinates
by a finite type `ι` (the paper's `Fin (m - 2n)`). The **real coordinate space** is
`RealConeModel κ ι = ℝ^{(Fin 2 × κ) ⊕ ι}`, with coordinates `x_a, y_a` (so that
`x_a + i y_a = r_a e^{iθ_a}`) and `s_i`. Its dimension is `2 #κ + #ι`, which can be odd.

## Main results

* `productConeMetric`: the tensor `g` at points of the regular part (`r_a ≠ 0` for all `a`).
  `productConeMetric_bounds`, `productConeMetric_bounds_of_le_one`: uniform equivalence with the
  Euclidean metric. For `β_a ≤ 1`: `b² |v|² ≤ g(v) ≤ |v|²` whenever `b ≤ β_a`.
* `productConeGram_eq`: the Gram matrix in the real coordinates is block diagonal, with the
  `2 × 2` cone blocks `paperConeGram` and the identity on `ℝ^ι`.
  `det_productConeGram`: `det g = ∏_a β_a²`.
* `productConeVolume_eq`: the Riemannian volume measure (Lebesgue measure with density `√det g`) is
  `(∏_a β_a) ·` Lebesgue measure. The singular set `{r_a = 0}` is Lebesgue-null.
  `map_ofLp_productConeVolume`: the same in the coordinates `ℝ^{(Fin 2 × κ) ⊕ ι}`, where Lebesgue
  measure is the product measure.
* `ConeProduct β ι`: the real coordinate space with the product distance
  `d = (∑_a d_a² + ∑_i |s_i - t_i|²)^{1/2}`. It is built as the `L²` product `PiLp 2` of the factor
  metric spaces (`ConeTwo`, `ℝ`), so the triangle inequality comes from Mathlib.
  `ConeProduct.dist_bounds_of_le_one`: `b |p - q| ≤ d(p, q) ≤ |p - q|` for `b ≤ β_a ≤ 1`;
  `ConeProduct.dist_bounds_uniform`: explicit constants for arbitrary angles;
  `ConeProduct.ball_subset_of_le_one`: ball inclusions;
  `ConeProduct.dist_of_cone_eq_zero`: distances from the vertex stratum `{r_a = 0 ∀ a}` are
  Euclidean, so balls centred there are Euclidean balls;
  `ConeProduct.dist_smul`: the dilation `p ↦ t p` scales distances by `t`;
  `ConeProduct.homeomorph`: the cone distance induces the Euclidean topology.

As for one factor, `ConeProduct` carries a formally defined distance. It is not yet proved to be the
length distance of `g` (`ConicalKahler.Real.ConeDistance`).
-/

@[expose] public section

open scoped Real
open MeasureTheory

namespace ConicalKahler

/-- The index type of the real coordinates: `inl (0, a) = x_a`, `inl (1, a) = y_a`, `inr i = s_i`. -/
abbrev RealConeIndex (κ ι : Type) : Type := (Fin 2 × κ) ⊕ ι

/-- **The real coordinate space** of the product of the cones indexed by `κ` and `ℝ^ι`. -/
abbrev RealConeModel (κ ι : Type) : Type := EuclideanSpace ℝ (RealConeIndex κ ι)

variable {κ ι : Type}

namespace RealConeModel

/-- The `a`-th cone component `x_a + i y_a = r_a e^{iθ_a}` of a point. -/
def cone (p : RealConeModel κ ι) (a : κ) : ℂ :=
  ⟨p (Sum.inl (0, a)), p (Sum.inl (1, a))⟩

/-- The Euclidean coordinates `s_i` of a point. -/
def eucl (p : RealConeModel κ ι) (i : ι) : ℝ :=
  p (Sum.inr i)

/-- The point with cone components `w_a` and Euclidean coordinates `s_i`. -/
def ofCones (w : κ → ℂ) (s : ι → ℝ) : RealConeModel κ ι :=
  WithLp.toLp 2 fun k => match k with
    | .inl (i, a) => ![(w a).re, (w a).im] i
    | .inr j => s j

@[simp] theorem cone_ofCones (w : κ → ℂ) (s : ι → ℝ) (a : κ) : (ofCones w s).cone a = w a := by
  apply Complex.ext <;> simp [cone, ofCones]

@[simp] theorem eucl_ofCones (w : κ → ℂ) (s : ι → ℝ) (i : ι) : (ofCones w s).eucl i = s i := by
  simp [eucl, ofCones]

theorem ofCones_cone_eucl (p : RealConeModel κ ι) : ofCones p.cone p.eucl = p := by
  refine PiLp.ext fun k => ?_
  rcases k with ⟨i, a⟩ | j
  · fin_cases i <;> simp [ofCones, cone]
  · simp [ofCones, eucl]

theorem ext_cone_eucl {p q : RealConeModel κ ι} (hc : ∀ a, p.cone a = q.cone a)
    (he : ∀ i, p.eucl i = q.eucl i) : p = q := by
  rw [← ofCones_cone_eucl p, ← ofCones_cone_eucl q, funext hc, funext he]

@[simp] theorem cone_zero (a : κ) : (0 : RealConeModel κ ι).cone a = 0 := by
  apply Complex.ext <;> simp [cone]

@[simp] theorem cone_add (p q : RealConeModel κ ι) (a : κ) :
    (p + q).cone a = p.cone a + q.cone a := by
  apply Complex.ext <;> simp [cone]

@[simp] theorem eucl_add (p q : RealConeModel κ ι) (i : ι) :
    (p + q).eucl i = p.eucl i + q.eucl i := by
  simp [eucl]

theorem continuous_cone (a : κ) : Continuous fun p : RealConeModel κ ι => p.cone a := by
  have h : (fun p : RealConeModel κ ι => p.cone a) = fun p =>
      ((p (Sum.inl (0, a)) : ℝ) : ℂ) + ((p (Sum.inl (1, a)) : ℝ) : ℂ) * Complex.I := by
    funext p
    apply Complex.ext <;> simp [cone]
  rw [h]
  exact (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ _)).add
    ((Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ _)).mul continuous_const)

@[simp] theorem cone_sub (p q : RealConeModel κ ι) (a : κ) :
    (p - q).cone a = p.cone a - q.cone a := by
  apply Complex.ext <;> simp [cone]

@[simp] theorem eucl_sub (p q : RealConeModel κ ι) (i : ι) :
    (p - q).eucl i = p.eucl i - q.eucl i := by
  simp [eucl]

@[simp] theorem cone_smul (t : ℝ) (p : RealConeModel κ ι) (a : κ) :
    (t • p).cone a = (t : ℂ) * p.cone a := by
  apply Complex.ext <;> simp [cone]

@[simp] theorem eucl_smul (t : ℝ) (p : RealConeModel κ ι) (i : ι) :
    (t • p).eucl i = t * p.eucl i := by
  simp [eucl]

variable [Fintype κ] [Fintype ι]

/-- `|p|² = ∑_a |p_a|² + ∑_i s_i²`. -/
theorem norm_sq_eq (p : RealConeModel κ ι) :
    ‖p‖ ^ 2 = ∑ a, ‖p.cone a‖ ^ 2 + ∑ i, p.eucl i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Fintype.sum_prod_type_right]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, cone, eucl, Complex.sq_norm,
    Complex.normSq_mk]
  ring_nf

theorem norm_sub_sq_eq (p q : RealConeModel κ ι) :
    ‖p - q‖ ^ 2 = ∑ a, ‖p.cone a - q.cone a‖ ^ 2 + ∑ i, (p.eucl i - q.eucl i) ^ 2 := by
  rw [norm_sq_eq]
  simp

variable [DecidableEq κ] [DecidableEq ι]

omit [Fintype κ] [Fintype ι] in
theorem cone_single_inl (i : Fin 2) (a' a : κ) :
    RealConeModel.cone (κ := κ) (ι := ι) (EuclideanSpace.single (Sum.inl (i, a')) (1 : ℝ)) a =
      if a' = a then ![(1 : ℂ), Complex.I] i else 0 := by
  by_cases h : a' = a
  · subst h
    rw [ite_eq_left rfl]
    fin_cases i <;> apply Complex.ext <;> simp [cone]
  · rw [ite_eq_right h]
    apply Complex.ext <;> simp [cone, Ne.symm h]

omit [Fintype κ] [Fintype ι] in
theorem cone_single_inr (j : ι) (a : κ) :
    RealConeModel.cone (κ := κ) (EuclideanSpace.single (Sum.inr j) (1 : ℝ)) a = 0 := by
  apply Complex.ext <;> simp [cone]

omit [Fintype κ] [Fintype ι] in
theorem eucl_single_inl (i : Fin 2) (a : κ) (j : ι) :
    RealConeModel.eucl (EuclideanSpace.single (Sum.inl (i, a)) (1 : ℝ)) j = 0 := by
  simp [eucl]

omit [Fintype κ] [Fintype ι] in
theorem eucl_single_inr (j' j : ι) :
    RealConeModel.eucl (κ := κ) (EuclideanSpace.single (Sum.inr j') (1 : ℝ)) j =
      if j' = j then 1 else 0 := by
  simp [eucl, eq_comm]

end RealConeModel

open RealConeModel

variable [Fintype κ] [Fintype ι]

/-! ### The metric tensor and its uniform equivalence with the Euclidean metric -/

/-- **The paper's model metric** `g = ∑_a (dr_a² + β_a² r_a² dθ_a²) + ds²` in the real coordinates,
at `p` (with `r_a ≠ 0`) on the tangent vector `v`. -/
noncomputable def productConeMetric (β : κ → ConeAngle) (p v : RealConeModel κ ι) : ℝ :=
  ∑ a, paperConeMetric (β a).beta (p.cone a) (v.cone a) + ∑ i, v.eucl i ^ 2

/-- **Uniform equivalence, arbitrary angles:** if `b ≤ min(1, β_a²)` and `max(1, β_a²) ≤ B` for
all `a`, and `b ≤ 1 ≤ B`, then `b |v|² ≤ g(v) ≤ B |v|²` on the regular part. -/
theorem productConeMetric_bounds {β : κ → ConeAngle} {b B : ℝ} (hb1 : b ≤ 1)
    (hb : ∀ a, b ≤ min 1 ((β a).beta ^ 2)) (hB1 : 1 ≤ B) (hB : ∀ a, max 1 ((β a).beta ^ 2) ≤ B)
    {p : RealConeModel κ ι} (hp : ∀ a, p.cone a ≠ 0) (v : RealConeModel κ ι) :
    b * ‖v‖ ^ 2 ≤ productConeMetric β p v ∧ productConeMetric β p v ≤ B * ‖v‖ ^ 2 := by
  rw [norm_sq_eq, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, productConeMetric]
  constructor
  · refine add_le_add (Finset.sum_le_sum fun a _ => ?_) (Finset.sum_le_sum fun i _ => ?_)
    · have h := (paperConeMetric_bounds (β a).beta (hp a) (v.cone a)).1
      rw [Complex.normSq_eq_norm_sq] at h
      exact (mul_le_mul_of_nonneg_right (hb a) (sq_nonneg _)).trans h
    · exact mul_le_of_le_one_left (sq_nonneg _) hb1
  · refine add_le_add (Finset.sum_le_sum fun a _ => ?_) (Finset.sum_le_sum fun i _ => ?_)
    · have h := (paperConeMetric_bounds (β a).beta (hp a) (v.cone a)).2
      rw [Complex.normSq_eq_norm_sq] at h
      exact h.trans (mul_le_mul_of_nonneg_right (hB a) (sq_nonneg _))
    · exact le_mul_of_one_le_left (sq_nonneg _) hB1

/-- **Uniform equivalence, `β_a ≤ 1`** (the paper's setting): if `0 ≤ b ≤ β_a ≤ 1` for all `a` and
`b ≤ 1`, then `b² |v|² ≤ g(v) ≤ |v|²` on the regular part. -/
theorem productConeMetric_bounds_of_le_one {β : κ → ConeAngle} (hβ1 : ∀ a, (β a).beta ≤ 1)
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hb : ∀ a, b ≤ (β a).beta) {p : RealConeModel κ ι}
    (hp : ∀ a, p.cone a ≠ 0) (v : RealConeModel κ ι) :
    b ^ 2 * ‖v‖ ^ 2 ≤ productConeMetric β p v ∧ productConeMetric β p v ≤ ‖v‖ ^ 2 := by
  have h := productConeMetric_bounds (β := β) (b := b ^ 2) (B := 1) (by nlinarith)
    (fun a => le_min (by nlinarith) (pow_le_pow_left₀ hb0 (hb a) 2)) le_rfl
    (fun a => max_le le_rfl (by nlinarith [(β a).pos, hβ1 a])) hp v
  rwa [one_mul] at h

/-! ### Gram matrix, volume density and Lebesgue measure -/

/-- The metric as a symmetric bilinear form. -/
noncomputable def productConeBilin (β : κ → ConeAngle) (p u v : RealConeModel κ ι) : ℝ :=
  ∑ a, paperConeBilin (β a).beta (p.cone a) (u.cone a) (v.cone a) + ∑ i, u.eucl i * v.eucl i

theorem productConeBilin_self (β : κ → ConeAngle) (p v : RealConeModel κ ι) :
    productConeBilin β p v v = productConeMetric β p v := by
  simp [productConeBilin, productConeMetric, paperConeBilin_self, sq]

theorem paperConeBilin_zero_left (β : ℝ) (w v : ℂ) : paperConeBilin β w 0 v = 0 := by
  simp [paperConeBilin]

theorem paperConeBilin_zero_right (β : ℝ) (w u : ℂ) : paperConeBilin β w u 0 = 0 := by
  simp [paperConeBilin]

section Gram

variable [DecidableEq κ] [DecidableEq ι]

/-- **The Gram matrix** `g(e_k, e_l)` of the metric in the real coordinates. -/
noncomputable def productConeGram (β : κ → ConeAngle) (p : RealConeModel κ ι) :
    Matrix (RealConeIndex κ ι) (RealConeIndex κ ι) ℝ :=
  Matrix.of fun k l =>
    productConeBilin β p (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)

/-- **The Gram matrix is block diagonal:** a `2 × 2` block `paperConeGram β_a` for each cone factor
and the identity on the Euclidean factor. -/
theorem productConeGram_eq (β : κ → ConeAngle) (p : RealConeModel κ ι) :
    productConeGram β p =
      Matrix.fromBlocks (Matrix.blockDiagonal fun a => paperConeGram (β a).beta (p.cone a)) 0 0 1 := by
  ext k l
  rcases k with ⟨i, a⟩ | i <;> rcases l with ⟨j, b⟩ | j
  · simp only [productConeGram, Matrix.of_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.blockDiagonal_apply, productConeBilin, cone_single_inl, eucl_single_inl, mul_zero,
      Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single a
      (fun c _ hc => by rw [ite_eq_right (Ne.symm hc), paperConeBilin_zero_left]) (by simp),
      ite_eq_left rfl]
    by_cases hab : a = b
    · subst hab
      rw [ite_eq_left rfl, ite_eq_left rfl]
      fin_cases i <;> fin_cases j <;> simp [paperConeGram]
    · rw [ite_eq_right (Ne.symm hab), ite_eq_right hab, paperConeBilin_zero_right]
  · simp [productConeGram, productConeBilin, cone_single_inr, eucl_single_inl,
      paperConeBilin_zero_right]
  · simp [productConeGram, productConeBilin, cone_single_inr, eucl_single_inl,
      paperConeBilin_zero_left]
  · simp only [productConeGram, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, productConeBilin,
      cone_single_inr, paperConeBilin_zero_left, Finset.sum_const_zero, zero_add, eucl_single_inr,
      Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]

/-- **`det g = ∏_a β_a²`** at every point of the regular part. -/
theorem det_productConeGram (β : κ → ConeAngle) {p : RealConeModel κ ι}
    (hp : ∀ a, p.cone a ≠ 0) : (productConeGram β p).det = ∏ a, (β a).beta ^ 2 := by
  rw [productConeGram_eq, Matrix.det_fromBlocks_zero₂₁, Matrix.det_blockDiagonal, Matrix.det_one,
    mul_one]
  exact Finset.prod_congr rfl fun a _ => det_paperConeGram _ (hp a)

/-- The Riemannian volume density: `√det g = ∏_a β_a`. -/
theorem sqrt_det_productConeGram (β : κ → ConeAngle) {p : RealConeModel κ ι}
    (hp : ∀ a, p.cone a ≠ 0) : √(productConeGram β p).det = ∏ a, (β a).beta := by
  rw [det_productConeGram β hp, Finset.prod_pow,
    Real.sqrt_sq (Finset.prod_nonneg fun a _ => (β a).pos.le)]

/-- The singular set `{r_a = 0}` of each cone factor is Lebesgue-null. -/
theorem ae_cone_ne_zero (a : κ) : ∀ᵐ p : RealConeModel κ ι, p.cone a ≠ 0 := by
  let L : RealConeModel κ ι →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Sum.inl (0, a) : RealConeIndex κ ι)).toLinearMap
  have hs : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single (Sum.inl (0, a) : RealConeIndex κ ι) (1 : ℝ) ∈
        LinearMap.ker L := h ▸ Submodule.mem_top
    simp [L] at hmem
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) (Measure.addHaar_submodule volume _ hs)
  simp only [Set.mem_ofPred_eq, not_not] at hp
  have h0 := congrArg Complex.re hp
  simp only [cone, Complex.zero_re] at h0
  simpa [L] using h0

/-- **The Riemannian volume measure** of `g`: Lebesgue measure in the real coordinates with
density `√det g`. -/
noncomputable def productConeVolume (β : κ → ConeAngle) : Measure (RealConeModel κ ι) :=
  volume.withDensity fun p => ENNReal.ofReal √(productConeGram β p).det

/-- **The Riemannian volume is `∏_a β_a` times Lebesgue measure.** -/
theorem productConeVolume_eq (β : κ → ConeAngle) :
    productConeVolume (ι := ι) β = ENNReal.ofReal (∏ a, (β a).beta) • volume := by
  rw [productConeVolume, ← withDensity_const]
  apply withDensity_congr_ae
  filter_upwards [ae_all_iff.mpr (ae_cone_ne_zero (ι := ι))] with p hp
  rw [sqrt_det_productConeGram β hp]

/-- The same statement in the coordinates `ℝ^{(Fin 2 × κ) ⊕ ι}`, where Lebesgue measure is the
product measure `volume = Measure.pi fun _ => volume`. -/
theorem map_ofLp_productConeVolume (β : κ → ConeAngle) :
    (productConeVolume (ι := ι) β).map WithLp.ofLp =
      ENNReal.ofReal (∏ a, (β a).beta) • (volume : Measure (RealConeIndex κ ι → ℝ)) := by
  rw [productConeVolume_eq, Measure.map_smul, (PiLp.volume_preserving_ofLp _).map_eq]
  exact (PiLp.volume_preserving_ofLp _).measurable.aemeasurable

end Gram

/-! ### The product distance -/

/-- The factors of the product: the cone `C(S¹_{2πβ_a})` for `a : κ`, the line `ℝ` for `i : ι`. -/
def ConeFactor (β : κ → ConeAngle) (ι : Type) : κ ⊕ ι → Type
  | .inl a => ConeTwo (β a)
  | .inr _ => ℝ

noncomputable instance instMetricSpaceConeFactor (β : κ → ConeAngle) :
    (k : κ ⊕ ι) → MetricSpace (ConeFactor β ι k)
  | .inl a => inferInstanceAs (MetricSpace (ConeTwo (β a)))
  | .inr _ => inferInstanceAs (MetricSpace ℝ)

/-- A point of the real model as a point of the `L²` product of the factors. -/
def toFactors (β : κ → ConeAngle) (p : RealConeModel κ ι) : PiLp 2 (ConeFactor β ι) :=
  WithLp.toLp 2 fun k => match k with
    | .inl a => (ConeTwo.mk (p.cone a) : ConeTwo (β a))
    | .inr i => (p.eucl i : ℝ)

omit [Fintype κ] [Fintype ι] in
theorem toFactors_injective (β : κ → ConeAngle) :
    Function.Injective (toFactors (ι := ι) β) := by
  intro p q h
  refine ext_cone_eucl (fun a => ?_) (fun i => ?_)
  · exact congrArg (fun x : PiLp 2 (ConeFactor β ι) => WithLp.ofLp x (Sum.inl a)) h
  · exact congrArg (fun x : PiLp 2 (ConeFactor β ι) => WithLp.ofLp x (Sum.inr i)) h

/-- **The product cone** `∏_a C(S¹_{2πβ_a}) × ℝ^ι` in the paper's real coordinates, with the
product distance. A type synonym of `RealConeModel κ ι`, which keeps its Euclidean metric. -/
def ConeProduct (_β : κ → ConeAngle) (ι : Type) : Type := RealConeModel κ ι

namespace ConeProduct

variable {β : κ → ConeAngle}

/-- The point of the product cone with real coordinates `p`. -/
def mk (p : RealConeModel κ ι) : ConeProduct β ι := p

/-- The real coordinates of a point. -/
def coord (x : ConeProduct β ι) : RealConeModel κ ι := x

omit [Fintype κ] [Fintype ι] in
@[simp] theorem coord_mk (p : RealConeModel κ ι) : coord (mk p : ConeProduct β ι) = p := rfl

noncomputable instance (β : κ → ConeAngle) : MetricSpace (ConeProduct β ι) :=
  MetricSpace.induced (fun x => toFactors β (coord x)) (fun _ _ h => toFactors_injective β h)
    inferInstance

/-- **The product distance:** `d(p, q)² = ∑_a d_{β_a}(p_a, q_a)² + ∑_i (s_i - t_i)²`. -/
theorem dist_mk (p q : RealConeModel κ ι) :
    dist (mk p : ConeProduct β ι) (mk q) =
      √(∑ a, coneDist (β a).beta (p.cone a) (q.cone a) ^ 2 + ∑ i, (p.eucl i - q.eucl i) ^ 2) := by
  change dist (toFactors β p) (toFactors β q) = _
  rw [PiLp.dist_eq_sum (by norm_num : 0 < (2 : ENNReal).toReal), ENNReal.toReal_ofNat,
    ← Real.sqrt_eq_rpow, Fintype.sum_sum_type]
  congr 2
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Real.rpow_two]
    rfl
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.rpow_two]
    change dist (p.eucl i) (q.eucl i) ^ 2 = _
    rw [Real.dist_eq, sq_abs]

/-- **Comparison with the Euclidean distance** from factorwise bounds `b ≤ 1 ≤ B`. -/
theorem dist_bounds {b B : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hB1 : 1 ≤ B)
    (hfac : ∀ a (z w : ℂ), b * ‖z - w‖ ≤ coneDist (β a).beta z w ∧
      coneDist (β a).beta z w ≤ B * ‖z - w‖)
    (p q : RealConeModel κ ι) :
    b * ‖p - q‖ ≤ dist (mk p : ConeProduct β ι) (mk q) ∧
      dist (mk p : ConeProduct β ι) (mk q) ≤ B * ‖p - q‖ := by
  rw [dist_mk, ← Real.sqrt_sq (norm_nonneg (p - q)), norm_sub_sq_eq]
  set D := ∑ a, coneDist (β a).beta (p.cone a) (q.cone a) ^ 2
  set E := ∑ a, ‖p.cone a - q.cone a‖ ^ 2
  set S := ∑ i, (p.eucl i - q.eucl i) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hlow : b ^ 2 * (E + S) ≤ D + S := by
    have h1 : b ^ 2 * E ≤ D := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (hfac a _ _).1 2
    have h2 : b ^ 2 * S ≤ S := mul_le_of_le_one_left hS (by nlinarith)
    linarith
  have hup : D + S ≤ B ^ 2 * (E + S) := by
    have h1 : D ≤ B ^ 2 * E := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (coneDist_nonneg _ _ _) (hfac a _ _).2 2
    have h2 : S ≤ B ^ 2 * S := le_mul_of_one_le_left hS (by nlinarith)
    linarith
  constructor
  · calc b * √(E + S) = √(b ^ 2 * (E + S)) := by
          rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb0]
      _ ≤ √(D + S) := Real.sqrt_le_sqrt hlow
  · calc √(D + S) ≤ √(B ^ 2 * (E + S)) := Real.sqrt_le_sqrt hup
      _ = B * √(E + S) := by rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq (by linarith)]

/-- **Comparison, `β_a ≤ 1`** (the paper's setting): `b |p - q| ≤ d(p, q) ≤ |p - q|` whenever
`0 ≤ b ≤ 1` and `b ≤ β_a` for all `a`. -/
theorem dist_bounds_of_le_one (hβ1 : ∀ a, (β a).beta ≤ 1) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hb : ∀ a, b ≤ (β a).beta) (p q : RealConeModel κ ι) :
    b * ‖p - q‖ ≤ dist (mk p : ConeProduct β ι) (mk q) ∧
      dist (mk p : ConeProduct β ι) (mk q) ≤ ‖p - q‖ := by
  have h := dist_bounds (β := β) hb0 hb1 le_rfl (fun a z w =>
    ⟨(mul_le_mul_of_nonneg_right (hb a) (norm_nonneg _)).trans
        (mul_norm_sub_le_coneDist (β a).pos.le (hβ1 a) z w),
      (coneDist_le_norm_sub (β a).pos.le (hβ1 a) z w).trans_eq (one_mul _).symm⟩) p q
  rwa [one_mul] at h

/-- A comparison constant below `min(1, β_a)` for every `a`. -/
noncomputable def lowerConst (β : κ → ConeAngle) : ℝ :=
  (1 + ∑ a, (β a).beta⁻¹)⁻¹

/-- A comparison constant above `max(1, πβ_a/2)` for every `a`. -/
noncomputable def upperConst (β : κ → ConeAngle) : ℝ :=
  1 + ∑ a, π * (β a).beta / 2

theorem sum_inv_nonneg (β : κ → ConeAngle) : 0 ≤ ∑ a, (β a).beta⁻¹ :=
  Finset.sum_nonneg fun a _ => inv_nonneg.mpr (β a).pos.le

theorem lowerConst_pos (β : κ → ConeAngle) : 0 < lowerConst β :=
  inv_pos.mpr (by linarith [sum_inv_nonneg β])

theorem lowerConst_le_one (β : κ → ConeAngle) : lowerConst β ≤ 1 :=
  inv_le_one_of_one_le₀ (by linarith [sum_inv_nonneg β])

theorem lowerConst_le_min (β : κ → ConeAngle) (a : κ) : lowerConst β ≤ min 1 (β a).beta := by
  refine le_min (lowerConst_le_one β) ?_
  have ha : (β a).beta⁻¹ ≤ 1 + ∑ c, (β c).beta⁻¹ := by
    have := Finset.single_le_sum (f := fun c => (β c).beta⁻¹)
      (fun c _ => inv_nonneg.mpr (β c).pos.le) (Finset.mem_univ a)
    linarith
  calc lowerConst β ≤ ((β a).beta⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr (β a).pos) ha
    _ = (β a).beta := inv_inv _

theorem one_le_upperConst (β : κ → ConeAngle) : 1 ≤ upperConst β := by
  have : 0 ≤ ∑ a, π * (β a).beta / 2 :=
    Finset.sum_nonneg fun a _ => by have := (β a).pos; positivity
  unfold upperConst
  linarith

theorem max_le_upperConst (β : κ → ConeAngle) (a : κ) : max 1 (π * (β a).beta / 2) ≤ upperConst β := by
  refine max_le (one_le_upperConst β) ?_
  have := Finset.single_le_sum (f := fun c => π * (β c).beta / 2)
    (fun c _ => by have := (β c).pos; positivity) (Finset.mem_univ a)
  unfold upperConst
  linarith

/-- **Comparison for arbitrary angles** with explicit constants. -/
theorem dist_bounds_uniform (p q : RealConeModel κ ι) :
    lowerConst β * ‖p - q‖ ≤ dist (mk p : ConeProduct β ι) (mk q) ∧
      dist (mk p : ConeProduct β ι) (mk q) ≤ upperConst β * ‖p - q‖ :=
  dist_bounds (lowerConst_pos β).le (lowerConst_le_one β) (one_le_upperConst β) (fun a z w =>
    ⟨(mul_le_mul_of_nonneg_right (lowerConst_le_min β a) (norm_nonneg _)).trans
        (coneDist_bounds (β a).pos z w).1,
      (coneDist_bounds (β a).pos z w).2.trans
        (mul_le_mul_of_nonneg_right (max_le_upperConst β a) (norm_nonneg _))⟩) p q

/-- **Ball inclusions** from comparison constants `0 < b`, `0 < B`. -/
theorem ball_subset {b B : ℝ} (hb : 0 < b) (hB : 0 < B)
    (hd : ∀ p q : RealConeModel κ ι, b * ‖p - q‖ ≤ dist (mk p : ConeProduct β ι) (mk q) ∧
      dist (mk p : ConeProduct β ι) (mk q) ≤ B * ‖p - q‖)
    (p : RealConeModel κ ι) (ρ : ℝ) :
    Metric.ball p (ρ / B) ⊆ mk ⁻¹' Metric.ball (mk p : ConeProduct β ι) ρ ∧
      mk ⁻¹' Metric.ball (mk p : ConeProduct β ι) ρ ⊆ Metric.ball p (ρ / b) := by
  constructor
  · intro q hq
    rw [Metric.mem_ball, dist_eq_norm, lt_div_iff₀ hB] at hq
    rw [Set.mem_preimage, Metric.mem_ball]
    exact (hd q p).2.trans_lt (by linarith)
  · intro q hq
    rw [Set.mem_preimage, Metric.mem_ball] at hq
    rw [Metric.mem_ball, dist_eq_norm, lt_div_iff₀ hb, mul_comm]
    exact (hd q p).1.trans_lt hq

/-- **Ball inclusions, `β_a ≤ 1`:** `B_E(p, ρ) ⊆ B_d(p, ρ) ⊆ B_E(p, ρ/b)` for `0 < b ≤ β_a`. -/
theorem ball_subset_of_le_one (hβ1 : ∀ a, (β a).beta ≤ 1) {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hb : ∀ a, b ≤ (β a).beta) (p : RealConeModel κ ι) (ρ : ℝ) :
    Metric.ball p ρ ⊆ mk ⁻¹' Metric.ball (mk p : ConeProduct β ι) ρ ∧
      mk ⁻¹' Metric.ball (mk p : ConeProduct β ι) ρ ⊆ Metric.ball p (ρ / b) := by
  have h := ball_subset hb0 one_pos (fun p q => dist_bounds_of_le_one hβ1 hb0.le hb1 hb p q
    |>.imp_right fun h => h.trans_eq (one_mul _).symm) p ρ
  rwa [div_one] at h

/-- **Distances from the vertex stratum** `{r_a = 0 for all a}` are Euclidean. -/
theorem dist_of_cone_eq_zero {p : RealConeModel κ ι} (hp : ∀ a, p.cone a = 0)
    (q : RealConeModel κ ι) : dist (mk p : ConeProduct β ι) (mk q) = ‖p - q‖ := by
  rw [dist_mk, ← Real.sqrt_sq (norm_nonneg (p - q)), norm_sub_sq_eq]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hp a, coneDist_vertex_left, zero_sub, norm_neg]

/-- **Balls centred on the vertex stratum are Euclidean balls.** -/
theorem ball_of_cone_eq_zero {p : RealConeModel κ ι} (hp : ∀ a, p.cone a = 0) (ρ : ℝ) :
    mk ⁻¹' Metric.ball (mk p : ConeProduct β ι) ρ = Metric.ball p ρ := by
  ext q
  rw [Set.mem_preimage, Metric.mem_ball, Metric.mem_ball, dist_comm, dist_of_cone_eq_zero hp,
    dist_eq_norm, norm_sub_rev]

/-- **Dilations:** `p ↦ t p` (i.e. `r_a ↦ t r_a`, `s ↦ t s`) scales the distance by `t`. -/
theorem dist_smul {t : ℝ} (ht : 0 < t) (p q : RealConeModel κ ι) :
    dist (mk (t • p) : ConeProduct β ι) (mk (t • q)) = t * dist (mk p : ConeProduct β ι) (mk q) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [dist_mk, dist_mk]
  simp only [cone_smul, eucl_smul, coneDist_mul_left _ ht', Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht, mul_pow, ← mul_sub, ← Finset.mul_sum, ← mul_add]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]

theorem lipschitzWith_mk :
    LipschitzWith (Real.toNNReal (upperConst β)) (mk : RealConeModel κ ι → ConeProduct β ι) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal _ (zero_le_one.trans (one_le_upperConst β)), dist_eq_norm]
  exact (dist_bounds_uniform p q).2

theorem lipschitzWith_coord :
    LipschitzWith (Real.toNNReal (lowerConst β)⁻¹) (coord : ConeProduct β ι → RealConeModel κ ι) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr (lowerConst_pos β).le), dist_eq_norm, inv_mul_eq_div,
    le_div_iff₀ (lowerConst_pos β), mul_comm]
  exact (dist_bounds_uniform (β := β) (coord x) (coord y)).1

/-- **The product cone distance induces the Euclidean topology** of the real coordinates. -/
noncomputable def homeomorph (β : κ → ConeAngle) (ι : Type) [Fintype ι] :
    RealConeModel κ ι ≃ₜ ConeProduct β ι where
  toFun := mk
  invFun := coord
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := lipschitzWith_mk.continuous
  continuous_invFun := lipschitzWith_coord.continuous

end ConeProduct

end ConicalKahler
