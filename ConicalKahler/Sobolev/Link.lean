module

public import ConicalKahler.Sobolev.Polar
public import ConicalKahler.Sobolev.FormSpectral
public import ConicalKahler.Sobolev.Rellich
public import ConicalKahler.Sobolev.Restrict
public import ConicalKahler.Sobolev.HarmonicApprox

/-!
# The link of a cone and its spectral theory (paper, Lemma 3.1)

Let `c` be a **conical** coefficient field on `ℝ^d` (`CoeffField.IsConical`): `A(t x) = A(x)` for
`t > 0` and `A(x) x = x`. The cone Laplacian `A = g⁻¹` is the example of interest (`ConeLink.lean`).
Then `A` is determined by its values on the unit sphere `S = S^{d-1}`, the link, and the radial
direction is `A`-orthogonal to the sphere.

**The link, without a manifold structure.** `L²(link)` is `L²(S, σ)` for the surface measure `σ`.
A function `φ` on the link is identified with its `0`-homogeneous extension `φ(x/|x|)`, and a vector
field `Γ` on the link with the `(-1)`-homogeneous field `|x|^{-1} Γ(x/|x|)`. The **link Sobolev
space** `linkW12` consists of the pairs `(φ, Γ) ∈ L²(S) × L²(S; ℝ^d)` such that `Γ` extended in
this way is the weak gradient of `φ` extended, on every shell `{a < |x| < b}`, `a > 0`. It is a
closed subspace, hence a Hilbert space.

**The link form** is `b((φ, Γ), (ψ, Θ)) = ∫_S ⟨A Γ, Θ⟩ dσ + ∫_S φ ψ dσ` (`linkForm`). It is
coercive on `linkW12`. The paper's operator `-Δ_ḡ` is the form `∫_S ⟨A Γ, Θ⟩ dσ` relative to
`L²(S)`.

## Results

* `CoeffField.IsConical.ae_coercive_sphere`: the ellipticity bounds hold `σ`-a.e. on the sphere.
* `linkW12`, `isClosed_linkW12`, `linkForm₀`, `isCoercive_linkForm₀`.
* `isCompactOperator_linkFst`: `linkW12 ↪ L²(S)` is **compact**. A cut-off on the shell
  `{1 < |x| < 4}` lands in `W^{1,2}_0`, where Rellich applies, and the `L²` norm on the sphere is
  controlled by the `L²` norm on `{2 < |x| < 3}`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set Metric
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

variable {d : ℕ} [NeZero d]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### Conical coefficient fields -/

/-- A coefficient field is **conical** if it is `0`-homogeneous, `A(t x) = A(x)` for `t > 0`, and
fixes the radial direction, `A(x) x = x`. Then the radial direction is `A`-orthogonal to the
spheres. The cone Laplacian `g⁻¹` is conical. -/
structure CoeffField.IsConical {d : ℕ} (c : CoeffField (EuclideanSpace ℝ (Fin d)) volume) : Prop where
  smul : ∀ {t : ℝ}, 0 < t → ∀ x, c.A (t • x) = c.A x
  radial : ∀ x, c.A x x = x

namespace CoeffField.IsConical

variable {c : CoeffField (EuclideanSpace ℝ (Fin d)) volume} (hc : c.IsConical)
include hc

theorem A_sphProj {x : 𝔼} (hx : x ≠ 0) : c.A (sphProj x) = c.A x := by
  conv_rhs => rw [← norm_smul_sphProj (x := x)]
  exact (hc.smul (norm_pos_iff.mpr hx) _).symm

/-- `⟨A(x) v, x⟩ = ⟨v, x⟩`. -/
theorem inner_A_self (x v : 𝔼) : ⟪c.A x v, x⟫_ℝ = ⟪v, x⟫_ℝ := by
  rw [c.symm, hc.radial]

/-- `⟨A(x) v, x/|x|⟩ = ⟨v, x/|x|⟩` for `x ≠ 0`. -/
theorem inner_A_sphProj {x : 𝔼} (hx : x ≠ 0) (v : 𝔼) :
    ⟪c.A x v, (sphProj x : 𝔼)⟫_ℝ = ⟪v, (sphProj x : 𝔼)⟫_ℝ := by
  rw [sphProj_coe hx, inner_smul_right, inner_smul_right, hc.inner_A_self]

/-- A property of `A(x)` holding almost everywhere holds `σ`-almost everywhere on the sphere. -/
theorem ae_sphere {P : (𝔼 →L[ℝ] 𝔼) → Prop} (h : ∀ᵐ x : 𝔼, P (c.A x)) :
    ∀ᵐ (w : Sph d) ∂(sphMeasure d), P (c.A (w : 𝔼)) := by
  refine ae_sphere_of_ae ?_
  have h0 : ∀ᵐ x : 𝔼, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [h, h0] with x hx hx0
  rw [hc.A_sphProj hx0]
  exact hx

theorem ae_coercive_sphere :
    ∀ᵐ (w : Sph d) ∂(sphMeasure d), ∀ v, c.lam * ‖v‖ ^ 2 ≤ ⟪c.A (w : 𝔼) v, v⟫_ℝ :=
  hc.ae_sphere (P := fun T => ∀ v, c.lam * ‖v‖ ^ 2 ≤ ⟪T v, v⟫_ℝ) c.coercive

theorem ae_norm_le_sphere : ∀ᵐ (w : Sph d) ∂(sphMeasure d), ∀ v, ‖c.A (w : 𝔼) v‖ ≤ c.Λ * ‖v‖ :=
  hc.ae_sphere (P := fun T => ∀ v, ‖T v‖ ≤ c.Λ * ‖v‖) c.ae_norm_apply_le

end CoeffField.IsConical

/-! ### Multiplication by `A` on the sphere -/

theorem norm_sq_eq_integral_L2 {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (G : Lp E 2 μ) :
    ‖G‖ ^ 2 = ∫ x, ‖G x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun x => real_inner_self_eq_norm_sq (G x))

namespace CoeffField

variable (c : CoeffField (EuclideanSpace ℝ (Fin d)) volume)

theorem aestronglyMeasurable_sphere_apply {G : Sph d → 𝔼}
    (hG : AEStronglyMeasurable G (sphMeasure d)) :
    AEStronglyMeasurable (fun w : Sph d => c.A w (G w)) (sphMeasure d) :=
  (ContinuousLinearMap.id ℝ (𝔼 →L[ℝ] 𝔼)).aestronglyMeasurable_comp₂
    (c.stronglyMeasurable.comp_measurable measurable_subtype_coe).aestronglyMeasurable hG

variable {c}

theorem memLp_sphere_apply (hc : c.IsConical) (G : Lp 𝔼 2 (sphMeasure d)) :
    MemLp (fun w : Sph d => c.A w (G w)) 2 (sphMeasure d) := by
  refine MemLp.of_le ((Lp.memLp G).const_smul c.Λ)
    (c.aestronglyMeasurable_sphere_apply (Lp.aestronglyMeasurable G)) ?_
  filter_upwards [hc.ae_norm_le_sphere] with w hw
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos c.Λ_pos]
  exact hw _

/-- **Multiplication by `A` on the sphere**, `Γ ↦ A Γ`, on `L²(S; ℝ^d)`. -/
def sphMulOp (hc : c.IsConical) : Lp 𝔼 2 (sphMeasure d) →L[ℝ] Lp 𝔼 2 (sphMeasure d) :=
  LinearMap.mkContinuous
    { toFun := fun G => (memLp_sphere_apply hc G).toLp _
      map_add' := fun G H => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_add G H] with x hx
        rw [hx, Pi.add_apply, map_add, Pi.add_apply]
      map_smul' := fun r G => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_smul r G] with x hx
        rw [hx, Pi.smul_apply, map_smul, Pi.smul_apply] }
    c.Λ fun G => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_sphere_apply hc G).coeFn_toLp, hc.ae_norm_le_sphere] with x h1 h2
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [h1]
      exact h2 _

theorem sphMulOp_ae (hc : c.IsConical) (G : Lp 𝔼 2 (sphMeasure d)) :
    sphMulOp hc G =ᵐ[sphMeasure d] fun w => c.A w (G w) :=
  (memLp_sphere_apply hc G).coeFn_toLp

theorem inner_sphMulOp (hc : c.IsConical) (G H : Lp 𝔼 2 (sphMeasure d)) :
    ⟪sphMulOp hc G, H⟫_ℝ = ∫ w, ⟪c.A w (G w), H w⟫_ℝ ∂(sphMeasure d) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [sphMulOp_ae hc G] with x hx
  rw [hx]

theorem inner_sphMulOp_comm (hc : c.IsConical) (G H : Lp 𝔼 2 (sphMeasure d)) :
    ⟪sphMulOp hc G, H⟫_ℝ = ⟪sphMulOp hc H, G⟫_ℝ := by
  rw [inner_sphMulOp, inner_sphMulOp]
  exact integral_congr_ae (Eventually.of_forall fun w => by
    change ⟪c.A w (G w), H w⟫_ℝ = ⟪c.A w (H w), G w⟫_ℝ
    rw [c.symm, real_inner_comm])

theorem lam_mul_norm_sq_le_sphMulOp (hc : c.IsConical) (G : Lp 𝔼 2 (sphMeasure d)) :
    c.lam * ‖G‖ ^ 2 ≤ ⟪sphMulOp hc G, G⟫_ℝ := by
  rw [norm_sq_eq_integral_L2, ← integral_const_mul, inner_sphMulOp]
  refine integral_mono_ae ?_ ?_ ?_
  · exact ((L2.integrable_inner G G).congr (Eventually.of_forall fun x =>
      real_inner_self_eq_norm_sq (G x))).const_mul _
  · exact (L2.integrable_inner (sphMulOp hc G) G).congr (by
      filter_upwards [sphMulOp_ae hc G] with x hx
      rw [hx])
  · filter_upwards [hc.ae_coercive_sphere] with x hx
    exact hx _

end CoeffField

/-! ### Shells -/

/-- The open shell `{a < |x| < b}`. -/
def shell (d : ℕ) (a b : ℝ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ‖x‖ ∈ Ioo a b}

theorem isOpen_shell (a b : ℝ) : IsOpen (shell d a b) := isOpen_Ioo.preimage continuous_norm

theorem isBounded_shell (a b : ℝ) : Bornology.IsBounded (shell d a b) :=
  (Metric.isBounded_closedBall (x := (0 : 𝔼)) (r := b)).subset fun x hx => by
    simpa using hx.2.le

theorem shell_mono {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') : shell d a b ⊆ shell d a' b' :=
  fun _ hx => ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩

theorem ne_zero_of_mem_shell {a b : ℝ} (ha : 0 ≤ a) {x : 𝔼} (hx : x ∈ shell d a b) : x ≠ 0 := by
  rintro rfl
  simp only [shell, mem_ofPred_eq, norm_zero, mem_Ioo] at hx
  linarith [hx.1]

theorem shellWeight_ne_top {a : ℝ} (ha : 0 < a) (b k : ℝ) : shellWeight d k a b ≠ ⊤ := by
  have hcont : ContinuousOn (fun r : ℝ => (r ^ k) ^ 2 * r ^ (d - 1)) (Icc a b) := by
    refine ContinuousOn.mul ?_ (continuousOn_pow _)
    refine ContinuousOn.pow (fun r hr => ?_) 2
    exact (Real.continuousAt_rpow_const r k (Or.inl (ha.trans_le hr.1).ne')).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal M * volume (Ioo a b)) ?_ ?_
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_Ioo_lt_top.ne
  · rw [← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun r hr => ENNReal.ofReal_le_ofReal ?_
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hM r (Ioo_subset_Icc_self hr)))

/-! ### The link Sobolev space -/

/-- Pairs `(φ, Γ)` of a function and a vector field on the link, `L²(S) × L²(S; ℝ^d)`. -/
abbrev LinkPair (d : ℕ) : Type :=
  WithLp 2 (Lp ℝ 2 (sphMeasure d) × Lp (EuclideanSpace ℝ (Fin d)) 2 (sphMeasure d))

/-- **The homogeneous extension of a link pair** to `Ω ⊆ {a < |x| < b}`, `a > 0`:
`(φ, Γ) ↦ (φ(x/|x|), |x|^{-1} Γ(x/|x|))`. -/
def linkEmb {Ω : Set 𝔼} {a b : ℝ} (ha : 0 < a) (hΩ : Ω ⊆ shell d a b) :
    LinkPair d →L[ℝ] L2Pair volume Ω :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 (volume.restrict Ω))
      (Lp 𝔼 2 (volume.restrict Ω))).symm.toContinuousLinearMap ∘L
    ((homL 0 ha.le hΩ (shellWeight_ne_top ha b 0)).prodMap
      (homL (-1) ha.le hΩ (shellWeight_ne_top ha b (-1)))) ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 (sphMeasure d))
        (Lp 𝔼 2 (sphMeasure d))).toContinuousLinearMap

theorem linkEmb_fst_ae {Ω : Set 𝔼} {a b : ℝ} (ha : 0 < a) (hΩ : Ω ⊆ shell d a b) (v : LinkPair d) :
    (linkEmb ha hΩ v).fst =ᵐ[volume.restrict Ω] homFun 0 v.fst :=
  homL_ae 0 ha.le hΩ (shellWeight_ne_top ha b 0) v.fst

theorem linkEmb_snd_ae {Ω : Set 𝔼} {a b : ℝ} (ha : 0 < a) (hΩ : Ω ⊆ shell d a b) (v : LinkPair d) :
    (linkEmb ha hΩ v).snd =ᵐ[volume.restrict Ω] homFun (-1) v.snd :=
  homL_ae (-1) ha.le hΩ (shellWeight_ne_top ha b (-1)) v.snd

/-- The shells `{1/(n+1) < |x| < n+1}` exhausting `ℝ^d \ {0}`. -/
abbrev shellN (d : ℕ) (n : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  shell d ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1)

theorem shellN_pos (n : ℕ) : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity

/-- The homogeneous extension to the shell `shellN d n`. -/
abbrev linkEmbN (d : ℕ) [NeZero d] (n : ℕ) : LinkPair d →L[ℝ] L2Pair volume (shellN d n) :=
  linkEmb (a := ((n : ℝ) + 1)⁻¹) (b := (n : ℝ) + 1) (shellN_pos n) (subset_refl _)

/-- **The link Sobolev space `W^{1,2}(link)`**: the pairs `(φ, Γ)` such that `|x|^{-1} Γ(x/|x|)` is
the weak gradient of `φ(x/|x|)` on every shell `{a < |x| < b}`, `a > 0`. -/
def linkW12 (d : ℕ) [NeZero d] : Submodule ℝ (LinkPair d) :=
  ⨅ n : ℕ, (W12 volume (shellN d n)).comap (linkEmbN d n).toLinearMap

theorem mem_linkW12 {v : LinkPair d} :
    v ∈ linkW12 d ↔ ∀ n : ℕ, linkEmbN d n v ∈ W12 volume (shellN d n) := by
  simp [linkW12, Submodule.mem_iInf]

theorem isClosed_linkW12 : IsClosed (linkW12 d : Set (LinkPair d)) := by
  have : (linkW12 d : Set (LinkPair d)) = ⋂ n : ℕ,
      (linkEmbN d n) ⁻¹' (W12 volume (shellN d n) : Set (L2Pair volume (shellN d n))) := by
    ext v
    simp [mem_linkW12]
  rw [this]
  exact isClosed_iInter fun n => (isClosed_W12 _).preimage (ContinuousLinearMap.continuous _)

instance : CompleteSpace (linkW12 d) := (isClosed_linkW12 (d := d)).completeSpace_coe

-- `linkW12` is only used through `mem_linkW12`; unfolding it is expensive.
attribute [irreducible] linkW12

/-- **Link pairs are `W^{1,2}` pairs on every region `Ω ⊆ {a < |x| < b}`, `a > 0`.** -/
theorem linkEmb_mem_W12 {v : LinkPair d} (hv : v ∈ linkW12 d) {Ω : Set 𝔼} {a b : ℝ}
    (ha : 0 < a) (hΩ : Ω ⊆ shell d a b) : linkEmb ha hΩ v ∈ W12 volume Ω := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max a⁻¹ b)
  have hsub : Ω ⊆ shellN d n := hΩ.trans (shell_mono ?_ ?_)
  · have h := restrict_mem_W12 hsub (mem_linkW12.mp hv n)
    convert h using 1
    refine L2Pair.ext volume ?_ ?_
    · refine Lp.ext ?_
      filter_upwards [linkEmb_fst_ae ha hΩ v, restrictLp_ae hsub (linkEmbN d n v).fst,
        ae_restrict_of_ae_restrict_of_subset hsub
          (linkEmb_fst_ae (a := ((n : ℝ) + 1)⁻¹) (b := (n : ℝ) + 1) (shellN_pos n) subset_rfl v)]
        with x h1 h2 h3
      rw [h1, L2Pair.restrict_fst, h2, h3]
    · refine Lp.ext ?_
      filter_upwards [linkEmb_snd_ae ha hΩ v, restrictLp_ae hsub (linkEmbN d n v).snd,
        ae_restrict_of_ae_restrict_of_subset hsub
          (linkEmb_snd_ae (a := ((n : ℝ) + 1)⁻¹) (b := (n : ℝ) + 1) (shellN_pos n) subset_rfl v)]
        with x h1 h2 h3
      rw [h1, L2Pair.restrict_snd, h2, h3]
  · rw [inv_le_comm₀ (by positivity) ha]
    linarith [le_max_left a⁻¹ b]
  · linarith [le_max_right a⁻¹ b]

/-! ### The link form -/

theorem norm_fst_le_L2 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β]
    (v : WithLp 2 (α × β)) : ‖v.fst‖ ≤ ‖v‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 v
  have h0 := sq_nonneg ‖v.snd‖
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)

theorem norm_snd_le_L2 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β]
    (v : WithLp 2 (α × β)) : ‖v.snd‖ ≤ ‖v‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 v
  have h0 := sq_nonneg ‖v.fst‖
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)

variable {c : CoeffField (EuclideanSpace ℝ (Fin d)) volume}

/-- **The link form** `b((φ, Γ), (ψ, Θ)) = ∫_S ⟨A Γ, Θ⟩ dσ + ∫_S φ ψ dσ`. -/
def linkForm (hc : c.IsConical) : LinkPair d →L[ℝ] LinkPair d →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun v w : LinkPair d =>
        ⟪CoeffField.sphMulOp hc v.snd, w.snd⟫_ℝ + ⟪v.fst, w.fst⟫_ℝ)
      (fun v₁ v₂ w => by simp only [WithLp.add_snd, WithLp.add_fst, map_add, inner_add_left]; ring)
      (fun r v w => by
        simp only [WithLp.smul_snd, WithLp.smul_fst, map_smul, real_inner_smul_left, smul_eq_mul]
        ring)
      (fun v w₁ w₂ => by simp only [WithLp.add_snd, WithLp.add_fst, inner_add_right]; ring)
      (fun r v w => by
        simp only [WithLp.smul_snd, WithLp.smul_fst, real_inner_smul_right, smul_eq_mul]
        ring))
    (c.Λ + 1) fun v w => by
      simp only [LinearMap.mk₂_apply, Real.norm_eq_abs]
      have h1 : |⟪CoeffField.sphMulOp hc v.snd, w.snd⟫_ℝ| ≤ c.Λ * ‖v‖ * ‖w‖ := by
        calc |⟪CoeffField.sphMulOp hc v.snd, w.snd⟫_ℝ|
            ≤ ‖CoeffField.sphMulOp hc v.snd‖ * ‖w.snd‖ := abs_real_inner_le_norm _ _
          _ ≤ (c.Λ * ‖v.snd‖) * ‖w.snd‖ := by
              gcongr
              exact (CoeffField.sphMulOp hc).le_of_opNorm_le
                (LinearMap.mkContinuous_norm_le _ c.Λ_pos.le _) _
          _ ≤ c.Λ * ‖v‖ * ‖w‖ := by
              have := c.Λ_pos
              gcongr
              · exact norm_snd_le_L2 v
              · exact norm_snd_le_L2 w
      have h2 : |⟪v.fst, w.fst⟫_ℝ| ≤ ‖v‖ * ‖w‖ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul (norm_fst_le_L2 v)
          (norm_fst_le_L2 w) (norm_nonneg _) (norm_nonneg _))
      calc |⟪CoeffField.sphMulOp hc v.snd, w.snd⟫_ℝ + ⟪v.fst, w.fst⟫_ℝ|
          ≤ c.Λ * ‖v‖ * ‖w‖ + ‖v‖ * ‖w‖ := (abs_add_le _ _).trans (add_le_add h1 h2)
        _ = (c.Λ + 1) * ‖v‖ * ‖w‖ := by ring

theorem linkForm_apply (hc : c.IsConical) (v w : LinkPair d) :
    linkForm hc v w = ⟪CoeffField.sphMulOp hc v.snd, w.snd⟫_ℝ + ⟪v.fst, w.fst⟫_ℝ := rfl

theorem linkForm_comm (hc : c.IsConical) (v w : LinkPair d) :
    linkForm hc v w = linkForm hc w v := by
  rw [linkForm_apply, linkForm_apply, CoeffField.inner_sphMulOp_comm, real_inner_comm v.fst]

/-- The link form on `W^{1,2}(link)`. -/
def linkForm₀ (hc : c.IsConical) : linkW12 d →L[ℝ] linkW12 d →L[ℝ] ℝ :=
  (linkForm hc).bilinearComp (linkW12 d).subtypeL (linkW12 d).subtypeL

theorem linkForm₀_apply (hc : c.IsConical) (v w : linkW12 d) :
    linkForm₀ hc v w = linkForm hc v w := rfl

theorem linkForm₀_comm (hc : c.IsConical) (v w : linkW12 d) :
    linkForm₀ hc v w = linkForm₀ hc w v := linkForm_comm hc _ _

/-- **The link form is coercive** on `W^{1,2}(link)`, with constant `min λ 1`. -/
theorem isCoercive_linkForm₀ (hc : c.IsConical) : IsCoercive (linkForm₀ hc) := by
  refine ⟨min c.lam 1, lt_min c.lam_pos one_pos, fun v => ?_⟩
  rw [linkForm₀_apply, linkForm_apply, real_inner_self_eq_norm_sq]
  have h1 := CoeffField.lam_mul_norm_sq_le_sphMulOp hc (v : LinkPair d).snd
  have hn : ‖v‖ ^ 2 = ‖(v : LinkPair d).fst‖ ^ 2 + ‖(v : LinkPair d).snd‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 (v : LinkPair d)
  have hm1 : min c.lam 1 ≤ c.lam := min_le_left _ _
  have hm2 : min c.lam 1 ≤ 1 := min_le_right _ _
  have hm0 : 0 ≤ min c.lam 1 := le_min c.lam_pos.le zero_le_one
  calc min c.lam 1 * ‖v‖ * ‖v‖ = min c.lam 1 * ‖(v : LinkPair d).snd‖ ^ 2 +
        min c.lam 1 * ‖(v : LinkPair d).fst‖ ^ 2 := by
        rw [mul_assoc, ← sq, hn]
        ring
    _ ≤ c.lam * ‖(v : LinkPair d).snd‖ ^ 2 + 1 * ‖(v : LinkPair d).fst‖ ^ 2 := by
        gcongr
    _ ≤ _ := by linarith

/-- The inclusion `W^{1,2}(link) → L²(S)`, `(φ, Γ) ↦ φ`. -/
def linkFst (d : ℕ) [NeZero d] : linkW12 d →L[ℝ] Lp ℝ 2 (sphMeasure d) :=
  (WithLp.fstL 2 ℝ _ _).comp (linkW12 d).subtypeL

theorem linkFst_apply (v : linkW12 d) : linkFst d v = (v : LinkPair d).fst := rfl

/-! ### Compactness of `W^{1,2}(link) ↪ L²(link)` -/

section CutL

variable {Ω : Set (EuclideanSpace ℝ (Fin d))}

theorem cutPair_add {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) (v w : L2Pair volume Ω) :
    cutPair hη (v + w) = cutPair hη v + cutPair hη w := by
  refine L2Pair.ext volume ?_ ?_
  · rw [WithLp.add_fst, cutPair_fst, cutPair_fst, cutPair_fst, ← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_add v.fst w.fst] with x hx
    simp only [cutFst, Pi.add_apply, WithLp.add_fst, hx]
    ring
  · rw [WithLp.add_snd, cutPair_snd, cutPair_snd, cutPair_snd, ← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_add v.fst w.fst, Lp.coeFn_add v.snd w.snd] with x hx hx'
    simp only [cutSnd, Pi.add_apply, WithLp.add_fst, WithLp.add_snd, hx, hx', smul_add, mul_add,
      add_smul]
    abel

theorem cutPair_smul {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) (r : ℝ) (v : L2Pair volume Ω) :
    cutPair hη (r • v) = r • cutPair hη v := by
  refine L2Pair.ext volume ?_ ?_
  · rw [WithLp.smul_fst, cutPair_fst, cutPair_fst, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_smul r v.fst] with x hx
    simp only [cutFst, Pi.smul_apply, WithLp.smul_fst, hx, smul_eq_mul]
    ring
  · rw [WithLp.smul_snd, cutPair_snd, cutPair_snd, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_smul r v.fst, Lp.coeFn_smul r v.snd] with x hx hx'
    simp only [cutSnd, Pi.smul_apply, WithLp.smul_fst, WithLp.smul_snd, hx, hx', smul_add,
      smul_eq_mul, smul_smul]
    congr 1
    · rw [mul_comm]
    · congr 1
      ring

theorem norm_cutPair_le {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) (h01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    {M : ℝ} (hM : ∀ x, ‖gradient η x‖ ≤ M) (v : L2Pair volume Ω) :
    ‖cutPair hη v‖ ≤ Real.sqrt (3 + 8 * M ^ 2) * ‖v‖ := by
  have hfst := norm_cutPair_fst_le hη h01 v
  have hsnd := norm_cutPair_snd_sq_le hη h01 hM v
  have hint : ∫ x in Ω, η x ^ 2 * ‖v.snd x‖ ^ 2 ≤ ‖v.snd‖ ^ 2 := by
    rw [norm_sq_eq_integral_L2]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
      ((Lp.memLp v.snd).norm.integrable_sq) (Eventually.of_forall fun x => ?_)
    have : η x ^ 2 ≤ 1 := by nlinarith [h01 x]
    calc η x ^ 2 * ‖v.snd x‖ ^ 2 ≤ 1 * ‖v.snd x‖ ^ 2 := by gcongr
      _ = _ := one_mul _
  have hn := WithLp.prod_norm_sq_eq_of_L2 (cutPair hη v)
  have hv := WithLp.prod_norm_sq_eq_of_L2 v
  have hf2 := pow_le_pow_left₀ (norm_nonneg _) hfst 2
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hA : 0 ≤ ‖v.fst‖ ^ 2 := sq_nonneg _
  have hB : 0 ≤ ‖v.snd‖ ^ 2 := sq_nonneg _
  have key : ‖cutPair hη v‖ ^ 2 ≤ (3 + 8 * M ^ 2) * ‖v‖ ^ 2 := by
    rw [hn, hv]
    have h8 : 0 ≤ 8 * M ^ 2 * ‖v.snd‖ ^ 2 := by positivity
    have : (3 + 8 * M ^ 2) * (‖v.fst‖ ^ 2 + ‖v.snd‖ ^ 2) =
        3 * ‖v.fst‖ ^ 2 + 8 * M ^ 2 * ‖v.fst‖ ^ 2 + 3 * ‖v.snd‖ ^ 2 +
          8 * M ^ 2 * ‖v.snd‖ ^ 2 := by ring
    rw [this]
    linarith
  have hs : (Real.sqrt (3 + 8 * M ^ 2) * ‖v‖) ^ 2 = (3 + 8 * M ^ 2) * ‖v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (hs ▸ key)

/-- **Cutting off as a bounded operator** `W^{1,2}(Ω) → W^{1,2}_0(Ω)`,
`(u, G) ↦ (η² u, ∇(η² u))`. -/
def cutL (hΩ : IsOpen Ω) {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) (h01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1) :
    W12 volume Ω →L[ℝ] H01 volume Ω :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨cutPair hη v, cutPair_mem_H01 hΩ v.2 hη⟩
      map_add' := fun v w => Subtype.ext (cutPair_add hη v w)
      map_smul' := fun r v => Subtype.ext (cutPair_smul hη r v) }
    (Real.sqrt (3 + 8 * (exists_bound_testFn hη).choose ^ 2)) fun _ =>
      norm_cutPair_le hη h01 (exists_bound_testFn hη).choose_spec.2.2 _

theorem cutL_coe (hΩ : IsOpen Ω) {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) (h01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (v : W12 volume Ω) : (cutL hΩ hη h01 v : L2Pair volume Ω) = cutPair hη v := rfl

end CutL

/-! ### Compactness -/

theorem norm_sq_eq_lintegral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  rw [Lp.norm_def, eLpNorm_two_eq (Lp.aestronglyMeasurable f), ← ENNReal.toReal_rpow,
    ← Real.sqrt_eq_rpow, Real.sq_sqrt ENNReal.toReal_nonneg]

theorem lintegral_sq_lt_top {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Lp E 2 μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ⊤ := by
  have h := Lp.eLpNorm_lt_top f
  rw [eLpNorm_two_eq (Lp.aestronglyMeasurable f)] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h

theorem one_le_shellWeight_two_three : 1 ≤ shellWeight d 0 2 3 := by
  calc (1 : ℝ≥0∞) = ∫⁻ r in Ioo (2 : ℝ) 3, ENNReal.ofReal 1 := by simp; norm_num
    _ ≤ shellWeight d 0 2 3 := by
        refine setLIntegral_mono (by fun_prop) fun r hr => ENNReal.ofReal_le_ofReal ?_
        rw [Real.rpow_zero, one_pow, one_mul]
        exact one_le_pow₀ (by linarith [hr.1])

theorem exists_linkCutoff : ∃ η : 𝔼 → ℝ, IsTestFn (shell d 1 4) η ∧
    (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ ∀ x ∈ shell d 2 3, η x = 1 := by
  have hK : IsCompact {x : 𝔼 | ‖x‖ ∈ Icc (2 : ℝ) 3} :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.preimage continuous_norm)
      ((Metric.isBounded_closedBall (x := (0 : 𝔼)) (r := 3)).subset fun x hx => by
        simpa using hx.2)
  have hKsub : {x : 𝔼 | ‖x‖ ∈ Icc (2 : ℝ) 3} ⊆ shell d 1 4 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨η, hη, h01, h1⟩ := exists_cutoff hK (isOpen_shell 1 4) hKsub
  exact ⟨η, hη, h01, fun x hx => h1 x ⟨hx.1.le, hx.2.le⟩⟩

/-- The extension of link pairs to `W^{1,2}` of the shell `{1 < |x| < 4}`. -/
def linkEmbW (d : ℕ) [NeZero d] : linkW12 d →L[ℝ] W12 volume (shell d 1 4) :=
  ((linkEmb (a := 1) (b := 4) one_pos subset_rfl).comp (linkW12 d).subtypeL).codRestrict _
    fun v => linkEmb_mem_W12 v.2 one_pos subset_rfl

/-- **The link space embeds compactly into `L²(S)`** (the compactness in the paper's proof of
Lemma 3.1). The pair is cut off to `W^{1,2}_0({1 < |x| < 4})`, where Rellich applies; the `L²(S)`
norm of `φ` is at most the `L²` norm of `φ(x/|x|)` on `{2 < |x| < 3}`. -/
theorem isCompactOperator_linkFst : IsCompactOperator (linkFst d) := by
  obtain ⟨η, hη, h01, h1⟩ := exists_linkCutoff (d := d)
  set J : linkW12 d →L[ℝ] Lp ℝ 2 (volume.restrict (shell d 1 4)) :=
    (H01.fstL (shell d 1 4)).comp ((cutL (isOpen_shell 1 4) hη h01).comp (linkEmbW d))
  have hJ : IsCompactOperator J :=
    (isCompactOperator_H01_fst (isOpen_shell 1 4) (isBounded_shell 1 4)).comp_clm _
  refine isCompactOperator_of_norm_le hJ one_pos fun v => ?_
  rw [one_mul]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  -- `J v = η² φ(x/|x|)` on the shell, and `= φ(x/|x|)` on `{2 < |x| < 3}`
  have hJv : (J v : 𝔼 → ℝ) =ᵐ[volume.restrict (shell d 1 4)]
      fun x => η x ^ 2 * homFun 0 (v : LinkPair d).fst x := by
    change ((cutPair hη (linkEmbW d v : L2Pair volume (shell d 1 4))).fst : 𝔼 → ℝ) =ᵐ[_] _
    rw [cutPair_fst]
    filter_upwards [(memLp_cutFst (v := (linkEmbW d v : L2Pair volume (shell d 1 4))) hη).coeFn_toLp,
      linkEmb_fst_ae (a := 1) (b := 4) one_pos subset_rfl (v : LinkPair d)] with x hx hx'
    rw [hx, cutFst]
    change η x ^ 2 * (linkEmb (a := 1) (b := 4) one_pos subset_rfl (v : LinkPair d)).fst x = _
    rw [hx']
  have hsub : shell d 2 3 ⊆ shell d 1 4 := shell_mono (by norm_num) (by norm_num)
  have hJv' : (J v : 𝔼 → ℝ) =ᵐ[volume.restrict (shell d 2 3)] homFun 0 (v : LinkPair d).fst := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hJv,
      ae_restrict_mem (measurableSet_shell (d := d) 2 3)] with x hx hx23
    rw [hx, h1 x hx23, one_pow, one_mul]
  have hlow : (∫⁻ w, ‖(v : LinkPair d).fst w‖ₑ ^ 2 ∂(sphMeasure d)) * shellWeight d 0 2 3 ≤
      ∫⁻ x in shell d 1 4, ‖J v x‖ₑ ^ 2 := by
    rw [← lintegral_shell_homFun 0 (Lp.aestronglyMeasurable _) (by norm_num : (0 : ℝ) ≤ 2) 3]
    calc ∫⁻ x in {x : 𝔼 | ‖x‖ ∈ Ioo 2 3}, ‖homFun 0 (v : LinkPair d).fst x‖ₑ ^ 2
        = ∫⁻ x in shell d 2 3, ‖J v x‖ₑ ^ 2 := by
          refine lintegral_congr_ae ?_
          filter_upwards [hJv'] with x hx
          rw [hx]
      _ ≤ _ := lintegral_mono_set hsub
  rw [linkFst_apply, norm_sq_eq_lintegral, norm_sq_eq_lintegral]
  refine ENNReal.toReal_mono (lintegral_sq_lt_top _).ne ?_
  calc ∫⁻ w, ‖(v : LinkPair d).fst w‖ₑ ^ 2 ∂(sphMeasure d)
      = (∫⁻ w, ‖(v : LinkPair d).fst w‖ₑ ^ 2 ∂(sphMeasure d)) * 1 := (mul_one _).symm
    _ ≤ (∫⁻ w, ‖(v : LinkPair d).fst w‖ₑ ^ 2 ∂(sphMeasure d)) * shellWeight d 0 2 3 := by
        gcongr
        exact one_le_shellWeight_two_three
    _ ≤ _ := hlow

end ConicalKahler.Sobolev
