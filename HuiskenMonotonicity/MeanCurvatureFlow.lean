/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.FirstVariationIntegral
import HuiskenMonotonicity.TransportFormula
import HuiskenMonotonicity.MetricEvolution

/-!
# Huisken's monotonicity formula for a mean curvature flow

For a smooth family of immersions `F : M × ℝ → E` of a closed manifold moving by mean
curvature at time `t`, `∂_t F = Hvec` (`IsMeanCurvatureFlowAt`), and the backward heat kernel
`ρ` centred at `(0, t₀)`,

  `d/dt ∫_M ρ(F, t) dμ_t = -∫_M ρ(F, t) ‖Hvec + F^⊥ / (2(t₀ - t))‖² dμ_t`

for `t < t₀` (Huisken 1990, Theorem 3.1; `huisken_monotonicity_origin`). The arbitrary centre
is in `Translation.lean`, flows on a time interval in `IntervalFlow.lean`.

The proof follows Huisken's:

* the transport formula (`hasDerivAt_integral_backwardHeatKernel`) differentiates the
  integral, with weight `½ tr(g⁻¹ ∂_t g) = -‖Hvec‖²` under the flow
  (`traceTimeDerivMetric_of_isMeanCurvatureFlowAt`);
* the chain rule along the flow gives `∂_t ρ + ⟨∇ρ, Hvec⟩`
  (`hasDerivAt_backwardHeatKernel_curve`);
* the resulting integrand is `-ρ ‖Hvec + F^⊥/(2τ)‖²` plus a multiple of the first-variation
  integrand (`huisken_pointwise_identity`), whose integral vanishes
  (`integral_firstVariation`).

The mean curvature vector is read in the chart at each point. Under the flow it is the time
velocity, hence continuous, which is what makes the integrands integrable. The one
geometric input beyond the first variation is that the velocity is normal in *every* chart,
not just in the chart at the point (`inner_meanCurvature_fderiv_chartRep`); the library's
`fderiv_fixed_chart_eq_trivialization_comp_mfderiv` reduces this to normality against the
manifold derivative.
-/

open scoped Manifold ContDiff Topology RealInnerProductSpace InnerProductSpace

noncomputable section

namespace HuiskenMonotonicity

open MeasureTheory Manifold DifferentialGeometry DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator

/-! ## The kernel along a curve -/

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The backward heat kernel along a moving point.** For a curve `γ` with velocity `γ'`,

  `d/ds ρ(γ s, s) = ρ (n/(2τ) - ‖γ‖²/(4τ²) - ⟪γ, γ'⟫/(2τ))`,

the sum of the time derivative and of the spatial gradient `-ρ γ/(2τ)` paired with `γ'`. -/
theorem hasDerivAt_backwardHeatKernel_curve (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀)
    {γ : ℝ → E} {γ' : E} (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s ↦ backwardHeatKernel m t₀ s (γ s))
      (backwardHeatKernel m t₀ t (γ t) *
        ((m : ℝ) / (2 * (t₀ - t)) - ‖γ t‖ ^ 2 / (4 * (t₀ - t) ^ 2) -
          ⟪γ t, γ'⟫_ℝ / (2 * (t₀ - t)))) t := by
  set K : ℝ × E → ℝ := fun q ↦ backwardHeatKernel m t₀ q.1 q.2
  have hK : DifferentiableAt ℝ K (t, γ t) :=
    ((contDiffOn_backwardHeatKernel_prod m t₀).contDiffAt
      ((isOpen_lt_fst_backwardHeatKernel t₀).mem_nhds
        (show (t, γ t) ∈ {q : ℝ × E | q.1 < t₀} from hτ))).differentiableAt (by simp)
  set D := fderiv ℝ K (t, γ t)
  have h₁ : D ((1 : ℝ), (0 : E)) = backwardHeatKernel m t₀ t (γ t) *
      ((m : ℝ) / (2 * (t₀ - t)) - ‖γ t‖ ^ 2 / (4 * (t₀ - t) ^ 2)) := by
    have hc : HasDerivAt (K ∘ fun s ↦ (s, γ t)) (D ((1 : ℝ), (0 : E))) t :=
      hK.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t (γ t)))
    exact hc.unique (hasDerivAt_backwardHeatKernel_time m t₀ hτ (γ t))
  have h₂ : D ((0 : ℝ), γ') =
      -(backwardHeatKernel m t₀ t (γ t) / (2 * (t₀ - t))) * ⟪γ t, γ'⟫_ℝ := by
    have hsp : HasFDerivAt (fun y : E ↦ K (t, y)) (D.comp (ContinuousLinearMap.inr ℝ ℝ E))
        (γ t) := hK.hasFDerivAt.comp (γ t) (hasFDerivAt_prodMk_right t (γ t))
    have happ := congrArg (fun L : E →L[ℝ] ℝ ↦ L γ') hsp.fderiv
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inr_apply] at happ
    rw [← happ]
    exact fderiv_backwardHeatKernel m t₀ hτ (γ t) γ'
  have hmain : HasDerivAt (K ∘ fun s ↦ (s, γ s)) (D ((1 : ℝ), γ')) t :=
    hK.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk hγ)
  have hsplit : D ((1 : ℝ), γ') = D ((1 : ℝ), (0 : E)) + D ((0 : ℝ), γ') := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  refine hmain.congr_deriv ?_
  rw [hsplit, h₁, h₂]
  ring

end Kernel

/-! ## Huisken's pointwise identity

Pure algebra in the inner product space `E`: if `F^T ⟂ F^⊥` and `H ⟂ F^T`, then the
chain-rule integrand differs from the squared-norm integrand by a multiple of the
first-variation integrand. -/

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pointwise identity: the chain-rule integrand equals the negated squared-norm
integrand plus `(1/(2τ))` times the first-variation integrand. Uses only the two
orthogonality axioms. -/
lemma huisken_pointwise_identity
    (n : ℕ) (τ : ℝ) (hτ : τ ≠ 0)
    (Fpt Fperp H : E) (ρ : ℝ)
    (hPosDecomp : ⟪Fpt - Fperp, Fperp⟫_ℝ = 0)
    (hMCNormal : ⟪H, Fpt - Fperp⟫_ℝ = 0) :
    ρ * ((n : ℝ) / (2 * τ) - ‖Fpt‖ ^ 2 / (4 * τ ^ 2)
          - ⟪Fpt, H⟫_ℝ / (2 * τ) - ‖H‖ ^ 2) =
      -(ρ * ‖H + (1 / (2 * τ)) • Fperp‖ ^ 2)
        + (1 / (2 * τ)) *
            (ρ * ((n : ℝ) - ‖Fpt - Fperp‖ ^ 2 / (2 * τ) + ⟪H, Fpt⟫_ℝ)) := by
  -- Expand ‖H + (1/(2τ)) • F^⊥‖² = ‖H‖² + ⟨H, F^⊥⟩/τ + ‖F^⊥‖²/(4τ²).
  have h_norm_sq :
      ‖H + (1 / (2 * τ)) • Fperp‖ ^ 2 =
        ‖H‖ ^ 2 + ⟪H, Fperp⟫_ℝ / τ + ‖Fperp‖ ^ 2 / (4 * τ ^ 2) := by
    rw [@norm_add_sq_real E _ _ H ((1 / (2 * τ)) • Fperp), real_inner_smul_right,
        norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  -- Expand ‖F‖² = ‖F^T‖² + ‖F^⊥‖². From posDecomp, ⟨F^T, F^⊥⟩ = 0, so
  -- ‖F‖² = ‖F^T + F^⊥‖² = ‖F^T‖² + 2⟨F^T, F^⊥⟩ + ‖F^⊥‖² = ‖F^T‖² + ‖F^⊥‖².
  have hFsplit : Fpt = (Fpt - Fperp) + Fperp := by abel
  have h_F_norm :
      ‖Fpt‖ ^ 2 = ‖Fpt - Fperp‖ ^ 2 + ‖Fperp‖ ^ 2 := by
    conv_lhs => rw [hFsplit]
    rw [@norm_add_sq_real E _ _ (Fpt - Fperp) Fperp, hPosDecomp]
    ring
  -- From `H ⟂ F^T`: ⟨H, F⟩ = ⟨H, F^T + F^⊥⟩ = 0 + ⟨H, F^⊥⟩ = ⟨H, F^⊥⟩.
  have h_inner_split :
      ⟪H, Fpt⟫_ℝ = ⟪H, Fperp⟫_ℝ := by
    conv_lhs => rw [hFsplit]
    rw [inner_add_right, hMCNormal, zero_add]
  have h_inner_sym : ⟪Fpt, H⟫_ℝ = ⟪H, Fpt⟫_ℝ := real_inner_comm _ _
  rw [h_norm_sq, h_F_norm, h_inner_sym, h_inner_split]
  field_simp
  ring

end Algebra

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

/-- The Borel σ-algebra, matching the one under which `surfaceMeasure` is stated. -/
local instance instMeasurableSpaceMeanCurvatureFlow : MeasurableSpace M := borel M

local instance instBorelSpaceMeanCurvatureFlow : BorelSpace M := ⟨rfl⟩

namespace SmoothImmersion

variable [T2Space M] [I.Boundaryless]

/-! ## Normality of the mean curvature vector in every chart -/

/-- The mean curvature vector is orthogonal to every tangent vector `df(w)`. -/
theorem inner_meanCurvature_mvfderiv (f : SmoothImmersion I M E) (p : M)
    (w : TangentSpace I p) :
    ⟪f.meanCurvature p, mvfderiv I f p w⟫_ℝ = 0 := by
  have hmd : MDifferentiableAt I 𝓘(ℝ, E) f p := f.contMDiff.mdifferentiableAt (by simp)
  have h := DifferentialGeometry.Manifold.mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint I hmd
    BoundarylessManifold.isInteriorPoint
  rw [show mvfderiv I f p w =
      fderiv ℝ (fun y ↦ f ((extChartAt I p).symm y)) (extChartAt I p p) w from
    congrArg (fun L : E₁ →L[ℝ] E ↦ L w) h]
  exact inner_normalPart_fderiv (chartModelBasis E₁).span_eq
    (f.isFrameInverse_chartInvGramOnE p (mem_extChartAt_target p))
    (fun i j ↦ chartInvGramOnE_symm (I := I) _ p i j _) _ w

/-- The mean curvature vector at a point is orthogonal to the tangent vectors of the chart
representation in *any* chart containing it. -/
theorem inner_meanCurvature_fderiv_chartRep (f : SmoothImmersion I M E)
    (α : M) {z : E₁} (hz : z ∈ (extChartAt I α).target) (v : E₁) :
    ⟪f.meanCurvature ((extChartAt I α).symm z), fderiv ℝ (f.chartRep α) z v⟫_ℝ = 0 := by
  set x := (extChartAt I α).symm z
  have hx : x ∈ (extChartAt I α).source := (extChartAt I α).map_target hz
  have hzx : extChartAt I α x = z := (extChartAt I α).right_inv hz
  have hcont : ContinuousAt f x := f.contMDiff.continuous.continuousAt
  have hfx : f x ∈ (extChartAt 𝓘(ℝ, E) (f x)).source := by simp
  have h := DifferentialGeometry.Topology.Manifold.fderiv_fixed_chart_eq_trivialization_comp_mfderiv
    (I := I) (J := 𝓘(ℝ, E)) f α (f x) x hx hfx hcont
  rw [extChartAt_model_space_eq_id, TangentBundle.continuousLinearMapAt_model_space] at h
  have happ := DFunLike.congr_fun h v
  simp only [PartialEquiv.refl_coe, Function.comp_def, id_eq] at happ
  rw [hzx] at happ
  change ⟪_, fderiv ℝ (fun y ↦ f ((extChartAt I α).symm y)) z v⟫_ℝ = 0
  rw [happ]
  exact f.inner_meanCurvature_mvfderiv x _

end SmoothImmersion

namespace SmoothImmersionFamily

variable [T2Space M] [I.Boundaryless]

/-! ## The velocity of a family, read in a chart -/

omit [T2Space M] in
/-- The time velocity of the space-time chart representation is differentiable on the chart
target. -/
theorem differentiableAt_timeVelocity_spaceTimeChartRep (F : SmoothImmersionFamily I M E)
    (α : M) (t : ℝ) {z : E₁} (hz : z ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ (timeVelocity (F.spaceTimeChartRep α) t) z := by
  have hs := isOpen_univ_prod_extChartAt_target (I := I) α
  have hΦ : ContDiffAt ℝ 2 (F.spaceTimeChartRep α) (t, z) :=
    ((F.contDiffOn_spaceTimeChartRep α).contDiffAt
      (hs.mem_nhds ⟨Set.mem_univ _, hz⟩)).of_le (by simp)
  have h1 : DifferentiableAt ℝ (fderiv ℝ (F.spaceTimeChartRep α)) (t, z) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (h1.comp z ((differentiableAt_const t).prodMk differentiableAt_id)).clm_apply
    (differentiableAt_const _)

omit [T2Space M] in
/-- If `∂_t F(p, t) = v`, then the time velocity of the chart representation at the chart
point of `p` is `v`. -/
theorem timeVelocity_spaceTimeChartRep_eq (F : SmoothImmersionFamily I M E) {t : ℝ} (α : M)
    {z : E₁} (hz : z ∈ (extChartAt I α).target) {v : E}
    (hv : HasDerivAt (fun s ↦ F ((extChartAt I α).symm z) s) v t) :
    timeVelocity (F.spaceTimeChartRep α) t z = v := by
  have hs := isOpen_univ_prod_extChartAt_target (I := I) α
  have hd : DifferentiableAt ℝ (F.spaceTimeChartRep α) (t, z) :=
    ((F.contDiffOn_spaceTimeChartRep α).contDiffAt
      (hs.mem_nhds ⟨Set.mem_univ _, hz⟩)).differentiableAt (by simp)
  have hc : HasDerivAt (F.spaceTimeChartRep α ∘ fun s ↦ (s, z))
      (fderiv ℝ (F.spaceTimeChartRep α) (t, z) ((1 : ℝ), (0 : E₁))) t :=
    hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t z))
  exact hc.unique hv

omit [T2Space M] in
/-- The time derivative of a smooth family is continuous in space. -/
theorem continuous_of_hasDerivAt (F : SmoothImmersionFamily I M E) {t : ℝ} {V : M → E}
    (hV : ∀ p, HasDerivAt (fun s ↦ F p s) (V p) t) : Continuous V := by
  rw [continuous_iff_continuousAt]
  intro p
  have hc : ContinuousAt (timeVelocity (F.spaceTimeChartRep p) t) (extChartAt I p p) :=
    (F.differentiableAt_timeVelocity_spaceTimeChartRep p t
      (mem_extChartAt_target p)).continuousAt
  refine (hc.comp (continuousAt_extChartAt p)).congr ?_
  filter_upwards [extChartAt_source_mem_nhds (I := I) p] with q hq
  have hz := (extChartAt I p).map_source hq
  refine F.timeVelocity_spaceTimeChartRep_eq p hz ?_
  rw [(extChartAt I p).left_inv hq]
  exact hV q

/-! ## The first variation of area

For any smooth family, `∂_t dμ = div_M V dμ` with `V` the velocity: the trace of the metric
evolution is twice the tangential divergence of the velocity. Huisken's two volume formulas
are its specialisations, `∂_t dμ = -H² dμ` under mean curvature flow ([7, Corollary 3.6] in
his paper) and `∂_s dμ = (n - H²) dμ` under the rescaled flow (proof of Corollary 3.2). -/

/-- **The first variation of area**: `tr(g⁻¹ ∂_t g) = 2 div_M V` for the velocity `V`, read in
the chart at `x`. -/
theorem traceTimeDerivMetric_eq_two_mul_tangentialDivergence (F : SmoothImmersionFamily I M E)
    (t : ℝ) (x : M) :
    traceTimeDerivMetric (I := I) F.inducedMetricFamily t x =
      2 * tangentialDivergence (F.chartRep t x) (timeVelocity (F.spaceTimeChartRep x) t)
        (chartModelBasis E₁)
        (fun i j ↦ chartInvGramOnE (F.slice t).inducedMetric x i j (extChartAt I x x))
        (extChartAt I x x) := by
  set y := extChartAt I x x
  set b := chartModelBasis E₁
  set V := timeVelocity (F.spaceTimeChartRep x) t
  set gInv : Fin (Module.finrank ℝ E₁) → Fin (Module.finrank ℝ E₁) → ℝ :=
    fun i j ↦ chartInvGramOnE (F.slice t).inducedMetric x i j y
  have hy : y ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hΦ : ContDiffAt ℝ 2 (F.spaceTimeChartRep x) (t, y) :=
    ((F.contDiffOn_spaceTimeChartRep x).contDiffAt
      ((isOpen_univ_prod_extChartAt_target (I := I) x).mem_nhds
        ⟨Set.mem_univ _, hy⟩)).of_le (by simp)
  -- the chart Gram entries are a `frameGram`, which evolves by the product rule
  have hderiv : ∀ i j, deriv (fun s ↦ chartGramMatrix (I := I)
      (F.inducedMetricFamily s) x x i j) t =
      ⟪frameTangent (F.chartRep t x) b y i, frameTangent V b y j⟫_ℝ +
        ⟪frameTangent V b y i, frameTangent (F.chartRep t x) b y j⟫_ℝ := by
    intro i j
    have hfun : (fun s ↦ chartGramMatrix (I := I) (F.inducedMetricFamily s) x x i j) =
        fun s ↦ frameGram (F.chartRep s x) b y i j := by
      funext s
      exact chartGramMatrix_inducedMetric_eq_frameGram_modelBasis F s x
        (mem_extChartAt_source x) i j
    rw [hfun]
    exact (hasDerivAt_frameGram (F := fun s ↦ F.chartRep s x) (V := timeVelocity _) b i j
      fun k ↦ hasDerivAt_fderiv_spatialSlice_of_contDiffAt hΦ (b k)).deriv
  have hinv : (chartGramMatrix (I := I) (F.inducedMetricFamily t) x x)⁻¹ = Matrix.of gInv := by
    ext i j
    change chartInvGramMatrix (I := I) (F.slice t).inducedMetric x x i j =
      chartInvGramOnE (F.slice t).inducedMetric x i j y
    rw [chartInvGramOnE_def, extChartAt_to_inv]
  rw [traceTimeDerivMetric_eq, hinv, Matrix.trace,
    ← trace_frameGram_deriv_eq_two_mul_tangentialDivergence b gInv
      fun i j ↦ chartInvGramOnE_symm (I := I) _ x i j _]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hderiv j i, real_inner_comm (frameTangent (F.chartRep t x) b y i) (frameTangent V b y j)]
  simp only [frameTangent_apply]
  rw [real_inner_comm (fderiv ℝ V y (b i)) (fderiv ℝ (F.chartRep t x) y (b j))]

end SmoothImmersionFamily

namespace SmoothImmersion

variable [T2Space M] [I.Boundaryless]

/-- The mean curvature vector paired with the trace of the second derivative is `‖Hvec‖²`:
`Hvec` is the normal part of that trace. -/
theorem inner_meanCurvature_meanCurvatureVectorFrame (f : SmoothImmersion I M E) (x : M) :
    ⟪f.meanCurvature x, meanCurvatureVectorFrame (f.chartRep x) (chartModelBasis E₁)
        (fun i j ↦ chartInvGramOnE f.inducedMetric x i j (extChartAt I x x))
        (extChartAt I x x)⟫_ℝ = ‖f.meanCurvature x‖ ^ 2 := by
  have hinv := f.isFrameInverse_chartInvGramOnE x (mem_extChartAt_target x)
  have hsymm : ∀ i j, chartInvGramOnE f.inducedMetric x i j (extChartAt I x x) =
      chartInvGramOnE f.inducedMetric x j i (extChartAt I x x) := fun i j ↦
    chartInvGramOnE_symm (I := I) _ x i j _
  have hN : normalPart (f.chartRep x) (chartModelBasis E₁)
      (fun i j ↦ chartInvGramOnE f.inducedMetric x i j (extChartAt I x x)) (extChartAt I x x)
      (f.meanCurvature x) = f.meanCurvature x :=
    normalPart_eq_self fun l ↦ inner_normalPart_frameTangent hinv hsymm _ l
  have h := inner_meanCurvatureNormal_eq hinv hsymm (f.meanCurvature x)
  rw [hN] at h
  exact h.symm.trans (real_inner_self_eq_norm_sq _)

/-- **`div_M Hvec = -‖Hvec‖²`.** For a field `ξ` on the chart that is the mean curvature vector
near the point, its tangential divergence is `-‖Hvec‖²`: `Hvec` is normal, and the divergence
of a normal field is `-⟪ξ, Hvec⟫`. -/
theorem tangentialDivergence_eq_neg_norm_sq_meanCurvature (f : SmoothImmersion I M E)
    (x : M) {ξ : E₁ → E} (hξ : DifferentiableAt ℝ ξ (extChartAt I x x))
    (heq : ∀ᶠ z in 𝓝 (extChartAt I x x), ξ z = f.meanCurvature ((extChartAt I x).symm z)) :
    tangentialDivergence (f.chartRep x) ξ (chartModelBasis E₁)
        (fun i j ↦ chartInvGramOnE f.inducedMetric x i j (extChartAt I x x))
        (extChartAt I x x) = -‖f.meanCurvature x‖ ^ 2 := by
  have hy := mem_extChartAt_target (I := I) x
  have hnormal : IsNormalAlongNear (f.chartRep x) ξ (extChartAt I x x) := by
    filter_upwards [heq, (isOpen_extChartAt_target (I := I) x).mem_nhds hy] with z hz hzt v
    rw [hz]
    exact f.inner_meanCurvature_fderiv_chartRep x hzt v
  rw [tangentialDivergence_of_isNormalAlong (f.contDiffAt_chartRep x hy) hξ hnormal,
    heq.self_of_nhds, extChartAt_to_inv, f.inner_meanCurvature_meanCurvatureVectorFrame]

end SmoothImmersion

namespace SmoothImmersionFamily

variable [T2Space M] [I.Boundaryless]

/-! ## Mean curvature flow at a time -/

/-- `F` moves by **mean curvature flow at time `t`**: `∂_t F = Hvec` at every point, at the
time `t`. The monotonicity formula at `t` needs the flow equation at `t` only. -/
def IsMeanCurvatureFlowAt (F : SmoothImmersionFamily I M E) (t : ℝ) : Prop :=
  ∀ p, HasDerivAt (fun s ↦ F p s) ((F.slice t).meanCurvature p) t

/-- Under mean curvature flow at `t`, the mean curvature vector is continuous: it is the
velocity. -/
theorem continuous_meanCurvature (F : SmoothImmersionFamily I M E) {t : ℝ}
    (hmcf : F.IsMeanCurvatureFlowAt t) : Continuous (F.slice t).meanCurvature :=
  F.continuous_of_hasDerivAt hmcf

/-- **The volume element under mean curvature flow** (Huisken's `∂_t μ_t = -H² μ_t`, from [7,
Corollary 3.6] in his paper): `tr(g⁻¹ ∂_t g) = 2 div_M Hvec = -2 ‖Hvec‖²`. -/
theorem traceTimeDerivMetric_of_isMeanCurvatureFlowAt (F : SmoothImmersionFamily I M E)
    {t : ℝ} (hmcf : F.IsMeanCurvatureFlowAt t) (x : M) :
    traceTimeDerivMetric (I := I) F.inducedMetricFamily t x =
      -2 * ‖(F.slice t).meanCurvature x‖ ^ 2 := by
  have hy := mem_extChartAt_target (I := I) x
  have heq : ∀ᶠ z in 𝓝 (extChartAt I x x), timeVelocity (F.spaceTimeChartRep x) t z =
      (F.slice t).meanCurvature ((extChartAt I x).symm z) := by
    filter_upwards [(isOpen_extChartAt_target (I := I) x).mem_nhds hy] with z hz
    exact F.timeVelocity_spaceTimeChartRep_eq x hz (hmcf _)
  have hdiv : tangentialDivergence (F.chartRep t x) (timeVelocity (F.spaceTimeChartRep x) t)
      (chartModelBasis E₁)
      (fun i j ↦ chartInvGramOnE (F.slice t).inducedMetric x i j (extChartAt I x x))
      (extChartAt I x x) = -‖(F.slice t).meanCurvature x‖ ^ 2 :=
    (F.slice t).tangentialDivergence_eq_neg_norm_sq_meanCurvature x
      (F.differentiableAt_timeVelocity_spaceTimeChartRep x t hy) heq
  rw [F.traceTimeDerivMetric_eq_two_mul_tangentialDivergence t x, hdiv]
  ring

end SmoothImmersionFamily

/-! ## The monotonicity formula -/

/-- The last step of Huisken's proof: if the derivative is the integral of
`-S + c · V`, where `V` is the first-variation integrand and integrates to zero, then it is
`-∫ S`. -/
theorem hasDerivAt_neg_integral_of_eq_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Φ : ℝ → ℝ} {t c : ℝ} {C S V : α → ℝ} (hT : HasDerivAt Φ (∫ p, C p ∂μ) t)
    (hsplit : ∀ p, C p = -S p + c * V p) (hC : Integrable C μ) (hV : Integrable V μ)
    (hV0 : ∫ p, V p ∂μ = 0) : HasDerivAt Φ (-∫ p, S p ∂μ) t := by
  have hS : S = fun p ↦ c * V p - C p := funext fun p ↦ by rw [hsplit]; ring
  rw [hS, integral_sub (hV.const_mul c) hC, integral_const_mul, hV0, mul_zero, zero_sub,
    neg_neg]
  exact hT

namespace SmoothImmersionFamily

variable [T2Space M] [I.Boundaryless]

/-- **Huisken's monotonicity formula** (Huisken 1990, Theorem 3.1), centred at the origin.
For a family of immersions of a closed `n`-manifold moving by mean curvature at time `t < t₀`,

  `d/dt ∫_M ρ(F, t) dμ_t = -∫_M ρ(F, t) ‖Hvec + F^⊥ / (2(t₀ - t))‖² dμ_t`.

As in Huisken's proof: differentiate under the moving measure, with `∂_t μ_t = -H² μ_t`; the
integrand is `-ρ ‖Hvec + F^⊥/(2τ)‖²` plus `1/(2τ)` times the first-variation integrand of
`Y = ρ F / τ`, whose integral vanishes. -/
theorem huisken_monotonicity_origin [CompactSpace M] (F : SmoothImmersionFamily I M E)
    (t₀ : ℝ) {t : ℝ} (hτ : t < t₀) (hmcf : F.IsMeanCurvatureFlowAt t) :
    HasDerivAt
      (fun s ↦ ∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ s (F p s)
        ∂(F.surfaceMeasure s))
      (-∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ t (F p t) *
          ‖(F.slice t).meanCurvature p + (1 / (2 * (t₀ - t))) • (F.slice t).normalPosition p‖ ^ 2
        ∂(F.surfaceMeasure t)) t := by
  set n := Module.finrank ℝ E₁
  set f := F.slice t
  -- the transport integrand, evaluated along the flow
  have hC : ∀ p, deriv (fun s ↦ backwardHeatKernel n t₀ s (F p s)) t +
        (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) F.inducedMetricFamily t p *
          backwardHeatKernel n t₀ t (F p t) =
      backwardHeatKernel n t₀ t (F p t) *
        ((n : ℝ) / (2 * (t₀ - t)) - ‖F p t‖ ^ 2 / (4 * (t₀ - t) ^ 2) -
          ⟪F p t, f.meanCurvature p⟫_ℝ / (2 * (t₀ - t)) - ‖f.meanCurvature p‖ ^ 2) := by
    intro p
    rw [(hasDerivAt_backwardHeatKernel_curve n t₀ hτ (hmcf p)).deriv,
      F.traceTimeDerivMetric_of_isMeanCurvatureFlowAt hmcf p]
    ring
  refine hasDerivAt_neg_integral_of_eq_add (hasDerivAt_integral_backwardHeatKernel F n hτ)
    (c := 1 / (2 * (t₀ - t))) (fun p ↦ ?_) ?_ (f.integrable_firstVariation n t₀ hτ)
    (f.integral_firstVariation n t₀ hτ)
  · -- Huisken's pointwise identity
    have h := huisken_pointwise_identity n (t₀ - t) (sub_pos.mpr hτ).ne' (F p t)
      (f.normalPosition p) (f.meanCurvature p) (backwardHeatKernel n t₀ t (F p t))
      (f.inner_sub_normalPosition p) (f.inner_meanCurvature_sub_normalPosition p)
    rw [show ‖F p t - f.normalPosition p‖ ^ 2 = f.tangentialSqNorm p from
      f.norm_sub_normalPosition_sq p, real_inner_comm (F p t) (f.meanCurvature p)] at h
    rw [hC p, h]
    rfl
  · -- the integrand is continuous on a closed manifold
    have hρ := (f.contMDiff_backwardHeatKernel_comp n t₀ hτ).continuous
    have hFc : Continuous fun p ↦ F p t := (F.contMDiff_timeSlice t).continuous
    have hHc := F.continuous_meanCurvature hmcf
    simp only [hC]
    exact f.integrable_of_continuous (by fun_prop)

end SmoothImmersionFamily

end HuiskenMonotonicity
