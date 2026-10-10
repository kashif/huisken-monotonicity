/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.MeanCurvatureFlow

/-!
# The rescaled monotonicity formula

Near a singular time `T`, Huisken rescales the flow by `F̃(·, s) = (2(T - t))^(-1/2) F(·, t)`,
`s = -½ log(T - t)`. The rescaled surfaces satisfy

  `∂_s F̃ = H̃ + F̃`

(Huisken 1990, equation (4)), and with the Gaussian `ρ̃(x) = exp(-|x|²/2)` (Corollary 3.2)

  `d/ds ∫_M ρ̃(F̃) dμ̃_s = -∫_M ρ̃(F̃) ‖H̃ + F̃^⊥‖² dμ̃_s`.

Huisken's proof: "The identity follows from `dμ_s/ds = (n - H²) μ_s` and a calculation
analogous to the proof of Theorem 3.1." It is followed here.

* The velocity `H̃ + F̃` is not normal, so the volume element evolves by
  `½ tr(g⁻¹ ∂_s g) = div_M (H̃ + F̃) = -‖H̃‖² + n`: the normal divergence identity for
  `H̃`, and `div_M F̃ = n` (`traceTimeDerivMetric_of_isRescaledMeanCurvatureFlowAt`).
* The chain rule gives `∂_s ρ̃(F̃) = -ρ̃ ⟪F̃, H̃ + F̃⟫`.
* `ρ̃` is the backward heat kernel at `τ = 1/2`, up to a constant, so the first variation
  identity and Huisken's pointwise identity of Theorem 3.1 apply at `τ = 1/2`.
-/

open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace

noncomputable section

namespace HuiskenMonotonicity

open MeasureTheory Manifold DifferentialGeometry DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

/-- The Borel σ-algebra, matching the one under which `surfaceMeasure` is stated. -/
local instance instMeasurableSpaceRescaledFlow : MeasurableSpace M := borel M

local instance instBorelSpaceRescaledFlow : BorelSpace M := ⟨rfl⟩

namespace SmoothImmersion

variable [T2Space M] [I.Boundaryless] [CompactSpace M]

/-- **The first variation identity for the rescaled kernel**:
`∫ ρ̃ (n - ‖Fᵀ‖² + ⟪F, Hvec⟫) dμ = 0`, the identity of Theorem 3.1 at `τ = 1/2`. -/
theorem integral_firstVariation_rescaled (f : SmoothImmersion I M E) :
    ∫ p, rescaledHeatKernel (f p) *
        ((Module.finrank ℝ E₁ : ℝ) - f.tangentialSqNorm p +
          ⟪f p, f.meanCurvature p⟫_ℝ) ∂f.surfaceMeasure = 0 := by
  set n := Module.finrank ℝ E₁
  have h := f.integral_firstVariation n (1 / 2) (t := 0) (by norm_num)
  have hpt : ∀ p, rescaledHeatKernel (f p) *
      ((n : ℝ) - f.tangentialSqNorm p + ⟪f p, f.meanCurvature p⟫_ℝ) =
      (2 * Real.pi) ^ ((n : ℝ) / 2) * (backwardHeatKernel n (1 / 2) 0 (f p) *
        ((n : ℝ) - f.tangentialSqNorm p / (2 * (1 / 2 - 0)) +
          ⟪f p, f.meanCurvature p⟫_ℝ)) := by
    intro p
    rw [rescaledHeatKernel_eq n, show (2 : ℝ) * (1 / 2 - 0) = 1 by norm_num, div_one]
    ring
  simp only [hpt]
  rw [integral_const_mul, h, mul_zero]

/-- The rescaled first-variation integrand is integrable on a closed manifold. -/
theorem integrable_firstVariation_rescaled (f : SmoothImmersion I M E) :
    Integrable (fun p ↦ rescaledHeatKernel (f p) *
        ((Module.finrank ℝ E₁ : ℝ) - f.tangentialSqNorm p +
          ⟪f p, f.meanCurvature p⟫_ℝ)) f.surfaceMeasure := by
  set n := Module.finrank ℝ E₁
  refine ((f.integrable_firstVariation n (1 / 2) (t := 0) (by norm_num)).const_mul
    ((2 * Real.pi) ^ ((n : ℝ) / 2))).congr (Filter.Eventually.of_forall fun p ↦ ?_)
  simp only
  rw [rescaledHeatKernel_eq n, show (2 : ℝ) * (1 / 2 - 0) = 1 by norm_num, div_one]
  ring

end SmoothImmersion

namespace SmoothImmersionFamily

variable [T2Space M] [I.Boundaryless]

/-- `F` satisfies the **rescaled mean curvature flow** equation `∂_s F = Hvec + F` at time
`s` (Huisken 1990, equation (4)). -/
def IsRescaledMeanCurvatureFlowAt (F : SmoothImmersionFamily I M E) (s : ℝ) : Prop :=
  ∀ p, HasDerivAt (fun r ↦ F p r) ((F.slice s).meanCurvature p + F p s) s

/-- Under the rescaled flow, the time velocity read in a chart is `Hvec + F`. -/
theorem timeVelocity_spaceTimeChartRep_rescaled (F : SmoothImmersionFamily I M E) {s : ℝ}
    (hmcf : F.IsRescaledMeanCurvatureFlowAt s) (α : M) {z : E₁}
    (hz : z ∈ (extChartAt I α).target) :
    timeVelocity (F.spaceTimeChartRep α) s z =
      (F.slice s).meanCurvature ((extChartAt I α).symm z) + F.chartRep s α z := by
  have hs := isOpen_univ_prod_extChartAt_target (I := I) α
  have hd : DifferentiableAt ℝ (F.spaceTimeChartRep α) (s, z) :=
    ((F.contDiffOn_spaceTimeChartRep α).contDiffAt
      (hs.mem_nhds ⟨Set.mem_univ _, hz⟩)).differentiableAt (by simp)
  have hc : HasDerivAt (F.spaceTimeChartRep α ∘ fun r ↦ (r, z))
      (fderiv ℝ (F.spaceTimeChartRep α) (s, z) ((1 : ℝ), (0 : E₁))) s :=
    hd.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id' s).prodMk (hasDerivAt_const s z))
  exact hc.unique (hmcf ((extChartAt I α).symm z))

/-- Under the rescaled flow, the mean curvature vector is continuous: it is the time
velocity minus the position, read in a chart. -/
theorem continuous_meanCurvature_rescaled (F : SmoothImmersionFamily I M E) {s : ℝ}
    (hmcf : F.IsRescaledMeanCurvatureFlowAt s) : Continuous (F.slice s).meanCurvature := by
  rw [continuous_iff_continuousAt]
  intro p
  have hc : ContinuousAt (fun z ↦ timeVelocity (F.spaceTimeChartRep p) s z - F.chartRep s p z)
      (extChartAt I p p) :=
    (F.differentiableAt_timeVelocity_spaceTimeChartRep p s
      (mem_extChartAt_target p)).continuousAt.sub
      (((F.slice s).contDiffAt_chartRep p (mem_extChartAt_target p)).continuousAt)
  refine (hc.comp (continuousAt_extChartAt p)).congr ?_
  filter_upwards [extChartAt_source_mem_nhds (I := I) p] with q hq
  change timeVelocity _ s (extChartAt I p q) - F.chartRep s p (extChartAt I p q) =
    (F.slice s).meanCurvature q
  rw [F.timeVelocity_spaceTimeChartRep_rescaled hmcf p ((extChartAt I p).map_source hq),
    (extChartAt I p).left_inv hq, add_sub_cancel_right]

/-- **The volume element under the rescaled flow**: `½ tr(g⁻¹ ∂_s g) = n - ‖Hvec‖²`, i.e.
`dμ_s/ds = (n - H²) μ_s`, as in Huisken's proof of Corollary 3.2. -/
theorem traceTimeDerivMetric_of_isRescaledMeanCurvatureFlowAt
    (F : SmoothImmersionFamily I M E) {s : ℝ} (hmcf : F.IsRescaledMeanCurvatureFlowAt s)
    (x : M) :
    traceTimeDerivMetric (I := I) F.inducedMetricFamily s x =
      2 * ((Module.finrank ℝ E₁ : ℝ) - ‖(F.slice s).meanCurvature x‖ ^ 2) := by
  set f := F.slice s
  set y := extChartAt I x x with hy_def
  set b := chartModelBasis E₁ with hb_def
  set Φ := F.spaceTimeChartRep x
  set Fc := F.chartRep s x
  set gInv : Fin (Module.finrank ℝ E₁) → Fin (Module.finrank ℝ E₁) → ℝ :=
    fun i j ↦ chartInvGramOnE f.inducedMetric x i j y with hgInv
  have hy : y ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hsymm : (extChartAt I x).symm y = x := extChartAt_to_inv x
  have hopen := isOpen_extChartAt_target (I := I) x
  have hs := isOpen_univ_prod_extChartAt_target (I := I) x
  have hΦ : ContDiffAt ℝ 2 Φ (s, y) :=
    ((F.contDiffOn_spaceTimeChartRep x).contDiffAt
      (hs.mem_nhds ⟨Set.mem_univ _, hy⟩)).of_le (by simp)
  have hF2 : ContDiffAt ℝ 2 Fc y := f.contDiffAt_chartRep x hy
  have hV := F.differentiableAt_timeVelocity_spaceTimeChartRep x s hy
  have hcomm : ∀ k, HasDerivAt (fun r ↦ frameTangent (F.chartRep r x) b y k)
      (frameTangent (timeVelocity Φ s) b y k) s := fun k ↦
    hasDerivAt_fderiv_spatialSlice_of_contDiffAt hΦ (b k)
  have hinvF : IsFrameInverse Fc b y gInv := f.isFrameInverse_chartInvGramOnE x hy
  have hsymmG : ∀ i j, gInv i j = gInv j i := fun i j ↦
    chartInvGramOnE_symm (I := I) _ x i j _
  have hinv : (chartGramMatrix (I := I) (F.inducedMetricFamily s) x x)⁻¹ = Matrix.of gInv := by
    ext i j
    change chartInvGramMatrix (I := I) f.inducedMetric x x i j =
      chartInvGramOnE f.inducedMetric x i j y
    rw [chartInvGramOnE_def, hsymm]
  have hderiv : ∀ i j, deriv (fun r ↦ chartGramMatrix (I := I)
      (F.inducedMetricFamily r) x x i j) s =
      ⟪frameTangent Fc b y i, frameTangent (timeVelocity Φ s) b y j⟫_ℝ +
        ⟪frameTangent (timeVelocity Φ s) b y i, frameTangent Fc b y j⟫_ℝ := by
    intro i j
    have hfun : (fun r ↦ chartGramMatrix (I := I) (F.inducedMetricFamily r) x x i j) =
        fun r ↦ frameGram (F.chartRep r x) b y i j := by
      funext r
      rw [inducedMetricFamily_apply]
      exact chartGramMatrix_inducedMetric_eq_frameGram_modelBasis F r x
        (mem_extChartAt_source x) i j
    rw [hfun]
    exact (hasDerivAt_frameGram (F := fun r ↦ F.chartRep r x) (V := timeVelocity Φ)
      b i j hcomm).deriv
  -- the trace is twice the tangential divergence of the velocity
  have htrace : traceTimeDerivMetric (I := I) F.inducedMetricFamily s x =
      2 * tangentialDivergence Fc (timeVelocity Φ s) b gInv y := by
    rw [traceTimeDerivMetric_eq, hinv, Matrix.trace,
      ← trace_frameGram_deriv_eq_two_mul_tangentialDivergence b gInv hsymmG]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hderiv j i, real_inner_comm (frameTangent Fc b y i)
      (frameTangent (timeVelocity Φ s) b y j)]
    simp only [frameTangent_apply]
    rw [real_inner_comm (fderiv ℝ (timeVelocity Φ s) y (b i)) (fderiv ℝ Fc y (b j))]
  -- the velocity splits as the normal field `Hvec` plus the position
  set Hc : E₁ → E := fun z ↦ timeVelocity Φ s z - Fc z with hHc
  have hFd : DifferentiableAt ℝ Fc y := hF2.differentiableAt (by norm_num)
  have hHcd : DifferentiableAt ℝ Hc y := hV.sub hFd
  have hHcy : Hc y = f.meanCurvature x := by
    rw [hHc]
    simp only
    rw [F.timeVelocity_spaceTimeChartRep_rescaled hmcf x hy, hsymm, add_sub_cancel_right]
  have hnormal : IsNormalAlongNear Fc Hc y := by
    filter_upwards [hopen.mem_nhds hy] with z hz v
    have hz' : Hc z = f.meanCurvature ((extChartAt I x).symm z) := by
      rw [hHc]
      simp only
      rw [F.timeVelocity_spaceTimeChartRep_rescaled hmcf x hz, add_sub_cancel_right]
    rw [hz']
    exact f.inner_meanCurvature_fderiv_chartRep x hz v
  have hdivV : tangentialDivergence Fc (timeVelocity Φ s) b gInv y =
      tangentialDivergence Fc Hc b gInv y + tangentialDivergence Fc Fc b gInv y := by
    rw [hHc, tangentialDivergence_sub Fc b gInv hV hFd]
    ring
  have hdivH : tangentialDivergence Fc Hc b gInv y = -‖f.meanCurvature x‖ ^ 2 := by
    rw [tangentialDivergence_of_isNormalAlong hF2 hHcd hnormal b gInv, hHcy]
    have hzero : ∀ l, ⟪f.meanCurvature x, frameTangent Fc b y l⟫_ℝ = 0 := fun l ↦
      inner_normalPart_frameTangent hinvF hsymmG _ l
    have hT0 : tangentialPart Fc b gInv y (f.meanCurvature x) = 0 := by
      simp only [tangentialPart, hzero, mul_zero, zero_smul, Finset.sum_const_zero]
    have hN : normalPart Fc b gInv y (f.meanCurvature x) = f.meanCurvature x := by
      rw [normalPart, hT0, sub_zero]
    have hHH := inner_meanCurvatureNormal_eq hinvF hsymmG (f.meanCurvature x)
    rw [hN] at hHH
    rw [← hHH]
    exact congrArg (fun r ↦ -r) (real_inner_self_eq_norm_sq _)
  have hdivF : tangentialDivergence Fc Fc b gInv y = (Module.finrank ℝ E₁ : ℝ) := by
    rw [tangentialDivergence_self Fc b hinvF, Fintype.card_fin]
  rw [htrace, hdivV, hdivH, hdivF]
  ring

/-- **The rescaled monotonicity formula** (Huisken 1990, Corollary 3.2). If a family of
immersions of a closed manifold satisfies the rescaled equation `∂_s F = Hvec + F` at time
`s`, then with `ρ̃(x) = exp(-|x|²/2)`

  `d/ds ∫_M ρ̃(F) dμ_s = -∫_M ρ̃(F) ‖Hvec + F^⊥‖² dμ_s`. -/
theorem huisken_monotonicity_rescaled [CompactSpace M] (F : SmoothImmersionFamily I M E)
    {s : ℝ} (hmcf : F.IsRescaledMeanCurvatureFlowAt s) :
    HasDerivAt (fun r ↦ ∫ p, rescaledHeatKernel (F p r) ∂(F.surfaceMeasure r))
      (-∫ p, rescaledHeatKernel (F p s) *
          ‖(F.slice s).meanCurvature p + (F.slice s).normalPosition p‖ ^ 2
        ∂(F.surfaceMeasure s)) s := by
  set n := Module.finrank ℝ E₁
  set f := F.slice s
  have hρ : Continuous fun p ↦ rescaledHeatKernel (F p s) :=
    contDiff_rescaledHeatKernel.continuous.comp (F.contMDiff_timeSlice s).continuous
  have hFc : Continuous fun p ↦ F p s := (F.contMDiff_timeSlice s).continuous
  have hHc : Continuous f.meanCurvature := F.continuous_meanCurvature_rescaled hmcf
  have hT := hasDerivAt_integral_comp F (contDiff_rescaledHeatKernel (E := E)) s
  -- the chain-rule integrand, with `dμ_s/ds = (n - H²) μ_s`
  have hC : ∀ p, deriv (fun r ↦ rescaledHeatKernel (F p r)) s +
        (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) F.inducedMetricFamily s p *
          rescaledHeatKernel (F p s) =
      rescaledHeatKernel (F p s) *
        ((n : ℝ) - ‖F p s‖ ^ 2 - ⟪F p s, f.meanCurvature p⟫_ℝ -
          ‖f.meanCurvature p‖ ^ 2) := by
    intro p
    rw [(hasDerivAt_rescaledHeatKernel_curve (hmcf p)).deriv,
      F.traceTimeDerivMetric_of_isRescaledMeanCurvatureFlowAt hmcf p, inner_add_right,
      real_inner_self_eq_norm_sq]
    ring
  -- Huisken's pointwise identity at `τ = 1/2`
  have hsplit : ∀ p, rescaledHeatKernel (F p s) *
        ((n : ℝ) - ‖F p s‖ ^ 2 - ⟪F p s, f.meanCurvature p⟫_ℝ -
          ‖f.meanCurvature p‖ ^ 2) =
      -(rescaledHeatKernel (F p s) * ‖f.meanCurvature p + f.normalPosition p‖ ^ 2) +
        rescaledHeatKernel (F p s) *
          ((n : ℝ) - f.tangentialSqNorm p + ⟪F p s, f.meanCurvature p⟫_ℝ) := by
    intro p
    have h := huisken_pointwise_identity n (1 / 2) (by norm_num) (F p s) (f.normalPosition p)
      (f.meanCurvature p) (rescaledHeatKernel (F p s))
      (f.inner_sub_normalPosition p) (f.inner_meanCurvature_sub_normalPosition p)
    rw [show ‖F p s - f.normalPosition p‖ ^ 2 = f.tangentialSqNorm p from
      f.norm_sub_normalPosition_sq p, real_inner_comm (F p s) (f.meanCurvature p)] at h
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (4 : ℝ) * (1 / 2) ^ 2 = 1 by norm_num,
      div_one, div_one, div_one, div_one, div_one, one_smul, one_mul] at h
    linarith
  have hFV : Integrable (fun p ↦ rescaledHeatKernel (F p s) *
      ((n : ℝ) - f.tangentialSqNorm p + ⟪F p s, f.meanCurvature p⟫_ℝ))
      (F.surfaceMeasure s) :=
    f.integrable_firstVariation_rescaled
  have hFV0 : ∫ p, rescaledHeatKernel (F p s) *
      ((n : ℝ) - f.tangentialSqNorm p + ⟪F p s, f.meanCurvature p⟫_ℝ)
      ∂(F.surfaceMeasure s) = 0 :=
    f.integral_firstVariation_rescaled
  have hCint : Integrable (fun p ↦ rescaledHeatKernel (F p s) *
      ((n : ℝ) - ‖F p s‖ ^ 2 - ⟪F p s, f.meanCurvature p⟫_ℝ -
        ‖f.meanCurvature p‖ ^ 2)) (F.surfaceMeasure s) :=
    f.integrable_of_continuous (by fun_prop)
  have hS : Integrable (fun p ↦ rescaledHeatKernel (F p s) *
      ‖f.meanCurvature p + f.normalPosition p‖ ^ 2) (F.surfaceMeasure s) := by
    refine (hFV.sub hCint).congr (Filter.Eventually.of_forall fun p ↦ ?_)
    simp only [Pi.sub_apply, hsplit p]
    ring
  have hval : ∫ p, (deriv (fun r ↦ rescaledHeatKernel (F p r)) s +
        (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) F.inducedMetricFamily s p *
          rescaledHeatKernel (F p s)) ∂(F.surfaceMeasure s) =
      -∫ p, rescaledHeatKernel (F p s) * ‖f.meanCurvature p + f.normalPosition p‖ ^ 2
        ∂(F.surfaceMeasure s) := by
    have hS' : Integrable (fun p ↦ -(rescaledHeatKernel (F p s) *
        ‖f.meanCurvature p + f.normalPosition p‖ ^ 2)) (F.surfaceMeasure s) := hS.neg
    simp only [hC, hsplit]
    rw [integral_add hS' hFV, integral_neg, hFV0, add_zero]
  rw [hval] at hT
  exact hT

end SmoothImmersionFamily

end HuiskenMonotonicity
