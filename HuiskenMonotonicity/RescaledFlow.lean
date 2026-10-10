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

open scoped Manifold ContDiff Topology RealInnerProductSpace InnerProductSpace

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

/-- Under the rescaled flow, the mean curvature vector is continuous: it is the velocity minus
the position. -/
theorem continuous_meanCurvature_rescaled (F : SmoothImmersionFamily I M E) {s : ℝ}
    (hmcf : F.IsRescaledMeanCurvatureFlowAt s) : Continuous (F.slice s).meanCurvature := by
  exact ((F.continuous_of_hasDerivAt hmcf).sub (F.contMDiff_timeSlice s).continuous).congr
    fun p ↦ add_sub_cancel_right _ _

/-- **The volume element under the rescaled flow** (Huisken's `dμ_s/ds = (n - H²) μ_s`, proof of
Corollary 3.2): `tr(g⁻¹ ∂_s g) = 2 div_M (Hvec + F) = 2 (n - ‖Hvec‖²)`. -/
theorem traceTimeDerivMetric_of_isRescaledMeanCurvatureFlowAt
    (F : SmoothImmersionFamily I M E) {s : ℝ} (hmcf : F.IsRescaledMeanCurvatureFlowAt s)
    (x : M) :
    traceTimeDerivMetric (I := I) F.inducedMetricFamily s x =
      2 * ((Module.finrank ℝ E₁ : ℝ) - ‖(F.slice s).meanCurvature x‖ ^ 2) := by
  set f := F.slice s
  set y := extChartAt I x x
  set b := chartModelBasis E₁
  set Fc := F.chartRep s x
  set V := timeVelocity (F.spaceTimeChartRep x) s
  set gInv : Fin (Module.finrank ℝ E₁) → Fin (Module.finrank ℝ E₁) → ℝ :=
    fun i j ↦ chartInvGramOnE f.inducedMetric x i j y
  have hy : y ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hV := F.differentiableAt_timeVelocity_spaceTimeChartRep x s hy
  have hFd : DifferentiableAt ℝ Fc y := (f.contDiffAt_chartRep x hy).differentiableAt (by simp)
  -- the velocity is `Hvec + F`, so `V - F` is the mean curvature vector near `y`
  have heq : ∀ᶠ z in 𝓝 y, V z - Fc z = f.meanCurvature ((extChartAt I x).symm z) := by
    filter_upwards [(isOpen_extChartAt_target (I := I) x).mem_nhds hy] with z hz
    rw [show V z = _ from F.timeVelocity_spaceTimeChartRep_eq x hz (hmcf _)]
    exact add_sub_cancel_right _ _
  -- `div V = div (V - F) + div F = -‖Hvec‖² + n`
  have hdivH : tangentialDivergence Fc (fun z ↦ V z - Fc z) b gInv y =
      -‖f.meanCurvature x‖ ^ 2 :=
    f.tangentialDivergence_eq_neg_norm_sq_meanCurvature x (hV.sub hFd) heq
  have hdivF : tangentialDivergence Fc Fc b gInv y = (Module.finrank ℝ E₁ : ℝ) := by
    rw [tangentialDivergence_self Fc b (f.isFrameInverse_chartInvGramOnE x hy),
      Fintype.card_fin]
  rw [tangentialDivergence_sub Fc b gInv hV hFd] at hdivH
  rw [F.traceTimeDerivMetric_eq_two_mul_tangentialDivergence s x]
  change 2 * tangentialDivergence Fc V b gInv y = _
  linarith

/-- **The rescaled monotonicity formula** (Huisken 1990, Corollary 3.2). If a family of
immersions of a closed manifold satisfies the rescaled equation `∂_s F = Hvec + F` at time
`s`, then with `ρ̃(x) = exp(-|x|²/2)`

  `d/ds ∫_M ρ̃(F) dμ_s = -∫_M ρ̃(F) ‖Hvec + F^⊥‖² dμ_s`.

Huisken: "The identity follows from `dμ_s/ds = (n - H²) μ_s` and a calculation analogous to
the proof of Theorem 3.1", which is Huisken's pointwise identity and the first variation
identity at `τ = 1/2`. -/
theorem huisken_monotonicity_rescaled [CompactSpace M] (F : SmoothImmersionFamily I M E)
    {s : ℝ} (hmcf : F.IsRescaledMeanCurvatureFlowAt s) :
    HasDerivAt (fun r ↦ ∫ p, rescaledHeatKernel (F p r) ∂(F.surfaceMeasure r))
      (-∫ p, rescaledHeatKernel (F p s) *
          ‖(F.slice s).meanCurvature p + (F.slice s).normalPosition p‖ ^ 2
        ∂(F.surfaceMeasure s)) s := by
  set n := Module.finrank ℝ E₁
  set f := F.slice s
  -- the transport integrand, with `dμ_s/ds = (n - H²) μ_s`
  have hC : ∀ p, deriv (fun r ↦ rescaledHeatKernel (F p r)) s +
        (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) F.inducedMetricFamily s p *
          rescaledHeatKernel (F p s) =
      rescaledHeatKernel (F p s) *
        ((n : ℝ) - ‖F p s‖ ^ 2 - ⟪F p s, f.meanCurvature p⟫_ℝ - ‖f.meanCurvature p‖ ^ 2) := by
    intro p
    rw [(hasDerivAt_rescaledHeatKernel_curve (hmcf p)).deriv,
      F.traceTimeDerivMetric_of_isRescaledMeanCurvatureFlowAt hmcf p, inner_add_right,
      real_inner_self_eq_norm_sq]
    ring
  refine hasDerivAt_neg_integral_of_eq_add
    (hasDerivAt_integral_comp F (contDiff_rescaledHeatKernel (E := E)) s) (c := 1)
    (fun p ↦ ?_) ?_ f.integrable_firstVariation_rescaled f.integral_firstVariation_rescaled
  · -- Huisken's pointwise identity at `τ = 1/2`
    have h := huisken_pointwise_identity n (1 / 2) (by norm_num) (F p s) (f.normalPosition p)
      (f.meanCurvature p) (rescaledHeatKernel (F p s))
      (f.inner_sub_normalPosition p) (f.inner_meanCurvature_sub_normalPosition p)
    rw [show ‖F p s - f.normalPosition p‖ ^ 2 = f.tangentialSqNorm p from
      f.norm_sub_normalPosition_sq p, real_inner_comm (F p s) (f.meanCurvature p)] at h
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (4 : ℝ) * (1 / 2) ^ 2 = 1 by norm_num,
      div_one, div_one, div_one, div_one, div_one, one_smul, one_mul] at h
    rw [hC p, one_mul]
    exact h
  · -- the integrand is continuous on a closed manifold
    have hρ : Continuous fun p ↦ rescaledHeatKernel (F p s) :=
      contDiff_rescaledHeatKernel.continuous.comp (F.contMDiff_timeSlice s).continuous
    have hFc : Continuous fun p ↦ F p s := (F.contMDiff_timeSlice s).continuous
    have hHc := F.continuous_meanCurvature_rescaled hmcf
    simp only [hC]
    exact f.integrable_of_continuous (by fun_prop)

end SmoothImmersionFamily

end HuiskenMonotonicity
