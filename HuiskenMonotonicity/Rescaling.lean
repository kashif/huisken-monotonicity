/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.IntervalFlow

/-!
# Rescaling a mean curvature flow

Huisken's §2 rescales a mean curvature flow `M_t`, `0 < t < T`, about its singular time:

  `F̃(p, s) = (2(T - t))^(-1/2) F(p, t)`,   `s(t) = -½ log(T - t)`        (Huisken (3)),

and observes that the rescaled surfaces, defined for `-½ log T < s < ∞`, satisfy

  `∂_s F̃ = H̃ + F̃`                                                     (Huisken (4)).

This file proves that, for a flow on `(a, T)`, so that Corollary 3.2 applies to the
rescaling of an actual mean curvature flow (`ImmersionFlowOn.antitoneOn_integral_rescale`).

The geometric input is the scaling of the mean curvature vector, `H(cF) = c⁻¹ H(F)`
(`SmoothImmersion.meanCurvature_dilate`): the metric scales by `c²`, its inverse by `c⁻²`,
the second derivative by `c`, and the normal projection does not change.
-/

open scoped Manifold ContDiff RealInnerProductSpace

open Set Filter

noncomputable section

namespace HuiskenMonotonicity

open MeasureTheory Manifold DifferentialGeometry DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Geometry.Operator

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

/-- The Borel σ-algebra, matching the one under which `surfaceMeasure` is stated. -/
local instance instMeasurableSpaceRescaling : MeasurableSpace M := borel M

local instance instBorelSpaceRescaling : BorelSpace M := ⟨rfl⟩

/-! ## Dilating an immersion -/

namespace SmoothImmersion

/-- The differential of a dilated map. -/
theorem mvfderiv_const_smul (f : SmoothImmersion I M E) (c : ℝ) (p : M) :
    mvfderiv I (fun q ↦ c • f q) p = c • mvfderiv I f p :=
  ((f.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt.const_smul c).mfderiv

/-- The dilate `c f` of a smooth immersion, `c ≠ 0`. -/
def dilate (f : SmoothImmersion I M E) {c : ℝ} (hc : c ≠ 0) : SmoothImmersion I M E :=
  ⟨fun p ↦ c • f p,
    (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ fun _ : M ↦ c).smul f.contMDiff, fun p v w hvw ↦
    f.mfderiv_injective p <| smul_right_injective E hc <|
      (DFunLike.congr_fun (f.mvfderiv_const_smul c p) v).symm.trans
        (hvw.trans (DFunLike.congr_fun (f.mvfderiv_const_smul c p) w))⟩

@[simp]
theorem dilate_apply (f : SmoothImmersion I M E) {c : ℝ} (hc : c ≠ 0) (p : M) :
    f.dilate hc p = c • f p :=
  rfl

variable [T2Space M]

/-- The chart Gram matrix of a dilate is `c²` times that of the immersion. -/
theorem chartGramMatrix_dilate (f : SmoothImmersion I M E) {c : ℝ} (hc : c ≠ 0)
    (α x : M) :
    chartGramMatrix (I := I) (f.dilate hc).inducedMetric α x =
      (c ^ 2) • chartGramMatrix (I := I) f.inducedMetric α x := by
  have hu : ∀ u : TangentSpace I x, mvfderiv I (f.dilate hc) x u = c • mvfderiv I f x u :=
    fun u ↦ by rw [show ⇑(f.dilate hc) = fun q ↦ c • f q from rfl, f.mvfderiv_const_smul c x]; rfl
  ext i j
  rw [Matrix.smul_apply, chartGramMatrix_inducedMetric, chartGramMatrix_inducedMetric,
    smul_eq_mul, hu, hu]
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- The inverse chart Gram matrix of a dilate is `c⁻²` times that of the immersion. -/
theorem chartInvGramOnE_dilate (f : SmoothImmersion I M E) {c : ℝ} (hc : c ≠ 0) (α : M)
    {y : E₁} (hy : y ∈ (extChartAt I α).target) (i j : Fin (Module.finrank ℝ E₁)) :
    chartInvGramOnE (f.dilate hc).inducedMetric α i j y =
      (c ^ 2)⁻¹ * chartInvGramOnE f.inducedMetric α i j y := by
  set x := (extChartAt I α).symm y
  have hbase : x ∈ (trivializationAt E₁ (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I),
      ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I α).map_target hy
  have hdet : IsUnit (chartGramMatrix (I := I) f.inducedMetric α x).det :=
    Matrix.isUnit_iff_isUnit_det _ |>.mp (chartGramMatrix_posDef (I := I) _ α hbase).isUnit
  have : Invertible (c ^ 2) := invertibleOfNonzero (pow_ne_zero 2 hc)
  have hM : (chartGramMatrix (I := I) (f.dilate hc).inducedMetric α x)⁻¹ =
      (c ^ 2)⁻¹ • (chartGramMatrix (I := I) f.inducedMetric α x)⁻¹ := by
    rw [chartGramMatrix_dilate, Matrix.inv_smul (k := c ^ 2) (h := hdet), invOf_eq_inv]
  have hij := congrFun (congrFun hM i) j
  rw [Matrix.smul_apply, smul_eq_mul] at hij
  exact hij

/-- **The mean curvature vector of a dilate**: `H(c f) = c⁻¹ H(f)`. -/
theorem meanCurvature_dilate (f : SmoothImmersion I M E) {c : ℝ} (hc : c ≠ 0) (p : M) :
    (f.dilate hc).meanCurvature p = c⁻¹ • f.meanCurvature p := by
  have hy : extChartAt I p p ∈ (extChartAt I p).target := mem_extChartAt_target p
  have hg : (fun k l ↦ chartInvGramOnE (f.dilate hc).inducedMetric p k l (extChartAt I p p)) =
      fun k l ↦ (c ^ 2)⁻¹ * chartInvGramOnE f.inducedMetric p k l (extChartAt I p p) := by
    funext k l
    exact f.chartInvGramOnE_dilate hc p hy k l
  change meanCurvatureNormal (c • f.chartRep p) (chartModelBasis E₁)
      (fun k l ↦ chartInvGramOnE (f.dilate hc).inducedMetric p k l (extChartAt I p p))
      (extChartAt I p p) = _
  rw [hg]
  exact meanCurvatureNormal_dilate _ hc _ _ _

end SmoothImmersion

/-! ## Huisken's rescaling -/

/-- The original time `t(s) = T - e^{-2s}` of the rescaled time `s = -½ log(T - t)`. -/
def rescaledTime (T s : ℝ) : ℝ := T - Real.exp (-2 * s)

/-- The rescaling factor `(2(T - t(s)))^(-1/2) = e^s / √2`. -/
def rescalingFactor (s : ℝ) : ℝ := Real.exp s / Real.sqrt 2

theorem rescalingFactor_pos (s : ℝ) : 0 < rescalingFactor s :=
  div_pos (Real.exp_pos s) (Real.sqrt_pos.mpr (by norm_num))

/-- The rescaling factor is `(2(T - t))^(-1/2)`, as in Huisken (3). -/
theorem rescalingFactor_eq (T s : ℝ) :
    rescalingFactor s = (2 * (T - rescaledTime T s)) ^ (-(1 / 2 : ℝ)) := by
  rw [rescalingFactor, rescaledTime, sub_sub_cancel, Real.rpow_neg (by positivity),
    Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul, ← Real.sqrt_eq_rpow]
  rw [show -2 * s * (1 / 2) = -s by ring, Real.exp_neg, mul_inv, inv_inv]
  ring

theorem hasDerivAt_rescaledTime (T s : ℝ) :
    HasDerivAt (rescaledTime T) (2 * Real.exp (-2 * s)) s := by
  have h := (((hasDerivAt_id' s).const_mul (-2 : ℝ)).exp).const_sub T
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_rescalingFactor (s : ℝ) :
    HasDerivAt rescalingFactor (rescalingFactor s) s :=
  (Real.hasDerivAt_exp s).div_const _

/-- The rescaled times: `s > -½ log(T - a)` exactly when `t(s) ∈ (a, T)`. -/
def rescaledTimes (a T : ℝ) : Set ℝ := Ioi (-(1 / 2) * Real.log (T - a))

theorem rescaledTime_mem {a T s : ℝ} (haT : a < T) (hs : s ∈ rescaledTimes a T) :
    rescaledTime T s ∈ Ioo a T := by
  simp only [rescaledTimes, mem_Ioi] at hs
  refine ⟨?_, sub_lt_self _ (Real.exp_pos _)⟩
  have h : Real.exp (-2 * s) < T - a := by
    rw [← Real.exp_log (sub_pos.mpr haT)]
    exact Real.exp_lt_exp.mpr (by linarith)
  rw [rescaledTime]
  linarith

namespace ImmersionFlowOn

variable {a T : ℝ}

/-- **Huisken's rescaling** of a flow on `(a, T)` about the time `T`:
`F̃(p, s) = (2(T - t))^(-1/2) F(p, t)` with `t = T - e^{-2s}`, for `s > -½ log(T - a)`. -/
def rescale (G : ImmersionFlowOn I M E (Ioo a T)) (haT : a < T) :
    ImmersionFlowOn I M E (rescaledTimes a T) where
  isOpen := isOpen_Ioi
  toFun p s := rescalingFactor s • G p (rescaledTime T s)
  contMDiffOn := by
    have hmap : ContMDiffOn ((I.prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun q : M × ℝ ↦ (q.1, rescaledTime T q.2)) (univ ×ˢ rescaledTimes a T) :=
      (contMDiff_fst.prodMk ((contDiff_const.sub
        ((contDiff_const.mul contDiff_id).exp)).contMDiff.comp contMDiff_snd)).contMDiffOn
    have hG := G.contMDiffOn.comp hmap fun q hq ↦ ⟨mem_univ _, rescaledTime_mem haT hq.2⟩
    have hfac : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : M × ℝ ↦ rescalingFactor q.2)
        (univ ×ˢ rescaledTimes a T) :=
      ((Real.contDiff_exp.div_const _).contMDiff.comp contMDiff_snd).contMDiffOn
    exact hfac.smul hG
  mfderiv_injective s hs p := by
    have hc := (rescalingFactor_pos s).ne'
    exact ((G.slice _ (rescaledTime_mem haT hs)).dilate hc).mfderiv_injective p

/-- A time slice of the rescaling is a dilate of a time slice of the flow. -/
theorem slice_rescale (G : ImmersionFlowOn I M E (Ioo a T)) (haT : a < T) {s : ℝ}
    (hs : s ∈ rescaledTimes a T) :
    (G.rescale haT).slice s hs =
      (G.slice _ (rescaledTime_mem haT hs)).dilate (rescalingFactor_pos s).ne' :=
  SmoothImmersion.ext fun _ ↦ rfl

variable [T2Space M] [I.Boundaryless]

omit [I.Boundaryless] in
/-- **The rescaled flow satisfies Huisken's equation (4)**, `∂_s F̃ = H̃ + F̃`. -/
theorem IsMeanCurvatureFlow.rescale {G : ImmersionFlowOn I M E (Ioo a T)}
    (hmcf : G.IsMeanCurvatureFlow) (haT : a < T) :
    (G.rescale haT).IsRescaledMeanCurvatureFlow := by
  intro s hs p
  have ht := rescaledTime_mem haT hs
  have hc := (rescalingFactor_pos s).ne'
  rw [slice_rescale, SmoothImmersion.meanCurvature_dilate]
  -- the chain rule in time, then the product rule with the rescaling factor
  have hG : HasDerivAt (fun r ↦ G p (rescaledTime T r))
      ((2 * Real.exp (-2 * s)) • (G.slice _ ht).meanCurvature p) s :=
    (hmcf _ ht p).scomp s (hasDerivAt_rescaledTime T s)
  have h := (hasDerivAt_rescalingFactor s).smul hG
  refine h.congr_deriv ?_
  change rescalingFactor s • (2 * Real.exp (-2 * s)) • (G.slice _ ht).meanCurvature p +
      rescalingFactor s • G p (rescaledTime T s) =
    (rescalingFactor s)⁻¹ • (G.slice _ ht).meanCurvature p +
      rescalingFactor s • G p (rescaledTime T s)
  congr 1
  rw [smul_smul]
  congr 1
  -- `λ · 2 e^{-2s} = λ⁻¹`, since `λ² = e^{2s}/2`
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [rescalingFactor, inv_div, show -2 * s = -s + -s by ring, Real.exp_add, Real.exp_neg]
  field_simp
  rw [h2]

variable [SigmaCompactSpace M] [CompactSpace M]

/-- **Huisken's monotonicity under rescaling.** For a mean curvature flow of a closed manifold
on `(a, T)`, the rescaled surfaces satisfy Corollary 3.2, so `s ↦ ∫_M ρ̃(F̃) dμ̃_s` is
non-increasing on `-½ log(T - a) < s < ∞`. -/
theorem antitoneOn_integral_rescale (G : ImmersionFlowOn I M E (Ioo a T))
    (hmcf : G.IsMeanCurvatureFlow) (haT : a < T) :
    AntitoneOn (fun s ↦ ∫ p, rescaledHeatKernel ((G.rescale haT) p s)
      ∂((G.rescale haT).surfaceMeasure s)) (rescaledTimes a T) :=
  (G.rescale haT).antitoneOn_integral_rescaled (convex_Ioi _) (hmcf.rescale haT)

end ImmersionFlowOn

end HuiskenMonotonicity
