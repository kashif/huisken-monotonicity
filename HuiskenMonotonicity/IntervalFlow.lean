/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.Translation
import HuiskenMonotonicity.RescaledFlow
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Flows on an open set of times, and monotonicity

A mean curvature flow of a closed manifold exists only on a bounded time interval: it becomes
singular in finite time. Huisken's rescaled flow, on the other hand, lives on a half-line
`(s₀, ∞)`. This file states Huisken's results for a family of immersions given on an open
set `J` of times only:

* `ImmersionFlowOn.huisken_monotonicity` — Theorem 3.1 at every `t ∈ J` with `t < t₀`;
* `ImmersionFlowOn.antitoneOn_integral` — **monotonicity**: for an interval `J`,
  `t ↦ ∫ ρ_{x₀,t₀} dμ_t` is non-increasing on `J ∩ (-∞, t₀)`;
* `ImmersionFlowOn.huisken_monotonicity_rescaled` and
  `ImmersionFlowOn.antitoneOn_integral_rescaled` — Corollary 3.2 for a rescaled flow, and
  monotonicity of `s ↦ ∫ ρ̃ dμ_s` on all of `J`.

The formulas at `t` depend only on the flow near `t`. A smooth reparametrisation of time
`φ : ℝ → J` that is the identity near `t` turns the flow into a `SmoothImmersionFamily`
agreeing with it near `t` (`ImmersionFlowOn.extendAt`), to which the global-in-time results
apply.
-/

open scoped Manifold ContDiff Topology

open Set Filter

noncomputable section

namespace HuiskenMonotonicity

open MeasureTheory Manifold

/-! ## Reparametrising time -/

/-- A smooth map `φ : ℝ → J` into an open set that is the identity near a given `t ∈ J`. -/
theorem exists_contDiff_reparam {J : Set ℝ} (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ s, φ s ∈ J) ∧ ∀ᶠ s in 𝓝 t, φ s = s := by
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hJ t ht
  let β : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨fun s ↦ t + β (s - t) * (s - t), ?_, fun s ↦ hball ?_, ?_⟩
  · exact contDiff_const.add
      ((β.contDiff.comp (contDiff_id.sub contDiff_const)).mul (contDiff_id.sub contDiff_const))
  · -- `β (s - t) * (s - t)` is zero unless `|s - t| < r`, and then it is smaller than `r`
    have hbound : |β (s - t) * (s - t)| < r := by
      by_cases hs : s - t ∈ Metric.ball (0 : ℝ) r
      · rw [abs_mul, abs_of_nonneg β.nonneg]
        have hlt : |s - t| < r := by simpa [Real.dist_eq] using hs
        calc β (s - t) * |s - t| ≤ 1 * |s - t| :=
              mul_le_mul_of_nonneg_right β.le_one (abs_nonneg _)
          _ < r := by linarith
      · have h0 : β (s - t) = 0 := by
          rw [← Function.notMem_support, β.support_eq]
          exact hs
        rw [h0, zero_mul, abs_zero]
        exact hr0
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
    exact hbound
  · have hmem : Metric.ball t (r / 2) ∈ 𝓝 t := Metric.ball_mem_nhds t (by positivity)
    filter_upwards [hmem] with s hs
    have h1 : β (s - t) = 1 := by
      apply β.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      rw [Metric.mem_ball, Real.dist_eq] at hs
      exact hs.le
    rw [h1, one_mul]
    ring

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

/-- The Borel σ-algebra, matching the one under which `surfaceMeasure` is stated. -/
local instance instMeasurableSpaceIntervalFlow : MeasurableSpace M := borel M

local instance instBorelSpaceIntervalFlow : BorelSpace M := ⟨rfl⟩

/-- Two smooth immersions with the same map are equal. -/
theorem SmoothImmersion.ext {f g : SmoothImmersion I M E} (h : ∀ p, f p = g p) : f = g := by
  cases f
  cases g
  congr
  funext p
  exact h p

variable (I M E) in
/-- A smooth family of immersions `F_t : M → E` defined for times in an open set `J`. -/
structure ImmersionFlowOn (J : Set ℝ) where
  /-- The set of times is open. -/
  isOpen : IsOpen J
  /-- The space-time map; its values outside `J` are irrelevant. -/
  toFun : M → ℝ → E
  /-- Joint smoothness on `M × J`. -/
  contMDiffOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (Function.uncurry toFun) (univ ×ˢ J)
  /-- Every time slice in `J` is an immersion: its differential is injective. -/
  mfderiv_injective : ∀ t ∈ J, ∀ p : M,
    Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q ↦ toFun q t) p)

namespace ImmersionFlowOn

variable {J : Set ℝ}

instance : CoeFun (ImmersionFlowOn I M E J) (fun _ ↦ M → ℝ → E) :=
  ⟨ImmersionFlowOn.toFun⟩

/-- The time slice at `t ∈ J`. -/
def slice (G : ImmersionFlowOn I M E J) (t : ℝ) (ht : t ∈ J) : SmoothImmersion I M E :=
  ⟨fun p ↦ G p t,
    G.contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const) fun _ ↦ ⟨mem_univ _, ht⟩,
    G.mfderiv_injective t ht⟩

/-- `G` moves by mean curvature: `∂_t G = Hvec` at every point and every time of `J`. -/
def IsMeanCurvatureFlow [T2Space M] (G : ImmersionFlowOn I M E J) : Prop :=
  ∀ t (ht : t ∈ J) p, HasDerivAt (fun s ↦ G p s) ((G.slice t ht).meanCurvature p) t

open Classical in
/-- The surface measure at time `t`, and `0` outside `J`. -/
def surfaceMeasure [T2Space M] [SigmaCompactSpace M] (G : ImmersionFlowOn I M E J)
    (t : ℝ) : Measure M :=
  if ht : t ∈ J then (G.slice t ht).surfaceMeasure else 0

/-- A global smooth family agreeing with `G` near `t ∈ J`, obtained by reparametrising
time. -/
def extendAt (G : ImmersionFlowOn I M E J) {t : ℝ} (ht : t ∈ J) :
    SmoothImmersionFamily I M E :=
  let φ := Classical.choose (exists_contDiff_reparam G.isOpen ht)
  have hφ := Classical.choose_spec (exists_contDiff_reparam G.isOpen ht)
  ⟨fun p s ↦ G p (φ s),
    G.contMDiffOn.comp_contMDiff (contMDiff_fst.prodMk (hφ.1.contMDiff.comp contMDiff_snd))
      fun q ↦ ⟨mem_univ _, hφ.2.1 q.2⟩,
    fun s ↦ G.mfderiv_injective (φ s) (hφ.2.1 s)⟩

/-- The extension agrees with `G` at all times near `t`. -/
theorem eventually_extendAt (G : ImmersionFlowOn I M E J) {t : ℝ} (ht : t ∈ J) :
    ∀ᶠ s in 𝓝 t, s ∈ J ∧ ∀ p, G.extendAt ht p s = G p s := by
  have hφ := (Classical.choose_spec (exists_contDiff_reparam G.isOpen ht)).2.2
  filter_upwards [hφ, G.isOpen.mem_nhds ht] with s hs hab
  exact ⟨hab, fun p ↦ congrArg (G p) hs⟩

/-- Near `t`, the slices of the extension are the slices of `G`. -/
theorem eventually_slice_extendAt (G : ImmersionFlowOn I M E J) {t : ℝ}
    (ht : t ∈ J) :
    ∀ᶠ s in 𝓝 t, ∃ hs : s ∈ J, (G.extendAt ht).slice s = G.slice s hs := by
  filter_upwards [G.eventually_extendAt ht] with s hs
  exact ⟨hs.1, SmoothImmersion.ext hs.2⟩

theorem slice_extendAt (G : ImmersionFlowOn I M E J) {t : ℝ} (ht : t ∈ J) :
    (G.extendAt ht).slice t = G.slice t ht := by
  obtain ⟨_, h⟩ := (G.eventually_slice_extendAt ht).self_of_nhds
  exact h

theorem extendAt_apply_self (G : ImmersionFlowOn I M E J) {t : ℝ} (ht : t ∈ J) (p : M) :
    G.extendAt ht p t = G p t :=
  ((G.eventually_extendAt ht).self_of_nhds).2 p

/-- A time derivative of `G` at `t` is one of its extension. -/
theorem hasDerivAt_extendAt (G : ImmersionFlowOn I M E J) {t : ℝ} (ht : t ∈ J) {p : M}
    {v : E} (h : HasDerivAt (fun s ↦ G p s) v t) :
    HasDerivAt (fun s ↦ G.extendAt ht p s) v t :=
  h.congr_of_eventuallyEq <| by
    filter_upwards [G.eventually_extendAt ht] with s hs
    exact hs.2 p

variable [T2Space M]

/-- A mean curvature flow on `J` extends to a family moving by mean curvature at `t`. -/
theorem IsMeanCurvatureFlow.extendAt {G : ImmersionFlowOn I M E J}
    (hmcf : G.IsMeanCurvatureFlow) {t : ℝ} (ht : t ∈ J) :
    (G.extendAt ht).IsMeanCurvatureFlowAt t := fun p ↦ by
  rw [G.slice_extendAt ht]
  exact G.hasDerivAt_extendAt ht (hmcf t ht p)

variable [SigmaCompactSpace M]

/-- Near `t`, the surface measures of the extension are those of `G`. -/
theorem eventually_surfaceMeasure_extendAt (G : ImmersionFlowOn I M E J) {t : ℝ}
    (ht : t ∈ J) :
    ∀ᶠ s in 𝓝 t, (G.extendAt ht).surfaceMeasure s = G.surfaceMeasure s := by
  filter_upwards [G.eventually_slice_extendAt ht] with s ⟨hs, h⟩
  rw [surfaceMeasure, dite_eq_left hs, SmoothImmersionFamily.surfaceMeasure, h]

theorem surfaceMeasure_extendAt_self (G : ImmersionFlowOn I M E J) {t : ℝ} (ht : t ∈ J) :
    (G.extendAt ht).surfaceMeasure t = G.surfaceMeasure t :=
  (G.eventually_surfaceMeasure_extendAt ht).self_of_nhds

/-- The derivative at `t` of `s ↦ ∫ K(s, F_s) dμ_s` is the same for `G` and its extension:
the two agree near `t`. -/
theorem hasDerivAt_integral_of_extendAt (G : ImmersionFlowOn I M E J) {t : ℝ} (ht : t ∈ J)
    {K : ℝ → E → ℝ} {D : ℝ}
    (h : HasDerivAt (fun s ↦ ∫ p, K s (G.extendAt ht p s)
      ∂((G.extendAt ht).surfaceMeasure s)) D t) :
    HasDerivAt (fun s ↦ ∫ p, K s (G p s) ∂(G.surfaceMeasure s)) D t :=
  h.congr_of_eventuallyEq <| by
    filter_upwards [G.eventually_extendAt ht, G.eventually_surfaceMeasure_extendAt ht]
      with s hs hμ
    simp only [hs.2, hμ]

variable [I.Boundaryless] [CompactSpace M]

/-- **Huisken's monotonicity formula** (Huisken 1990, Theorem 3.1) for a mean curvature flow
of a closed `n`-manifold on an open set of times `J`. For `t ∈ J` and the backward
heat kernel centred at `(x₀, t₀)` with `t < t₀`,

  `d/dt ∫_M ρ_{x₀,t₀}(F, t) dμ_t
      = -∫_M ρ_{x₀,t₀}(F, t) ‖Hvec + (F - x₀)^⊥ / (2(t₀ - t))‖² dμ_t`. -/
theorem huisken_monotonicity (G : ImmersionFlowOn I M E J) (hmcf : G.IsMeanCurvatureFlow)
    (x₀ : E) (t₀ : ℝ) {t : ℝ} (ht : t ∈ J) (hτ : t < t₀) :
    HasDerivAt
      (fun s ↦ ∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ s (G p s - x₀)
        ∂(G.surfaceMeasure s))
      (-∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ t (G p t - x₀) *
          ‖(G.slice t ht).meanCurvature p +
            (1 / (2 * (t₀ - t))) • (G.slice t ht).normalComponent p (G p t - x₀)‖ ^ 2
        ∂(G.surfaceMeasure t)) t := by
  have h := (G.extendAt ht).huisken_monotonicity x₀ t₀ hτ (hmcf.extendAt ht)
  simp only [G.slice_extendAt ht, G.extendAt_apply_self ht, G.surfaceMeasure_extendAt_self ht]
    at h
  exact G.hasDerivAt_integral_of_extendAt ht
    (K := fun s x ↦ backwardHeatKernel (Module.finrank ℝ E₁) t₀ s (x - x₀)) h

/-- A function with derivative `-(∫ ρ ‖·‖²)` at every point of a convex open set is
non-increasing there. -/
private theorem antitoneOn_of_hasDerivAt_nonpos {D : Set ℝ} (hD : Convex ℝ D)
    (hDo : IsOpen D) {g : ℝ → ℝ} (hg : ∀ s ∈ D, ∃ c ≤ 0, HasDerivAt g c s) :
    AntitoneOn g D := by
  choose c hc hgc using hg
  refine antitoneOn_of_deriv_nonpos hD
    (fun s hs ↦ (hgc s hs).continuousAt.continuousWithinAt) ?_ ?_
  · rw [hDo.interior_eq]
    exact fun s hs ↦ (hgc s hs).differentiableAt.differentiableWithinAt
  · rw [hDo.interior_eq]
    intro s hs
    rw [(hgc s hs).deriv]
    exact hc s hs

/-- **Huisken's monotonicity**: along a mean curvature flow of a closed manifold on an
interval `J` of times, the Gaussian density `t ↦ ∫_M ρ_{x₀,t₀}(F, t) dμ_t` is non-increasing
on the times of `J` before `t₀`. -/
theorem antitoneOn_integral (G : ImmersionFlowOn I M E J) (hJ : Convex ℝ J)
    (hmcf : G.IsMeanCurvatureFlow) (x₀ : E) (t₀ : ℝ) :
    AntitoneOn
      (fun s ↦ ∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ s (G p s - x₀)
        ∂(G.surfaceMeasure s))
      (J ∩ Iio t₀) :=
  antitoneOn_of_hasDerivAt_nonpos (hJ.inter (convex_Iio t₀)) (G.isOpen.inter isOpen_Iio)
    fun _ hs ↦ ⟨_, neg_nonpos.mpr (integral_nonneg fun _ ↦
      mul_nonneg (backwardHeatKernel_pos hs.2 _).le (sq_nonneg _)),
      G.huisken_monotonicity hmcf x₀ t₀ hs.1 hs.2⟩

/-! ## The rescaled flow -/

/-- `G` satisfies the rescaled mean curvature flow equation `∂_s G = Hvec + G` at every time
of `J` (Huisken 1990, equation (4)). -/
def IsRescaledMeanCurvatureFlow (G : ImmersionFlowOn I M E J) : Prop :=
  ∀ s (hs : s ∈ J) p, HasDerivAt (fun r ↦ G p r) ((G.slice s hs).meanCurvature p + G p s) s

omit [SigmaCompactSpace M] [I.Boundaryless] [CompactSpace M] in
/-- A rescaled flow on `J` extends to a family satisfying the rescaled equation at `s`. -/
theorem IsRescaledMeanCurvatureFlow.extendAt {G : ImmersionFlowOn I M E J}
    (hmcf : G.IsRescaledMeanCurvatureFlow) {s : ℝ} (hs : s ∈ J) :
    (G.extendAt hs).IsRescaledMeanCurvatureFlowAt s := fun p ↦ by
  rw [G.slice_extendAt hs, G.extendAt_apply_self hs]
  exact G.hasDerivAt_extendAt hs (hmcf s hs p)

/-- **The rescaled monotonicity formula** (Huisken 1990, Corollary 3.2) for a rescaled flow
of a closed manifold on an open set of times `J`: at every `s ∈ J`,

  `d/ds ∫_M ρ̃(F) dμ_s = -∫_M ρ̃(F) ‖Hvec + F^⊥‖² dμ_s`,   `ρ̃(x) = exp(-|x|²/2)`. -/
theorem huisken_monotonicity_rescaled (G : ImmersionFlowOn I M E J)
    (hmcf : G.IsRescaledMeanCurvatureFlow) {s : ℝ} (hs : s ∈ J) :
    HasDerivAt (fun r ↦ ∫ p, rescaledHeatKernel (G p r) ∂(G.surfaceMeasure r))
      (-∫ p, rescaledHeatKernel (G p s) *
          ‖(G.slice s hs).meanCurvature p + (G.slice s hs).normalPosition p‖ ^ 2
        ∂(G.surfaceMeasure s)) s := by
  have h := (G.extendAt hs).huisken_monotonicity_rescaled (hmcf.extendAt hs)
  simp only [G.slice_extendAt hs, G.extendAt_apply_self hs, G.surfaceMeasure_extendAt_self hs]
    at h
  exact G.hasDerivAt_integral_of_extendAt hs (K := fun _ x ↦ rescaledHeatKernel x) h

/-- **Monotonicity under the rescaled flow**: on an interval `J` of times,
`s ↦ ∫_M ρ̃(F) dμ_s` is non-increasing. This is the form in which Huisken studies the
rescaled surfaces as `s → ∞`. -/
theorem antitoneOn_integral_rescaled (G : ImmersionFlowOn I M E J) (hJ : Convex ℝ J)
    (hmcf : G.IsRescaledMeanCurvatureFlow) :
    AntitoneOn (fun r ↦ ∫ p, rescaledHeatKernel (G p r) ∂(G.surfaceMeasure r)) J :=
  antitoneOn_of_hasDerivAt_nonpos hJ G.isOpen
    fun _ hs ↦ ⟨_, neg_nonpos.mpr (integral_nonneg fun _ ↦
      mul_nonneg (rescaledHeatKernel_pos _).le (sq_nonneg _)),
      G.huisken_monotonicity_rescaled hmcf hs⟩

end ImmersionFlowOn

end HuiskenMonotonicity
