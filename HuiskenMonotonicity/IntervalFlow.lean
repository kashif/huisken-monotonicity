/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.Translation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Flows on a time interval, and monotonicity

A mean curvature flow of a closed manifold exists only on a bounded time interval: it becomes
singular in finite time. This file states Huisken's theorem for a family of immersions given
on an open time interval `(a, b)` only:

* `ImmersionFlowOn.huisken_monotonicity` — the monotonicity formula at every `t ∈ (a, b)`
  with `t < t₀`;
* `ImmersionFlowOn.antitoneOn_integral` — **monotonicity**: `t ↦ ∫ ρ_{x₀,t₀} dμ_t` is
  non-increasing on `(a, b) ∩ (-∞, t₀)`.

The formula at `t` depends only on the flow near `t`. A smooth reparametrisation of time
`φ : ℝ → (a, b)` that is the identity near `t` turns the flow into a `SmoothImmersionFamily`
agreeing with it near `t` (`ImmersionFlowOn.extendAt`), to which the global-in-time results
apply.
-/

open scoped Manifold ContDiff Topology

open Set Filter

noncomputable section

namespace HuiskenMonotonicity

open MeasureTheory Manifold

/-! ## Reparametrising time -/

/-- A smooth map `φ : ℝ → (a, b)` that is the identity near a given `t ∈ (a, b)`. -/
theorem exists_contDiff_reparam {a b t : ℝ} (ht : t ∈ Ioo a b) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ s, φ s ∈ Ioo a b) ∧ ∀ᶠ s in 𝓝 t, φ s = s := by
  set r := min (t - a) (b - t) with hr
  have hr0 : 0 < r := lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)
  let β : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨fun s => t + β (s - t) * (s - t), ?_, fun s => ?_, ?_⟩
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
    have hra : r ≤ t - a := min_le_left _ _
    have hrb : r ≤ b - t := min_le_right _ _
    rw [abs_lt] at hbound
    constructor <;> linarith [hbound.1, hbound.2]
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
/-- A smooth family of immersions `F_t : M → E` defined for times in the open interval
`(a, b)`. -/
structure ImmersionFlowOn (a b : ℝ) where
  /-- The space-time map; its values outside `(a, b)` are irrelevant. -/
  toFun : M → ℝ → E
  /-- Joint smoothness on `M × (a, b)`. -/
  contMDiffOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (Function.uncurry toFun)
    (univ ×ˢ Ioo a b)
  /-- Every time slice in `(a, b)` is an immersion. -/
  isImmersion : ∀ t ∈ Ioo a b, IsImmersion I 𝓘(ℝ, E) ∞ (fun p => toFun p t)

namespace ImmersionFlowOn

variable {a b : ℝ}

instance : CoeFun (ImmersionFlowOn I M E a b) (fun _ => M → ℝ → E) :=
  ⟨ImmersionFlowOn.toFun⟩

/-- The time slice at `t ∈ (a, b)`. -/
def slice (G : ImmersionFlowOn I M E a b) (t : ℝ) (ht : t ∈ Ioo a b) : SmoothImmersion I M E :=
  ⟨fun p => G p t,
    G.contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const) fun _ => ⟨mem_univ _, ht⟩,
    G.isImmersion t ht⟩

/-- `G` moves by mean curvature: `∂_t G = Hvec` at every point and every time of `(a, b)`. -/
def IsMeanCurvatureFlow [T2Space M] (G : ImmersionFlowOn I M E a b) : Prop :=
  ∀ t (ht : t ∈ Ioo a b) p, HasDerivAt (fun s => G p s) ((G.slice t ht).meanCurvature p) t

/-- The surface measure at time `t`, and `0` outside `(a, b)`. -/
def surfaceMeasure [T2Space M] [SigmaCompactSpace M] (G : ImmersionFlowOn I M E a b)
    (t : ℝ) : Measure M :=
  if ht : t ∈ Ioo a b then (G.slice t ht).surfaceMeasure else 0

/-- A global smooth family agreeing with `G` near `t ∈ (a, b)`, obtained by reparametrising
time. -/
def extendAt (G : ImmersionFlowOn I M E a b) {t : ℝ} (ht : t ∈ Ioo a b) :
    SmoothImmersionFamily I M E :=
  let φ := Classical.choose (exists_contDiff_reparam ht)
  have hφ := Classical.choose_spec (exists_contDiff_reparam ht)
  ⟨fun p s => G p (φ s),
    G.contMDiffOn.comp_contMDiff (contMDiff_fst.prodMk (hφ.1.contMDiff.comp contMDiff_snd))
      fun q => ⟨mem_univ _, hφ.2.1 q.2⟩,
    fun s => G.isImmersion (φ s) (hφ.2.1 s)⟩

/-- The extension agrees with `G` at all times near `t`. -/
theorem eventually_extendAt (G : ImmersionFlowOn I M E a b) {t : ℝ} (ht : t ∈ Ioo a b) :
    ∀ᶠ s in 𝓝 t, s ∈ Ioo a b ∧ ∀ p, G.extendAt ht p s = G p s := by
  have hφ := (Classical.choose_spec (exists_contDiff_reparam ht)).2.2
  filter_upwards [hφ, isOpen_Ioo.mem_nhds ht] with s hs hab
  exact ⟨hab, fun p => congrArg (G p) hs⟩

/-- Near `t`, the slices of the extension are the slices of `G`. -/
theorem eventually_slice_extendAt (G : ImmersionFlowOn I M E a b) {t : ℝ}
    (ht : t ∈ Ioo a b) :
    ∀ᶠ s in 𝓝 t, ∃ hs : s ∈ Ioo a b, (G.extendAt ht).slice s = G.slice s hs := by
  filter_upwards [G.eventually_extendAt ht] with s hs
  exact ⟨hs.1, SmoothImmersion.ext hs.2⟩

theorem slice_extendAt (G : ImmersionFlowOn I M E a b) {t : ℝ} (ht : t ∈ Ioo a b) :
    (G.extendAt ht).slice t = G.slice t ht := by
  obtain ⟨_, h⟩ := (G.eventually_slice_extendAt ht).self_of_nhds
  exact h

variable [T2Space M]

/-- A mean curvature flow on `(a, b)` extends to a family moving by mean curvature at `t`. -/
theorem IsMeanCurvatureFlow.extendAt {G : ImmersionFlowOn I M E a b}
    (hmcf : G.IsMeanCurvatureFlow) {t : ℝ} (ht : t ∈ Ioo a b) :
    (G.extendAt ht).IsMeanCurvatureFlowAt t := by
  intro p
  rw [G.slice_extendAt ht]
  refine (hmcf t ht p).congr_of_eventuallyEq ?_
  filter_upwards [G.eventually_extendAt ht] with s hs
  exact hs.2 p

variable [SigmaCompactSpace M]

/-- Near `t`, the surface measures of the extension are those of `G`. -/
theorem eventually_surfaceMeasure_extendAt (G : ImmersionFlowOn I M E a b) {t : ℝ}
    (ht : t ∈ Ioo a b) :
    ∀ᶠ s in 𝓝 t, (G.extendAt ht).surfaceMeasure s = G.surfaceMeasure s := by
  filter_upwards [G.eventually_slice_extendAt ht] with s ⟨hs, h⟩
  rw [surfaceMeasure, dif_pos hs, SmoothImmersionFamily.surfaceMeasure, h]

variable [I.Boundaryless] [CompactSpace M]

/-- **Huisken's monotonicity formula** (Huisken 1990, Theorem 3.1) for a mean curvature flow
of a closed `n`-manifold on the time interval `(a, b)`. For `t ∈ (a, b)` and the backward
heat kernel centred at `(x₀, t₀)` with `t < t₀`,

  `d/dt ∫_M ρ_{x₀,t₀}(F, t) dμ_t
      = -∫_M ρ_{x₀,t₀}(F, t) ‖Hvec + (F - x₀)^⊥ / (2(t₀ - t))‖² dμ_t`. -/
theorem huisken_monotonicity (G : ImmersionFlowOn I M E a b) (hmcf : G.IsMeanCurvatureFlow)
    (x₀ : E) (t₀ : ℝ) {t : ℝ} (ht : t ∈ Ioo a b) (hτ : t < t₀) :
    HasDerivAt
      (fun s => ∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ s (G p s - x₀)
        ∂(G.surfaceMeasure s))
      (-∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ t (G p t - x₀) *
          ‖(G.slice t ht).meanCurvature p +
            (1 / (2 * (t₀ - t))) • (G.slice t ht).normalComponent p (G p t - x₀)‖ ^ 2
        ∂(G.surfaceMeasure t)) t := by
  set F := G.extendAt ht with hF
  have h := F.huisken_monotonicity x₀ t₀ hτ (hmcf.extendAt ht)
  rw [G.slice_extendAt ht] at h
  have hFt : ∀ p, F p t = G p t := fun p => ((G.eventually_extendAt ht).self_of_nhds).2 p
  have hμt : F.surfaceMeasure t = G.surfaceMeasure t :=
    (G.eventually_surfaceMeasure_extendAt ht).self_of_nhds
  simp only [hFt, hμt] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [G.eventually_extendAt ht, G.eventually_surfaceMeasure_extendAt ht]
    with s hs hμ
  rw [hF]
  simp only [hs.2, hμ]

/-- **Huisken's monotonicity**: along a mean curvature flow of a closed manifold on `(a, b)`,
the Gaussian density `t ↦ ∫_M ρ_{x₀,t₀}(F, t) dμ_t` is non-increasing on the times of
`(a, b)` before `t₀`. -/
theorem antitoneOn_integral (G : ImmersionFlowOn I M E a b) (hmcf : G.IsMeanCurvatureFlow)
    (x₀ : E) (t₀ : ℝ) :
    AntitoneOn
      (fun s => ∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ s (G p s - x₀)
        ∂(G.surfaceMeasure s))
      (Ioo a (min b t₀)) := by
  have hsub : ∀ {s}, s ∈ Ioo a (min b t₀) → s ∈ Ioo a b ∧ s < t₀ := fun hs =>
    ⟨⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩, hs.2.trans_le (min_le_right _ _)⟩
  have hderiv := fun {s} (hs : s ∈ Ioo a (min b t₀)) =>
    G.huisken_monotonicity hmcf x₀ t₀ (hsub hs).1 (hsub hs).2
  refine antitoneOn_of_deriv_nonpos (convex_Ioo a (min b t₀)) ?_ ?_ ?_
  · exact fun s hs => (hderiv hs).continuousAt.continuousWithinAt
  · rw [interior_Ioo]
    exact fun s hs => (hderiv hs).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro s hs
    rw [(hderiv hs).deriv, neg_nonpos]
    exact integral_nonneg fun p => mul_nonneg (backwardHeatKernel_pos (hsub hs).2 _).le
      (sq_nonneg _)

end ImmersionFlowOn

end HuiskenMonotonicity
