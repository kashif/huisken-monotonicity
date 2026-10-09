/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.Geometry.InducedRiemannianMetric
import HuiskenMonotonicity.HeatKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The transport formula for a moving surface measure

`DifferentialGeometry.Integral.Measure.volume_variation_formula` differentiates an integral
against a moving Riemannian measure. Two hypotheses stand between it and Huisken's
situation, and both are global in time.

The metric family is fine: `metricFamilyRegularAt_inducedMetricFamily` discharges
`MetricFamilyRegularAt` for the induced metric family, because a `SmoothImmersionFamily` is
jointly smooth on all of `M × ℝ` by construction.

The integrand is not. `FunctionRegularAt` asks for continuity on all of `ℝ × M`, and the
backward heat kernel centred at `t₀` is singular there. Since the conclusion is a derivative
at a point, the way through is to replace the integrand by one that agrees with it near the
time in question and is globally regular, then transfer with
`volume_variation_formula_of_eventuallyEq`.

This file builds that replacement: a smooth time cutoff, equal to one near `t` and supported
strictly before `t₀`, multiplied into the kernel. Away from the support the product is
identically zero, and on `{s < t₀}` it is a product of smooth functions, so the two
descriptions glue to something globally smooth.
-/

open scoped Manifold ContDiff
open Metric

noncomputable section

namespace HuiskenMonotonicity

open Manifold DifferentialGeometry DifferentialGeometry.Integral.Measure

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

/-- The Borel σ-algebra, matching the local instance under which the library states
`riemannianVolumeMeasure`. -/
local instance : MeasurableSpace M := borel M

local instance : BorelSpace M := ⟨rfl⟩

/-! ## The time cutoff -/

/-- A smooth bump in time, equal to one on `|s - t| ≤ (t₀-t)/4` and supported in
`|s - t| < (t₀-t)/2`. The outer radius is chosen so that the support lies strictly before
`t₀`, which is where the kernel is singular. -/
def timeCutoff {t₀ t : ℝ} (h : t < t₀) : ContDiffBump t where
  rIn := (t₀ - t) / 4
  rOut := (t₀ - t) / 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

@[simp]
lemma timeCutoff_rOut {t₀ t : ℝ} (h : t < t₀) :
    (timeCutoff h).rOut = (t₀ - t) / 2 := rfl

/-- The cutoff is one on a neighbourhood of `t`. -/
lemma timeCutoff_eventuallyEq_one {t₀ t : ℝ} (h : t < t₀) :
    ∀ᶠ s in nhds t, (timeCutoff h) s = 1 :=
  (timeCutoff h).eventuallyEq_one

/-- Beyond the support of the cutoff the time is past `t + (t₀-t)/2`, hence the cutoff
vanishes there. -/
lemma timeCutoff_eq_zero_of_gt {t₀ t : ℝ} (h : t < t₀) {s : ℝ}
    (hs : (t + t₀) / 2 < s) : (timeCutoff h) s = 0 := by
  refine (timeCutoff h).zero_of_le_dist ?_
  rw [timeCutoff_rOut h, Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

/-! ## The cut-off integrand -/

/-- The kernel along the flow, damped by the time cutoff. Agrees with the undamped
integrand near `t`, and is globally smooth. -/
def cutoffIntegrand (F : SmoothImmersionFamily I M E) (n : ℕ) {t₀ t : ℝ} (h : t < t₀) :
    ℝ → M → ℝ :=
  fun s x => (timeCutoff h) s * backwardHeatKernel n t₀ s (F x s)

/-- The space-time map of the family, read as a function of `(time, point)`. -/
lemma contMDiffAt_flow_swap (F : SmoothImmersionFamily I M E) (p : ℝ × M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞ (fun q : ℝ × M => F q.2 q.1) p := by
  have hswap : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × M => (q.2, q.1)) := contMDiff_snd.prodMk contMDiff_fst
  exact ((F.contMDiff_spaceTime.comp hswap).of_le (by simp)).contMDiffAt

/-- **The cut-off integrand is globally smooth.**

Two descriptions glue. Where the time is before `t₀` it is a product of the cutoff with the
kernel along the flow, both smooth there. Where the time is past the support of the cutoff
it vanishes identically. Every time is in one case or the other, since the support ends
strictly before `t₀`. -/
theorem contMDiff_cutoffIntegrand (F : SmoothImmersionFamily I M E) (n : ℕ)
    {t₀ t : ℝ} (h : t < t₀) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => cutoffIntegrand F n h p.1 p.2) := by
  intro p
  rcases lt_or_ge p.1 t₀ with hlt | hge
  · -- before `t₀`: a product of smooth factors
    have hcut : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => (timeCutoff h) q.1) p :=
      (((timeCutoff h).contDiff).contDiffAt).comp_contMDiffAt
        contMDiff_fst.contMDiffAt
    have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞
        (fun q : ℝ × M => (q.1, F q.2 q.1)) p :=
      (contMDiff_fst.contMDiffAt).prodMk_space (contMDiffAt_flow_swap F p)
    have hker : ContDiffAt ℝ ∞
        (fun y : ℝ × E => backwardHeatKernel n t₀ y.1 y.2) (p.1, F p.2 p.1) :=
      ((contDiffOn_backwardHeatKernel_prod n t₀).contDiffAt
        ((isOpen_lt_fst_backwardHeatKernel (V := E) t₀).mem_nhds hlt)).of_le (by simp)
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        ((fun y : ℝ × E => backwardHeatKernel n t₀ y.1 y.2) ∘
          fun q : ℝ × M => (q.1, F q.2 q.1)) p :=
      ContDiffAt.comp_contMDiffAt (I := 𝓘(ℝ, ℝ).prod I)
        (g := fun y : ℝ × E => backwardHeatKernel n t₀ y.1 y.2)
        (f := fun q : ℝ × M => (q.1, F q.2 q.1)) (x := p) hker hpair
    exact hcut.mul hcomp
  · -- past the support of the cutoff: identically zero nearby
    have hopen : IsOpen {q : ℝ × M | (t + t₀) / 2 < q.1} :=
      isOpen_lt continuous_const continuous_fst
    have hmem : p ∈ {q : ℝ × M | (t + t₀) / 2 < q.1} := by
      have : (t + t₀) / 2 < t₀ := by linarith
      exact lt_of_lt_of_le this hge
    have hzero : ∀ᶠ q in nhds p,
        (fun q : ℝ × M => cutoffIntegrand F n h q.1 q.2) q = (fun _ : ℝ × M => (0 : ℝ)) q := by
      filter_upwards [hopen.mem_nhds hmem] with q hq
      simp only [cutoffIntegrand, timeCutoff_eq_zero_of_gt h hq, zero_mul]
    exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hzero

/-! ## The transport formula -/

/-- The cut-off integrand is regular in the library's sense. -/
theorem functionRegularAt_cutoffIntegrand (F : SmoothImmersionFamily I M E) (n : ℕ)
    {t₀ t : ℝ} (h : t < t₀) (t' : ℝ) :
    FunctionRegularAt (M := M) (cutoffIntegrand F n h) t' :=
  FunctionRegularAt.of_contMDiff (I := I) _ (contMDiff_cutoffIntegrand F n h) t'

/-- Near `t` the cut-off integrand is the kernel along the flow. -/
theorem cutoffIntegrand_eventuallyEq (F : SmoothImmersionFamily I M E) (n : ℕ)
    {t₀ t : ℝ} (h : t < t₀) :
    ∀ᶠ s in nhds t,
      (fun x : M => backwardHeatKernel n t₀ s (F x s)) = cutoffIntegrand F n h s := by
  filter_upwards [timeCutoff_eventuallyEq_one h] with s hs
  funext x
  rw [cutoffIntegrand, hs, one_mul]

/-- **The transport formula for the surface measure of an immersion family.**

For `t < t₀`,

`d/dt ∫ ρ(F(·,t)) dμ_t = ∫ (∂_t ρ(F(·,t)) + ½ tr(g⁻¹ ∂_t g) · ρ(F(·,t))) dμ_t`,

with `μ_t` the surface measure of the induced metric. Under mean curvature flow the weight
`½ tr(g⁻¹ ∂_t g)` is `-‖Hvec‖²` (`traceTimeDerivMetric_of_isMeanCurvatureFlow`). -/
theorem hasDerivAt_integral_backwardHeatKernel
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (F : SmoothImmersionFamily I M E)
    (n : ℕ) {t₀ t : ℝ} (h : t < t₀) :
    HasDerivAt
      (fun s : ℝ => ∫ x, backwardHeatKernel n t₀ s (F x s) ∂(F.surfaceMeasure s))
      (∫ x, (deriv (fun s : ℝ => backwardHeatKernel n t₀ s (F x s)) t
              + (1 / 2 : ℝ) *
                traceTimeDerivMetric (I := I) (F.inducedMetricFamily) t x *
                backwardHeatKernel n t₀ t (F x t))
          ∂(F.surfaceMeasure t)) t := by
  have hmeas := F.surfaceMeasure_eq_riemannianMeasureFamily
  rw [hmeas]
  exact volume_variation_formula_of_eventuallyEq (I := I)
    (F.metricFamilyRegularAt_inducedMetricFamily t)
    (functionRegularAt_cutoffIntegrand F n h t)
    (cutoffIntegrand_eventuallyEq F n h)

end HuiskenMonotonicity
