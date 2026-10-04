/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.Geometry.InducedMetric
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Analysis.Integration.Measure.Family.VolumeVariation

/-!
# The induced Riemannian metric and surface measure of an immersion family

`HuiskenMonotonicity.Geometry.InducedMetric` builds the pullback inner product

`g_t(v, w) = ⟪dF_t v, dF_t w⟫`

pointwise, but stops short of bundling it as a Riemannian metric: that additionally needs
smooth dependence of the form on the base point in manifold charts.

`DifferentialGeometry` supplies precisely that missing step. Its
`SmoothRiemannianMetric.pullback` bundles the pullback of a metric along an immersion, with
the chart-smoothness discharged by `SmoothRiemannianMetric.pullbackInner_contMDiff`. This
file applies it to the Euclidean metric on the ambient space to obtain

* `inducedMetric` — the bundled `SmoothRiemannianMetric I M` of a single time slice;
* `inducedMetricFamily` — the time-indexed family, in the shape
  `ℝ → SmoothRiemannianMetric I M` required by
  `DifferentialGeometry.Integral.Measure.volume_variation_formula`;
* `surfaceMeasure` — the Riemannian volume measure `dμ_t`, replacing the placeholder
  `HuiskenMonotonicity.SurfaceMeasure`.

## The global-in-time immersion hypothesis

`volume_variation_formula` differentiates the metric family in time at *every* real time
(see `MetricFamilyRegularAt`), so it needs a family defined on all of `ℝ`. The
constructions here therefore take the immersion condition as an argument quantified over
every time, rather than only over `F.IsValidTime`. Supplying junk values outside `[0, T)`
would not do: the regularity hypothesis quantifies over all `t : ℝ`, not just interior
times.

## Measurable structure

`DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure` is stated with the Borel
σ-algebra of `M` installed as a local instance, so this file installs the same one. Any
downstream statement about `surfaceMeasure` must use that σ-algebra, which is why the
measurable structure is *not* taken as an instance parameter here.
-/

open scoped Manifold ContDiff

open MeasureTheory

noncomputable section

namespace HuiskenMonotonicity

open Manifold DifferentialGeometry DifferentialGeometry.Integral.Measure

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ⊤ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

/-- The Borel σ-algebra, matching the local instance under which
`DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure` is stated. -/
local instance : MeasurableSpace M := borel M

local instance : BorelSpace M := ⟨rfl⟩

namespace SmoothImmersionFamily

section Metric

variable [T2Space M]

/-- The Riemannian metric induced on `M` by the time slice `F_t`, bundled as a
`SmoothRiemannianMetric`.

This is the pullback of the ambient Euclidean metric along `F_t`. The smooth dependence on
the base point — the step left open in `HuiskenMonotonicity.Geometry.InducedMetric` — comes
from `DifferentialGeometry.SmoothRiemannianMetric.pullbackInner_contMDiff`. -/
def inducedMetric (F : SmoothImmersionFamily I M E) (t : ℝ)
    (himm : ∀ p : M, Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p)) :
    SmoothRiemannianMetric I M :=
  (euclideanMetric (E := E)).pullback (I := I) (fun p => F p t)
    ((F.contMDiff_timeSlice t).of_le le_top) himm

@[simp]
theorem inducedMetric_inner (F : SmoothImmersionFamily I M E) (t : ℝ)
    (himm : ∀ p : M, Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    (p : M) (v w : TangentSpace I p) :
    (F.inducedMetric t himm).inner p v w =
      @inner ℝ E _ (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p v)
        (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p w) :=
  rfl

/-- The bundled induced metric agrees with the pointwise pullback form of
`HuiskenMonotonicity.Geometry.InducedMetric`. -/
theorem inducedMetric_inner_eq_inducedInner (F : SmoothImmersionFamily I M E) (t : ℝ)
    (himm : ∀ p : M, Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    (p : M) (v w : TangentSpace I p) :
    (F.inducedMetric t himm).inner p v w = F.inducedInner p t v w :=
  rfl

/-- At a valid time the immersion hypothesis of `inducedMetric` is automatic. -/
theorem mfderiv_injective_of_isValidTime (F : SmoothImmersionFamily I M E) {t : ℝ}
    (ht : F.IsValidTime t) (p : M) :
    Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p) :=
  Upstream.isImmersion_mfderiv_injective (F.isImmersion_time' ht) p

/-- The time-indexed family of induced metrics, in the shape consumed by
`DifferentialGeometry.Integral.Measure.volume_variation_formula`. -/
def inducedMetricFamily (F : SmoothImmersionFamily I M E)
    (himm : ∀ (t : ℝ) (p : M), Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p)) :
    ℝ → SmoothRiemannianMetric I M :=
  fun t => F.inducedMetric t (himm t)

@[simp]
theorem inducedMetricFamily_apply (F : SmoothImmersionFamily I M E)
    (himm : ∀ (t : ℝ) (p : M), Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    (t : ℝ) :
    F.inducedMetricFamily himm t = F.inducedMetric t (himm t) :=
  rfl

end Metric

section SurfaceMeasure

variable [T2Space M] [SigmaCompactSpace M]

/-- The surface measure `dμ_t` of the time slice `F_t`: the Riemannian volume measure of the
induced metric.

This replaces the placeholder `HuiskenMonotonicity.SurfaceMeasure`, whose `μ` field was
unconstrained data. -/
def surfaceMeasure (F : SmoothImmersionFamily I M E)
    (himm : ∀ (t : ℝ) (p : M), Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    (t : ℝ) : Measure M :=
  riemannianVolumeMeasure I M (F.inducedMetricFamily himm t)

@[simp]
theorem surfaceMeasure_apply (F : SmoothImmersionFamily I M E)
    (himm : ∀ (t : ℝ) (p : M), Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    (t : ℝ) :
    F.surfaceMeasure himm t = riemannianVolumeMeasure I M (F.inducedMetric t (himm t)) :=
  rfl

/-- The surface measure is the Riemannian measure family of the induced metric family. This
is the form in which `volume_variation_formula` expects the measure. -/
theorem surfaceMeasure_eq_riemannianMeasureFamily (F : SmoothImmersionFamily I M E)
    (himm : ∀ (t : ℝ) (p : M), Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p)) :
    F.surfaceMeasure himm =
      riemannianMeasureFamily (I := I) (M := M) (F.inducedMetricFamily himm) :=
  rfl

end SurfaceMeasure

end SmoothImmersionFamily

end HuiskenMonotonicity
