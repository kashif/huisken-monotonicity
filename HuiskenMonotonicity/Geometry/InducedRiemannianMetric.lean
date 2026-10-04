/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.Geometry.InducedMetric
import HuiskenMonotonicity.MetricEvolution
import DifferentialGeometry.Topology.Manifold.MFDeriv.Interior
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

/-! ### The chart Gram matrix of the induced metric

`DifferentialGeometry.Integral.Measure.traceTimeDerivMetric`, the weight consumed by
`volume_variation_formula`, is the trace of `G⁻¹ ∂ₜG` where `G` is
`Tensor.Coordinates.chartGramMatrix` of the metric family at `x₀ = x`. The identification
below is the first step in evaluating that weight for the induced metric: the chart Gram
matrix is the matrix of inner products of the pushed-forward chart frame vectors. -/

/-- The chart Gram matrix of the induced metric is the Gram matrix of the chart frame pushed
forward by `dF_t`. -/
theorem chartGramMatrix_inducedMetric (F : SmoothImmersionFamily I M E) (t : ℝ)
    (himm : ∀ p : M, Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    (x₀ x : M) (i j : Fin (Module.finrank ℝ E₁)) :
    Tensor.Coordinates.chartGramMatrix (I := I) (F.inducedMetric t himm) x₀ x i j =
      @inner ℝ E _
        (mfderiv I 𝓘(ℝ, E) (fun q => F q t) x
          (Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i x))
        (mfderiv I 𝓘(ℝ, E) (fun q => F q t) x
          (Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j x)) := by
  rw [Tensor.Coordinates.chartGramMatrix_apply, inducedMetric_inner]

/-- The same, for the time-indexed family: the entries whose time derivative
`traceTimeDerivMetric` differentiates. -/
theorem chartGramMatrix_inducedMetricFamily (F : SmoothImmersionFamily I M E)
    (himm : ∀ (t : ℝ) (p : M), Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    (t : ℝ) (x₀ x : M) (i j : Fin (Module.finrank ℝ E₁)) :
    Tensor.Coordinates.chartGramMatrix (I := I) (F.inducedMetricFamily himm t) x₀ x i j =
      @inner ℝ E _
        (mfderiv I 𝓘(ℝ, E) (fun q => F q t) x
          (Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i x))
        (mfderiv I 𝓘(ℝ, E) (fun q => F q t) x
          (Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j x)) :=
  chartGramMatrix_inducedMetric F t (himm t) x₀ x i j

/-! ### The chart representation

The chart Gram matrix is a Gram matrix of Fréchet derivatives: `mfderiv` of a time slice,
viewed on the model space, is the `fderiv` of the chart representation
`F_t ∘ (extChartAt I x).symm`. That identification turns the entries of the chart Gram
matrix into `frameGram` of the chart representation, which is the form the metric evolution
results of `MetricEvolution.lean` consume.

The frame used is `chartBasisVecFiber x · x`, the chart frame at its own base point. Its
value is never needed: the tangential calculus is stated for an arbitrary frame, so the
frame may be carried along opaquely. -/

/-- The chart representation of the time slice `F_t` around `x`, as a map between model
spaces. -/
def chartRep (F : SmoothImmersionFamily I M E) (t : ℝ) (x : M) : E₁ → E :=
  fun y => F ((extChartAt I x).symm y) t

/-- The chart frame of the chart around `x₀`, evaluated at `x`, read in the model space.

`MetricFamilyRegularAt` quantifies over `x₀` and over all `x` in the trivialization base
set, so the frame has to be allowed off the diagonal even though `traceTimeDerivMetric`
itself only uses `x₀ = x`. The chart in which the derivative is taken is always the one at
`x`; only the frame comes from `x₀`. -/
def chartFrameAt (x₀ x : M) (i : Fin (Module.finrank ℝ E₁)) : E₁ :=
  Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i x

/-- The chart frame at its own base point, read in the model space. -/
def chartFrame (x : M) (i : Fin (Module.finrank ℝ E₁)) : E₁ :=
  chartFrameAt (I := I) x x i

/-- The chart Gram matrix of the induced metric is `frameGram` of the chart representation.

This is the identification that lets `hasDerivAt_frameGram_of_isNormalAlong` and
`trace_metricEvolution` evaluate `traceTimeDerivMetric`, which is defined through
`chartGramMatrix` at `x₀ = x`. -/
theorem chartGramMatrix_inducedMetric_eq_frameGram [BoundarylessManifold I M]
    (F : SmoothImmersionFamily I M E) (t : ℝ)
    (himm : ∀ p : M, Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    (x₀ x : M) (i j : Fin (Module.finrank ℝ E₁)) :
    Tensor.Coordinates.chartGramMatrix (I := I) (F.inducedMetric t himm) x₀ x i j =
      frameGram (F.chartRep t x) (chartFrameAt (I := I) x₀ x) (extChartAt I x x) i j := by
  have hmd : MDifferentiableAt I 𝓘(ℝ, E) (fun q => F q t) x :=
    (F.contMDiff_timeSlice t).mdifferentiableAt (by simp)
  have hint : I.IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  have h := DifferentialGeometry.Manifold.mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint
    I hmd hint
  rw [chartGramMatrix_inducedMetric, frameGram, frameTangent_apply, frameTangent_apply]
  simp only [chartFrameAt]
  congr 1
  · exact congrArg
      (fun L : E₁ →L[ℝ] E => L (Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i x)) h
  · exact congrArg
      (fun L : E₁ →L[ℝ] E => L (Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j x)) h

/-! ### The time derivative of the chart Gram entries

With the chart Gram matrix identified as a `frameGram`, the metric evolution equation
applies to it directly. The velocity is supplied as a family `V` of fields on the model
space, which is what the chart representation produces. -/

/-- The chart Gram entries of the induced metric family evolve by `-2 ⟪V, D²F(b_i, b_j)⟫`,
the entries whose trace `traceTimeDerivMetric` takes. -/
theorem hasDerivAt_chartGramMatrix_inducedMetricFamily [BoundarylessManifold I M]
    (F : SmoothImmersionFamily I M E)
    (himm : ∀ (t : ℝ) (p : M), Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    {V : ℝ → E₁ → E} {t : ℝ} (x₀ x : M) (i j : Fin (Module.finrank ℝ E₁))
    (hF2 : ContDiff ℝ 2 (F.chartRep t x))
    (hV : Differentiable ℝ (V t))
    (hnormal : IsNormalAlong (F.chartRep t x) (V t))
    (hcomm : ∀ k : Fin (Module.finrank ℝ E₁),
      HasDerivAt
        (fun s => frameTangent (F.chartRep s x) (chartFrameAt (I := I) x₀ x)
          (extChartAt I x x) k)
        (frameTangent (V t) (chartFrameAt (I := I) x₀ x) (extChartAt I x x) k) t) :
    HasDerivAt
      (fun s => Tensor.Coordinates.chartGramMatrix (I := I)
        (F.inducedMetricFamily himm s) x₀ x i j)
      (-2 * @inner ℝ E _ (V t (extChartAt I x x))
        (secondDerivative (F.chartRep t x) (extChartAt I x x)
          (chartFrameAt (I := I) x₀ x i) (chartFrameAt (I := I) x₀ x j))) t := by
  have hfun : (fun s => Tensor.Coordinates.chartGramMatrix (I := I)
        (F.inducedMetricFamily himm s) x₀ x i j)
      = fun s => frameGram (F.chartRep s x) (chartFrameAt (I := I) x₀ x)
          (extChartAt I x x) i j := by
    funext s
    rw [inducedMetricFamily_apply]
    exact chartGramMatrix_inducedMetric_eq_frameGram F s (himm s) x₀ x i j
  rw [hfun]
  exact hasDerivAt_frameGram_of_isNormalAlong
    (F := fun s => F.chartRep s x) (V := V) (chartFrameAt (I := I) x₀ x) i j
    hF2 hV hnormal hcomm

/-- The inverse chart Gram matrix of the induced metric family, as a `Matrix`.

Naming it is not cosmetic: in a position expecting `Idx → Idx → ℝ` the notation `⁻¹` would
elaborate as the pointwise `Pi.instInv` rather than `Matrix.inv`, which is not what
`traceTimeDerivMetric` uses. -/
noncomputable def chartGramInv (F : SmoothImmersionFamily I M E)
    (himm : ∀ (t : ℝ) (p : M), Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    (t : ℝ) (x : M) :
    Matrix (Fin (Module.finrank ℝ E₁)) (Fin (Module.finrank ℝ E₁)) ℝ :=
  (Tensor.Coordinates.chartGramMatrix (I := I) (F.inducedMetricFamily himm t) x x)⁻¹

/-- **The transport weight of the induced metric family.**

`traceTimeDerivMetric`, the quantity `volume_variation_formula` halves to form its weight,
evaluates to `-2 ⟪V, Hvec⟫` for a velocity normal along the immersion. Under mean curvature
flow `V = Hvec`, so the weight becomes `-‖Hvec‖²`, the classical evolution of the volume
element. -/
theorem traceTimeDerivMetric_inducedMetricFamily [BoundarylessManifold I M]
    (F : SmoothImmersionFamily I M E)
    (himm : ∀ (t : ℝ) (p : M), Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    {V : ℝ → E₁ → E} {t : ℝ} (x : M)
    (hF2 : ContDiff ℝ 2 (F.chartRep t x))
    (hV : Differentiable ℝ (V t))
    (hnormal : IsNormalAlong (F.chartRep t x) (V t))
    (hcomm : ∀ k : Fin (Module.finrank ℝ E₁),
      HasDerivAt
        (fun s => frameTangent (F.chartRep s x) (chartFrame (I := I) x)
          (extChartAt I x x) k)
        (frameTangent (V t) (chartFrame (I := I) x) (extChartAt I x x) k) t) :
    traceTimeDerivMetric (I := I) (F.inducedMetricFamily himm) t x =
      -2 * @inner ℝ E _ (V t (extChartAt I x x))
        (meanCurvatureVectorFrame (F.chartRep t x) (chartFrame (I := I) x)
          (F.chartGramInv himm t x) (extChartAt I x x)) := by
  have hderiv : ∀ i j : Fin (Module.finrank ℝ E₁),
      deriv (fun s => Tensor.Coordinates.chartGramMatrix (I := I)
        (F.inducedMetricFamily himm s) x x i j) t =
        -2 * @inner ℝ E _ (V t (extChartAt I x x))
          (secondDerivative (F.chartRep t x) (extChartAt I x x)
            (chartFrame (I := I) x i) (chartFrame (I := I) x j)) :=
    fun i j =>
      (hasDerivAt_chartGramMatrix_inducedMetricFamily F himm x x i j hF2 hV hnormal
        hcomm).deriv
  rw [traceTimeDerivMetric_eq, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, chartGramInv]
  calc ∑ i, ∑ j,
        F.chartGramInv himm t x i j *
          deriv (fun s => Tensor.Coordinates.chartGramMatrix (I := I)
            (F.inducedMetricFamily himm s) x x j i) t
      = ∑ i, ∑ j,
          F.chartGramInv himm t x i j *
            (-2 * @inner ℝ E _ (V t (extChartAt I x x))
              (secondDerivative (F.chartRep t x) (extChartAt I x x)
                (chartFrame (I := I) x i) (chartFrame (I := I) x j))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hderiv j i, secondDerivative_symm hF2]
    _ = -2 * @inner ℝ E _ (V t (extChartAt I x x))
          (meanCurvatureVectorFrame (F.chartRep t x) (chartFrame (I := I) x)
            (F.chartGramInv himm t x) (extChartAt I x x)) :=
        trace_metricEvolution (F := F.chartRep t x) (V := V t)
          (x := extChartAt I x x) (chartFrame (I := I) x) (F.chartGramInv himm t x)

/-- **Mean curvature flow: the transport weight is `-‖Hvec‖²`.**

`volume_variation_formula` halves this, so its weight is `-‖Hvec‖²`, which is the classical
statement `∂_t dμ = -H² dμ` that Huisken's proof cites. -/
theorem traceTimeDerivMetric_inducedMetricFamily_meanCurvatureFlow
    [BoundarylessManifold I M]
    (F : SmoothImmersionFamily I M E)
    (himm : ∀ (t : ℝ) (p : M), Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p))
    {V : ℝ → E₁ → E} {t : ℝ} (x : M)
    (hF2 : ContDiff ℝ 2 (F.chartRep t x))
    (hV : Differentiable ℝ (V t))
    (hnormal : IsNormalAlong (F.chartRep t x) (V t))
    (hcomm : ∀ k : Fin (Module.finrank ℝ E₁),
      HasDerivAt
        (fun s => frameTangent (F.chartRep s x) (chartFrame (I := I) x)
          (extChartAt I x x) k)
        (frameTangent (V t) (chartFrame (I := I) x) (extChartAt I x x) k) t)
    (hmcf : V t (extChartAt I x x) =
      meanCurvatureVectorFrame (F.chartRep t x) (chartFrame (I := I) x)
        (F.chartGramInv himm t x) (extChartAt I x x)) :
    traceTimeDerivMetric (I := I) (F.inducedMetricFamily himm) t x =
      -2 * ‖meanCurvatureVectorFrame (F.chartRep t x) (chartFrame (I := I) x)
        (F.chartGramInv himm t x) (extChartAt I x x)‖ ^ 2 := by
  rw [traceTimeDerivMetric_inducedMetricFamily F himm x hF2 hV hnormal hcomm, hmcf,
    real_inner_self_eq_norm_sq]

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
