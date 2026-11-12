/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import DifferentialGeometry.Geometry.Metric.Euclidean.Curvature
import DifferentialGeometry.Geometry.Connection.ChartBridge.Connection.Christoffel

/-!
# Unfolding the ambient second fundamental form

`secondFundamentalFormAmbientAt` is defined through the private `gaussDefectModelValue`, so
its value in charts cannot be named outside its file. This file restates that value publicly,
with the same body, and proves the unfolding by `rfl`:

  `II(u, v) = D²F(u, v) + Γ_M(dι u, dι v) - dι(Γ_N(u, v))`

in the charts at `x` and `ι x`, where `F` is `ι` written in those charts.

It also records that the Christoffel contraction of the Euclidean metric vanishes, from the
library's `euclideanMetric_chartChristoffel_eq_zero`.

Intended upstream: make `gaussDefectModelValue` and `secondFundamentalFormAmbientAt_apply`
public.
-/

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold
open scoped ContDiff Manifold

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [NeZero (Module.finrank ℝ EN)]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The ambient second fundamental form in the charts at `x` and `ι x`:
`D²F(u, v) + Γ_M(dι u, dι v) - dι(Γ_N(u, v))`. A public copy of the library's private
`gaussDefectModelValue`. -/
def secondFundamentalFormModelValue
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) (x : N)
    (u v : EN) : E :=
  let F : EN → E := writtenInExtChartAt IN I x iota
  let xE : EN := extChartAt IN x x
  let iotaE : E := extChartAt I (iota x) (iota x)
  let diota : EN →L[ℝ] E :=
    tangentLinearMapToModel (mfderiv IN I iota x)
  fderiv ℝ (fderiv ℝ F) xE u v +
      chartChristoffelContraction (I := I) gM (iota x)
        (diota u) (diota v) iotaE -
    diota (chartChristoffelContraction (I := IN) gN x u v xE)

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [IN.Boundaryless] [I.Boundaryless] in
/-- **The ambient second fundamental form in charts.** -/
theorem secondFundamentalFormAmbientAt_eq_modelValue
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) (x : N)
    (u v : TangentSpace IN x) :
    secondFundamentalFormAmbientAt gN gM iota x u v =
      (tangentSpaceModelContinuousLinearEquiv (I := I) (iota x)).symm
        (secondFundamentalFormModelValue gN gM iota x
          (tangentSpaceModelContinuousLinearEquiv (I := IN) x u)
          (tangentSpaceModelContinuousLinearEquiv (I := IN) x v)) :=
  rfl

section Euclidean

open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Geometry.Operator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Christoffel contraction of the Euclidean metric vanishes. -/
theorem euclideanMetric_chartChristoffelContraction (x : V) (v w y : V) :
    chartChristoffelContraction (I := 𝓘(ℝ, V)) (euclideanMetric (E := V)) x v w y = 0 := by
  have h0 : ∀ i j k, chartChristoffel (I := 𝓘(ℝ, V)) (euclideanMetric (E := V)) x i j k y = 0 :=
    fun i j k ↦ congrFun (euclideanMetric_chartChristoffel_eq_zero x i j k) y
  simp only [chartChristoffelContraction, h0, zero_mul, Finset.sum_const_zero, zero_smul]

end Euclidean

end DifferentialGeometry.Geometry
