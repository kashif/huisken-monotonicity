/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import DifferentialGeometry.Geometry.Operator.Gradient.Basic

/-!
# The mean curvature vector of an isometric immersion

`DifferentialGeometry` carries the vector-valued second fundamental form of a Riemannian
isometric immersion, `secondFundamentalFormAt`, with values in
`IsRiemannianIsometricImmersion.normalSpaceAt`. It does not carry its metric trace. This
file adds that trace: the **mean curvature vector** `Hvec = tr_{gN} A`.

A search of the library finds no declaration mentioning mean curvature in any spelling, so
this is new API rather than a restatement.

## Main definitions

* `meanCurvatureVectorInBasis h basis gInv` — the trace `gInv i j • A (basis i) (basis j)`
  relative to a basis of the tangent space and a matrix of inverse-metric components.
* `meanCurvatureVectorAt h x` — the mean curvature vector, obtained by instantiating the
  above at the chart frame `chartFrameBasisAt x` and the library's inverse chart Gram matrix,
  the convention of the library's chart Gram matrix, Voss-Weyl divergence and Laplacian.

## Conventions

The basis-relative shape follows `Operator.metricTrace0S2TensorInBasis`, which traces a
`(0, s+2)`-tensor as `∑ i, ∑ j, gInv i j • …`, and the correctness of the component matrix
is expressed with the library's own `Tensor0SBundle.MetricInverseInBasis` predicate rather
than a matrix inverse. The canonical instance uses the library's `chartInvGramMatrix`, so no new
inverse-metric construction is introduced.

Tracing against a basis, rather than summing over a `gN`-orthonormal basis, avoids
installing a second `InnerProductSpace` structure on `TangentSpace IN x` alongside the one
coming from the model space; that clash is why the library elsewhere resorts to
`attribute [-instance]`.

The value lies in `h.normalSpaceAt x` by construction, so normality is a typing fact rather
than a theorem, and no orientation or unit normal is chosen. The definition is therefore
available in every codimension and on non-orientable submanifolds.

## Remaining work

`meanCurvatureVectorInBasis` is independent of the chosen basis, by
`Tensor0SBundle.MetricInverseInBasis.unique` once both bases are related by a change of
basis. The library proves uniqueness of `gInv` for a *fixed* basis
(`MetricInverseInBasis.unique`) and its symmetry (`MetricInverseInBasis.symmetric`), but has
no cross-basis invariance lemma for a metric trace, so that statement is left to a
follow-up rather than asserted here.

Intended upstream location: `DifferentialGeometry/Geometry/Submanifold/MeanCurvature.lean`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold
open scoped ContDiff Manifold BigOperators

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

section MeanCurvature

variable {gN : SmoothRiemannianMetric IN N}
  {gM : SmoothRiemannianMetric I M} {iota : N → M}

/-- The metric trace of the second fundamental form relative to a basis of the tangent space
and a matrix `gInv` of inverse-metric components:

`∑ i, ∑ j, gInv i j • A (basis i) (basis j)`.

The intended `gInv` satisfies `Tensor0SBundle.MetricInverseInBasis gN x basis gInv`; for the
mean curvature vector proper, use `meanCurvatureVectorAt`, which supplies the canonical
coordinate frame and its inverse-metric components. -/
def meanCurvatureVectorInBasis
    {Idx : Type*} [Fintype Idx]
    (h : IsRiemannianIsometricImmersion gN gM iota) {x : N}
    (basis : Module.Basis Idx ℝ (TangentSpace IN x))
    (gInv : Idx → Idx → ℝ) :
    h.normalSpaceAt x :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j • h.secondFundamentalFormAt x (basis i) (basis j)

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [IN.Boundaryless] [I.Boundaryless] in
theorem meanCurvatureVectorInBasis_eq_sum
    {Idx : Type*} [Fintype Idx]
    (h : IsRiemannianIsometricImmersion gN gM iota) {x : N}
    (basis : Module.Basis Idx ℝ (TangentSpace IN x))
    (gInv : Idx → Idx → ℝ) :
    meanCurvatureVectorInBasis h basis gInv =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j • h.secondFundamentalFormAt x (basis i) (basis j) :=
  rfl

/-- The chart frame at `x`: the library's `chartBasisVecFiber x · x`, which is the model basis
`chartModelBasis` read in the tangent space at the centre of the chart. It is the frame the
library's chart Gram matrix, Voss-Weyl divergence and Laplacian use. -/
def chartFrameBasisAt (x : N) : Module.Basis (Fin (Module.finrank ℝ EN)) ℝ (TangentSpace IN x) :=
  (Tensor.Coordinates.chartModelBasis EN).map
    (tangentSpaceModelContinuousLinearEquiv (I := IN) x).symm.toLinearEquiv

/-- The **mean curvature vector** of an isometric immersion at `x`: the metric trace of the
second fundamental form, taken in the chart frame at `x` against the library's inverse chart
Gram matrix.

By construction the value lies in `h.normalSpaceAt x`, so the definition needs neither an
orientation nor a unit normal, and applies in any codimension. -/
def meanCurvatureVectorAt
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    h.normalSpaceAt x :=
  meanCurvatureVectorInBasis h (chartFrameBasisAt x)
    (fun i j ↦ Operator.chartInvGramMatrix (I := IN) gN x x i j)

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [IN.Boundaryless] [I.Boundaryless] in
@[simp]
theorem meanCurvatureVectorAt_eq_inBasis
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    meanCurvatureVectorAt h x =
      meanCurvatureVectorInBasis h (chartFrameBasisAt x)
        (fun i j ↦ Operator.chartInvGramMatrix (I := IN) gN x x i j) :=
  rfl

end MeanCurvature

end DifferentialGeometry.Geometry
