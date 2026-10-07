/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.Geometry.InducedRiemannianMetric
import HuiskenMonotonicity.GaussFormula
import DifferentialGeometry.Geometry.Connection.DivergenceCovariantTrace
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartInverseGramDerivative

/-!
# The extrinsic divergence of a tangential field is the Voss-Weyl divergence

The tangential divergence of a vector field along an immersion is defined extrinsically,
`div_M X = g^{ij} ⟪D̄_{∂_i F} X, ∂_j F⟫`. For a tangential field `X = dF(Z)` it should agree
with the intrinsic divergence of `Z`, which in a chart is the Voss-Weyl formula

  `div Z = (1/√g) ∂_i (√g Z^i)`.

This is the Gauss-formula half of the divergence theorem for an immersed submanifold: the
divergence theorem says `∫ div_M X dμ = -∫ ⟪X, Hvec⟫ dμ`, and for the tangential part it
reduces to the intrinsic `∫ div Z dμ = 0`.

The library computes the right-hand side: `localDivergence` is the Voss-Weyl formula, and it
supplies Jacobi's formula in chart form, `∂_i √g = (∑_k Γ^k_{ik}) √g` with
`∑_k Γ^k_{ik} = ½ g^{kl} ∂_i g_{lk}`. `GaussFormula.lean` computes the left-hand side,
`div_M (∑ Z^k ∂_k F) = ∂_i Z^i + Z^k · ½ g^{ij} ∂_k g_{ij}`. The two meet because the
library's chart Gram matrix of the induced metric, read on the model space, is literally the
`frameGram` of the chart representation against the model basis.
-/

open scoped Manifold ContDiff

noncomputable section

namespace HuiskenMonotonicity

open Manifold DifferentialGeometry DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator
  DifferentialGeometry.Geometry.Connection

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ⊤ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

namespace SmoothImmersionFamily

variable [T2Space M]

/-- On the chart target, the library's inverse chart Gram matrix is an inverse metric for the
model basis in the sense of `IsFrameInverse`. -/
theorem isFrameInverse_chartInvGramOnE [I.Boundaryless] (F : SmoothImmersionFamily I M E)
    (t : ℝ) (α : M) {z : E₁} (hz : z ∈ (extChartAt I α).target) :
    IsFrameInverse (F.chartRep t α) (chartModelBasis E₁) z
      (fun k l => chartInvGramOnE (F.inducedMetric t) α k l z) := by
  have hmem : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hz
  have hbase : (extChartAt I α).symm z ∈ (trivializationAt E₁ (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I),
      ← extChartAt_source_eq_chartAt_source (I := I)]
    exact hmem
  have hmul := chartInvGramMatrix_mul_chartGramMatrix (I := I) (F.inducedMetric t) α hbase
  intro i j
  have hentry := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← chartGramOnE_inducedMetricFamily F α k j t hz]
  rfl

end SmoothImmersionFamily

end HuiskenMonotonicity
