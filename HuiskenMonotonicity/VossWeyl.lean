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
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

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

/-- The chart representation of a time slice is `C²` at points of the chart target. -/
theorem contDiffAt_chartRep [I.Boundaryless] (F : SmoothImmersionFamily I M E) (t : ℝ)
    (α : M) {y : E₁} (hy : y ∈ (extChartAt I α).target) :
    ContDiffAt ℝ 2 (F.chartRep t α) y := by
  have hs := isOpen_univ_prod_extChartAt_target (I := I) α
  have hmem : ((t, y) : ℝ × E₁) ∈ (Set.univ : Set ℝ) ×ˢ (extChartAt I α).target :=
    ⟨Set.mem_univ _, hy⟩
  have hΦ : ContDiffAt ℝ 2 (F.spaceTimeChartRep α) (t, y) :=
    ((F.contDiffOn_spaceTimeChartRep α).contDiffAt (hs.mem_nhds hmem)).of_le (by simp)
  have hcomp : ContDiffAt ℝ 2 (F.spaceTimeChartRep α ∘ fun z : E₁ => ((t, z) : ℝ × E₁)) y :=
    hΦ.comp y (contDiffAt_const.prodMk contDiffAt_id)
  exact hcomp

/-- The library's partial derivative of a chart Gram entry is the Fréchet derivative of the
corresponding `frameGram` entry, since the two functions agree on the open chart target. -/
theorem partialDeriv_chartGramOnE [I.Boundaryless] (F : SmoothImmersionFamily I M E)
    (t : ℝ) (α : M) {y : E₁} (hy : y ∈ (extChartAt I α).target)
    (i j k : Fin (Module.finrank ℝ E₁)) :
    partialDeriv k (chartGramOnE (F.inducedMetric t) α i j) y =
      fderiv ℝ (fun z => frameGram (F.chartRep t α) (chartModelBasis E₁) z i j) y
        (chartModelBasis E₁ k) := by
  have hev : chartGramOnE (F.inducedMetric t) α i j =ᶠ[nhds y]
      fun z => frameGram (F.chartRep t α) (chartModelBasis E₁) z i j := by
    filter_upwards [(isOpen_extChartAt_target (I := I) α).mem_nhds hy] with z hz
    exact chartGramOnE_inducedMetricFamily F α i j t hz
  rw [partialDeriv, hev.fderiv_eq]

/-- **The Voss-Weyl divergence is the extrinsic tangential divergence.**

For coefficient functions `Z^i` on the chart, the Voss-Weyl formula
`(1/√g) ∂_i(√g Z^i)` for the induced metric equals the tangential divergence of the
tangential field `∑ Z^k ∂_k F` along the chart representation.

The left-hand side is the library's `localDivergence` written out; the right-hand side is the
extrinsic divergence of `TangentialCalculus.lean`. Both reduce to
`∂_i Z^i + Z^i · ½ g^{kl} ∂_i g_{kl}`: the left by the library's form of Jacobi's formula,
the right by the contracted Christoffel identity. -/
theorem vossWeyl_eq_tangentialDivergence [I.Boundaryless] (F : SmoothImmersionFamily I M E)
    (t : ℝ) (α : M) {y : E₁} (hy : y ∈ (extChartAt I α).target)
    {Z : Fin (Module.finrank ℝ E₁) → E₁ → ℝ} (hZ : ∀ k, DifferentiableAt ℝ (Z k) y) :
    (∑ i, partialDeriv i (fun z => Z i z * chartDensityOnE (F.inducedMetric t) α z) y) /
        chartDensityOnE (F.inducedMetric t) α y =
      tangentialDivergence (F.chartRep t α)
        (tangentField (F.chartRep t α) (chartModelBasis E₁) Z) (chartModelBasis E₁)
        (fun k l => chartInvGramOnE (F.inducedMetric t) α k l y) y := by
  set ρ := chartDensityOnE (F.inducedMetric t) α with hρ
  have hopen := isOpen_extChartAt_target (I := I) α
  have hint : y ∈ interior (extChartAt I α).target := by rwa [hopen.interior_eq]
  have hρd : DifferentiableAt ℝ ρ y :=
    ((chartDensityOnE_contDiffOn (I := I) (F.inducedMetric t) α).differentiableOn (by simp) y
      hy).differentiableAt (hopen.mem_nhds hy)
  have hρpos : 0 < ρ y := by
    have hbase : (extChartAt I α).symm y ∈ (trivializationAt E₁ (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I),
        ← extChartAt_source_eq_chartAt_source (I := I)]
      exact (extChartAt I α).map_target hy
    exact chartDensity_pos (I := I) (F.inducedMetric t) α hbase
  -- the left-hand side, term by term: product rule, then Jacobi's formula
  have hterm : ∀ i, partialDeriv i (fun z => Z i z * ρ z) y =
      (partialDeriv i (Z i) y + Z i y * ((1 / 2 : ℝ) * ∑ k, ∑ l,
        chartInvGramOnE (F.inducedMetric t) α k l y *
          partialDeriv i (chartGramOnE (F.inducedMetric t) α l k) y)) * ρ y := by
    intro i
    have hmul : fderiv ℝ (fun z => Z i z * ρ z) y =
        Z i y • fderiv ℝ ρ y + ρ y • fderiv ℝ (Z i) y := fderiv_mul (hZ i) hρd
    have hjac := partialDeriv_chartDensityOnE_eq_sum_chartChristoffel_diag (I := I)
      (F.inducedMetric t) α i hint
    rw [sum_chartChristoffel_diag_eq_half_trace (I := I) (F.inducedMetric t) α i y] at hjac
    rw [partialDeriv, hmul]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show fderiv ℝ ρ y (chartModelBasis E₁ i) = partialDeriv i ρ y from rfl, hjac]
    simp only [partialDeriv]
    ring
  have hlhs : (∑ i, partialDeriv i (fun z => Z i z * ρ z) y) / ρ y =
      ∑ i, (partialDeriv i (Z i) y + Z i y * ((1 / 2 : ℝ) * ∑ k, ∑ l,
        chartInvGramOnE (F.inducedMetric t) α k l y *
          partialDeriv i (chartGramOnE (F.inducedMetric t) α l k) y)) := by
    simp only [hterm, ← Finset.sum_mul]
    rw [mul_div_cancel_right₀ _ hρpos.ne']
  rw [hlhs, tangentialDivergence_tangentField (contDiffAt_chartRep F t α hy)
    (chartModelBasis E₁) (isFrameInverse_chartInvGramOnE F t α hy)
    (fun i j => chartInvGramOnE_symm (I := I) (F.inducedMetric t) α i j y) hZ,
    Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  -- match the library's chart quantities to the frame quantities, then relabel
  have hS : ∑ k, ∑ l, chartInvGramOnE (F.inducedMetric t) α k l y *
        partialDeriv i (chartGramOnE (F.inducedMetric t) α l k) y =
      ∑ k, ∑ l, chartInvGramOnE (F.inducedMetric t) α k l y *
        fderiv ℝ (fun z => frameGram (F.chartRep t α) (chartModelBasis E₁) z k l) y
          (chartModelBasis E₁ i) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [partialDeriv_chartGramOnE F t α hy, fderiv_frameGram_comm]
  rw [hS]
  ring

/-- **Beltrami's formula for `|F|²/2` in a chart.** With the library's inverse chart Gram
matrix as the inverse metric, the tangential divergence of the tangential part of the
position vector is `n + ⟪F, Hvec⟫`. -/
theorem tangentialDivergence_tangentialPart_chartRep [I.Boundaryless]
    (F : SmoothImmersionFamily I M E) (t : ℝ) (α : M) {y : E₁}
    (hy : y ∈ (extChartAt I α).target) :
    tangentialDivergence (F.chartRep t α)
        (fun z => tangentialPart (F.chartRep t α) (chartModelBasis E₁)
          (fun k l => chartInvGramOnE (F.inducedMetric t) α k l z) z (F.chartRep t α z))
        (chartModelBasis E₁) (fun k l => chartInvGramOnE (F.inducedMetric t) α k l y) y =
      (Module.finrank ℝ E₁ : ℝ) + @inner ℝ E _ (F.chartRep t α y)
        (meanCurvatureNormal (F.chartRep t α) (chartModelBasis E₁)
          (fun k l => chartInvGramOnE (F.inducedMetric t) α k l y) y) := by
  have hopen := isOpen_extChartAt_target (I := I) α
  have h := tangentialDivergence_tangentialPart_position (contDiffAt_chartRep F t α hy)
    (chartModelBasis E₁) (chartModelBasis E₁).span_eq
    (fun z k l => chartInvGramOnE (F.inducedMetric t) α k l z)
    (by filter_upwards [hopen.mem_nhds hy] with z hz
        exact isFrameInverse_chartInvGramOnE F t α hz)
    (fun z i j => chartInvGramOnE_symm (I := I) (F.inducedMetric t) α i j z)
    (fun k l => ((chartInvGramOnE_contDiffOn (I := I) (F.inducedMetric t) α k l).contDiffAt
      (hopen.mem_nhds hy)).differentiableAt (by simp))
  simpa using h

end SmoothImmersionFamily

end HuiskenMonotonicity
