/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.FirstVariationIntegral
import HuiskenMonotonicity.Upstream.DifferentialGeometry.Geometry.Submanifold.MeanCurvature
import HuiskenMonotonicity.Upstream.DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Unfold

/-!
# The mean curvature vector is the library's

`SmoothImmersion.meanCurvature` is computed in a chart: the normal part of the trace
`g^{ij} ∂_i∂_j F` of the plain second derivative of the chart representation. This file proves
that it is the mean curvature vector in the library's sense: the metric trace of the library's
second fundamental form `secondFundamentalFormAt` of `f`, regarded as a Riemannian isometric
immersion into the Euclidean space (`meanCurvatureVectorAt`).

In the charts at `p` and `f p` the library's ambient second fundamental form is
`∂²F(u, v) + Γ_E(dF u, dF v) - dF(Γ_M(u, v))`
(`secondFundamentalFormAmbientAt_eq_modelValue`). The Euclidean Christoffel symbols vanish, and
the library proves the result normal, so it is the normal part of `∂²F(u, v)`: the term
`dF(Γ_M(u, v))` is tangent. Both traces are taken in the chart frame against the library's
inverse chart Gram matrix.
-/

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

namespace HuiskenMonotonicity

open Manifold DifferentialGeometry DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
  DifferentialGeometry.Geometry.Riemannian.Geodesic

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]
variable [T2Space M] [I.Boundaryless]

namespace SmoothImmersion

omit [I.Boundaryless] in
/-- A smooth immersion in mathlib's sense is a Riemannian isometric immersion of its induced
metric into the Euclidean space. -/
theorem isRiemannianIsometricImmersion (f : SmoothImmersion I M E)
    (hf : IsImmersion I 𝓘(ℝ, E) ∞ f) :
    IsRiemannianIsometricImmersion f.inducedMetric (euclideanMetric (E := E)) f :=
  ⟨hf, fun x u v => by rw [euclideanMetric_inner, inducedMetric_inner]; rfl⟩

omit [T2Space M] [I.Boundaryless] in
/-- The written-in-charts form of `f` at `p` is its chart representation. -/
theorem writtenInExtChartAt_eq_chartRep (f : SmoothImmersion I M E) (p : M) :
    writtenInExtChartAt I 𝓘(ℝ, E) p f = f.chartRep p := by
  funext y
  simp [writtenInExtChartAt, chartRep]

omit [T2Space M] in
/-- The differential at `p`, read in the chart at `p`. -/
theorem tangentLinearMapToModel_mfderiv (f : SmoothImmersion I M E) (p : M) (w : E₁) :
    tangentLinearMapToModel (mfderiv I 𝓘(ℝ, E) f p) w =
      fderiv ℝ (f.chartRep p) (extChartAt I p p) w := by
  have hmd : MDifferentiableAt I 𝓘(ℝ, E) f p := f.contMDiff.mdifferentiableAt (by simp)
  rw [tangentLinearMapToModel_mfderiv_eq_fderiv_writtenInExtChartAt hmd w,
    f.writtenInExtChartAt_eq_chartRep]

/-- **The library's ambient second fundamental form of an immersion into a Euclidean
space**, in the charts at `p`: `∂²F(u, v) - dF(Γ_M(u, v))`. -/
theorem secondFundamentalFormModelValue_eq (f : SmoothImmersion I M E) (p : M) (u v : E₁) :
    secondFundamentalFormModelValue f.inducedMetric (euclideanMetric (E := E)) f p u v =
      secondDerivative (f.chartRep p) (extChartAt I p p) u v -
        fderiv ℝ (f.chartRep p) (extChartAt I p p)
          (chartChristoffelContraction (I := I) f.inducedMetric p u v (extChartAt I p p)) := by
  simp only [secondFundamentalFormModelValue, euclideanMetric_chartChristoffelContraction,
    add_zero, f.writtenInExtChartAt_eq_chartRep, secondDerivative,
    f.tangentLinearMapToModel_mfderiv]

variable [NeZero (Module.finrank ℝ E₁)] [NeZero (Module.finrank ℝ E)]

omit [NeZero (Module.finrank ℝ E₁)] [NeZero (Module.finrank ℝ E)] in
/-- **The mean curvature vector is the library's.** For a smooth immersion `f` into a Euclidean
space, `SmoothImmersion.meanCurvature` is the metric trace of the library's second fundamental
form of `f`, as a Riemannian isometric immersion of its induced metric. The tangent space of
`E` is `E` itself; `tangentSpaceModelContinuousLinearEquiv` is the identity. -/
theorem meanCurvatureVectorAt_eq (f : SmoothImmersion I M E)
    (hf : IsImmersion I 𝓘(ℝ, E) ∞ f) (p : M) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (f p)
        (meanCurvatureVectorAt (f.isRiemannianIsometricImmersion hf) p) =
      f.meanCurvature p := by
  set h := f.isRiemannianIsometricImmersion hf
  set eE := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (f p)
  set eN := tangentSpaceModelContinuousLinearEquiv (I := I) p
  set y := extChartAt I p p with hy_def
  set b := chartModelBasis E₁ with hb_def
  set Fc := f.chartRep p
  set gInv : Fin (Module.finrank ℝ E₁) → Fin (Module.finrank ℝ E₁) → ℝ :=
    fun i j => chartInvGramOnE f.inducedMetric p i j y with hgInv
  have hy : y ∈ (extChartAt I p).target := mem_extChartAt_target p
  have hinv : IsFrameInverse Fc b y gInv := f.isFrameInverse_chartInvGramOnE p hy
  have hsymm : ∀ i j, gInv i j = gInv j i := fun i j =>
    chartInvGramOnE_symm (I := I) _ p i j _
  -- the library's inverse metric at the centre is ours
  have hg : ∀ i j, chartInvGramMatrix (I := I) f.inducedMetric p p i j = gInv i j := by
    intro i j
    rw [hgInv]
    simp only [chartInvGramOnE_def, y, extChartAt_to_inv]
  -- the chart frame is the model basis
  have hB : ∀ i, eN (chartFrameBasisAt (IN := I) p i) = b i := fun i => by
    rw [chartFrameBasisAt, Module.Basis.map_apply]
    exact eN.apply_symm_apply _
  -- the second fundamental form, read in `E`, is the normal part of the second derivative
  have hII : ∀ u v : TangentSpace I p,
      eE (secondFundamentalFormAmbientAt f.inducedMetric (euclideanMetric (E := E)) f p u v) =
        normalPart Fc b gInv y (secondDerivative Fc y (eN u) (eN v)) := by
    intro u v
    have hval : eE (secondFundamentalFormAmbientAt f.inducedMetric (euclideanMetric (E := E))
        f p u v) = secondFundamentalFormModelValue f.inducedMetric (euclideanMetric (E := E))
          f p (eN u) (eN v) := by
      rw [secondFundamentalFormAmbientAt_eq_modelValue]
      exact eE.apply_symm_apply _
    have hnorm : ∀ k, ⟪secondFundamentalFormModelValue f.inducedMetric
        (euclideanMetric (E := E)) f p (eN u) (eN v), frameTangent Fc b y k⟫ = 0 := by
      intro k
      have h0 := h.secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero p u v (eN.symm (b k))
      rw [euclideanMetric_inner] at h0
      rw [← hval, frameTangent_apply, ← f.tangentLinearMapToModel_mfderiv p]
      exact h0
    rw [hval]
    have hsplit : secondDerivative Fc y (eN u) (eN v) =
        secondFundamentalFormModelValue f.inducedMetric (euclideanMetric (E := E)) f p
          (eN u) (eN v) + fderiv ℝ Fc y (chartChristoffelContraction (I := I) f.inducedMetric p
            (eN u) (eN v) y) := by
      rw [f.secondFundamentalFormModelValue_eq p, sub_add_cancel]
    rw [hsplit, ← normalPartₗ_apply, map_add, normalPartₗ_apply, normalPartₗ_apply,
      normalPart_eq_self hnorm, normalPart_fderiv_eq_zero (chartModelBasis E₁).span_eq hinv hsymm,
      add_zero]
  -- trace both sides
  rw [meanCurvatureVectorAt_eq_inBasis, meanCurvatureVectorInBasis_eq_sum, Submodule.coe_sum,
    map_sum]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    h.secondFundamentalFormAt_coe_eq_ambient, hII, hB, hg]
  change _ = normalPart Fc b gInv y (meanCurvatureVectorFrame Fc b gInv y)
  rw [meanCurvatureVectorFrame, ← normalPartₗ_apply, map_sum]
  simp only [map_sum, map_smul, normalPartₗ_apply]

end SmoothImmersion

end HuiskenMonotonicity
