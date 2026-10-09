/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.VossWeyl
import HuiskenMonotonicity.HeatKernel
import DifferentialGeometry.Geometry.Operator.Laplacian.VossWeylFormula
import DifferentialGeometry.Geometry.Operator.Gradient.Coordinates

/-!
# The first variation of Huisken's integral, on the manifold

Huisken's proof of the monotonicity formula integrates the divergence of the test field
`ρ F` over the evolving submanifold. Following the standard split of the divergence theorem
for a submanifold, the tangential half is an integration by parts on the parameter manifold
with the gradient of `u = |F|²/2`:

  `∫ X(ρ) dμ = -∫ ρ Δu dμ`,   `X = ∇u`.

The two integrands are computed here, with the library's gradient, Laplacian and directional
derivative:

* `Δu = n + ⟪F, Hvec⟫`, Beltrami's formula (`laplacian_halfSqNorm`);
* `X(ρ) = ⟨∇u, ∇ρ⟩ = -(ρ / (2τ)) ‖Fᵀ‖²`
  (`tangentSectionAction_gradG_halfSqNorm_backwardHeatKernel`),

and assembled into the first variation identity
`∫ ρ (n - ‖Fᵀ‖² / (2τ) + ⟪F, Hvec⟫) dμ = 0` (`integral_firstVariation`).

Both are read in the chart at the point, where the tangential calculus of
`TangentialCalculus.lean` applies to the chart representation of `F`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace HuiskenMonotonicity

open MeasureTheory Manifold DifferentialGeometry DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator
  DifferentialGeometry.Integral.DivergenceTheorem

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

section Kernel

variable {Idx : Type*} [Fintype Idx]

/-- The kernel pulled back along `F`, differentiated in a coordinate direction. -/
theorem fderiv_backwardHeatKernel_comp
    (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀)
    {F : E₁ → E} (b : Idx → E₁) (x : E₁)
    (hF : DifferentiableAt ℝ F x) (i : Idx) :
    fderiv ℝ (fun y => backwardHeatKernel m t₀ t (F y)) x (b i) =
      -(backwardHeatKernel m t₀ t (F x) / (2 * (t₀ - t))) *
        @inner ℝ E _ (F x) (frameTangent F b x i) := by
  have hρ : DifferentiableAt ℝ (fun y : E => backwardHeatKernel m t₀ t y) (F x) :=
    (contDiff_backwardHeatKernel m t₀ hτ).differentiable (by norm_num) (F x)
  have h : HasFDerivAt (fun y => backwardHeatKernel m t₀ t (F y))
      ((fderiv ℝ (fun y : E => backwardHeatKernel m t₀ t y) (F x)).comp (fderiv ℝ F x)) x :=
    hρ.hasFDerivAt.comp x hF.hasFDerivAt
  rw [h.fderiv]
  simpa using fderiv_backwardHeatKernel m t₀ hτ (F x) (frameTangent F b x i)

end Kernel

/-- The Borel σ-algebra, matching the one under which the library's Riemannian volume measure,
and hence `surfaceMeasure`, is stated. -/
local instance instMeasurableSpaceFirstVariation : MeasurableSpace M := borel M

local instance instBorelSpaceFirstVariation : BorelSpace M := ⟨rfl⟩

namespace SmoothImmersion

variable [T2Space M]

/-! ## Mean curvature and tangential norm on the parameter manifold

Both are read in the chart at the point, with the library's inverse chart Gram matrix as the
inverse metric. -/

/-- The mean curvature vector of the time slice at `p`, read in the chart at `p`. -/
def meanCurvature (f : SmoothImmersion I M E) (p : M) : E :=
  meanCurvatureNormal (f.chartRep p) (chartModelBasis E₁)
    (fun k l => chartInvGramOnE (f.inducedMetric) p k l (extChartAt I p p))
    (extChartAt I p p)

/-- The squared length `‖Fᵀ‖²` of the tangential part of the position vector at `p`, read in
the chart at `p`. -/
def tangentialSqNorm (f : SmoothImmersion I M E) (p : M) : ℝ :=
  tangentialNormSq (f.chartRep p) (chartModelBasis E₁)
    (fun k l => chartInvGramOnE (f.inducedMetric) p k l (extChartAt I p p))
    (extChartAt I p p) (f p)

/-- The normal part `F^⊥` of the position vector at `p`, read in the chart at `p`. -/
def normalPosition (f : SmoothImmersion I M E) (p : M) : E :=
  normalPart (f.chartRep p) (chartModelBasis E₁)
    (fun k l => chartInvGramOnE (f.inducedMetric) p k l (extChartAt I p p))
    (extChartAt I p p) (f p)

section Orthogonality

variable [I.Boundaryless]

/-- The position vector minus its normal part is its tangential part. -/
theorem sub_normalPosition (f : SmoothImmersion I M E) (p : M) :
    f p - f.normalPosition p =
      tangentialPart (f.chartRep p) (chartModelBasis E₁)
        (fun k l => chartInvGramOnE (f.inducedMetric) p k l (extChartAt I p p))
        (extChartAt I p p) (f p) := by
  simp [normalPosition, normalPart]

/-- `F = Fᵀ + F^⊥` is an orthogonal splitting. -/
theorem inner_sub_normalPosition (f : SmoothImmersion I M E) (p : M) :
    @inner ℝ E _ (f p - f.normalPosition p) (f.normalPosition p) = 0 := by
  rw [sub_normalPosition, real_inner_comm, normalPosition]
  exact inner_normalPart_tangentialPart (f.isFrameInverse_chartInvGramOnE p
    (mem_extChartAt_target p)) (fun i j => chartInvGramOnE_symm (I := I) _ p i j _) _ _

/-- The mean curvature vector is orthogonal to `Fᵀ`. -/
theorem inner_meanCurvature_sub_normalPosition (f : SmoothImmersion I M E) (p : M) : @inner ℝ E _ (f.meanCurvature p) (f p - f.normalPosition p) = 0 := by
  rw [sub_normalPosition, meanCurvature, meanCurvatureNormal]
  exact inner_normalPart_tangentialPart (f.isFrameInverse_chartInvGramOnE p
    (mem_extChartAt_target p)) (fun i j => chartInvGramOnE_symm (I := I) _ p i j _) _ _

/-- `‖F - F^⊥‖² = ‖Fᵀ‖²`. -/
theorem norm_sub_normalPosition_sq (f : SmoothImmersion I M E) (p : M) :
    ‖f p - f.normalPosition p‖ ^ 2 = f.tangentialSqNorm p := by
  have hsplit : @inner ℝ E _ (f p - f.normalPosition p) (f p) =
      @inner ℝ E _ (f p - f.normalPosition p) (f p - f.normalPosition p) +
        @inner ℝ E _ (f p - f.normalPosition p) (f.normalPosition p) := by
    rw [← inner_add_right, sub_add_cancel]
  rw [← real_inner_self_eq_norm_sq, tangentialSqNorm,
    ← inner_tangentialPart_self (fun i j => chartInvGramOnE_symm (I := I) _ p i j _),
    ← sub_normalPosition, hsplit, inner_sub_normalPosition, add_zero]

end Orthogonality

/-! ## The Laplacian of `|F|²/2` -/

/-- Half the squared length of the position vector, `u = |F|²/2`, as a smooth function on the
parameter manifold. -/
def halfSqNorm (f : SmoothImmersion I M E) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun p => ‖f p‖ ^ 2 / 2,
    ((contDiff_norm_sq ℝ).div_const 2).comp_contMDiff (f.contMDiff)⟩

/-- In a chart, the coordinate derivatives of `|F|²/2` are `⟪F, ∂_l F⟫`. -/
theorem partialDeriv_scalarOnE_halfSqNorm [I.Boundaryless] (f : SmoothImmersion I M E) (α : M) {z : E₁} (hz : z ∈ (extChartAt I α).target)
    (l : Fin (Module.finrank ℝ E₁)) :
    partialDeriv l (scalarOnE (I := I) α (f.halfSqNorm)) z =
      @inner ℝ E _ (f.chartRep α z)
        (frameTangent (f.chartRep α) (chartModelBasis E₁) z l) := by
  have hd := (f.contDiffAt_chartRep α hz).differentiableAt (by norm_num)
  have h := HasFDerivAt.mul_const hd.hasFDerivAt.norm_sq (1 / 2 : ℝ)
  change fderiv ℝ (fun y => ‖f.chartRep α y‖ ^ 2 / 2) z (chartModelBasis E₁ l) = _
  rw [show (fun y => ‖f.chartRep α y‖ ^ 2 / 2) =
      fun y => ‖f.chartRep α y‖ ^ 2 * (1 / 2) by funext y; ring, h.fderiv]
  simp [frameTangent]

/-- In a chart, the library's gradient field of `|F|²/2`, written along `F`, is the tangential
part of the position vector. -/
theorem tangentField_gradChartCoeffOnE_halfSqNorm [I.Boundaryless]
    (f : SmoothImmersion I M E) (α : M) {z : E₁}
    (hz : z ∈ (extChartAt I α).target) :
    tangentField (f.chartRep α) (chartModelBasis E₁)
        (gradChartCoeffOnE (I := I) (f.inducedMetric) α (f.halfSqNorm)) z =
      tangentialPart (f.chartRep α) (chartModelBasis E₁)
        (fun k l => chartInvGramOnE (f.inducedMetric) α k l z) z (f.chartRep α z) := by
  simp only [tangentField, tangentialPart, gradChartCoeffOnE_def,
    f.partialDeriv_scalarOnE_halfSqNorm α hz, Finset.sum_smul]

/-- **Beltrami's formula for `|F|²/2`.** The library's Laplacian of the induced metric applied
to `u = |F|²/2` is

  `Δ u = n + ⟪F, Hvec⟫`,

with the mean curvature vector read in the chart at the point. This is the identity
`Δ_M |F|² = 2n + 2⟪F, Hvec⟫` behind the first variation of Huisken's integral. -/
theorem laplacian_halfSqNorm [I.Boundaryless] (f : SmoothImmersion I M E) (x : M) :
    ΔG (f.inducedMetric) (f.halfSqNorm) x =
      (Module.finrank ℝ E₁ : ℝ) + @inner ℝ E _ (f x) (f.meanCurvature x) := by
  unfold meanCurvature
  set y := extChartAt I x x with hy_def
  have hy : y ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hopen := isOpen_extChartAt_target (I := I) x
  have hsymm : (extChartAt I x).symm y = x := extChartAt_to_inv x
  set gInv : E₁ → Fin (Module.finrank ℝ E₁) → Fin (Module.finrank ℝ E₁) → ℝ :=
    fun z k l => chartInvGramOnE (f.inducedMetric) x k l z with hgInv
  -- the gradient coefficients agree near `y` with a manifestly differentiable expression
  have hgd : ∀ k l, DifferentiableAt ℝ (fun z => gInv z k l) y := fun k l =>
    ((chartInvGramOnE_contDiffOn (I := I) (f.inducedMetric) x k l).contDiffAt
      (hopen.mem_nhds hy)).differentiableAt (by simp)
  have hF := f.contDiffAt_chartRep x hy
  have hT : ∀ l, DifferentiableAt ℝ
      (fun z => frameTangent (f.chartRep x) (chartModelBasis E₁) z l) y := fun l =>
    (hasFDerivAt_fderiv_apply hF (chartModelBasis E₁ l)).differentiableAt
  have hZ : ∀ k, DifferentiableAt ℝ
      (gradChartCoeffOnE (I := I) (f.inducedMetric) x (f.halfSqNorm) k) y := by
    intro k
    have hd : DifferentiableAt ℝ (fun z => ∑ l, gInv z k l *
        @inner ℝ E _ (f.chartRep x z)
          (frameTangent (f.chartRep x) (chartModelBasis E₁) z l)) y :=
      DifferentiableAt.fun_sum fun l _ =>
        (hgd k l).mul ((hF.differentiableAt (by norm_num)).inner ℝ (hT l))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hy] with z hz
    simp only [gradChartCoeffOnE_def, f.partialDeriv_scalarOnE_halfSqNorm x hz, hgInv]
  have htan : tangentField (f.chartRep x) (chartModelBasis E₁)
        (gradChartCoeffOnE (I := I) (f.inducedMetric) x (f.halfSqNorm)) =ᶠ[nhds y]
      fun z => tangentialPart (f.chartRep x) (chartModelBasis E₁) (gInv z) z
        (f.chartRep x z) := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact f.tangentField_gradChartCoeffOnE_halfSqNorm x hz
  refine (voss_weyl_laplacian_formula_pointwise (I := I) (f.inducedMetric) x
      (f.halfSqNorm).contMDiff (mem_chart_source H x)).trans ?_
  have hvw := f.vossWeyl_eq_tangentialDivergence x hy hZ
  have hbel := f.tangentialDivergence_tangentialPart_chartRep x hy
  have hpt : f.chartRep x y = f x := by
    change f ((extChartAt I x).symm y) = f x
    rw [hsymm]
  unfold tangentialDivergence at hvw hbel
  rw [htan.fderiv_eq] at hvw
  rw [hpt] at hbel
  have hρ : chartDensityOnE (f.inducedMetric) x y = chartDensity (f.inducedMetric) x x := by
    change chartDensity _ x ((extChartAt I x).symm y) = _
    rw [hsymm]
  rw [← hbel, ← hvw, hρ, chartVossWeylLaplacian_def]
  rfl

/-! ## The directional derivative of the kernel along the gradient of `|F|²/2` -/

/-- **`X(ρ)` for `X = ∇(|F|²/2)`.** The derivative of the backward heat kernel along the
gradient of `u = |F|²/2` is

  `X(ρ) = ⟨∇u, ∇ρ⟩ = -(ρ / (2τ)) ‖Fᵀ‖²`. -/
theorem tangentSectionAction_gradG_halfSqNorm_backwardHeatKernel [I.Boundaryless]
    (f : SmoothImmersion I M E) (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀) (x : M) :
    tangentSectionAction (gradG (f.inducedMetric) (f.halfSqNorm))
        (fun p => backwardHeatKernel m t₀ t (f p)) x =
      -(backwardHeatKernel m t₀ t (f x) / (2 * (t₀ - t))) * f.tangentialSqNorm x := by
  unfold tangentialSqNorm
  set y := extChartAt I x x with hy_def
  have hy : y ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hsymm : (extChartAt I x).symm y = x := extChartAt_to_inv x
  have hx : x ∈ (trivializationAt E₁ (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hxint : y ∈ interior (extChartAt I x).target := by
    rwa [(isOpen_extChartAt_target (I := I) x).interior_eq]
  have hpt : f.chartRep x y = f x := by
    change f ((extChartAt I x).symm y) = f x
    rw [hsymm]
  have hd := (f.contDiffAt_chartRep x hy).differentiableAt (by norm_num)
  rw [tangentSectionAction_def, grad_g_apply, ← inner_gradFun_right,
    inner_gradFun_eq_chartInvGram_sum _ x _ _ hx hxint, tangentialNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hρ : partialDeriv j
      (scalarOnE (I := I) x fun p => backwardHeatKernel m t₀ t (f p)) y =
      -(backwardHeatKernel m t₀ t (f.chartRep x y) / (2 * (t₀ - t))) *
        @inner ℝ E _ (f.chartRep x y)
          (frameTangent (f.chartRep x) (chartModelBasis E₁) y j) :=
    fderiv_backwardHeatKernel_comp m t₀ hτ (chartModelBasis E₁) y hd j
  rw [hρ, f.partialDeriv_scalarOnE_halfSqNorm x hy i, hpt, chartInvGramOnE_def, hsymm]
  ring

/-! ## The first variation identity -/

/-- The first-variation integrand is `X(ρ) + ρ div X` for `X = ∇(|F|²/2)`. -/
theorem firstVariation_integrand_eq [I.Boundaryless] (f : SmoothImmersion I M E)
    (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀) (p : M) :
    backwardHeatKernel m t₀ t (f p) *
        ((Module.finrank ℝ E₁ : ℝ) - f.tangentialSqNorm p / (2 * (t₀ - t)) +
          @inner ℝ E _ (f p) (f.meanCurvature p)) =
      tangentSectionAction (gradG (f.inducedMetric) (f.halfSqNorm))
          (fun q => backwardHeatKernel m t₀ t (f q)) p +
        backwardHeatKernel m t₀ t (f p) *
          divergenceG (f.inducedMetric) (gradG (f.inducedMetric) (f.halfSqNorm)) p := by
  rw [f.tangentSectionAction_gradG_halfSqNorm_backwardHeatKernel m t₀ hτ p,
    ← Δ_g_def, f.laplacian_halfSqNorm p]
  ring

section Closed

variable [I.Boundaryless] [CompactSpace M] (f : SmoothImmersion I M E) (m : ℕ) (t₀ : ℝ)
  {t : ℝ} (hτ : t < t₀)

include hτ in
/-- The kernel pulled back along a time slice is smooth. -/
theorem contMDiff_backwardHeatKernel_comp :
    ContMDiff I 𝓘(ℝ) ∞ fun p => backwardHeatKernel m t₀ t (f p) :=
  ((contDiff_backwardHeatKernel m t₀ hτ).of_le (by simp)).comp_contMDiff
    (f.contMDiff)

omit [I.Boundaryless] in
/-- On a closed manifold, every continuous function is integrable for the surface measure. -/
theorem integrable_of_continuous {g : M → ℝ} (hg : Continuous g) :
    Integrable g f.surfaceMeasure := by
  have : IsFiniteMeasureOnCompacts f.surfaceMeasure :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) f.inducedMetric
  exact hg.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))

include hτ in
/-- The first-variation integrand is integrable on a closed manifold. -/
theorem integrable_firstVariation :
    Integrable (fun p => backwardHeatKernel m t₀ t (f p) *
        ((Module.finrank ℝ E₁ : ℝ) - f.tangentialSqNorm p / (2 * (t₀ - t)) +
          @inner ℝ E _ (f p) (f.meanCurvature p))) (f.surfaceMeasure) := by
  have hρ := f.contMDiff_backwardHeatKernel_comp m t₀ hτ
  simp only [f.firstVariation_integrand_eq m t₀ hτ]
  exact f.integrable_of_continuous
    ((tangentSectionAction_contMDiff _ hρ).continuous.add
      (hρ.continuous.mul (divergence_g_contMDiff _ _).continuous))

include hτ in
/-- **The first variation identity for Huisken's integral.** On a closed parameter manifold,

  `∫ ρ (n - ‖Fᵀ‖² / (2τ) + ⟪F, Hvec⟫) dμ = 0`.

This is the divergence theorem applied to the test field `ρ F`, in the form of the library's
integration by parts `∫ X(ρ) dμ = -∫ ρ div X dμ` with `X = ∇(|F|²/2)`: the integrand is
`X(ρ) + ρ Δ(|F|²/2)`. -/
theorem integral_firstVariation :
    ∫ p, backwardHeatKernel m t₀ t (f p) *
        ((Module.finrank ℝ E₁ : ℝ) - f.tangentialSqNorm p / (2 * (t₀ - t)) +
          @inner ℝ E _ (f p) (f.meanCurvature p)) ∂(f.surfaceMeasure) = 0 := by
  set g := f.inducedMetric
  set X := gradG g (f.halfSqNorm)
  have hρ := f.contMDiff_backwardHeatKernel_comp m t₀ hτ
  have hX : HasCompactSupport X :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  have h₁ : Integrable (fun p => tangentSectionAction X
      (fun q => backwardHeatKernel m t₀ t (f q)) p) (f.surfaceMeasure) :=
    f.integrable_of_continuous (tangentSectionAction_contMDiff X hρ).continuous
  have h₂ : Integrable (fun p => backwardHeatKernel m t₀ t (f p) * divergenceG g X p)
      (f.surfaceMeasure) :=
    f.integrable_of_continuous (hρ.continuous.mul (divergence_g_contMDiff g X).continuous)
  simp only [f.firstVariation_integrand_eq m t₀ hτ]
  rw [integral_add h₁ h₂]
  change ∫ p, _ ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
    ∫ p, _ ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0
  rw [integral_tangentSectionAction_eq_neg_integral_smul_divergence g hρ X hX]
  ring

end Closed

end SmoothImmersion

end HuiskenMonotonicity
