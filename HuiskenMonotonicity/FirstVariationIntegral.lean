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
variable [IsManifold I ⊤ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

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

namespace SmoothImmersionFamily

variable [T2Space M]

/-! ## Mean curvature and tangential norm on the parameter manifold

Both are read in the chart at the point, with the library's inverse chart Gram matrix as the
inverse metric. -/

/-- The mean curvature vector of the time slice at `p`, read in the chart at `p`. -/
def meanCurvature (F : SmoothImmersionFamily I M E) (t : ℝ) (p : M) : E :=
  meanCurvatureNormal (F.chartRep t p) (chartModelBasis E₁)
    (fun k l => chartInvGramOnE (F.inducedMetric t) p k l (extChartAt I p p))
    (extChartAt I p p)

/-- The squared length `‖Fᵀ‖²` of the tangential part of the position vector at `p`, read in
the chart at `p`. -/
def tangentialSqNorm (F : SmoothImmersionFamily I M E) (t : ℝ) (p : M) : ℝ :=
  tangentialNormSq (F.chartRep t p) (chartModelBasis E₁)
    (fun k l => chartInvGramOnE (F.inducedMetric t) p k l (extChartAt I p p))
    (extChartAt I p p) (F p t)

/-- The normal part `F^⊥` of the position vector at `p`, read in the chart at `p`. -/
def normalPosition (F : SmoothImmersionFamily I M E) (t : ℝ) (p : M) : E :=
  normalPart (F.chartRep t p) (chartModelBasis E₁)
    (fun k l => chartInvGramOnE (F.inducedMetric t) p k l (extChartAt I p p))
    (extChartAt I p p) (F p t)

section Orthogonality

variable [I.Boundaryless]

/-- The position vector minus its normal part is its tangential part. -/
theorem sub_normalPosition (F : SmoothImmersionFamily I M E) (t : ℝ) (p : M) :
    F p t - F.normalPosition t p =
      tangentialPart (F.chartRep t p) (chartModelBasis E₁)
        (fun k l => chartInvGramOnE (F.inducedMetric t) p k l (extChartAt I p p))
        (extChartAt I p p) (F p t) := by
  simp [normalPosition, normalPart]

/-- `F = Fᵀ + F^⊥` is an orthogonal splitting. -/
theorem inner_sub_normalPosition (F : SmoothImmersionFamily I M E) (t : ℝ) (p : M) :
    @inner ℝ E _ (F p t - F.normalPosition t p) (F.normalPosition t p) = 0 := by
  rw [sub_normalPosition, real_inner_comm, normalPosition]
  exact inner_normalPart_tangentialPart (isFrameInverse_chartInvGramOnE F t p
    (mem_extChartAt_target p)) (fun i j => chartInvGramOnE_symm (I := I) _ p i j _) _ _

/-- The mean curvature vector is orthogonal to `Fᵀ`. -/
theorem inner_meanCurvature_sub_normalPosition (F : SmoothImmersionFamily I M E) (t : ℝ)
    (p : M) : @inner ℝ E _ (F.meanCurvature t p) (F p t - F.normalPosition t p) = 0 := by
  rw [sub_normalPosition, meanCurvature, meanCurvatureNormal]
  exact inner_normalPart_tangentialPart (isFrameInverse_chartInvGramOnE F t p
    (mem_extChartAt_target p)) (fun i j => chartInvGramOnE_symm (I := I) _ p i j _) _ _

/-- `‖F - F^⊥‖² = ‖Fᵀ‖²`. -/
theorem norm_sub_normalPosition_sq (F : SmoothImmersionFamily I M E) (t : ℝ) (p : M) :
    ‖F p t - F.normalPosition t p‖ ^ 2 = F.tangentialSqNorm t p := by
  have hsplit : @inner ℝ E _ (F p t - F.normalPosition t p) (F p t) =
      @inner ℝ E _ (F p t - F.normalPosition t p) (F p t - F.normalPosition t p) +
        @inner ℝ E _ (F p t - F.normalPosition t p) (F.normalPosition t p) := by
    rw [← inner_add_right, sub_add_cancel]
  rw [← real_inner_self_eq_norm_sq, tangentialSqNorm,
    ← inner_tangentialPart_self (fun i j => chartInvGramOnE_symm (I := I) _ p i j _),
    ← sub_normalPosition, hsplit, inner_sub_normalPosition, add_zero]

end Orthogonality

/-! ## The Laplacian of `|F|²/2` -/

/-- Half the squared length of the position vector, `u = |F|²/2`, as a smooth function on the
parameter manifold. -/
def halfSqNorm (F : SmoothImmersionFamily I M E) (t : ℝ) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun p => ‖F p t‖ ^ 2 / 2,
    ((contDiff_norm_sq ℝ).div_const 2).comp_contMDiff ((F.contMDiff_timeSlice t).of_le le_top)⟩

/-- In a chart, the coordinate derivatives of `|F|²/2` are `⟪F, ∂_l F⟫`. -/
theorem partialDeriv_scalarOnE_halfSqNorm [I.Boundaryless] (F : SmoothImmersionFamily I M E)
    (t : ℝ) (α : M) {z : E₁} (hz : z ∈ (extChartAt I α).target)
    (l : Fin (Module.finrank ℝ E₁)) :
    partialDeriv l (scalarOnE (I := I) α (F.halfSqNorm t)) z =
      @inner ℝ E _ (F.chartRep t α z)
        (frameTangent (F.chartRep t α) (chartModelBasis E₁) z l) := by
  have hd := (contDiffAt_chartRep F t α hz).differentiableAt (by norm_num)
  have h := HasFDerivAt.mul_const hd.hasFDerivAt.norm_sq (1 / 2 : ℝ)
  change fderiv ℝ (fun y => ‖F.chartRep t α y‖ ^ 2 / 2) z (chartModelBasis E₁ l) = _
  rw [show (fun y => ‖F.chartRep t α y‖ ^ 2 / 2) =
      fun y => ‖F.chartRep t α y‖ ^ 2 * (1 / 2) by funext y; ring, h.fderiv]
  simp [frameTangent]

/-- In a chart, the library's gradient field of `|F|²/2`, written along `F`, is the tangential
part of the position vector. -/
theorem tangentField_gradChartCoeffOnE_halfSqNorm [I.Boundaryless]
    (F : SmoothImmersionFamily I M E) (t : ℝ) (α : M) {z : E₁}
    (hz : z ∈ (extChartAt I α).target) :
    tangentField (F.chartRep t α) (chartModelBasis E₁)
        (gradChartCoeffOnE (I := I) (F.inducedMetric t) α (F.halfSqNorm t)) z =
      tangentialPart (F.chartRep t α) (chartModelBasis E₁)
        (fun k l => chartInvGramOnE (F.inducedMetric t) α k l z) z (F.chartRep t α z) := by
  simp only [tangentField, tangentialPart, gradChartCoeffOnE_def,
    partialDeriv_scalarOnE_halfSqNorm F t α hz, Finset.sum_smul]

/-- **Beltrami's formula for `|F|²/2`.** The library's Laplacian of the induced metric applied
to `u = |F|²/2` is

  `Δ u = n + ⟪F, Hvec⟫`,

with the mean curvature vector read in the chart at the point. This is the identity
`Δ_M |F|² = 2n + 2⟪F, Hvec⟫` behind the first variation of Huisken's integral. -/
theorem laplacian_halfSqNorm [I.Boundaryless] (F : SmoothImmersionFamily I M E) (t : ℝ)
    (x : M) :
    ΔG (F.inducedMetric t) (F.halfSqNorm t) x =
      (Module.finrank ℝ E₁ : ℝ) + @inner ℝ E _ (F x t) (F.meanCurvature t x) := by
  unfold meanCurvature
  set y := extChartAt I x x with hy_def
  have hy : y ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hopen := isOpen_extChartAt_target (I := I) x
  have hsymm : (extChartAt I x).symm y = x := extChartAt_to_inv x
  set gInv : E₁ → Fin (Module.finrank ℝ E₁) → Fin (Module.finrank ℝ E₁) → ℝ :=
    fun z k l => chartInvGramOnE (F.inducedMetric t) x k l z with hgInv
  -- the gradient coefficients agree near `y` with a manifestly differentiable expression
  have hgd : ∀ k l, DifferentiableAt ℝ (fun z => gInv z k l) y := fun k l =>
    ((chartInvGramOnE_contDiffOn (I := I) (F.inducedMetric t) x k l).contDiffAt
      (hopen.mem_nhds hy)).differentiableAt (by simp)
  have hF := contDiffAt_chartRep F t x hy
  have hT : ∀ l, DifferentiableAt ℝ
      (fun z => frameTangent (F.chartRep t x) (chartModelBasis E₁) z l) y := fun l =>
    (hasFDerivAt_fderiv_apply hF (chartModelBasis E₁ l)).differentiableAt
  have hZ : ∀ k, DifferentiableAt ℝ
      (gradChartCoeffOnE (I := I) (F.inducedMetric t) x (F.halfSqNorm t) k) y := by
    intro k
    have hd : DifferentiableAt ℝ (fun z => ∑ l, gInv z k l *
        @inner ℝ E _ (F.chartRep t x z)
          (frameTangent (F.chartRep t x) (chartModelBasis E₁) z l)) y :=
      DifferentiableAt.fun_sum fun l _ =>
        (hgd k l).mul ((hF.differentiableAt (by norm_num)).inner ℝ (hT l))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hy] with z hz
    simp only [gradChartCoeffOnE_def, partialDeriv_scalarOnE_halfSqNorm F t x hz, hgInv]
  have htan : tangentField (F.chartRep t x) (chartModelBasis E₁)
        (gradChartCoeffOnE (I := I) (F.inducedMetric t) x (F.halfSqNorm t)) =ᶠ[nhds y]
      fun z => tangentialPart (F.chartRep t x) (chartModelBasis E₁) (gInv z) z
        (F.chartRep t x z) := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact tangentField_gradChartCoeffOnE_halfSqNorm F t x hz
  refine (voss_weyl_laplacian_formula_pointwise (I := I) (F.inducedMetric t) x
      (F.halfSqNorm t).contMDiff (mem_chart_source H x)).trans ?_
  have hvw := vossWeyl_eq_tangentialDivergence F t x hy hZ
  have hbel := tangentialDivergence_tangentialPart_chartRep F t x hy
  have hpt : F.chartRep t x y = F x t := by
    change F ((extChartAt I x).symm y) t = F x t
    rw [hsymm]
  unfold tangentialDivergence at hvw hbel
  rw [htan.fderiv_eq] at hvw
  rw [hpt] at hbel
  have hρ : chartDensityOnE (F.inducedMetric t) x y = chartDensity (F.inducedMetric t) x x := by
    change chartDensity _ x ((extChartAt I x).symm y) = _
    rw [hsymm]
  rw [← hbel, ← hvw, hρ, chartVossWeylLaplacian_def]
  rfl

/-! ## The directional derivative of the kernel along the gradient of `|F|²/2` -/

/-- **`X(ρ)` for `X = ∇(|F|²/2)`.** The derivative of the backward heat kernel along the
gradient of `u = |F|²/2` is

  `X(ρ) = ⟨∇u, ∇ρ⟩ = -(ρ / (2τ)) ‖Fᵀ‖²`. -/
theorem tangentSectionAction_gradG_halfSqNorm_backwardHeatKernel [I.Boundaryless]
    (F : SmoothImmersionFamily I M E) (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀) (x : M) :
    tangentSectionAction (gradG (F.inducedMetric t) (F.halfSqNorm t))
        (fun p => backwardHeatKernel m t₀ t (F p t)) x =
      -(backwardHeatKernel m t₀ t (F x t) / (2 * (t₀ - t))) * F.tangentialSqNorm t x := by
  unfold tangentialSqNorm
  set y := extChartAt I x x with hy_def
  have hy : y ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hsymm : (extChartAt I x).symm y = x := extChartAt_to_inv x
  have hx : x ∈ (trivializationAt E₁ (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hxint : y ∈ interior (extChartAt I x).target := by
    rwa [(isOpen_extChartAt_target (I := I) x).interior_eq]
  have hpt : F.chartRep t x y = F x t := by
    change F ((extChartAt I x).symm y) t = F x t
    rw [hsymm]
  have hd := (contDiffAt_chartRep F t x hy).differentiableAt (by norm_num)
  rw [tangentSectionAction_def, grad_g_apply, ← inner_gradFun_right,
    inner_gradFun_eq_chartInvGram_sum _ x _ _ hx hxint, tangentialNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hρ : partialDeriv j
      (scalarOnE (I := I) x fun p => backwardHeatKernel m t₀ t (F p t)) y =
      -(backwardHeatKernel m t₀ t (F.chartRep t x y) / (2 * (t₀ - t))) *
        @inner ℝ E _ (F.chartRep t x y)
          (frameTangent (F.chartRep t x) (chartModelBasis E₁) y j) :=
    fderiv_backwardHeatKernel_comp m t₀ hτ (chartModelBasis E₁) y hd j
  rw [hρ, partialDeriv_scalarOnE_halfSqNorm F t x hy i, hpt, chartInvGramOnE_def, hsymm]
  ring

/-! ## The first variation identity -/

/-- The first-variation integrand is `X(ρ) + ρ div X` for `X = ∇(|F|²/2)`. -/
theorem firstVariation_integrand_eq [I.Boundaryless] (F : SmoothImmersionFamily I M E)
    (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀) (p : M) :
    backwardHeatKernel m t₀ t (F p t) *
        ((Module.finrank ℝ E₁ : ℝ) - F.tangentialSqNorm t p / (2 * (t₀ - t)) +
          @inner ℝ E _ (F p t) (F.meanCurvature t p)) =
      tangentSectionAction (gradG (F.inducedMetric t) (F.halfSqNorm t))
          (fun q => backwardHeatKernel m t₀ t (F q t)) p +
        backwardHeatKernel m t₀ t (F p t) *
          divergenceG (F.inducedMetric t) (gradG (F.inducedMetric t) (F.halfSqNorm t)) p := by
  rw [tangentSectionAction_gradG_halfSqNorm_backwardHeatKernel F m t₀ hτ p,
    ← Δ_g_def, laplacian_halfSqNorm F t p]
  ring

section Closed

variable [I.Boundaryless] [CompactSpace M] (F : SmoothImmersionFamily I M E) (m : ℕ) (t₀ : ℝ)
  {t : ℝ} (hτ : t < t₀)

include hτ in
/-- The kernel pulled back along a time slice is smooth. -/
theorem contMDiff_backwardHeatKernel_comp :
    ContMDiff I 𝓘(ℝ) ∞ fun p => backwardHeatKernel m t₀ t (F p t) :=
  ((contDiff_backwardHeatKernel m t₀ hτ).of_le le_top).comp_contMDiff
    ((F.contMDiff_timeSlice t).of_le le_top)

omit [I.Boundaryless] in
/-- On a closed manifold, every continuous function is integrable for the surface measure. -/
theorem integrable_of_continuous {f : M → ℝ} (hf : Continuous f) :
    Integrable f (F.surfaceMeasure t) := by
  have : IsFiniteMeasureOnCompacts (F.surfaceMeasure t) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) (F.inducedMetricFamily t)
  exact hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))

include hτ in
/-- The first-variation integrand is integrable on a closed manifold. -/
theorem integrable_firstVariation :
    Integrable (fun p => backwardHeatKernel m t₀ t (F p t) *
        ((Module.finrank ℝ E₁ : ℝ) - F.tangentialSqNorm t p / (2 * (t₀ - t)) +
          @inner ℝ E _ (F p t) (F.meanCurvature t p))) (F.surfaceMeasure t) := by
  have hρ := contMDiff_backwardHeatKernel_comp F m t₀ hτ
  simp only [firstVariation_integrand_eq F m t₀ hτ]
  exact integrable_of_continuous F
    ((tangentSectionAction_contMDiff _ hρ).continuous.add
      (hρ.continuous.mul (divergence_g_contMDiff _ _).continuous))

include hτ in
/-- **The first variation identity for Huisken's integral.** On a closed parameter manifold,

  `∫ ρ (n - ‖Fᵀ‖² / (2τ) + ⟪F, Hvec⟫) dμ = 0`.

This is the divergence theorem applied to the test field `ρ F`, in the form of the library's
integration by parts `∫ X(ρ) dμ = -∫ ρ div X dμ` with `X = ∇(|F|²/2)`: the integrand is
`X(ρ) + ρ Δ(|F|²/2)`. -/
theorem integral_firstVariation :
    ∫ p, backwardHeatKernel m t₀ t (F p t) *
        ((Module.finrank ℝ E₁ : ℝ) - F.tangentialSqNorm t p / (2 * (t₀ - t)) +
          @inner ℝ E _ (F p t) (F.meanCurvature t p)) ∂(F.surfaceMeasure t) = 0 := by
  set g := F.inducedMetric t
  set X := gradG g (F.halfSqNorm t)
  have hρ := contMDiff_backwardHeatKernel_comp F m t₀ hτ
  have hX : HasCompactSupport X :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  have h₁ : Integrable (fun p => tangentSectionAction X
      (fun q => backwardHeatKernel m t₀ t (F q t)) p) (F.surfaceMeasure t) :=
    integrable_of_continuous F (tangentSectionAction_contMDiff X hρ).continuous
  have h₂ : Integrable (fun p => backwardHeatKernel m t₀ t (F p t) * divergenceG g X p)
      (F.surfaceMeasure t) :=
    integrable_of_continuous F (hρ.continuous.mul (divergence_g_contMDiff g X).continuous)
  simp only [firstVariation_integrand_eq F m t₀ hτ]
  rw [integral_add h₁ h₂]
  change ∫ p, _ ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
    ∫ p, _ ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0
  rw [integral_tangentSectionAction_eq_neg_integral_smul_divergence g hρ X hX]
  ring

end Closed

end SmoothImmersionFamily

end HuiskenMonotonicity
