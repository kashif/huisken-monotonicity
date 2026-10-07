/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.VossWeyl
import HuiskenMonotonicity.FirstVariation
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

/-- **The first variation identity for Huisken's integral.** On a closed parameter manifold,

  `∫ ρ (n - ‖Fᵀ‖² / (2τ) + ⟪F, Hvec⟫) dμ = 0`.

This is the divergence theorem applied to the test field `ρ F`, in the form of the library's
integration by parts `∫ X(ρ) dμ = -∫ ρ div X dμ` with `X = ∇(|F|²/2)`: the integrand is
`X(ρ) + ρ Δ(|F|²/2)`. -/
theorem integral_firstVariation [I.Boundaryless] [CompactSpace M]
    (F : SmoothImmersionFamily I M E) (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀) :
    ∫ p, backwardHeatKernel m t₀ t (F p t) *
        ((Module.finrank ℝ E₁ : ℝ) - F.tangentialSqNorm t p / (2 * (t₀ - t)) +
          @inner ℝ E _ (F p t) (F.meanCurvature t p)) ∂(F.surfaceMeasure t) = 0 := by
  set g := F.inducedMetric t
  set X := gradG g (F.halfSqNorm t)
  set ρ : M → ℝ := fun p => backwardHeatKernel m t₀ t (F p t)
  have hρ : ContMDiff I 𝓘(ℝ) ∞ ρ :=
    ((contDiff_backwardHeatKernel m t₀ hτ).of_le le_top).comp_contMDiff
      ((F.contMDiff_timeSlice t).of_le le_top)
  have hcpt : ∀ f : M → ℝ, HasCompactSupport f := fun f =>
    isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  have hX : HasCompactSupport X :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  haveI := riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hμ : F.surfaceMeasure t = riemannianVolumeMeasure (I := I) (M := M) g := rfl
  have hint₁ : Integrable (tangentSectionAction X ρ) (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (tangentSectionAction_contMDiff X hρ).continuous.integrable_of_hasCompactSupport (hcpt _)
  have hint₂ : Integrable (fun p => ρ p * divergenceG g X p)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (hρ.continuous.mul (divergence_g_contMDiff g X).continuous).integrable_of_hasCompactSupport
      (hcpt _)
  have hpt : ∀ p, ρ p * ((Module.finrank ℝ E₁ : ℝ) - F.tangentialSqNorm t p / (2 * (t₀ - t)) +
        @inner ℝ E _ (F p t) (F.meanCurvature t p)) =
      tangentSectionAction X ρ p + ρ p * divergenceG g X p := by
    intro p
    rw [tangentSectionAction_gradG_halfSqNorm_backwardHeatKernel F m t₀ hτ p,
      ← Δ_g_def, laplacian_halfSqNorm F t p]
    ring
  rw [hμ, integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hint₁ hint₂,
    integral_tangentSectionAction_eq_neg_integral_smul_divergence g hρ X hX]
  ring

end SmoothImmersionFamily

end HuiskenMonotonicity
