/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.MeanCurvatureFlow

/-!
# The monotonicity formula at an arbitrary centre

Huisken's formula is stated for the backward heat kernel centred at an arbitrary space-time
point `(x₀, t₀)`, `ρ_{x₀,t₀}(x, t) = ρ_{0,t₀}(x - x₀, t)`. Translating the immersion by `-x₀`
reduces it to the formula at the origin: a translation changes neither the induced metric,
nor the surface measure, nor the mean curvature vector, nor the flow equation, and it turns
the normal part of the position vector into the normal part of `F - x₀`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace HuiskenMonotonicity

open MeasureTheory Manifold DifferentialGeometry DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Geometry.Operator

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

/-- The Borel σ-algebra, matching the one under which `surfaceMeasure` is stated. -/
local instance instMeasurableSpaceTranslation : MeasurableSpace M := borel M

local instance instBorelSpaceTranslation : BorelSpace M := ⟨rfl⟩

/-- Translation `x ↦ x - c` of the ambient space, as a diffeomorphism. -/
def translationDiffeomorph (c : E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ where
  toEquiv := Equiv.subRight c
  contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

namespace SmoothImmersion

/-- The translate `f - c` of a smooth immersion. -/
def translate (f : SmoothImmersion I M E) (c : E) : SmoothImmersion I M E :=
  ⟨fun p => f p - c, f.contMDiff.sub contMDiff_const,
    f.isImmersion.comp_diffeomorph (translationDiffeomorph c)⟩

@[simp]
theorem translate_apply (f : SmoothImmersion I M E) (c : E) (p : M) :
    f.translate c p = f p - c :=
  rfl

/-- Translation does not change the differential. -/
theorem mfderiv_translate (f : SmoothImmersion I M E) (c : E) (p : M) :
    mfderiv I 𝓘(ℝ, E) (f.translate c) p = mfderiv I 𝓘(ℝ, E) f p := by
  have hf : MDifferentiableAt I 𝓘(ℝ, E) f p := f.contMDiff.mdifferentiableAt (by simp)
  change mfderiv I 𝓘(ℝ, E) (⇑f - fun _ => c) p = _
  rw [mfderiv_sub hf mdifferentiableAt_const, mfderiv_const]
  exact sub_zero (mfderiv I 𝓘(ℝ, E) f p : E₁ →L[ℝ] E)

variable [T2Space M]

/-- Translation does not change the induced metric. -/
theorem inducedMetric_translate (f : SmoothImmersion I M E) (c : E) :
    (f.translate c).inducedMetric = f.inducedMetric := by
  ext p v w
  simp only [inducedMetric_inner, mfderiv_translate]
  rfl

/-- Translation does not change the surface measure. -/
theorem surfaceMeasure_translate [SigmaCompactSpace M] (f : SmoothImmersion I M E) (c : E) :
    (f.translate c).surfaceMeasure = f.surfaceMeasure := by
  simp only [surfaceMeasure, inducedMetric_translate]

/-- Translation does not change the derivative of a chart representation. -/
theorem fderiv_chartRep_translate (f : SmoothImmersion I M E) (c : E) (α : M) :
    fderiv ℝ ((f.translate c).chartRep α) = fderiv ℝ (f.chartRep α) := by
  funext y
  exact fderiv_sub_const c

/-- Translation does not change the mean curvature vector. -/
theorem meanCurvature_translate (f : SmoothImmersion I M E) (c : E) (p : M) :
    (f.translate c).meanCurvature p = f.meanCurvature p := by
  simp only [meanCurvature, inducedMetric_translate,
    meanCurvatureNormal_congr (f.fderiv_chartRep_translate c p)]

/-- Translation does not change the normal component of a vector. -/
theorem normalComponent_translate (f : SmoothImmersion I M E) (c : E) (p : M) (v : E) :
    (f.translate c).normalComponent p v = f.normalComponent p v := by
  simp only [normalComponent, inducedMetric_translate,
    normalPart_congr (f.fderiv_chartRep_translate c p)]

/-- The normal part of the translated position vector is the normal part of `f - c`. -/
theorem normalPosition_translate (f : SmoothImmersion I M E) (c : E) (p : M) :
    (f.translate c).normalPosition p = f.normalComponent p (f p - c) := by
  rw [normalPosition, normalComponent_translate, translate_apply]

end SmoothImmersion

namespace SmoothImmersionFamily

/-- The translate `F - c` of a smooth immersion family. -/
def translate (F : SmoothImmersionFamily I M E) (c : E) : SmoothImmersionFamily I M E :=
  ⟨fun p t => F p t - c, F.contMDiff_spaceTime.sub contMDiff_const,
    fun t => ((F.slice t).translate c).isImmersion⟩

@[simp]
theorem translate_apply (F : SmoothImmersionFamily I M E) (c : E) (p : M) (t : ℝ) :
    F.translate c p t = F p t - c :=
  rfl

theorem slice_translate (F : SmoothImmersionFamily I M E) (c : E) (t : ℝ) :
    (F.translate c).slice t = (F.slice t).translate c :=
  rfl

variable [T2Space M]

theorem surfaceMeasure_translate [SigmaCompactSpace M] (F : SmoothImmersionFamily I M E)
    (c : E) (t : ℝ) : (F.translate c).surfaceMeasure t = F.surfaceMeasure t :=
  (F.slice t).surfaceMeasure_translate c

/-- Translation preserves mean curvature flow. -/
theorem IsMeanCurvatureFlowAt.translate {F : SmoothImmersionFamily I M E} {t : ℝ}
    (hmcf : F.IsMeanCurvatureFlowAt t) (c : E) : (F.translate c).IsMeanCurvatureFlowAt t := by
  intro p
  rw [slice_translate, SmoothImmersion.meanCurvature_translate]
  exact (hmcf p).sub_const c

variable [I.Boundaryless]

/-- **Huisken's monotonicity formula** (Huisken 1990, Theorem 3.1). For a family of
immersions of a closed `n`-manifold moving by mean curvature at time `t`, and the backward
heat kernel centred at `(x₀, t₀)` with `t < t₀`,

  `d/dt ∫_M ρ_{x₀,t₀}(F, t) dμ_t
      = -∫_M ρ_{x₀,t₀}(F, t) ‖Hvec + (F - x₀)^⊥ / (2(t₀ - t))‖² dμ_t`. -/
theorem huisken_monotonicity [CompactSpace M] (F : SmoothImmersionFamily I M E)
    (x₀ : E) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀) (hmcf : F.IsMeanCurvatureFlowAt t) :
    HasDerivAt
      (fun s => ∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ s (F p s - x₀)
        ∂(F.surfaceMeasure s))
      (-∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ t (F p t - x₀) *
          ‖(F.slice t).meanCurvature p +
            (1 / (2 * (t₀ - t))) • (F.slice t).normalComponent p (F p t - x₀)‖ ^ 2
        ∂(F.surfaceMeasure t)) t := by
  have h := (F.translate x₀).huisken_monotonicity_origin t₀ hτ (hmcf.translate x₀)
  simp only [surfaceMeasure_translate, translate_apply, slice_translate,
    SmoothImmersion.meanCurvature_translate, SmoothImmersion.normalPosition_translate,
    slice_apply] at h
  exact h

end SmoothImmersionFamily

end HuiskenMonotonicity
