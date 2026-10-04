/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.SmoothImmersionFamily
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The metric induced by a smooth immersion family

For a spatial immersion `F_t : M → E`, the pullback of the Euclidean inner product is

`g_t(v, w) = ⟪dF_t(v), dF_t(w)⟫`.

This file bundles the expression as a continuous bilinear form and proves its algebraic properties
and positive definiteness at valid times. Packaging the family as a smooth `RiemannianBundle` is
left to the next stage, since that additionally requires smooth dependence in manifold charts.
-/

open scoped Manifold ContDiff

noncomputable section

namespace HuiskenMonotonicity

open Manifold

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ⊤ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

namespace SmoothImmersionFamily

/-- The Euclidean inner product pulled back along the spatial differential, as a continuous
bilinear form on the tangent space. -/
def inducedInnerForm (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (F.spatialDifferential p t)).comp
    ((innerSL ℝ).comp (F.spatialDifferential p t))

/-- The value of the metric induced by `F_t` on two tangent vectors. -/
def inducedInner (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ)
    (v w : TangentSpace I p) : ℝ :=
  F.inducedInnerForm p t v w

@[simp]
theorem inducedInnerForm_apply (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ)
    (v w : TangentSpace I p) :
    F.inducedInnerForm p t v w =
      @inner ℝ E _ (F.spatialDifferential p t v) (F.spatialDifferential p t w) :=
  rfl

@[simp]
theorem inducedInner_zero_left (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ)
    (w : TangentSpace I p) : F.inducedInner p t 0 w = 0 := by
  simp [inducedInner]

@[simp]
theorem inducedInner_zero_right (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ)
    (v : TangentSpace I p) : F.inducedInner p t v 0 = 0 := by
  simp [inducedInner]

theorem inducedInner_add_left (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ)
    (u v w : TangentSpace I p) :
    F.inducedInner p t (u + v) w = F.inducedInner p t u w + F.inducedInner p t v w := by
  simp [inducedInner]

theorem inducedInner_add_right (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ)
    (u v w : TangentSpace I p) :
    F.inducedInner p t u (v + w) = F.inducedInner p t u v + F.inducedInner p t u w := by
  change inner ℝ (F.spatialDifferential p t u)
      (F.spatialDifferential p t (v + w)) = _
  rw [map_add, inner_add_right]
  rfl

theorem inducedInner_smul_left (F : SmoothImmersionFamily I M E) (p : M) (t c : ℝ)
    (v w : TangentSpace I p) :
    F.inducedInner p t (c • v) w = c * F.inducedInner p t v w := by
  simp [inducedInner]

theorem inducedInner_smul_right (F : SmoothImmersionFamily I M E) (p : M) (t c : ℝ)
    (v w : TangentSpace I p) :
    F.inducedInner p t v (c • w) = c * F.inducedInner p t v w := by
  simp [inducedInner]

theorem inducedInner_symm (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ)
    (v w : TangentSpace I p) : F.inducedInner p t v w = F.inducedInner p t w v := by
  exact real_inner_comm _ _

theorem inducedInner_self_nonneg (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ)
    (v : TangentSpace I p) : 0 ≤ F.inducedInner p t v v :=
  real_inner_self_nonneg

theorem inducedInner_self_eq_norm_sq (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ)
    (v : TangentSpace I p) :
    F.inducedInner p t v v = ‖F.spatialDifferential p t v‖ ^ 2 := by
  simpa only [inducedInner, inducedInnerForm_apply] using
    real_inner_self_eq_norm_sq (F.spatialDifferential p t v)

/-- At a valid time, the induced quadratic form vanishes only on the zero tangent vector. -/
theorem inducedInner_self_eq_zero_iff (F : SmoothImmersionFamily I M E) {t : ℝ}
    (ht : F.IsValidTime t) (p : M) (v : TangentSpace I p) :
    F.inducedInner p t v v = 0 ↔ v = 0 := by
  change inner ℝ (F.spatialDifferential p t v) (F.spatialDifferential p t v) = 0 ↔ v = 0
  rw [inner_self_eq_zero]
  constructor
  · intro hv
    exact F.spatialDifferential_injective ht p (hv.trans (map_zero _).symm)
  · rintro rfl
    exact map_zero _

/-- At a valid time, the induced quadratic form is strictly positive on nonzero vectors. -/
theorem inducedInner_self_pos (F : SmoothImmersionFamily I M E) {t : ℝ}
    (ht : F.IsValidTime t) (p : M) {v : TangentSpace I p} (hv : v ≠ 0) :
    0 < F.inducedInner p t v v :=
  (F.inducedInner_self_nonneg p t v).lt_of_ne fun hzero ↦
    hv ((F.inducedInner_self_eq_zero_iff ht p v).mp hzero.symm)

end SmoothImmersionFamily

end HuiskenMonotonicity
