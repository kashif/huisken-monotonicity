/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.Flow
import HuiskenMonotonicity.Upstream.ImmersionInjective
import Mathlib.Geometry.Manifold.Immersion

/-!
# Smooth families of immersed hypersurfaces

This file strengthens `ImmersionFamily` with the manifold smoothness and immersion hypotheses
needed for geometric mean curvature flow. The space-time map is required to be smooth on
`M × ℝ`; the time interval `[0, T)` selects the part used by the flow.
-/

open scoped Manifold ContDiff

namespace HuiskenMonotonicity

open Manifold

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E₁ H)
variable (M : Type v) [TopologicalSpace M] [ChartedSpace H M]
variable (E : Type w) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A smooth family of immersions `F_t : M → E` for `0 ≤ t < T`.

Smoothness is recorded for the uncurried map `M × ℝ → E`. Requiring an extension to all real
times avoids putting a manifold-with-boundary structure on `[0, T)` and is sufficient for every
local time derivative used in mean curvature flow. -/
structure SmoothImmersionFamily [IsManifold I ⊤ M] [FiniteDimensional ℝ E₁]
    [FiniteDimensional ℝ E] where
  /-- Maximal existence time. -/
  T : ℝ
  /-- Positivity of the existence time. -/
  T_pos : 0 < T
  /-- The space-time immersion map. -/
  toFun : M → ℝ → E
  /-- Joint smoothness in space and time. -/
  contMDiff_spaceTime :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ⊤ (Function.uncurry toFun)
  /-- Every time slice in `[0, T)` is a smooth immersion. -/
  isImmersion_time :
    ∀ t : ℝ, 0 ≤ t → t < T → IsImmersion I 𝓘(ℝ, E) ⊤ (fun p => toFun p t)

namespace SmoothImmersionFamily

variable {I M E}
variable [sourceManifold : IsManifold I ⊤ M]
variable [sourceFiniteDimensional : FiniteDimensional ℝ E₁]
variable [ambientFiniteDimensional : FiniteDimensional ℝ E]

instance : CoeFun (SmoothImmersionFamily I M E) (fun _ => M → ℝ → E) :=
  ⟨SmoothImmersionFamily.toFun⟩

/-- The valid half-open time interval of a smooth immersion family. -/
def IsValidTime (F : SmoothImmersionFamily I M E) (t : ℝ) : Prop :=
  0 ≤ t ∧ t < F.T

/-- A smooth family restricts to the old continuity-only flow interface. -/
def toImmersionFamily (F : SmoothImmersionFamily I M E) : ImmersionFamily M E where
  T := F.T
  T_pos := F.T_pos
  toFun := F.toFun
  continuous_toFun := F.contMDiff_spaceTime.continuous

/-- Applying the continuity-only adapter agrees with applying the smooth family. -/
@[simp]
theorem toImmersionFamily_apply (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ) :
    F.toImmersionFamily p t = F p t :=
  rfl

/-- The continuity-only adapter preserves the maximal existence time. -/
@[simp]
theorem toImmersionFamily_T (F : SmoothImmersionFamily I M E) :
    F.toImmersionFamily.T = F.T :=
  rfl

/-- Each fixed-time spatial slice is smooth. -/
theorem contMDiff_timeSlice (F : SmoothImmersionFamily I M E) (t : ℝ) :
    ContMDiff I 𝓘(ℝ, E) ⊤ (fun p => F p t) :=
  F.contMDiff_spaceTime.curry_left

/-- Each fixed-point trajectory is smooth in time. -/
theorem contMDiff_pointTrajectory (F : SmoothImmersionFamily I M E) (p : M) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ⊤ (fun t => F p t) :=
  F.contMDiff_spaceTime.curry_right

/-- The time velocity of a smooth immersion family. -/
noncomputable def timeVelocity (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ) : E :=
  deriv (fun s => F p s) t

/-- Point trajectories have derivative `timeVelocity`. -/
theorem hasDerivAt_pointTrajectory (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ) :
    HasDerivAt (fun s => F p s) (F.timeVelocity p t) t := by
  apply DifferentiableAt.hasDerivAt
  have h := F.contMDiff_pointTrajectory p
  rw [contMDiff_iff_contDiff] at h
  exact h.differentiable (by norm_num) t

/-- The old flow predicate holds for the canonical time velocity of the smooth family. -/
theorem isMeanCurvatureFlow_timeVelocity (F : SmoothImmersionFamily I M E) :
    IsMeanCurvatureFlow F.toImmersionFamily F.timeVelocity := by
  intro p t _ _
  exact F.hasDerivAt_pointTrajectory p t

/-- The spatial differential `d(F_t)_p`. -/
noncomputable def spatialDifferential (F : SmoothImmersionFamily I M E) (p : M) (t : ℝ) :
    TangentSpace I p →L[ℝ] E :=
  (NormedSpace.fromTangentSpace (F p t)).toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p)

/-- At valid times, each spatial slice is an immersion. -/
theorem isImmersion_time' (F : SmoothImmersionFamily I M E) {t : ℝ}
    (ht : F.IsValidTime t) :
    IsImmersion I 𝓘(ℝ, E) ⊤ (fun p => F p t) :=
  F.isImmersion_time t ht.1 ht.2

/-- At valid times, the spatial differential is injective. -/
theorem spatialDifferential_injective (F : SmoothImmersionFamily I M E) {t : ℝ}
    (ht : F.IsValidTime t) (p : M) : Function.Injective (F.spatialDifferential p t) := by
  exact (NormedSpace.fromTangentSpace (F p t)).injective.comp
    (Upstream.isImmersion_mfderiv_injective (F.isImmersion_time' ht) p)

/-- The dimension conditions making a smooth immersion family a hypersurface family. -/
def IsHypersurfaceFamily (_F : SmoothImmersionFamily I M E) (n : ℕ) : Prop :=
  Module.finrank ℝ E₁ = n ∧ Module.finrank ℝ E = n + 1

/-- The tangent spaces have the declared hypersurface dimension. -/
theorem finrank_tangentSpace (F : SmoothImmersionFamily I M E) {n : ℕ}
    (hF : F.IsHypersurfaceFamily n) (p : M) :
    Module.finrank ℝ (TangentSpace I p) = n := by
  change Module.finrank ℝ E₁ = n
  exact hF.1

/-- The ambient space has dimension one greater than the hypersurface. -/
theorem finrank_ambient (F : SmoothImmersionFamily I M E) {n : ℕ}
    (hF : F.IsHypersurfaceFamily n) :
    Module.finrank ℝ E = n + 1 :=
  hF.2

end SmoothImmersionFamily

end HuiskenMonotonicity
