/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Smooth immersions and smooth families of immersions

A smooth immersion `f : M → E`, and a smooth family of immersions `F_t : M → E`, recorded as a
jointly smooth map `M × ℝ → E` each of whose time slices is an immersion. Fixed-time geometry
lives on `SmoothImmersion`, and a family reads it off its slices `F.slice t`.

Both conditions are imposed at *every* real time, not only on the interval on which a flow is
considered. Two reasons. Smoothness on all of `M × ℝ` avoids a manifold-with-boundary
structure on a half-open time interval and is what makes the induced metric family regular
in the sense of the transport formula, whose regularity hypothesis is global in time. And
the induced metric is defined from the immersion condition, so a metric family on all of `ℝ`
needs the immersion condition on all of `ℝ`; that is `mfderiv_injective` below.
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

/-- A smooth immersion `f : M → E`. All fixed-time geometry (induced metric, surface measure,
mean curvature) is attached to this structure, so that it visibly depends on a single time
slice of a family only. -/
structure SmoothImmersion [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]
    where
  /-- The map. -/
  toFun : M → E
  /-- Smoothness. -/
  contMDiff : ContMDiff I 𝓘(ℝ, E) ∞ toFun
  /-- The immersion condition: the differential is injective at every point, which is exactly
  what the induced metric needs. Every immersion in the sense of mathlib's `IsImmersion` gives
  one (`ofIsImmersion`); the converse, that an injective differential makes `f` an immersion in
  finite dimensions, is not yet in mathlib. -/
  mfderiv_injective : ∀ p, Function.Injective (mfderiv I 𝓘(ℝ, E) toFun p)

/-- A smooth family of immersions `F_t : M → E`, indexed by all real times. -/
structure SmoothImmersionFamily [IsManifold I ∞ M] [FiniteDimensional ℝ E₁]
    [FiniteDimensional ℝ E] where
  /-- The space-time map. -/
  toFun : M → ℝ → E
  /-- Joint smoothness in space and time. -/
  contMDiff_spaceTime :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (Function.uncurry toFun)
  /-- Every time slice is an immersion: its differential is injective. -/
  mfderiv_injective : ∀ (t : ℝ) (p : M),
    Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q ↦ toFun q t) p)

variable {I M E}
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

namespace SmoothImmersion

instance : CoeFun (SmoothImmersion I M E) (fun _ ↦ M → E) :=
  ⟨SmoothImmersion.toFun⟩

/-- A smooth immersion in the sense of mathlib's `IsImmersion`. -/
def ofIsImmersion (f : M → E) (hf : IsImmersion I 𝓘(ℝ, E) ∞ f) : SmoothImmersion I M E :=
  ⟨f, hf.contMDiff, hf.mfderiv_injective (by simp)⟩

end SmoothImmersion

namespace SmoothImmersionFamily

instance : CoeFun (SmoothImmersionFamily I M E) (fun _ ↦ M → ℝ → E) :=
  ⟨SmoothImmersionFamily.toFun⟩

/-- Each time slice is smooth. -/
theorem contMDiff_timeSlice (F : SmoothImmersionFamily I M E) (t : ℝ) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun p ↦ F p t) :=
  F.contMDiff_spaceTime.curry_left

/-- The time slice `F_t`, as a smooth immersion. -/
def slice (F : SmoothImmersionFamily I M E) (t : ℝ) : SmoothImmersion I M E :=
  ⟨fun p ↦ F p t, F.contMDiff_timeSlice t, F.mfderiv_injective t⟩

@[simp]
theorem slice_apply (F : SmoothImmersionFamily I M E) (t : ℝ) (p : M) :
    F.slice t p = F p t :=
  rfl

end SmoothImmersionFamily

end HuiskenMonotonicity
