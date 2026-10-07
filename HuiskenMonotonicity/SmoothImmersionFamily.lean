/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.Upstream.ImmersionInjective
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Smooth families of immersed hypersurfaces

A smooth family of immersions `F_t : M → E`, recorded as a jointly smooth map `M × ℝ → E`
each of whose time slices is an immersion.

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

/-- A smooth family of immersions `F_t : M → E`, indexed by all real times. -/
structure SmoothImmersionFamily [IsManifold I ⊤ M] [FiniteDimensional ℝ E₁]
    [FiniteDimensional ℝ E] where
  /-- The space-time map. -/
  toFun : M → ℝ → E
  /-- Joint smoothness in space and time. -/
  contMDiff_spaceTime :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ⊤ (Function.uncurry toFun)
  /-- Every time slice is a smooth immersion. -/
  isImmersion : ∀ t : ℝ, IsImmersion I 𝓘(ℝ, E) ⊤ (fun p => toFun p t)

namespace SmoothImmersionFamily

variable {I M E}
variable [IsManifold I ⊤ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

instance : CoeFun (SmoothImmersionFamily I M E) (fun _ => M → ℝ → E) :=
  ⟨SmoothImmersionFamily.toFun⟩

/-- Each time slice is smooth. -/
theorem contMDiff_timeSlice (F : SmoothImmersionFamily I M E) (t : ℝ) :
    ContMDiff I 𝓘(ℝ, E) ⊤ (fun p => F p t) :=
  F.contMDiff_spaceTime.curry_left

/-- Each time slice has injective differential. This is the hypothesis the induced metric
family is built from, discharged once and for all. -/
theorem mfderiv_injective (F : SmoothImmersionFamily I M E) (t : ℝ) (p : M) :
    Function.Injective (mfderiv I 𝓘(ℝ, E) (fun q => F q t) p) :=
  Upstream.isImmersion_mfderiv_injective (F.isImmersion t) p

end SmoothImmersionFamily

end HuiskenMonotonicity
