/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Kashif Rasul
-/

import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-!
# Injectivity of the differential of an immersion

This file contains a minimal local port of mathlib PRs `#41796` and `#42012`. It proves only the
implication needed by this project: a smooth immersion has injective manifold differential. The
proof is isolated here so it can be deleted when the corresponding mathlib declarations merge.
-/

open Function Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace HuiskenMonotonicity.Upstream

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section ExtendedChart

open IsManifold

variable {e : OpenPartialHomeomorph M H}

private theorem mdifferentiableAt_extend {x : M} (he : e ∈ maximalAtlas I 1 M)
    (hx : x ∈ e.source) : MDiffAt (e.extend I) x :=
  (e.contMDiffAt_extend he hx).mdifferentiableAt (by simp)

private theorem mdifferentiableWithinAt_extend_symm {z : E}
    (he : e ∈ maximalAtlas I 1 M) (hz : z ∈ (e.extend I).target) :
    MDiffAt[range I] (e.extend I).symm z := by
  have hI : MDiffAt[range I] I.symm z :=
    I.mdifferentiableWithinAt_symm (e.extend_target_subset_range hz)
  apply MDifferentiableAt.comp_mdifferentiableWithinAt _ _ hI
  exact mdifferentiableAt_symm_of_mem_maximalAtlas he (by simp_all)

private theorem mfderiv_extend_comp_mfderivWithin_extend_symm
    {y : E} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ (e.extend I).target) :
    (mfderiv% (e.extend I) ((e.extend I).symm y)) ∘L
      (mfderiv[range I] (e.extend I).symm y) = ContinuousLinearMap.id _ _ := by
  have hUnique : UniqueMDiffAt[range I] y := by
    apply I.uniqueMDiffOn
    exact e.extend_target_subset_range hy
  have hy' : (e.extend I).symm y ∈ e.source := PartialEquiv.map_target _ (by simp_all)
  rw [← mfderiv_comp_mfderivWithin]
  · rw [← mfderivWithin_id hUnique]
    apply Filter.EventuallyEq.mfderivWithin_eq
    · have hright : (e.extend I) ((e.extend I).symm y) = y := (e.extend I).right_inv hy
      filter_upwards [hright ▸ e.extend_target_mem_nhdsWithin hy' (I := I)] with z hz
      simp_all
    · simp_all
  · exact mdifferentiableAt_extend he hy'
  · exact mdifferentiableWithinAt_extend_symm he hy
  · exact hUnique

private theorem mfderivWithin_extend_symm_comp_mfderiv_extend
    {y : E} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ (e.extend I).target) :
    (mfderiv[range I] (e.extend I).symm y) ∘L
      (mfderiv% (e.extend I) ((e.extend I).symm y)) = ContinuousLinearMap.id _ _ := by
  have hy' : (e.extend I).symm y ∈ e.source := by simp_all
  have hUnique : UniqueMDiffAt[(e.extend I).source] ((e.extend I).symm y) := by
    rw [e.extend_source]
    exact e.open_source.uniqueMDiffWithinAt hy'
  have hmfderiv : mfderiv% (e.extend I) ((e.extend I).symm y) =
      mfderiv[(e.extend I).source] (e.extend I) ((e.extend I).symm y) := by
    rw [mfderivWithin_eq_mfderiv hUnique]
    exact mdifferentiableAt_extend he hy'
  rw [hmfderiv, ← mfderivWithin_comp_of_eq]
  · rw [← mfderivWithin_id hUnique]
    apply Filter.EventuallyEq.mfderivWithin_eq
    · filter_upwards [e.extend_source_mem_nhdsWithin (I := I) hy'] with z hz
      simp only [Function.comp_def, PartialEquiv.left_inv (e.extend I) hz, id_eq]
    · simp only [Function.comp_def, PartialEquiv.right_inv (e.extend I) hy, id_eq]
  · exact mdifferentiableWithinAt_extend_symm he hy
  · exact (mdifferentiableAt_extend he hy').mdifferentiableWithinAt
  · intro z hz
    exact e.extend_target_subset_range ((e.extend I).map_source hz)
  · exact hUnique
  · exact (e.extend I).right_inv hy

private theorem isInvertible_mfderiv_extend {y : M} (he : e ∈ maximalAtlas I 1 M)
    (hy : y ∈ e.source) : (mfderiv% (e.extend I) y).IsInvertible := by
  have hy' : e.extend I y ∈ (e.extend I).target := (e.extend I).map_source (by simpa using hy)
  have hInvertible := ContinuousLinearMap.IsInvertible.of_inverse
    (mfderiv_extend_comp_mfderivWithin_extend_symm he hy')
    (mfderivWithin_extend_symm_comp_mfderiv_extend he hy')
  rwa [(e.extend I).left_inv (by simpa using hy)] at hInvertible

end ExtendedChart

section Immersion

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type*} [TopologicalSpace H']
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
variable {H₂ : Type*} [TopologicalSpace H₂]
variable {I₂ : ModelWithCorners 𝕜 E₂ H₂}
variable {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]

private theorem hasLeftInverse_mfderiv_comp {f : M → M'} {g : M' → M₂} {x : M}
    (hg : (mfderiv I' I₂ g (f x)).HasLeftInverse)
    (hf : (mfderiv I I' f x).HasLeftInverse) :
    (mfderiv I I₂ (g ∘ f) x).HasLeftInverse := by
  rw [mfderiv_comp x
    (mdifferentiableAt_of_mfderiv_injective hg.injective)
    (mdifferentiableAt_of_mfderiv_injective hf.injective)]
  exact hg.comp hf

private theorem hasLeftInverse_mfderiv_of_comp {f : M → M'} {g : M' → M₂} {x : M}
    (hf : MDiffAt f x) (hg : MDiffAt g (f x))
    (hgf : (mfderiv I I₂ (g ∘ f) x).HasLeftInverse) :
    (mfderiv I I' f x).HasLeftInverse := by
  rw [mfderiv_comp x hg hf] at hgf
  exact ContinuousLinearMap.HasLeftInverse.of_comp hgf

private theorem hasLeftInverse_mfderiv_congr {f g : M → M'} {x : M}
    (hf : (mfderiv I I' f x).HasLeftInverse) (hgf : g =ᶠ[nhds x] f) :
    (mfderiv I I' g x).HasLeftInverse := by
  rwa [hgf.mfderiv_eq]

variable {E'' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners 𝕜 E'' G}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : M → N} {x : M}

private theorem isImmersionAtOfComplement_mfderiv_hasLeftInverse
    (h : Manifold.IsImmersionAtOfComplement F I J ⊤ f x) :
    (mfderiv I J f x).HasLeftInverse := by
  suffices (mfderiv I 𝓘(𝕜, E'') ((h.codChart.extend J) ∘ f) x).HasLeftInverse by
    apply hasLeftInverse_mfderiv_of_comp
      (h.contMDiffAt.mdifferentiableAt (by simp))
      (mdifferentiableAt_extend
        (IsManifold.maximalAtlas_subset_of_le (by simp) h.codChart_mem_maximalAtlas)
        h.mem_codChart_source)
      this
  let rhs : E →L[𝕜] E'' :=
    h.equiv.toContinuousLinearMap.comp ((ContinuousLinearMap.id _ _).prod 0)
  have heq : EqOn ((h.codChart.extend J) ∘ f) (rhs ∘ (h.domChart.extend I))
      h.domChart.source := by
    intro x' hx'
    trans ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm ∘
      (h.domChart.extend I)) x'
    · simp [h.domChart.left_inv hx']
    · exact h.writtenInCharts ((h.domChart.extend I).map_source' (by simpa))
  apply hasLeftInverse_mfderiv_congr
    (hgf := Filter.eventually_of_mem
      (h.domChart.open_source.mem_nhds h.mem_domChart_source) heq)
  apply hasLeftInverse_mfderiv_comp (I := I) (I' := 𝓘(𝕜, E))
    (I₂ := 𝓘(𝕜, E'')) (f := h.domChart.extend I) (g := rhs)
  · rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    exact h.equiv.hasLeftInverse.comp ContinuousLinearMap.HasLeftInverse.inl
  · exact ContinuousLinearMap.HasLeftInverse.of_isInvertible <| isInvertible_mfderiv_extend
        (IsManifold.maximalAtlas_subset_of_le (by simp) h.domChart_mem_maximalAtlas)
        (by simp [h.mem_domChart_source])

/-- A smooth immersion has injective manifold differential at every point.

Ported from mathlib PR `#41796`; remove this theorem when its upstream counterpart is available. -/
theorem isImmersion_mfderiv_injective (h : Manifold.IsImmersion I J ⊤ f) (x : M) :
    Function.Injective (mfderiv I J f x) :=
  (isImmersionAtOfComplement_mfderiv_hasLeftInverse
    (h.isImmersionOfComplement_complement x)).injective

end Immersion

end HuiskenMonotonicity.Upstream
