/-
Copyright (c) 2025 Patrick Massot, Michael Rothgang, Heather Macbeth.
Released under Apache 2.0 license as described in the file LICENSE.

**VENDORED** from open mathlib PR #36299 (`feat: metric connections`),
specifically the +14 lines added to
`Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean`. Once that PR
lands in mathlib master, this file should be removed and the import
swapped to `Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions`.
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

@[expose] public section

open NormedSpace
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {f g : M → E'} {z : M}

theorem fromTangentSpace_mfderiv_add (hf : MDiffAt f z) (hg : MDiffAt g z) :
    (fromTangentSpace _).toContinuousLinearMap ∘L (mfderiv% (f + g) z)
    = (fromTangentSpace _).toContinuousLinearMap ∘L (mfderiv% f z)
    + (fromTangentSpace _).toContinuousLinearMap ∘L (mfderiv% g z) :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv

theorem fromTangentSpace_mfderiv_add_apply (hf : MDiffAt f z) (hg : MDiffAt g z)
    {x : M} (v : TangentSpace I x) :
    fromTangentSpace _ (mfderiv% (f + g) z v)
    = fromTangentSpace _ (mfderiv% f z v) + fromTangentSpace _ (mfderiv% g z v) :=
  congr($(fromTangentSpace_mfderiv_add hf hg) v)
