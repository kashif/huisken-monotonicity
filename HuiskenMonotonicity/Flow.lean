/-
Abstract structure for an evolving family of immersed hypersurfaces and their mean
curvature flow.

Mathlib (as of v4.30.0-rc2) provides `Manifold.IsImmersion` and the metric layer of
Riemannian geometry, but it does **not** yet define:

  * the second fundamental form of an isometric immersion;
  * the mean curvature vector;
  * the induced volume measure on the image of an immersion;
  * the first variation of area / divergence theorem on a submanifold.

So we cannot yet write `MeanCurvatureFlow F` as the literal PDE `∂_t F = H`. What we do
here is set up the **interface** that the statement of Huisken's monotonicity theorem can
use, with each missing geometric primitive marked as a field to be discharged later.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace HuiskenMonotonicity

/-- Data of a smooth family of immersions of a fixed `n`-manifold `M` into Euclidean
ambient space `E`, parameterised by a half-open time interval `[0, T)`.

The smoothness/immersion hypotheses required for MCF go beyond plain continuity; this
structure is the bare minimum needed to *state* Huisken's theorem. -/
structure ImmersionFamily
    (M : Type*) (E : Type*)
    [TopologicalSpace M] [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- Maximal existence time. -/
  T : ℝ
  /-- Positivity of the existence time. -/
  T_pos : 0 < T
  /-- The map `F : M × [0, T) → E`. -/
  toFun : M → ℝ → E
  /-- Continuity of `F` in `(p, t)`. -/
  continuous_toFun : Continuous (fun pt : M × ℝ => toFun pt.1 pt.2)

namespace ImmersionFamily

variable {M E : Type*} [TopologicalSpace M] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

instance : CoeFun (ImmersionFamily M E) (fun _ => M → ℝ → E) := ⟨ImmersionFamily.toFun⟩

end ImmersionFamily

/-- Predicate that an `ImmersionFamily F` solves mean curvature flow.

The intended statement is

  ∀ p ∈ M, ∀ t ∈ [0, T),  ∂_t F(p, t) = H(p, t),

where `H(p, t)` is the mean curvature vector of `F(·, t)` at `p`. Defining `H`
requires the second fundamental form of an isometric immersion, which is not yet in
mathlib. We therefore axiomatise the predicate so that downstream statements (Huisken's
monotonicity formula) can be written. When mean curvature lands in mathlib, replace
this by the literal PDE. -/
class IsMeanCurvatureFlow
    {M E : Type*} [TopologicalSpace M] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : ImmersionFamily M E) : Prop where
  /-- Witness that the family solves the mean curvature flow. Currently opaque. -/
  out : True

/-- Placeholder for the surface measure on `F(·, t)(M)`.

In the formula `(d/dt) ∫_{M_t} ρ dμ_t = …`, `dμ_t` is the volume element induced by the
restricted Euclidean metric. Once mathlib has an "induced volume of an isometric
immersion", this becomes `MeasureTheory.Measure.map (F · t) μ_M` weighted by the
Jacobian. -/
structure SurfaceMeasure
    {M E : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : ImmersionFamily M E) where
  /-- The measure on `M` representing `dμ_t` at time `t`. -/
  μ : ℝ → MeasureTheory.Measure M

end HuiskenMonotonicity
