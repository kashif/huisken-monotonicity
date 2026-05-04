/-
Abstract structure for an evolving family of immersed hypersurfaces and their mean
curvature flow.

Mathlib (as of v4.30.0-rc2) provides `Manifold.IsImmersion` and the metric layer of
Riemannian geometry, but it does **not** yet define:

  * the second fundamental form of an isometric immersion;
  * the mean curvature vector;
  * the induced volume measure on the image of an immersion;
  * the first variation of area / divergence theorem on a submanifold.

We can still write the MCF equation `∂_t F = H` literally, by *parameterising* the
predicate `IsMeanCurvatureFlow F H` over both the family `F` and an externally supplied
velocity field `H : M → ℝ → E`. The geometric content — that `H(p, t)` actually equals
the mean curvature vector of `F(·, t)(M)` at `F(p, t)` — is left to the caller until
mathlib gains the second fundamental form. Other missing primitives (surface measure,
divergence theorem) appear here as further placeholder fields.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
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

/-- An `ImmersionFamily F` solves mean curvature flow with prescribed velocity field
`H : M → ℝ → E` if for every point `p` and every interior time `t ∈ [0, T)`,

  `∂/∂s F(p, s) ∣_{s = t} = H(p, t)`.

Geometrically `H(p, t)` is the mean curvature vector of the hypersurface
`F(·, t)(M)` at the image point `F(p, t)`. Mathlib does not yet construct that
vector from `F` alone (the second fundamental form and the induced volume of an
isometric immersion are missing), so the predicate takes `H` as explicit data:
the caller supplies the mean curvature vector field, and `IsMeanCurvatureFlow F H`
asserts that `F` evolves with that velocity. Once mean curvature lands in mathlib,
this can be specialised to the unique geometric `H`. -/
def IsMeanCurvatureFlow
    {M E : Type*} [TopologicalSpace M] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : ImmersionFamily M E) (H : M → ℝ → E) : Prop :=
  ∀ p : M, ∀ t : ℝ, 0 ≤ t → t < F.T → HasDerivAt (fun s => F p s) (H p t) t

/-- The **rescaled** mean curvature flow predicate. Under Huisken's parabolic rescaling
`F̃(p, s) = (2(T - t))^(-1/2) F(p, t)`, `s = -½ log(T - t)`, the rescaled family
satisfies the augmented evolution equation

  `∂/∂s' F̃(p, s') ∣_{s' = s} = H̃(p, s) + F̃(p, s)`,

where the extra `F̃` term arises from differentiating the time-dependent rescaling
factor. Same caveats as `IsMeanCurvatureFlow`: the velocity-direction `H̃` is taken
as explicit data until mathlib gains the second fundamental form. -/
def IsRescaledMeanCurvatureFlow
    {M E : Type*} [TopologicalSpace M] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : ImmersionFamily M E) (H : M → ℝ → E) : Prop :=
  ∀ p : M, ∀ s : ℝ, 0 ≤ s → s < F.T →
    HasDerivAt (fun s' => F p s') (H p s + F p s) s

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
