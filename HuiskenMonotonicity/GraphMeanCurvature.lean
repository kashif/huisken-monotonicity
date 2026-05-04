/-
Mean curvature of a graph hypersurface in `ℝⁿ⁺¹`.

For a smooth function `f : EuclideanSpace ℝ (Fin n) → ℝ` viewed as the height of a
hypersurface `M = { (x, f(x)) : x ∈ U }` over an open `U ⊂ ℝⁿ`, classical differential
geometry gives the *mean curvature* of `M` as the divergence

  `H(x) = div( ∇f / √(1 + ‖∇f‖²) )(x).`

(Schnürer, "Lectures on MCF", Lemma 2.1, with the lower-normal convention
`ν = (∇f, -1) / √(1 + ‖∇f‖²)`. The upper-normal convention `ν = (-∇f, 1) / v` flips
the sign.)

This module **defines** that quantity directly. It bypasses the abstract second
fundamental form and induced volume measure — neither of which is in mathlib v4.30.0-rc2
— and gives us a workable notion of mean curvature for graphs that we can use to attack
the rotationally symmetric (§5) and self-similar shrinking sphere cases of Huisken
(1990) without first formalising the full submanifold theory.
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace HuiskenMonotonicity

open scoped Gradient

variable {n : ℕ}

/-- The graph area-element factor `v(x) = √(1 + ‖∇f(x)‖²)` arising from the induced
metric of the graph hypersurface `y = f(x)`. Always positive (≥ 1), since the inside
is `≥ 1`. -/
noncomputable def graphAreaFactor
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (1 + ‖∇ f x‖ ^ 2)

/-- The mean curvature of the graph hypersurface `y = f(x)` at the point `(x, f(x))`,
defined directly by the divergence formula

  `H(x) = Σᵢ ∂/∂xᵢ ( ∂ᵢf(x) / √(1 + ‖∇f(x)‖²) )`.

This is the lower-normal convention from Schnürer §2 (Lemma 2.1); the upper-normal
form differs by a sign. -/
noncomputable def meanCurvatureGraph
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, (∇ (fun y : EuclideanSpace ℝ (Fin n) => ∇ f y i / graphAreaFactor f y) x) i

/-! ## Sanity checks -/

/-- Area factor of a constant graph is `1`: a horizontal hyperplane has `v ≡ 1`. -/
@[simp] lemma graphAreaFactor_const (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    graphAreaFactor (fun _ => c) x = 1 := by
  unfold graphAreaFactor
  simp

/-- A horizontal hyperplane (constant graph) has zero mean curvature. -/
@[simp] lemma meanCurvatureGraph_const (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    meanCurvatureGraph (fun _ => c) x = 0 := by
  unfold meanCurvatureGraph
  simp

end HuiskenMonotonicity
