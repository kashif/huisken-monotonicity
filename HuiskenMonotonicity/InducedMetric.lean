/-
**Induced (pullback) metric of a smooth map.**

For a smooth map `F : E₁ → E₂` between an inner product space `E₁` (source — e.g.
`EuclideanSpace ℝ (Fin n)` for coordinate parametrisations) and an inner product
space `E₂` (target — the ambient space of an immersion), the *induced bilinear form*
on `E₁` at a point `x ∈ E₁` is

  `g_x(v, w) := ⟨dF_x v, dF_x w⟩_{E₂}`.

When `F` is an immersion at `x` (i.e., `dF_x` is injective), `g_x` is positive
definite, hence a Riemannian metric pulled back from the ambient inner product.
The Gram matrix `g_ij(x) := g_x(eᵢ, eⱼ) = ⟨∂F/∂xⁱ(x), ∂F/∂xʲ(x)⟩` is what classical
references call *the induced metric in coordinates* (see e.g. Schnürer §2 or the
"Geometry of Hypersurfaces" appendix).

Integrating against `√(det gᵢⱼ) dx` yields the surface measure on `F(M)`; this is
the connection to volume elements and ultimately to the first variation formula
that powers Huisken's monotonicity.

This file develops the definition and basic properties for general inner product
source/target. A specialisation to graphs `F(x) = (x, f(x))` lives in
`CoordinateHypersurface.lean`.

These declarations are designed to migrate cleanly to mathlib once the API
stabilises (target name something like `Mathlib.Analysis.InnerProductSpace.Pullback`).
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace HuiskenMonotonicity

variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
variable {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/-- The induced (pullback) bilinear form on `E₁` from a map `F : E₁ → E₂`,
evaluated at a point `x` on tangent vectors `v, w`:

  `g_x(v, w) = ⟨dF_x v, dF_x w⟩_{E₂}`.

When `F` is differentiable at `x` and an immersion (i.e. `fderiv ℝ F x` is
injective), `g_x` is a Riemannian metric pulled back from the ambient inner
product on `E₂`. -/
noncomputable def inducedMetric
    (F : E₁ → E₂) (x : E₁) (v w : E₁) : ℝ :=
  @inner ℝ E₂ _ (fderiv ℝ F x v) (fderiv ℝ F x w)

/-- The Gram matrix entries of the induced metric in a chosen basis.
For the standard basis of `EuclideanSpace ℝ (Fin n)` this gives the classical
formula `g_ij(x) = ⟨∂F/∂xⁱ(x), ∂F/∂xʲ(x)⟩`. -/
noncomputable def inducedMetricMatrix {ι : Type*}
    (F : E₁ → E₂) (x : E₁) (b : ι → E₁) (i j : ι) : ℝ :=
  inducedMetric F x (b i) (b j)

namespace inducedMetric

/-! ## Basic algebraic properties

Pure consequences of the inner product on `E₂` and the linearity of `fderiv ℝ F x`. -/

variable (F : E₁ → E₂) (x : E₁)

@[simp] lemma zero_left (w : E₁) : inducedMetric F x 0 w = 0 := by
  simp [inducedMetric]

@[simp] lemma zero_right (v : E₁) : inducedMetric F x v 0 = 0 := by
  simp [inducedMetric]

lemma symm (v w : E₁) : inducedMetric F x v w = inducedMetric F x w v := by
  rw [inducedMetric, inducedMetric, real_inner_comm]

lemma add_left (u v w : E₁) :
    inducedMetric F x (u + v) w =
      inducedMetric F x u w + inducedMetric F x v w := by
  rw [inducedMetric, inducedMetric, inducedMetric,
      (fderiv ℝ F x).map_add, inner_add_left]

lemma add_right (u v w : E₁) :
    inducedMetric F x u (v + w) =
      inducedMetric F x u v + inducedMetric F x u w := by
  rw [symm, add_left, symm F x v u, symm F x w u]

lemma smul_left (c : ℝ) (v w : E₁) :
    inducedMetric F x (c • v) w = c * inducedMetric F x v w := by
  rw [inducedMetric, inducedMetric, (fderiv ℝ F x).map_smul, real_inner_smul_left]

lemma smul_right (c : ℝ) (v w : E₁) :
    inducedMetric F x v (c • w) = c * inducedMetric F x v w := by
  rw [symm, smul_left, symm F x w v]

/-! ## Positive definiteness -/

lemma self_nonneg (v : E₁) : 0 ≤ inducedMetric F x v v :=
  real_inner_self_nonneg

/-- The induced metric of a vector with itself is the squared norm of its image. -/
lemma self_eq_norm_sq (v : E₁) :
    inducedMetric F x v v = ‖fderiv ℝ F x v‖ ^ 2 := by
  rw [inducedMetric, real_inner_self_eq_norm_sq]

/-- For an immersion (injective differential), `g_x(v, v) = 0` only when `v = 0`. -/
lemma self_eq_zero_iff_of_injective
    (hInj : Function.Injective (fderiv ℝ F x)) (v : E₁) :
    inducedMetric F x v v = 0 ↔ v = 0 := by
  rw [inducedMetric, inner_self_eq_zero]
  exact ⟨fun h => hInj (h.trans (map_zero _).symm), fun h => h ▸ map_zero _⟩

/-- At an immersion point, the induced metric is positive definite. -/
lemma self_pos_of_injective
    (hInj : Function.Injective (fderiv ℝ F x)) {v : E₁} (hv : v ≠ 0) :
    0 < inducedMetric F x v v :=
  (self_nonneg F x v).lt_of_ne fun h =>
    hv ((self_eq_zero_iff_of_injective F x hInj v).mp h.symm)

end inducedMetric

namespace inducedMetricMatrix

/-! ## Properties of the Gram-matrix form -/

variable {ι : Type*} (F : E₁ → E₂) (x : E₁) (b : ι → E₁)

lemma symm (i j : ι) :
    inducedMetricMatrix F x b i j = inducedMetricMatrix F x b j i :=
  inducedMetric.symm F x (b i) (b j)

lemma diagonal_nonneg (i : ι) : 0 ≤ inducedMetricMatrix F x b i i :=
  inducedMetric.self_nonneg F x (b i)

end inducedMetricMatrix

end HuiskenMonotonicity
