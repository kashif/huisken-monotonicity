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
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

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

/-! ## Induced Gram matrix in the standard basis

The classical formula `g_ij(x) = ⟨∂F/∂x^i(x), ∂F/∂x^j(x)⟩` of background.latex
(eq. 1.12 for graphs) packaged as a mathlib `Matrix (Fin n) (Fin n) ℝ`. This
specialisation of `inducedMetricMatrix` to the standard basis of
`EuclideanSpace ℝ (Fin n)` lets us hook into the mathlib matrix API
(symmetry, determinant, eigenvalues, …) for the metric.

The same matrix-shaped layout will be used for the second fundamental form
in a follow-up module. -/

/-- The Gram matrix of the induced metric in the standard basis of
`EuclideanSpace ℝ (Fin n)`:
  `(inducedGramMatrix F x) i j = ⟨∂F/∂x^i(x), ∂F/∂x^j(x)⟩`. -/
noncomputable def inducedGramMatrix {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    inducedMetricMatrix F x (fun k => EuclideanSpace.single k 1) i j

lemma inducedGramMatrix_apply {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    inducedGramMatrix F x i j =
      inducedMetric F x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
  rfl

/-- The Gram matrix is symmetric: `g_ij = g_ji`. -/
lemma inducedGramMatrix_isSymm {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) :
    (inducedGramMatrix F x).IsSymm :=
  Matrix.IsSymm.ext fun i j =>
    inducedMetricMatrix.symm F x (fun k => EuclideanSpace.single k 1) j i

/-- Diagonal entries of the Gram matrix are non-negative:
`g_ii = ‖∂F/∂x^i‖² ≥ 0`. -/
lemma inducedGramMatrix_diagonal_nonneg {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    0 ≤ inducedGramMatrix F x i i :=
  inducedMetricMatrix.diagonal_nonneg F x (fun k => EuclideanSpace.single k 1) i

/-- The induced Gram matrix is the mathlib `Matrix.gram` of the partial-derivative
vectors `(∂F/∂x^i)_i`. This makes the mathlib Gram-matrix API (PSD, PosDef under
linear independence, etc.) available for `inducedGramMatrix`. -/
lemma inducedGramMatrix_eq_gram {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) :
    inducedGramMatrix F x =
      Matrix.gram ℝ (fun i : Fin n => fderiv ℝ F x (EuclideanSpace.single i 1)) := by
  ext i j
  rfl

/-- The induced Gram matrix is positive semi-definite. -/
lemma inducedGramMatrix_posSemidef {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) :
    (inducedGramMatrix F x).PosSemidef := by
  rw [inducedGramMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℝ _

/-- The Gram-matrix determinant is non-negative. -/
lemma inducedGramMatrix_det_nonneg {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ (inducedGramMatrix F x).det :=
  (inducedGramMatrix_posSemidef F x).det_nonneg

/-! ## Volume element

The classical volume element of an immersion `F : ℝⁿ → E` at a point `x` is
  `√(det g_ij(x))`,
the Riemannian volume form pulled back through `F`. Integrating against this
density on `ℝⁿ` yields the surface measure on the image; in the graph case
`F(x) = (x, f(x))` it reduces to `√(1 + ‖∇f‖²) dx`. -/

/-- The induced volume element of `F : ℝⁿ → E` at `x`, defined as the square
root of the determinant of the induced Gram matrix:
  `dμ_F(x) = √(det g_ij(x)) dx`.
For non-immersion points the determinant can vanish, so the volume element is
just non-negative in general. Positivity at immersion points (when
`fderiv ℝ F x` is injective) is a follow-up. -/
noncomputable def inducedVolumeElement {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (inducedGramMatrix F x).det

@[simp] lemma inducedVolumeElement_nonneg {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ inducedVolumeElement F x :=
  Real.sqrt_nonneg _

/-- The squared volume element equals the Gram determinant. -/
lemma inducedVolumeElement_sq {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) :
    inducedVolumeElement F x ^ 2 = (inducedGramMatrix F x).det :=
  Real.sq_sqrt (inducedGramMatrix_det_nonneg F x)

/-! ## Positivity at immersion points

When `F` is an immersion at `x` (i.e. `fderiv ℝ F x` is injective), the
partial-derivative vectors `(∂F/∂x^i)_i` are linearly independent. This
upgrades the Gram matrix from positive semi-definite to positive definite,
hence its determinant and volume element are strictly positive. -/

/-- The partial-derivative vectors of an immersion are linearly independent. -/
lemma linearIndependent_fderiv_single_of_injective {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n))
    (hInj : Function.Injective (fderiv ℝ F x)) :
    LinearIndependent ℝ
      (fun i : Fin n => fderiv ℝ F x (EuclideanSpace.single i 1)) := by
  -- Standard basis of `EuclideanSpace ℝ (Fin n)` is linearly independent;
  -- inject through the linear map `fderiv ℝ F x`.
  have h_basis : LinearIndependent ℝ
      (fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) := by
    have h := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
    convert h using 1
    funext i
    simp
  have h_ker : LinearMap.ker (fderiv ℝ F x).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr hInj
  exact h_basis.map' (fderiv ℝ F x).toLinearMap h_ker

/-- At an immersion point, the induced Gram matrix is positive definite. -/
lemma inducedGramMatrix_posDef_of_injective {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n))
    (hInj : Function.Injective (fderiv ℝ F x)) :
    (inducedGramMatrix F x).PosDef := by
  rw [inducedGramMatrix_eq_gram]
  exact Matrix.posDef_gram_of_linearIndependent
    (linearIndependent_fderiv_single_of_injective F x hInj)

/-- At an immersion point, `det g_ij > 0`. -/
lemma inducedGramMatrix_det_pos_of_injective {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n))
    (hInj : Function.Injective (fderiv ℝ F x)) :
    0 < (inducedGramMatrix F x).det :=
  (inducedGramMatrix_posDef_of_injective F x hInj).det_pos

/-- At an immersion point, the volume element is strictly positive. -/
lemma inducedVolumeElement_pos_of_injective {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n))
    (hInj : Function.Injective (fderiv ℝ F x)) :
    0 < inducedVolumeElement F x :=
  Real.sqrt_pos.mpr (inducedGramMatrix_det_pos_of_injective F x hInj)

/-! ## Inverse metric `g^{ij}`

The inverse of the induced Gram matrix; well-defined as soon as `F` is an
immersion at `x`. Used to raise indices on covariant tensors and to take
metric traces (e.g. `H = g^ij h_ij` for the mean curvature scalar). -/

/-- The inverse induced metric matrix `g^{ij}(x)`, i.e. the matrix inverse of
the induced Gram matrix. Well-defined (and the actual inverse) at immersion
points; off-immersion the value defaults to zero (mathlib convention for
`Matrix.inv` on non-invertible matrices). -/
noncomputable def inducedInverseMetricMatrix {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  (inducedGramMatrix F x)⁻¹

/-- At an immersion point, `g^{ij}` is the (left) inverse of `g_ij`. -/
lemma inducedInverseMetricMatrix_mul_inducedGramMatrix_of_injective {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n))
    (hInj : Function.Injective (fderiv ℝ F x)) :
    inducedInverseMetricMatrix F x * inducedGramMatrix F x = 1 := by
  unfold inducedInverseMetricMatrix
  exact Matrix.nonsing_inv_mul _ <|
    isUnit_iff_ne_zero.mpr (inducedGramMatrix_det_pos_of_injective F x hInj).ne'

/-- At an immersion point, `g^{ij}` is the (right) inverse of `g_ij`. -/
lemma inducedGramMatrix_mul_inducedInverseMetricMatrix_of_injective {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n))
    (hInj : Function.Injective (fderiv ℝ F x)) :
    inducedGramMatrix F x * inducedInverseMetricMatrix F x = 1 := by
  unfold inducedInverseMetricMatrix
  exact Matrix.mul_nonsing_inv _ <|
    isUnit_iff_ne_zero.mpr (inducedGramMatrix_det_pos_of_injective F x hInj).ne'

/-- The inverse metric matrix is symmetric. -/
lemma inducedInverseMetricMatrix_isSymm {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E₂) (x : EuclideanSpace ℝ (Fin n)) :
    (inducedInverseMetricMatrix F x).IsSymm := by
  unfold inducedInverseMetricMatrix Matrix.IsSymm
  rw [Matrix.transpose_nonsing_inv, (inducedGramMatrix_isSymm F x).eq]

end HuiskenMonotonicity
