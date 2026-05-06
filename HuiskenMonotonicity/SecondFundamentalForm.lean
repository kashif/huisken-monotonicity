/-
**Second fundamental form of an immersion.**

For a smooth immersion `F : E₁ → E` between inner product spaces, equipped with a
chosen unit normal field `ν : E₁ → E` (codimension-1 setting), the *second
fundamental form* at `x ∈ E₁` is the bilinear form on `E₁` given by

  `h_x(v, w) := -⟨D²F_x(v, w),\, ν(x)⟩_E`.

In coordinates `g_ij = ⟨∂F/∂x^i, ∂F/∂x^j⟩` (the induced metric), the matrix
entries are `h_ij(x) = -⟨∂²F/∂x^i∂x^j(x),\, ν(x)⟩` (Schnürer Lemma 2.1, the
"lower-normal" sign convention; cf. Huisken §1, background.latex eq. 1.13).

Symmetry (`h_ij = h_ji`) follows from Schwarz's theorem applied to `D²F`.

Designed to migrate cleanly to mathlib once the abstract second fundamental form
lands; in the meantime, parallels `InducedMetric.lean` in shape and naming.
-/

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace HuiskenMonotonicity

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The (vector-valued) Hessian `D²F_x(v, w) ∈ E` of a smooth map `F : E₁ → E`,
extracted from the iterated Fréchet derivative. Symmetric in `v, w` for
`ContDiff ℝ 2 F` (`secondDerivative_symm`). -/
noncomputable def secondDerivative
    (F : E₁ → E) (x : E₁) (v w : E₁) : E :=
  iteratedFDeriv ℝ 2 F x ![v, w]

/-- Schwarz: `D²F_x(v, w) = D²F_x(w, v)` for `ContDiff ℝ 2` functions. -/
lemma secondDerivative_symm
    {F : E₁ → E} (hF : ContDiff ℝ 2 F) (x : E₁) (v w : E₁) :
    secondDerivative F x v w = secondDerivative F x w v := by
  -- Extract `HasFDerivAt`s for `F` (everywhere) and for `fderiv F` (at `x`).
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have h_diff : ∀ y, HasFDerivAt F (fderiv ℝ F y) y :=
    fun y => (hF1 y).hasFDerivAt
  have hF2 : ContDiff ℝ 1 (fderiv ℝ F) := (contDiff_succ_iff_fderiv.mp hF).2.2
  have h_diff' : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    (hF2.differentiable (by norm_num) x).hasFDerivAt
  -- Convert `iteratedFDeriv 2` to `fderiv (fderiv f) v w`, apply Schwarz.
  unfold secondDerivative
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  exact second_derivative_symmetric h_diff h_diff' v w

/-- The second fundamental form of an immersion `F : E₁ → E` with chosen unit
normal `ν : E₁ → E`, evaluated at `x` on tangent vectors `v, w`:

  `h_x(v, w) = -⟨D²F_x(v, w),\, ν(x)⟩`.

The minus sign matches the "lower-normal" convention of Schnürer §2 / Huisken §1
(background.latex eq. 1.13). For codimension-1 immersions there is a global
choice of `ν` up to sign (orientation); the choice is supplied externally. -/
noncomputable def secondFundamentalForm
    (F : E₁ → E) (ν : E₁ → E) (x : E₁) (v w : E₁) : ℝ :=
  -@inner ℝ E _ (secondDerivative F x v w) (ν x)

/-- Symmetry of the second fundamental form: `h_x(v, w) = h_x(w, v)`. -/
lemma secondFundamentalForm_symm
    {F : E₁ → E} (ν : E₁ → E) (hF : ContDiff ℝ 2 F) (x : E₁) (v w : E₁) :
    secondFundamentalForm F ν x v w = secondFundamentalForm F ν x w v := by
  unfold secondFundamentalForm
  rw [secondDerivative_symm hF x v w]

/-! ## Coordinate matrix on `EuclideanSpace ℝ (Fin n)` -/

/-- Matrix entries of the second fundamental form in the standard basis of
`EuclideanSpace ℝ (Fin n)`:
  `(secondFundamentalFormMatrix F ν x) i j = -⟨∂²F/∂x^i∂x^j(x), ν(x)⟩`. -/
noncomputable def secondFundamentalFormMatrix {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → E) (ν : EuclideanSpace ℝ (Fin n) → E)
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    secondFundamentalForm F ν x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- Symmetry of the second-fundamental-form matrix: `h_ij = h_ji`. -/
lemma secondFundamentalFormMatrix_isSymm {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → E} (ν : EuclideanSpace ℝ (Fin n) → E)
    (hF : ContDiff ℝ 2 F) (x : EuclideanSpace ℝ (Fin n)) :
    (secondFundamentalFormMatrix F ν x).IsSymm :=
  Matrix.IsSymm.ext fun i j =>
    (secondFundamentalForm_symm ν hF x
      (EuclideanSpace.single j 1) (EuclideanSpace.single i 1))

end HuiskenMonotonicity
