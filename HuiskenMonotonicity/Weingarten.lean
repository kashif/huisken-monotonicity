/-
**The Weingarten equation, orientation-free.**

In oriented coordinates the Weingarten equation reads

  `ν^α_{;i} = h^k_i X^α_{;k}`

(Schnürer, *Lectures on mean curvature flow without singularities*, eq. (2.3)), which
presupposes a choice of unit normal `ν` and the shape operator `h^k_i`. To keep orientation
out of the development, this file proves the equivalent statement in the form that needs no
normal field:

  `⟪D_v ξ, D_w F⟫ = -⟪ξ, D²F(v, w)⟫`     for `ξ` normal along `F`.

Read as adjointness, the tangential part of the derivative of a normal field is the
negative of the second fundamental form paired against that field. Taking `ξ = ν` and
contracting recovers the coordinate form; contracting against the inverse metric instead
gives the pointwise identity `div_M(X^⊥) = -⟪X, Hvec⟫` behind the first variation formula.

The ambient space here is a Euclidean inner product space, so the ambient connection is the
ordinary Fréchet derivative and no connection machinery is needed.

The proof is one differentiation: `⟪ξ, D_w F⟫` vanishes identically because `ξ` is normal,
so its derivative in the direction `v` vanishes, and the product rule for the inner product
splits that derivative into the two terms of the claim.
-/

import HuiskenMonotonicity.SecondFundamentalForm
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace HuiskenMonotonicity

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A field `ξ : E₁ → E` is *normal along* `F` when it is orthogonal to every tangent
vector `dF_y(v)`, at every point `y`.

This is the orientation-free replacement for "`ξ` is a multiple of the unit normal": in
codimension one it says exactly that, but it needs no choice of sign and makes sense in any
codimension. -/
def IsNormalAlong (F ξ : E₁ → E) : Prop :=
  ∀ y : E₁, ∀ v : E₁, @inner ℝ E _ (ξ y) (fderiv ℝ F y v) = 0

/-- **The Weingarten equation, orientation-free form.**

For `ξ` normal along `F`,

  `⟪dξ_x(v), dF_x(w)⟫ = -⟪ξ x, D²F_x(v, w)⟫`.

Equivalent to the coordinate Weingarten equation but with no unit normal and no shape
operator, so it holds in any codimension and on non-orientable submanifolds. -/
theorem inner_fderiv_eq_neg_inner_secondDerivative
    {F ξ : E₁ → E} (hF : ContDiff ℝ 2 F) (hξ : Differentiable ℝ ξ)
    (hnormal : IsNormalAlong F ξ) (x : E₁) (v w : E₁) :
    @inner ℝ E _ (fderiv ℝ ξ x v) (fderiv ℝ F x w) =
      -@inner ℝ E _ (ξ x) (secondDerivative F x v w) := by
  -- `fderiv ℝ F` is itself differentiable, so `y ↦ dF_y(w)` has a derivative at `x`.
  have hFd : ContDiff ℝ 1 (fderiv ℝ F) := (contDiff_succ_iff_fderiv.mp hF).2.2
  have hFd' : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    (hFd.differentiable (by norm_num) x).hasFDerivAt
  have hG : HasFDerivAt (fun y => fderiv ℝ F y w)
      ((fderiv ℝ (fderiv ℝ F) x).flip w) x := by
    simpa using hFd'.clm_apply (hasFDerivAt_const w x)
  have hξd : HasFDerivAt ξ (fderiv ℝ ξ x) x := (hξ x).hasFDerivAt
  -- The scalar function `y ↦ ⟪ξ y, dF_y(w)⟫` is identically zero.
  have hzero : (fun y => @inner ℝ E _ (ξ y) (fderiv ℝ F y w)) = fun _ => (0 : ℝ) := by
    funext y
    exact hnormal y w
  -- Its derivative therefore vanishes; the product rule gives the two terms.
  have hprod := hξd.inner (𝕜 := ℝ) hG
  have hconstd : HasFDerivAt (fun y => @inner ℝ E _ (ξ y) (fderiv ℝ F y w))
      (0 : E₁ →L[ℝ] ℝ) x := by
    rw [hzero]
    exact hasFDerivAt_const _ _
  have hderiv_eq := hprod.unique hconstd
  -- Evaluate the equality of derivatives at `v`.
  have happ := congrArg (fun L : E₁ →L[ℝ] ℝ => L v) hderiv_eq
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply] at happ
  -- `happ : ⟪ξ x, D²F(v, w)⟫ + ⟪dξ(v), dF(w)⟫ = 0`.
  have hsd : secondDerivative F x v w = fderiv ℝ (fderiv ℝ F) x v w := by
    unfold secondDerivative
    rw [iteratedFDeriv_two_apply]
    rfl
  rw [hsd]
  linarith [happ]

/-- Specialisation to a chosen unit normal: this is the coordinate Weingarten equation
paired against a tangent vector, and exhibits `secondFundamentalForm` as the object the
Weingarten equation produces. -/
theorem inner_fderiv_eq_secondFundamentalForm
    {F ν : E₁ → E} (hF : ContDiff ℝ 2 F) (hν : Differentiable ℝ ν)
    (hnormal : IsNormalAlong F ν) (x : E₁) (v w : E₁) :
    @inner ℝ E _ (fderiv ℝ ν x v) (fderiv ℝ F x w) =
      secondFundamentalForm F ν x v w := by
  rw [inner_fderiv_eq_neg_inner_secondDerivative hF hν hnormal x v w,
    secondFundamentalForm, real_inner_comm]

end HuiskenMonotonicity
