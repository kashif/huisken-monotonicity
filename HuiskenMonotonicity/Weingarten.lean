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

/-- The second derivative as an iterated Fréchet derivative. -/
lemma secondDerivative_eq_fderiv_fderiv (F : E₁ → E) (x v w : E₁) :
    secondDerivative F x v w = fderiv ℝ (fderiv ℝ F) x v w := by
  unfold secondDerivative
  rw [iteratedFDeriv_two_apply]
  rfl

/-- Symmetry of the second derivative at a point where the map is `C²`. Only local
smoothness is needed, which matters because a chart representation is smooth on the chart
target and nowhere else. -/
lemma secondDerivative_symm_of_contDiffAt {F : E₁ → E} {x : E₁} (hF : ContDiffAt ℝ 2 F x)
    (v w : E₁) : secondDerivative F x v w = secondDerivative F x w v := by
  rw [secondDerivative_eq_fderiv_fderiv, secondDerivative_eq_fderiv_fderiv]
  exact hF.isSymmSndFDerivAt (by simp) v w

/-- A tangent vector `y ↦ dF_y(w)` has derivative `v ↦ D²F(v, w)`. -/
theorem hasFDerivAt_fderiv_apply {F : E₁ → E} {x : E₁} (hF : ContDiffAt ℝ 2 F x) (w : E₁) :
    HasFDerivAt (fun y => fderiv ℝ F y w) ((fderiv ℝ (fderiv ℝ F) x).flip w) x := by
  have hFd : ContDiffAt ℝ 1 (fderiv ℝ F) x := hF.fderiv_right (by norm_num)
  have hFd' : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    (hFd.differentiableAt (by norm_num)).hasFDerivAt
  simpa using hFd'.clm_apply (hasFDerivAt_const w x)

/-- A field `ξ : E₁ → E` is *normal along* `F` near `x` when, at every point of a neighbourhood
of `x`, it is orthogonal to every tangent vector `dF_y(v)`.

This is the orientation-free replacement for "`ξ` is a multiple of the unit normal": in
codimension one it says exactly that, but it needs no choice of sign and makes sense in any
codimension. It is local because the maps it is applied to, chart representations, are only
defined, and normal, on a chart. -/
def IsNormalAlongNear (F ξ : E₁ → E) (x : E₁) : Prop :=
  ∀ᶠ y in nhds x, ∀ v : E₁, @inner ℝ E _ (ξ y) (fderiv ℝ F y v) = 0

/-- **The Weingarten equation, orientation-free form.**

For `ξ` normal along `F` near `x`,

  `⟪dξ_x(v), dF_x(w)⟫ = -⟪ξ x, D²F_x(v, w)⟫`.

Equivalent to the coordinate Weingarten equation (Schnürer, *Lectures on mean curvature flow
without singularities*, eq. (2.3)) but with no unit normal and no shape operator, so it holds
in any codimension and on non-orientable submanifolds.

The proof is one differentiation: `⟪ξ, dF w⟫` vanishes near `x` because `ξ` is normal, so its
derivative at `x` vanishes, and the product rule splits that derivative into the two terms. -/
theorem inner_fderiv_eq_neg_inner_secondDerivative
    {F ξ : E₁ → E} {x : E₁} (hF : ContDiffAt ℝ 2 F x) (hξ : DifferentiableAt ℝ ξ x)
    (hnormal : IsNormalAlongNear F ξ x) (v w : E₁) :
    @inner ℝ E _ (fderiv ℝ ξ x v) (fderiv ℝ F x w) =
      -@inner ℝ E _ (ξ x) (secondDerivative F x v w) := by
  have hprod := hξ.hasFDerivAt.inner (𝕜 := ℝ) (hasFDerivAt_fderiv_apply hF w)
  have hzero : (fun y => @inner ℝ E _ (ξ y) (fderiv ℝ F y w)) =ᶠ[nhds x]
      fun _ => (0 : ℝ) := by
    filter_upwards [hnormal] with y hy
    exact hy w
  have hconstd : HasFDerivAt (fun y => @inner ℝ E _ (ξ y) (fderiv ℝ F y w))
      (0 : E₁ →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq hzero
  have happ := congrArg (fun L : E₁ →L[ℝ] ℝ => L v) (hprod.unique hconstd)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply] at happ
  rw [secondDerivative_eq_fderiv_fderiv]
  linarith [happ]

/-- Specialisation to a chosen unit normal: this is the coordinate Weingarten equation
paired against a tangent vector, and exhibits `secondFundamentalForm` as the object the
Weingarten equation produces. -/
theorem inner_fderiv_eq_secondFundamentalForm
    {F ν : E₁ → E} {x : E₁} (hF : ContDiffAt ℝ 2 F x) (hν : DifferentiableAt ℝ ν x)
    (hnormal : IsNormalAlongNear F ν x) (v w : E₁) :
    @inner ℝ E _ (fderiv ℝ ν x v) (fderiv ℝ F x w) =
      secondFundamentalForm F ν x v w := by
  rw [inner_fderiv_eq_neg_inner_secondDerivative hF hν hnormal v w,
    secondFundamentalForm, real_inner_comm]

end HuiskenMonotonicity
