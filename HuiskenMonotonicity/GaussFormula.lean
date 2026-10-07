/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.TangentialCalculus

/-!
# The Gauss formula, in coordinates

For an immersion into a Euclidean space the tangential part of the second derivative is
governed by the Christoffel symbols of the induced metric; the normal part is the second
fundamental form (Schnürer, *Lectures on mean curvature flow without singularities*,
eq. (2.2), `X_{;ij} = -h_{ij} ν`, where the covariant second derivative `X_{;ij}` is
`∂_i∂_j X - Γ^k_{ij} ∂_k X`). In the form needed here this is
the **Koszul identity for the pullback metric**: with `g_{jk} = ⟪∂_j F, ∂_k F⟫`,

  `⟪D²F(∂_i, ∂_j), ∂_k F⟫ = ½ (∂_i g_{jk} + ∂_j g_{ik} - ∂_k g_{ij})`.

The right-hand side is the Christoffel symbol of the first kind of the induced metric, so
the identity says that the tangential component of `D²F(∂_i, ∂_j)` is `Γ^l_{ij} ∂_l F`.
That is the Gauss formula, and it is what identifies the extrinsic divergence of a
tangential field with the intrinsic divergence of the corresponding vector field.

The proof needs no connection: differentiate `g_{jk} = ⟪∂_j F, ∂_k F⟫` by the product rule,
form the Koszul combination, and cancel using symmetry of the second derivative.
-/

namespace HuiskenMonotonicity

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The second derivative as an iterated Fréchet derivative. -/
lemma secondDerivative_eq_fderiv_fderiv (F : E₁ → E) (x v w : E₁) :
    secondDerivative F x v w = fderiv ℝ (fderiv ℝ F) x v w := by
  unfold secondDerivative
  rw [iteratedFDeriv_two_apply]
  rfl

/-- A tangent vector `y ↦ dF_y(w)` has derivative `v ↦ D²F(v, w)`. -/
theorem hasFDerivAt_fderiv_apply {F : E₁ → E} (hF : ContDiff ℝ 2 F) (x w : E₁) :
    HasFDerivAt (fun y => fderiv ℝ F y w) ((fderiv ℝ (fderiv ℝ F) x).flip w) x := by
  have hFd : ContDiff ℝ 1 (fderiv ℝ F) := (contDiff_succ_iff_fderiv.mp hF).2.2
  have hFd' : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    (hFd.differentiable (by norm_num) x).hasFDerivAt
  simpa using hFd'.clm_apply (hasFDerivAt_const w x)

/-- **The derivative of a Gram entry**, by the product rule:

  `∂_v g_{jk} = ⟪D²F(v, ∂_j), ∂_k F⟫ + ⟪∂_j F, D²F(v, ∂_k)⟫`. -/
theorem fderiv_frameGram {F : E₁ → E} (hF : ContDiff ℝ 2 F) (b : Idx → E₁)
    (x v : E₁) (j k : Idx) :
    fderiv ℝ (fun y => frameGram F b y j k) x v =
      @inner ℝ E _ (secondDerivative F x v (b j)) (frameTangent F b x k) +
        @inner ℝ E _ (frameTangent F b x j) (secondDerivative F x v (b k)) := by
  have hprod := (hasFDerivAt_fderiv_apply hF x (b j)).inner (𝕜 := ℝ)
    (hasFDerivAt_fderiv_apply hF x (b k))
  have hfun : (fun y => frameGram F b y j k) =
      fun y => @inner ℝ E _ (fderiv ℝ F y (b j)) (fderiv ℝ F y (b k)) := rfl
  rw [hfun, hprod.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, ContinuousLinearMap.flip_apply,
    frameTangent_apply, secondDerivative_eq_fderiv_fderiv]
  ring

/-- **The Koszul identity for the pullback metric.**

  `⟪D²F(∂_i, ∂_j), ∂_k F⟫ = ½ (∂_i g_{jk} + ∂_j g_{ik} - ∂_k g_{ij})`.

The right-hand side is the Christoffel symbol of the first kind of the induced metric, so
this is the Gauss formula in coordinates. -/
theorem inner_secondDerivative_frameTangent_eq_koszul {F : E₁ → E} (hF : ContDiff ℝ 2 F)
    (b : Idx → E₁) (x : E₁) (i j k : Idx) :
    @inner ℝ E _ (secondDerivative F x (b i) (b j)) (frameTangent F b x k) =
      (fderiv ℝ (fun y => frameGram F b y j k) x (b i) +
        fderiv ℝ (fun y => frameGram F b y i k) x (b j) -
        fderiv ℝ (fun y => frameGram F b y i j) x (b k)) / 2 := by
  rw [fderiv_frameGram hF, fderiv_frameGram hF, fderiv_frameGram hF]
  -- name the three distinct second-derivative pairings
  have s1 := secondDerivative_symm hF x (b j) (b i)
  have s2 := secondDerivative_symm hF x (b k) (b i)
  have s3 := secondDerivative_symm hF x (b k) (b j)
  rw [s1, s2, s3, real_inner_comm (frameTangent F b x j) (secondDerivative F x (b i) (b k))]
  ring

end HuiskenMonotonicity
