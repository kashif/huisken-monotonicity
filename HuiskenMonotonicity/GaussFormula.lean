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

/-- The Gram matrix is symmetric as a function, so its directional derivatives are too. -/
lemma fderiv_frameGram_comm (F : E₁ → E) (b : Idx → E₁) (x v : E₁) (j k : Idx) :
    fderiv ℝ (fun y => frameGram F b y j k) x v =
      fderiv ℝ (fun y => frameGram F b y k j) x v := by
  have h : (fun y => frameGram F b y j k) = fun y => frameGram F b y k j :=
    funext fun y => frameGram_symm F b y j k
  rw [h]

/-- **The contracted Christoffel symbol.**

  `g^{ij} ⟪D²F(∂_i, ∂_k), ∂_j F⟫ = ½ g^{ij} ∂_k g_{ij}`.

That is `Γ^i_{ik} = ½ g^{ij} ∂_k g_{ij}`, the quantity that turns the extrinsic divergence of
a tangential field into the Voss-Weyl divergence `(1/√g) ∂_i(√g Z^i)`, once Jacobi's formula
identifies it with `∂_k log √det g`. Of the three Koszul terms, the two that differentiate in
the summed directions cancel against each other under the symmetric inverse metric. -/
theorem sum_inner_secondDerivative_frameTangent_eq_half_trace {F : E₁ → E}
    (hF : ContDiff ℝ 2 F) (b : Idx → E₁) (gInv : Idx → Idx → ℝ)
    (hsymm : ∀ i j, gInv i j = gInv j i) (x : E₁) (k : Idx) :
    ∑ i, ∑ j, gInv i j *
        @inner ℝ E _ (secondDerivative F x (b i) (b k)) (frameTangent F b x j) =
      (∑ i, ∑ j, gInv i j * fderiv ℝ (fun y => frameGram F b y i j) x (b k)) / 2 := by
  -- the two Koszul terms differentiating in a summed direction coincide
  have hcancel :
      ∑ i, ∑ j, gInv i j * fderiv ℝ (fun y => frameGram F b y k j) x (b i) =
        ∑ i, ∑ j, gInv i j * fderiv ℝ (fun y => frameGram F b y i k) x (b j) := by
    rw [Finset.sum_comm (f := fun i j => gInv i j * fderiv ℝ (fun y => frameGram F b y i k) x (b j))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm j i, fderiv_frameGram_comm F b x (b i) j k]
  have hterm : ∀ i j, gInv i j *
        @inner ℝ E _ (secondDerivative F x (b i) (b k)) (frameTangent F b x j) =
      (gInv i j * fderiv ℝ (fun y => frameGram F b y k j) x (b i) +
        gInv i j * fderiv ℝ (fun y => frameGram F b y i j) x (b k) -
        gInv i j * fderiv ℝ (fun y => frameGram F b y i k) x (b j)) / 2 := by
    intro i j
    rw [inner_secondDerivative_frameTangent_eq_koszul hF b x i k j]
    ring
  simp only [hterm, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hcancel]
  ring

/-! ## The divergence of a tangential field -/

/-- The tangential field with coefficients `Z^k` in the frame: `ξ = ∑ k, Z^k ∂_k F`. -/
noncomputable def tangentField (F : E₁ → E) (b : Idx → E₁) (Z : Idx → E₁ → ℝ) (y : E₁) : E :=
  ∑ k, Z k y • frameTangent F b y k

/-- The derivative of a tangential field, by the product rule:

  `∂_v ξ = ∑ k, (∂_v Z^k) ∂_k F + Z^k D²F(v, ∂_k)`. -/
theorem fderiv_tangentField {F : E₁ → E} (hF : ContDiff ℝ 2 F) (b : Idx → E₁)
    {Z : Idx → E₁ → ℝ} {x : E₁} (hZ : ∀ k, DifferentiableAt ℝ (Z k) x) (v : E₁) :
    fderiv ℝ (tangentField F b Z) x v =
      ∑ k, (fderiv ℝ (Z k) x v • frameTangent F b x k +
        Z k x • secondDerivative F x v (b k)) := by
  have hk : ∀ k ∈ (Finset.univ : Finset Idx),
      HasFDerivAt (fun y => Z k y • fderiv ℝ F y (b k))
        (Z k x • (fderiv ℝ (fderiv ℝ F) x).flip (b k) +
          (fderiv ℝ (Z k) x).smulRight (fderiv ℝ F x (b k))) x :=
    fun k _ => (hZ k).hasFDerivAt.smul (hasFDerivAt_fderiv_apply hF x (b k))
  have hsum := HasFDerivAt.fun_sum hk
  have hfun : tangentField F b Z = fun y => ∑ k, Z k y • fderiv ℝ F y (b k) := rfl
  rw [hfun, hsum.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smulRight_apply, frameTangent_apply, secondDerivative_eq_fderiv_fderiv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_comm]

/-- **The divergence of a tangential field, in coordinates.**

  `div_M (∑ k, Z^k ∂_k F) = ∑ i, ∂_i Z^i + ∑ k, Z^k · ½ g^{ij} ∂_k g_{ij}`.

With Jacobi's formula `½ g^{ij} ∂_k g_{ij} = ∂_k log √det g` the right-hand side is the
Voss-Weyl divergence `(1/√g) ∂_i(√g Z^i)`, which is the intrinsic divergence of the vector
field `Z`. So this is the statement that the extrinsic divergence of a tangential field equals
the intrinsic divergence of the field it pushes forward. -/
theorem tangentialDivergence_tangentField {F : E₁ → E} (hF : ContDiff ℝ 2 F)
    (b : Idx → E₁) {gInv : Idx → Idx → ℝ} {x : E₁}
    (hinv : IsFrameInverse F b x gInv) (hsymm : ∀ i j, gInv i j = gInv j i)
    {Z : Idx → E₁ → ℝ} (hZ : ∀ k, DifferentiableAt ℝ (Z k) x) :
    tangentialDivergence F (tangentField F b Z) b gInv x =
      ∑ i, fderiv ℝ (Z i) x (b i) +
        ∑ k, Z k x *
          ((∑ i, ∑ j, gInv i j * fderiv ℝ (fun y => frameGram F b y i j) x (b k)) / 2) := by
  -- the inverse metric contracts the Gram matrix to the identity
  have hdelta : ∀ i k, ∑ j, gInv i j * frameGram F b x k j = if i = k then 1 else 0 := by
    intro i k
    rw [← hinv i k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [frameGram_symm]
  -- expand each summand of the divergence
  have hexp : ∀ i j, gInv i j *
        @inner ℝ E _ (fderiv ℝ (tangentField F b Z) x (b i)) (frameTangent F b x j) =
      ∑ k, (fderiv ℝ (Z k) x (b i) * (gInv i j * frameGram F b x k j) +
        Z k x * (gInv i j *
          @inner ℝ E _ (secondDerivative F x (b i) (b k)) (frameTangent F b x j))) := by
    intro i j
    rw [fderiv_tangentField hF b hZ, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, frameGram]
    ring
  rw [tangentialDivergence]
  simp only [hexp, Finset.sum_add_distrib]
  congr 1
  · -- the coefficient-derivative part collapses to the trace
    calc ∑ i, ∑ j, ∑ k, fderiv ℝ (Z k) x (b i) * (gInv i j * frameGram F b x k j)
        = ∑ i, ∑ k, fderiv ℝ (Z k) x (b i) * ∑ j, gInv i j * frameGram F b x k j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, fderiv ℝ (Z i) x (b i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hdelta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
            if_true]
  · -- the coefficient part is the contracted Christoffel symbol
    calc ∑ i, ∑ j, ∑ k, Z k x * (gInv i j *
            @inner ℝ E _ (secondDerivative F x (b i) (b k)) (frameTangent F b x j))
        = ∑ k, Z k x * ∑ i, ∑ j, gInv i j *
            @inner ℝ E _ (secondDerivative F x (b i) (b k)) (frameTangent F b x j) := by
          simp only [Finset.mul_sum]
          conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sum_inner_secondDerivative_frameTangent_eq_half_trace hF b gInv hsymm x k]

end HuiskenMonotonicity
