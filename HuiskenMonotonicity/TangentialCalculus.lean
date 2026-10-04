/-
**Tangential divergence and the normal divergence identity.**

The tangential divergence of a vector field along an immersion `F` is defined by
contracting the ambient derivative against the inverse induced metric,

  `div_M X = g^{ij} ⟪D̄_{∂_i F} X, ∂_j F⟫`.

The divergence theorem for immersed submanifolds splits into two pieces: the tangential
part integrates to zero by Stokes, and the normal part satisfies the pointwise identity

  `div_M(X^⊥) = ⟪X, ν⟫ g^{ij} h_ij = ⟪X, ν⟫ H = -⟪X, Hvec⟫`.

This file proves that pointwise identity, orientation-free. It is the inverse-metric
contraction of the Weingarten equation: Weingarten converts each `⟪dξ(∂_i), ∂_j F⟫` into
`-⟪ξ, D²F(∂_i, ∂_j)⟫`, and contracting with `g^{ij}` assembles the mean curvature vector on
the right.

The ambient space is a Euclidean inner product space, so `D̄` is the ordinary Fréchet
derivative and no connection machinery is needed.

## Frames and the inverse metric

Everything is stated relative to a frame `b : Idx → E₁` of the model space together with a
matrix `gInv` of inverse-metric components, rather than for a fixed standard basis of
`EuclideanSpace ℝ (Fin n)`. Two reasons:

* a derivative on a manifold reduces to a Fréchet derivative of the chart representation
  `f ∘ (extChartAt I x).symm`, a map between model spaces carrying whatever frame the
  chart supplies, so fixing a standard basis would force a change of frame later;
* the correctness of `gInv` is carried by the predicate `IsFrameInverse` rather than by a
  matrix inverse, which is how an inverse metric is usually packaged.

`IsFrameInverse` is needed only where the trace of the identity appears, in
`tangentialDivergence_self`. The normal divergence identity holds for any `gInv`.

## A remark on Christoffel terms

`meanCurvatureVectorFrame` contracts the *plain* second derivative, `g^{ij} ∂_i∂_j F`, not
the second covariant derivative `g^{ij} X_{;ij}`. The two differ by the tangential term
`g^{ij} Γ^k_{ij} ∂_k F`. That discrepancy is invisible here: every statement pairs the
vector against a field normal along `F`, and a normal field annihilates `∂_k F`. So
`⟪ξ, g^{ij} ∂_i∂_j F⟫ = ⟪ξ, g^{ij} X_{;ij}⟫ = ⟪ξ, Hvec⟫` with no Christoffel symbols
anywhere, which is why this layer needs no connection.
-/

import HuiskenMonotonicity.Weingarten

namespace HuiskenMonotonicity

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-! ## Frame quantities -/

/-- The tangent vector `∂_i F = dF_x(b i)` of `F` in the frame `b`. -/
noncomputable def frameTangent (F : E₁ → E) (b : Idx → E₁) (x : E₁) (i : Idx) : E :=
  fderiv ℝ F x (b i)

@[simp]
lemma frameTangent_apply (F : E₁ → E) (b : Idx → E₁) (x : E₁) (i : Idx) :
    frameTangent F b x i = fderiv ℝ F x (b i) :=
  rfl

/-- The induced Gram matrix `g_ij = ⟪∂_i F, ∂_j F⟫` in the frame `b`. -/
noncomputable def frameGram (F : E₁ → E) (b : Idx → E₁) (x : E₁) (i j : Idx) : ℝ :=
  @inner ℝ E _ (frameTangent F b x i) (frameTangent F b x j)

lemma frameGram_symm (F : E₁ → E) (b : Idx → E₁) (x : E₁) (i j : Idx) :
    frameGram F b x i j = frameGram F b x j i :=
  real_inner_comm _ _

/-- `gInv` is a matrix of inverse-metric components for the frame `b` at `x`.

Packaged by the relation it satisfies rather than by a matrix inverse, so that it transfers
to any frame. -/
def IsFrameInverse (F : E₁ → E) (b : Idx → E₁) (x : E₁) (gInv : Idx → Idx → ℝ) : Prop :=
  ∀ i j : Idx, ∑ k, gInv i k * frameGram F b x k j = if i = j then 1 else 0

/-! ## Divergence, mean curvature, gradient, tangential norm -/

/-- **Tangential divergence** of a field `ξ` on the model space:

  `div_M ξ = ∑ i, ∑ j, g^{ij} ⟪dξ(b i), ∂_j F⟫`. -/
noncomputable def tangentialDivergence
    (F ξ : E₁ → E) (b : Idx → E₁) (gInv : Idx → Idx → ℝ) (x : E₁) : ℝ :=
  ∑ i, ∑ j, gInv i j * @inner ℝ E _ (fderiv ℝ ξ x (b i)) (frameTangent F b x j)

/-- The **mean curvature vector**: the inverse-metric trace of the second derivative,

  `Hvec = g^{ij} D²F(b i, b j)`. -/
noncomputable def meanCurvatureVectorFrame
    (F : E₁ → E) (b : Idx → E₁) (gInv : Idx → Idx → ℝ) (x : E₁) : E :=
  ∑ i, ∑ j, gInv i j • secondDerivative F x (b i) (b j)

/-- The **tangential gradient** of a scalar function:

  `∇_M f = ∑ i, ∑ j, g^{ij} (∂_i f) ∂_j F`. -/
noncomputable def tangentialGradient
    (F : E₁ → E) (f : E₁ → ℝ) (b : Idx → E₁) (gInv : Idx → Idx → ℝ) (x : E₁) : E :=
  ∑ i, ∑ j, (gInv i j * fderiv ℝ f x (b i)) • frameTangent F b x j

/-- The **squared tangential norm** of an ambient vector `v`:

  `‖v^T‖² = ∑ i, ∑ j, g^{ij} ⟪v, ∂_i F⟫ ⟪v, ∂_j F⟫`.

The squared length of the orthogonal projection of `v` onto the tangent space, written
without constructing the projection. -/
noncomputable def tangentialNormSq
    (F : E₁ → E) (b : Idx → E₁) (gInv : Idx → Idx → ℝ) (x : E₁) (v : E) : ℝ :=
  ∑ i, ∑ j, gInv i j *
    (@inner ℝ E _ v (frameTangent F b x i) * @inner ℝ E _ v (frameTangent F b x j))

/-! ## The normal divergence identity -/

/-- **The normal divergence identity**, the normal half of the divergence theorem.

For a field `ξ` normal along `F`,

  `div_M ξ = -⟪ξ, Hvec⟫`.

The inverse-metric contraction of `inner_fderiv_eq_neg_inner_secondDerivative`; needs no
unit normal, and holds for an arbitrary `gInv`. -/
theorem tangentialDivergence_of_isNormalAlong
    {F ξ : E₁ → E} (hF : ContDiff ℝ 2 F) (hξ : Differentiable ℝ ξ)
    (hnormal : IsNormalAlong F ξ) (b : Idx → E₁) (gInv : Idx → Idx → ℝ) (x : E₁) :
    tangentialDivergence F ξ b gInv x =
      -@inner ℝ E _ (ξ x) (meanCurvatureVectorFrame F b gInv x) := by
  have hR : -@inner ℝ E _ (ξ x) (meanCurvatureVectorFrame F b gInv x) =
      ∑ i, ∑ j, -(@inner ℝ E _ (ξ x)
        (gInv i j • secondDerivative F x (b i) (b j))) := by
    simp only [meanCurvatureVectorFrame, inner_sum, Finset.sum_neg_distrib]
  rw [tangentialDivergence, hR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [frameTangent_apply,
    inner_fderiv_eq_neg_inner_secondDerivative hF hξ hnormal x (b i) (b j),
    real_inner_smul_right]
  ring

/-- The identity read the other way round. -/
theorem inner_meanCurvatureVectorFrame_eq_neg_tangentialDivergence
    {F ξ : E₁ → E} (hF : ContDiff ℝ 2 F) (hξ : Differentiable ℝ ξ)
    (hnormal : IsNormalAlong F ξ) (b : Idx → E₁) (gInv : Idx → Idx → ℝ) (x : E₁) :
    @inner ℝ E _ (ξ x) (meanCurvatureVectorFrame F b gInv x) =
      -tangentialDivergence F ξ b gInv x := by
  rw [tangentialDivergence_of_isNormalAlong hF hξ hnormal b gInv x, neg_neg]

/-! ## Gradient, product rule, and the position field -/

/-- Pairing the tangential gradient against a vector contracts to the same inverse-metric
sum, which is what makes the projection-free formulation work. -/
lemma inner_tangentialGradient
    (F : E₁ → E) (f : E₁ → ℝ) (b : Idx → E₁) (gInv : Idx → Idx → ℝ) (x : E₁) (v : E) :
    @inner ℝ E _ (tangentialGradient F f b gInv x) v =
      ∑ i, ∑ j, gInv i j *
        (fderiv ℝ f x (b i) * @inner ℝ E _ (frameTangent F b x j) v) := by
  simp only [tangentialGradient, sum_inner, real_inner_smul_left]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Product rule for the tangential divergence.**

  `div_M (f • ξ) = ⟪∇_M f, ξ⟫ + f * div_M ξ`. -/
theorem tangentialDivergence_smul
    (F : E₁ → E) {f : E₁ → ℝ} {ξ : E₁ → E} (b : Idx → E₁) (gInv : Idx → Idx → ℝ)
    {x : E₁} (hf : DifferentiableAt ℝ f x) (hξ : DifferentiableAt ℝ ξ x) :
    tangentialDivergence F (fun y => f y • ξ y) b gInv x =
      @inner ℝ E _ (tangentialGradient F f b gInv x) (ξ x) +
        f x * tangentialDivergence F ξ b gInv x := by
  have hd : ∀ i : Idx,
      fderiv ℝ (fun y => f y • ξ y) x (b i) =
        (fderiv ℝ f x (b i)) • ξ x + f x • fderiv ℝ ξ x (b i) := by
    intro i
    have h : HasFDerivAt (fun y => f y • ξ y)
        (f x • fderiv ℝ ξ x + (fderiv ℝ f x).smulRight (ξ x)) x :=
      hf.hasFDerivAt.smul hξ.hasFDerivAt
    rw [h.fderiv]
    simp [add_comm]
  rw [inner_tangentialGradient, tangentialDivergence, tangentialDivergence,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hd i, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_comm (frameTangent F b x j) (ξ x)]
  ring

/-- **`div_M F = dim M`**: the tangential divergence of the position vector is the number of
frame directions.

This is where the bare `n` in Huisken's first-variation integrand comes from: applying the
divergence theorem to `Y = ρ F / τ` produces `ρ * div_M F = n * ρ` as one of its terms.

The proof is that the contraction `g^{ij} g_ij` is the trace of the identity. -/
theorem tangentialDivergence_self
    (F : E₁ → E) (b : Idx → E₁) {gInv : Idx → Idx → ℝ} {x : E₁}
    (hinv : IsFrameInverse F b x gInv) :
    tangentialDivergence F F b gInv x = (Fintype.card Idx : ℝ) := by
  have hstep : tangentialDivergence F F b gInv x
      = ∑ i : Idx, ∑ k : Idx, gInv i k * frameGram F b x k i := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [frameGram_symm, frameGram, frameTangent_apply]
    rfl
  calc tangentialDivergence F F b gInv x
      = ∑ i : Idx, ∑ k : Idx, gInv i k * frameGram F b x k i := hstep
    _ = ∑ _i : Idx, (1 : ℝ) := Finset.sum_congr rfl fun i _ => by simpa using hinv i i
    _ = (Fintype.card Idx : ℝ) := by simp

end HuiskenMonotonicity
