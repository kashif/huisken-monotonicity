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
    {F ξ : E₁ → E} {x : E₁} (hF : ContDiffAt ℝ 2 F x) (hξ : DifferentiableAt ℝ ξ x)
    (hnormal : IsNormalAlongNear F ξ x) (b : Idx → E₁) (gInv : Idx → Idx → ℝ) :
    tangentialDivergence F ξ b gInv x =
      -@inner ℝ E _ (ξ x) (meanCurvatureVectorFrame F b gInv x) := by
  have hR : -@inner ℝ E _ (ξ x) (meanCurvatureVectorFrame F b gInv x) =
      ∑ i, ∑ j, -(@inner ℝ E _ (ξ x)
        (gInv i j • secondDerivative F x (b i) (b j))) := by
    simp only [meanCurvatureVectorFrame, inner_sum, Finset.sum_neg_distrib]
  rw [tangentialDivergence, hR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [frameTangent_apply,
    inner_fderiv_eq_neg_inner_secondDerivative hF hξ hnormal (b i) (b j),
    real_inner_smul_right]
  ring

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

/-! ## Tangential and normal parts

The tangential part of an ambient vector is its projection onto the tangent space,
written through the inverse metric so that no projection operator is constructed:

  `vᵀ = ∑ k, ∑ l, g^{kl} ⟪v, ∂_l F⟫ ∂_k F`,   `v^⊥ = v - vᵀ`.

`meanCurvatureVectorFrame` is the plain trace `g^{ij} D²F(∂_i, ∂_j)`, which has a tangential
Christoffel component; its normal part is the mean curvature vector proper. The difference is
invisible against a normal field, but not against the position vector, which is what
Huisken's first-variation identity pairs it with. -/

/-- The **tangential part** of an ambient vector. -/
noncomputable def tangentialPart
    (F : E₁ → E) (b : Idx → E₁) (gInv : Idx → Idx → ℝ) (x : E₁) (v : E) : E :=
  ∑ k, ∑ l, (gInv k l * @inner ℝ E _ v (frameTangent F b x l)) • frameTangent F b x k

/-- The **normal part** of an ambient vector. -/
noncomputable def normalPart
    (F : E₁ → E) (b : Idx → E₁) (gInv : Idx → Idx → ℝ) (x : E₁) (v : E) : E :=
  v - tangentialPart F b gInv x v

/-- The **mean curvature vector**: the normal part of the inverse-metric trace of the second
derivative. -/
noncomputable def meanCurvatureNormal
    (F : E₁ → E) (b : Idx → E₁) (gInv : Idx → Idx → ℝ) (x : E₁) : E :=
  normalPart F b gInv x (meanCurvatureVectorFrame F b gInv x)

/-- The tangential part pairs with each frame vector as the vector itself does. -/
theorem inner_tangentialPart_frameTangent
    {F : E₁ → E} {b : Idx → E₁} {gInv : Idx → Idx → ℝ} {x : E₁}
    (hinv : IsFrameInverse F b x gInv) (hsymm : ∀ i j, gInv i j = gInv j i)
    (v : E) (j : Idx) :
    @inner ℝ E _ (tangentialPart F b gInv x v) (frameTangent F b x j) =
      @inner ℝ E _ v (frameTangent F b x j) := by
  have hstep : @inner ℝ E _ (tangentialPart F b gInv x v) (frameTangent F b x j) =
      ∑ l, @inner ℝ E _ v (frameTangent F b x l) *
        ∑ k, gInv l k * frameGram F b x k j := by
    simp only [tangentialPart, sum_inner, real_inner_smul_left, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hsymm k l, frameGram]
    ring
  rw [hstep]
  simp only [hinv _ j, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The normal part is orthogonal to every frame vector. -/
theorem inner_normalPart_frameTangent
    {F : E₁ → E} {b : Idx → E₁} {gInv : Idx → Idx → ℝ} {x : E₁}
    (hinv : IsFrameInverse F b x gInv) (hsymm : ∀ i j, gInv i j = gInv j i)
    (v : E) (j : Idx) :
    @inner ℝ E _ (normalPart F b gInv x v) (frameTangent F b x j) = 0 := by
  rw [normalPart, inner_sub_left, inner_tangentialPart_frameTangent hinv hsymm, sub_self]

/-- The normal part is orthogonal to the tangential part of any vector. -/
theorem inner_normalPart_tangentialPart
    {F : E₁ → E} {b : Idx → E₁} {gInv : Idx → Idx → ℝ} {x : E₁}
    (hinv : IsFrameInverse F b x gInv) (hsymm : ∀ i j, gInv i j = gInv j i)
    (v w : E) :
    @inner ℝ E _ (normalPart F b gInv x v) (tangentialPart F b gInv x w) = 0 := by
  simp only [tangentialPart, inner_sum, real_inner_smul_right,
    inner_normalPart_frameTangent hinv hsymm, mul_zero, Finset.sum_const_zero]

/-- The squared tangential norm is the squared length of the tangential part. -/
theorem inner_tangentialPart_self
    {F : E₁ → E} {b : Idx → E₁} {gInv : Idx → Idx → ℝ} {x : E₁}
    (hsymm : ∀ i j, gInv i j = gInv j i) (v : E) :
    @inner ℝ E _ (tangentialPart F b gInv x v) v = tangentialNormSq F b gInv x v := by
  simp only [tangentialPart, tangentialNormSq, sum_inner, real_inner_smul_left]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsymm j i, real_inner_comm (frameTangent F b x j) v]
  ring

/-- Pairing with the mean curvature vector sees only the normal part of the other vector, and
on a normal vector it agrees with pairing against the plain trace. -/
theorem inner_meanCurvatureNormal_eq
    {F : E₁ → E} {b : Idx → E₁} {gInv : Idx → Idx → ℝ} {x : E₁}
    (hinv : IsFrameInverse F b x gInv) (hsymm : ∀ i j, gInv i j = gInv j i) (v : E) :
    @inner ℝ E _ v (meanCurvatureNormal F b gInv x) =
      @inner ℝ E _ (normalPart F b gInv x v) (meanCurvatureVectorFrame F b gInv x) := by
  have hv : v = normalPart F b gInv x v + tangentialPart F b gInv x v := by
    simp [normalPart]
  have hH : meanCurvatureVectorFrame F b gInv x =
      meanCurvatureNormal F b gInv x +
        tangentialPart F b gInv x (meanCurvatureVectorFrame F b gInv x) := by
    simp [meanCurvatureNormal, normalPart]
  have h0 : @inner ℝ E _ (tangentialPart F b gInv x v) (meanCurvatureNormal F b gInv x) = 0 := by
    rw [real_inner_comm, meanCurvatureNormal, inner_normalPart_tangentialPart hinv hsymm]
  conv_lhs => rw [hv]
  conv_rhs => rw [hH]
  rw [inner_add_left, inner_add_right, inner_normalPart_tangentialPart hinv hsymm, add_zero, h0,
    add_zero]

/-! ## Beltrami's formula for the squared distance

`Δ_M (|F|²/2) = n + ⟪F, Hvec⟫`, the form of Beltrami's formula `Δ_M F = Hvec` that Huisken's
first-variation step uses. The gradient of `|F|²/2` is the tangential part of the position
vector, so the statement is about the divergence of that field. It follows the split of the
divergence theorem for a submanifold: `F = Fᵀ + F^⊥`, with `div F = n` and, `F^⊥` being normal,
`div F^⊥ = -⟪F^⊥, Hvec⟫`.

The inverse metric is allowed to vary with the point, as it does in a chart; it must be an
inverse metric near the point and have differentiable entries there. -/

/-- The tangential divergence is additive in the field. -/
theorem tangentialDivergence_sub (F : E₁ → E) {ξ₁ ξ₂ : E₁ → E} (b : Idx → E₁)
    (gInv : Idx → Idx → ℝ) {x : E₁} (h₁ : DifferentiableAt ℝ ξ₁ x)
    (h₂ : DifferentiableAt ℝ ξ₂ x) :
    tangentialDivergence F (fun y => ξ₁ y - ξ₂ y) b gInv x =
      tangentialDivergence F ξ₁ b gInv x - tangentialDivergence F ξ₂ b gInv x := by
  simp only [tangentialDivergence, fderiv_fun_sub h₁ h₂, ContinuousLinearMap.sub_apply,
    inner_sub_left, mul_sub, Finset.sum_sub_distrib]

/-- The tangential part of a differentiable field is differentiable, when the inverse metric
is. -/
theorem differentiableAt_tangentialPart {F : E₁ → E} {x : E₁} (hF : ContDiffAt ℝ 2 F x)
    (b : Idx → E₁) {gInv : E₁ → Idx → Idx → ℝ}
    (hg : ∀ k l, DifferentiableAt ℝ (fun y => gInv y k l) x) {v : E₁ → E}
    (hv : DifferentiableAt ℝ v x) :
    DifferentiableAt ℝ (fun y => tangentialPart F b (gInv y) y (v y)) x := by
  have hT : ∀ k, DifferentiableAt ℝ (fun y => frameTangent F b y k) x := fun k =>
    (hasFDerivAt_fderiv_apply hF (b k)).differentiableAt
  unfold tangentialPart
  refine DifferentiableAt.fun_sum fun k _ => DifferentiableAt.fun_sum fun l _ => ?_
  exact ((hg k l).mul (hv.inner ℝ (hT l))).smul (hT k)

/-- **Beltrami's formula for `|F|²/2`.** The tangential divergence of the tangential part of
the position vector is `n + ⟪F, Hvec⟫`. -/
theorem tangentialDivergence_tangentialPart_position {F : E₁ → E} {x : E₁}
    (hF : ContDiffAt ℝ 2 F x) (b : Idx → E₁) (hb : Submodule.span ℝ (Set.range b) = ⊤)
    (gInv : E₁ → Idx → Idx → ℝ)
    (hinv : ∀ᶠ y in nhds x, IsFrameInverse F b y (gInv y))
    (hsymm : ∀ y i j, gInv y i j = gInv y j i)
    (hg : ∀ k l, DifferentiableAt ℝ (fun y => gInv y k l) x) :
    tangentialDivergence F (fun y => tangentialPart F b (gInv y) y (F y)) b (gInv x) x =
      (Fintype.card Idx : ℝ) +
        @inner ℝ E _ (F x) (meanCurvatureNormal F b (gInv x) x) := by
  have hFd : DifferentiableAt ℝ F x := hF.differentiableAt (by norm_num)
  have hN : DifferentiableAt ℝ (fun y => normalPart F b (gInv y) y (F y)) x :=
    hFd.sub (differentiableAt_tangentialPart hF b hg hFd)
  -- the tangential part is the position vector minus its normal part
  have hT : (fun y => tangentialPart F b (gInv y) y (F y)) =
      fun y => F y - normalPart F b (gInv y) y (F y) := by
    funext y
    simp [normalPart]
  -- the normal part is normal along F near x: `v ↦ ⟪N, dF v⟫` is linear and vanishes on the
  -- spanning frame
  have hnormal : IsNormalAlongNear F (fun y => normalPart F b (gInv y) y (F y)) x := by
    filter_upwards [hinv] with y hy v
    set L : E₁ →L[ℝ] ℝ :=
      (innerSL ℝ (normalPart F b (gInv y) y (F y))).comp (fderiv ℝ F y) with hL
    have hker : Submodule.span ℝ (Set.range b) ≤ LinearMap.ker (L : E₁ →ₗ[ℝ] ℝ) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simpa [hL, frameTangent] using inner_normalPart_frameTangent hy (hsymm y) (F y) j
    have hv : v ∈ LinearMap.ker (L : E₁ →ₗ[ℝ] ℝ) := hker (hb ▸ Submodule.mem_top)
    simpa [hL] using hv
  rw [hT, tangentialDivergence_sub F b (gInv x) hFd hN,
    tangentialDivergence_self F b hinv.self_of_nhds,
    tangentialDivergence_of_isNormalAlong hF hN hnormal b (gInv x),
    inner_meanCurvatureNormal_eq hinv.self_of_nhds (hsymm x)]
  ring

end HuiskenMonotonicity
