/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.TangentialCalculus

/-!
# Evolution of the induced metric

For a family of immersions with velocity `V`, differentiating `g_ij = ⟪∂_i F, ∂_j F⟫` in
time and exchanging the spatial and time derivatives gives

  `∂_t g_ij = ⟪∂_i V, ∂_j F⟫ + ⟪∂_i F, ∂_j V⟫`

(`hasDerivAt_frameGram`). Contracting against the inverse metric gives twice the tangential
divergence of the velocity,

  `g^{ij} ∂_t g_ij = 2 div_M V`

(`trace_frameGram_deriv_eq_two_mul_tangentialDivergence`), which is the evolution of the volume
element, `∂_t dμ = div_M V dμ`. Huisken's two volume formulas are its specialisations:
`∂_t dμ = -H² dμ` under mean curvature flow, and `∂_s dμ = (n - H²) dμ` under the rescaled
flow (Schnürer, *Lectures on mean curvature flow without singularities*, Lemma 4.1, gives the
first in the oriented form `∂_t g_ij = -2 H h_ij`).

## The commutation hypothesis

The step that exchanges `∂_i` and `∂_t` is isolated as the hypothesis `hcomm`, saying that
the time derivative of the `i`-th coordinate tangent vector is the `i`-th coordinate tangent
vector of the velocity. `hasDerivAt_fderiv_spatialSlice_of_contDiffAt` below discharges it from
joint differentiability of the space-time map, by symmetry of the second derivative.
-/

open scoped InnerProductSpace

namespace HuiskenMonotonicity

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-! ## The evolution equation -/

omit [Fintype Idx] [DecidableEq Idx] in
/-- Time derivative of the induced Gram matrix for a family with velocity `V`.

`hcomm` is the exchange of the spatial and time derivatives; see
`hasDerivAt_fderiv_spatialSlice_of_contDiffAt`, which supplies it for any frame. -/
theorem hasDerivAt_frameGram
    {F V : ℝ → E₁ → E} (b : Idx → E₁) {t : ℝ} {x : E₁} (i j : Idx)
    (hcomm : ∀ k : Idx,
      HasDerivAt (fun s ↦ frameTangent (F s) b x k) (frameTangent (V t) b x k) t) :
    HasDerivAt (fun s ↦ frameGram (F s) b x i j)
      (⟪frameTangent (F t) b x i, frameTangent (V t) b x j⟫_ℝ +
        ⟪frameTangent (V t) b x i, frameTangent (F t) b x j⟫_ℝ) t :=
  HasDerivAt.inner ℝ (hcomm i) (hcomm j)

/-! ## The trace: the first variation of area

The trace of the metric evolution is twice the tangential divergence of the velocity, the
pointwise form of the first variation of area `∂_t dμ = div_M V dμ`. For mean curvature flow
`V = Hvec` is normal and `div_M Hvec = -‖Hvec‖²`, giving `∂_t dμ = -H² dμ`; for the rescaled
flow `V = Hvec + F` and `div_M F = n` give `∂_s dμ = (n - H²) dμ`. -/
omit [DecidableEq Idx] in
/-- The trace of the metric evolution, for an arbitrary velocity, is twice the tangential
divergence of the velocity.

Symmetry of `gInv` is needed and is available for any genuine inverse metric. -/
theorem trace_frameGram_deriv_eq_two_mul_tangentialDivergence
    {F V : E₁ → E} (b : Idx → E₁) (gInv : Idx → Idx → ℝ) {x : E₁}
    (hsymm : ∀ i j : Idx, gInv i j = gInv j i) :
    ∑ i, ∑ j, gInv i j *
        (⟪fderiv ℝ V x (b i), frameTangent F b x j⟫_ℝ +
          ⟪frameTangent F b x i, fderiv ℝ V x (b j)⟫_ℝ) =
      2 * tangentialDivergence F V b gInv x := by
  have hsplit : ∑ i, ∑ j, gInv i j *
        (⟪fderiv ℝ V x (b i), frameTangent F b x j⟫_ℝ +
          ⟪frameTangent F b x i, fderiv ℝ V x (b j)⟫_ℝ)
      = (∑ i, ∑ j, gInv i j *
            ⟪fderiv ℝ V x (b i), frameTangent F b x j⟫_ℝ)
        + ∑ i, ∑ j, gInv i j *
            ⟪frameTangent F b x i, fderiv ℝ V x (b j)⟫_ℝ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  -- the second sum is the first, after swapping the summation indices
  have hswap : ∑ i, ∑ j, gInv i j *
        ⟪frameTangent F b x i, fderiv ℝ V x (b j)⟫_ℝ
      = ∑ i, ∑ j, gInv i j *
            ⟪fderiv ℝ V x (b i), frameTangent F b x j⟫_ℝ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hsymm j i, real_inner_comm (frameTangent F b x j) (fderiv ℝ V x (b i))]
  rw [hsplit, hswap, tangentialDivergence]
  ring

/-! ## Discharging the commutation hypothesis

For a jointly twice-differentiable space-time map, the time derivative of a spatial
derivative is the spatial derivative of the time derivative. Both sides are the mixed
second derivative of the joint map, in the two orders, so the statement is an instance of
symmetry of the second derivative. -/

section Commutation

/-- The time-`t` spatial slice of a space-time map. -/
def spatialSlice (Φ : ℝ × E₁ → E) (t : ℝ) : E₁ → E := fun y ↦ Φ (t, y)

/-- The velocity of a space-time map: the partial derivative in the time direction. -/
noncomputable def timeVelocity (Φ : ℝ × E₁ → E) (t : ℝ) : E₁ → E :=
  fun y ↦ fderiv ℝ Φ (t, y) (1, 0)

/-- **Commutation of the spatial and time derivatives, local form.**

Only `ContDiffAt` at the point is required. This matters for manifold data: a chart
representation `fun y ↦ f ((extChartAt I x).symm y)` is smooth on the chart target and
nowhere else, so a global hypothesis would be unusable.

Both sides are the mixed second derivative of `Φ` in the two orders, so the proof is
`second_derivative_symmetric_of_eventually`. -/
theorem hasDerivAt_fderiv_spatialSlice_of_contDiffAt
    {Φ : ℝ × E₁ → E} {t : ℝ} {x : E₁} (hΦ : ContDiffAt ℝ 2 Φ (t, x)) (v : E₁) :
    HasDerivAt (fun s ↦ fderiv ℝ (spatialSlice Φ s) x v)
      (fderiv ℝ (timeVelocity Φ t) x v) t := by
  -- `Φ` is differentiable on a neighbourhood of `(t, x)`.
  have hev : ∀ᶠ q in nhds ((t, x) : ℝ × E₁), HasFDerivAt Φ (fderiv ℝ Φ q) q := by
    filter_upwards [hΦ.eventually (by norm_num)] with q hq
    exact (hq.differentiableAt (by norm_num)).hasFDerivAt
  have hΦ2 : ContDiffAt ℝ 1 (fderiv ℝ Φ) (t, x) := hΦ.fderiv_right (by norm_num)
  have hd2 : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (t, x)) (t, x) :=
    (hΦ2.differentiableAt (by norm_num)).hasFDerivAt
  set D := fderiv ℝ (fderiv ℝ Φ) (t, x) with hD
  -- Left side: differentiate `s ↦ dΦ_{(s,x)}(0, v)` in `s`.
  have hLinner : HasFDerivAt (fun p : ℝ × E₁ ↦ fderiv ℝ Φ p (0, v))
      (D.flip (0, v)) (t, x) := by
    simpa using hd2.clm_apply (hasFDerivAt_const ((0 : ℝ), v) (t, x))
  have hLcomp : HasFDerivAt
      ((fun p : ℝ × E₁ ↦ fderiv ℝ Φ p (0, v)) ∘ fun s : ℝ ↦ (s, x))
      ((D.flip (0, v)).comp (ContinuousLinearMap.inl ℝ ℝ E₁)) t :=
    hLinner.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)
  have hL : HasFDerivAt (fun s : ℝ ↦ fderiv ℝ Φ (s, x) (0, v))
      ((D.flip (0, v)).comp (ContinuousLinearMap.inl ℝ ℝ E₁)) t := hLcomp
  have hLd := hL.hasDerivAt
  -- Near `t` the slice derivative agrees with that partial derivative.
  have hmap : Filter.Tendsto (fun s : ℝ ↦ ((s, x) : ℝ × E₁)) (nhds t)
      (nhds ((t, x) : ℝ × E₁)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hfun : ∀ᶠ s in nhds t,
      fderiv ℝ (spatialSlice Φ s) x v = fderiv ℝ Φ (s, x) (0, v) := by
    filter_upwards [hmap.eventually hev] with s hs
    have h : HasFDerivAt (spatialSlice Φ s)
        ((fderiv ℝ Φ (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E₁)) x :=
      hs.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) s x)
    rw [h.fderiv]
    rfl
  -- Right side: differentiate `y ↦ dΦ_{(t,y)}(1, 0)` in `y`.
  have hRinner : HasFDerivAt (fun p : ℝ × E₁ ↦ fderiv ℝ Φ p (1, 0))
      (D.flip ((1 : ℝ), (0 : E₁))) (t, x) := by
    simpa using hd2.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : E₁)) (t, x))
  have hRcomp : HasFDerivAt
      ((fun p : ℝ × E₁ ↦ fderiv ℝ Φ p (1, 0)) ∘ fun y : E₁ ↦ (t, y))
      ((D.flip ((1 : ℝ), (0 : E₁))).comp (ContinuousLinearMap.inr ℝ ℝ E₁)) x :=
    hRinner.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  have hR : HasFDerivAt (timeVelocity Φ t)
      ((D.flip ((1 : ℝ), (0 : E₁))).comp (ContinuousLinearMap.inr ℝ ℝ E₁)) x := hRcomp
  have hRv : fderiv ℝ (timeVelocity Φ t) x v = D ((0 : ℝ), v) ((1 : ℝ), (0 : E₁)) := by
    rw [hR.fderiv]
    rfl
  have hsymm : D ((1 : ℝ), (0 : E₁)) ((0 : ℝ), v) = D ((0 : ℝ), v) ((1 : ℝ), (0 : E₁)) :=
    second_derivative_symmetric_of_eventually hev hd2 _ _
  rw [hRv, ← hsymm]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
  convert hLd using 1
  rfl

/-- The time derivative of a spatial partial derivative is the mixed second derivative.

Extracted from the proof of `hasDerivAt_fderiv_spatialSlice_of_contDiffAt`, where it is the
left-hand computation. Stated separately because the regularity hypothesis of the transport
formula needs it on its own, without the symmetry step. -/
theorem hasDerivAt_fderiv_partial_time
    {Φ : ℝ × E₁ → E} {t : ℝ} {x : E₁} (hΦ : ContDiffAt ℝ 2 Φ (t, x)) (v : E₁) :
    HasDerivAt (fun s : ℝ ↦ fderiv ℝ Φ (s, x) ((0 : ℝ), v))
      (fderiv ℝ (fderiv ℝ Φ) (t, x) ((1 : ℝ), (0 : E₁)) ((0 : ℝ), v)) t := by
  have hΦ2 : ContDiffAt ℝ 1 (fderiv ℝ Φ) (t, x) := hΦ.fderiv_right (by norm_num)
  have hd2 : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (t, x)) (t, x) :=
    (hΦ2.differentiableAt (by norm_num)).hasFDerivAt
  set D := fderiv ℝ (fderiv ℝ Φ) (t, x) with hD
  have hinner : HasFDerivAt (fun p : ℝ × E₁ ↦ fderiv ℝ Φ p ((0 : ℝ), v))
      (D.flip ((0 : ℝ), v)) (t, x) := by
    simpa using hd2.clm_apply (hasFDerivAt_const ((0 : ℝ), v) (t, x))
  have hcomp : HasFDerivAt
      ((fun p : ℝ × E₁ ↦ fderiv ℝ Φ p ((0 : ℝ), v)) ∘ fun s : ℝ ↦ (s, x))
      ((D.flip ((0 : ℝ), v)).comp (ContinuousLinearMap.inl ℝ ℝ E₁)) t :=
    hinner.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)
  have hL : HasFDerivAt (fun s : ℝ ↦ fderiv ℝ Φ (s, x) ((0 : ℝ), v))
      ((D.flip ((0 : ℝ), v)).comp (ContinuousLinearMap.inl ℝ ℝ E₁)) t := hcomp
  convert hL.hasDerivAt using 1
  rfl

end Commutation

end HuiskenMonotonicity
