/-
**Evolution of the induced metric under a normal velocity.**

For a family of immersions with velocity `V`, differentiating
`g_ij = ⟪∂_i F, ∂_j F⟫` in time and exchanging the spatial and time derivatives gives

  `∂_t g_ij = ⟪∂_i V, ∂_j F⟫ + ⟪∂_i F, ∂_j V⟫`.

When `V` is normal along `F`, each term is handled by the Weingarten equation, and the two
collapse into one:

  `∂_t g_ij = -2 ⟪V, D²F(∂_i, ∂_j)⟫`.

This is the orientation-free form of the classical evolution equation
`∂_t g_ij = -2 F h_ij` for the normal velocity `∂_t X = -F ν` (Schnürer, *Lectures on mean
curvature flow without singularities*, Lemma 4.1): taking `V = -F ν` and using
`h_ij = -⟪D²X(∂_i, ∂_j), ν⟫` recovers it, with no choice of normal needed here.

Contracting against the inverse metric gives the trace that drives the evolution of the
volume element,

  `g^{ij} ∂_t g_ij = -2 ⟪V, Hvec⟫`,

and under mean curvature flow, where `V = Hvec`, this is `-2‖Hvec‖²`. Half of it,
`-‖Hvec‖²`, is the weight appearing in the transport formula for a moving Riemannian
measure, which is the form in which the classical statement `∂_t dμ = -H² dμ` is used.

## The commutation hypothesis

The step that exchanges `∂_i` and `∂_t` is isolated as the hypothesis `hcomm`, saying that
the time derivative of the `i`-th coordinate tangent vector is the `i`-th coordinate tangent
vector of the velocity. `hasDerivAt_fderiv_spatialSlice` below discharges it from
joint differentiability of the space-time map, by symmetry of the second derivative.
-/

import HuiskenMonotonicity.TangentialCalculus

namespace HuiskenMonotonicity

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-! ## The evolution equation -/

/-- Time derivative of the induced Gram matrix for a family with velocity `V`.

`hcomm` is the exchange of the spatial and time derivatives; see
`hasDerivAt_fderiv_spatialSlice`, which supplies it for any frame. -/
theorem hasDerivAt_frameGram
    {F V : ℝ → E₁ → E} (b : Idx → E₁) {t : ℝ} {x : E₁} (i j : Idx)
    (hcomm : ∀ k : Idx,
      HasDerivAt (fun s => frameTangent (F s) b x k) (frameTangent (V t) b x k) t) :
    HasDerivAt (fun s => frameGram (F s) b x i j)
      (@inner ℝ E _ (frameTangent (F t) b x i) (frameTangent (V t) b x j) +
        @inner ℝ E _ (frameTangent (V t) b x i) (frameTangent (F t) b x j)) t :=
  HasDerivAt.inner ℝ (hcomm i) (hcomm j)

/-- **The evolution equation of the induced metric under a normal velocity.**

`∂_t g_ij = -2 ⟪V, D²F(∂_i, ∂_j)⟫`.

Orientation-free form of `∂_t g_ij = -2 F h_ij`. -/
theorem hasDerivAt_frameGram_of_isNormalAlong
    {F V : ℝ → E₁ → E} (b : Idx → E₁) {t : ℝ} {x : E₁} (i j : Idx)
    (hF : ContDiff ℝ 2 (F t)) (hV : Differentiable ℝ (V t))
    (hnormal : IsNormalAlong (F t) (V t))
    (hcomm : ∀ k : Idx,
      HasDerivAt (fun s => frameTangent (F s) b x k) (frameTangent (V t) b x k) t) :
    HasDerivAt (fun s => frameGram (F s) b x i j)
      (-2 * @inner ℝ E _ (V t x) (secondDerivative (F t) x (b i) (b j))) t := by
  have hbase := hasDerivAt_frameGram (V := V) b i j hcomm
  have hji : @inner ℝ E _ (frameTangent (F t) b x i) (frameTangent (V t) b x j) =
      -@inner ℝ E _ (V t x) (secondDerivative (F t) x (b i) (b j)) := by
    rw [real_inner_comm, frameTangent_apply, frameTangent_apply,
      inner_fderiv_eq_neg_inner_secondDerivative hF hV hnormal x (b j) (b i),
      secondDerivative_symm hF x (b j) (b i)]
  have hij : @inner ℝ E _ (frameTangent (V t) b x i) (frameTangent (F t) b x j) =
      -@inner ℝ E _ (V t x) (secondDerivative (F t) x (b i) (b j)) := by
    rw [frameTangent_apply, frameTangent_apply,
      inner_fderiv_eq_neg_inner_secondDerivative hF hV hnormal x (b i) (b j)]
  rw [hji, hij] at hbase
  convert hbase using 1
  ring

/-! ## The trace -/

/-- The inverse-metric trace of the metric evolution:

`g^{ij} ∂_t g_ij = -2 ⟪V, Hvec⟫`.

This is the quantity the transport formula for a moving Riemannian measure consumes, there
weighted by `1/2`. Pure contraction: once the pointwise evolution equation is known, this
step needs no hypotheses at all. -/
theorem trace_metricEvolution
    {F V : E₁ → E} (b : Idx → E₁) (gInv : Idx → Idx → ℝ) {x : E₁} :
    ∑ i, ∑ j, gInv i j *
        (-2 * @inner ℝ E _ (V x) (secondDerivative F x (b i) (b j))) =
      -2 * @inner ℝ E _ (V x) (meanCurvatureVectorFrame F b gInv x) := by
  have hR : @inner ℝ E _ (V x) (meanCurvatureVectorFrame F b gInv x) =
      ∑ i, ∑ j, gInv i j *
        @inner ℝ E _ (V x) (secondDerivative F x (b i) (b j)) := by
    simp only [meanCurvatureVectorFrame, inner_sum, real_inner_smul_right]
  rw [hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Mean curvature flow: with `V = Hvec` the trace is `-2‖Hvec‖²`, so half of it is
`-‖Hvec‖²`. This is the orientation-free form of `∂_t dμ = -H² dμ`. -/
theorem trace_metricEvolution_meanCurvatureFlow
    {F V : E₁ → E} (b : Idx → E₁) (gInv : Idx → Idx → ℝ) {x : E₁}
    (hmcf : V x = meanCurvatureVectorFrame F b gInv x) :
    ∑ i, ∑ j, gInv i j *
        (-2 * @inner ℝ E _ (V x) (secondDerivative F x (b i) (b j))) =
      -2 * ‖meanCurvatureVectorFrame F b gInv x‖ ^ 2 := by
  rw [trace_metricEvolution b gInv, hmcf, real_inner_self_eq_norm_sq]

/-! ## Discharging the commutation hypothesis

For a jointly twice-differentiable space-time map, the time derivative of a spatial
derivative is the spatial derivative of the time derivative. Both sides are the mixed
second derivative of the joint map, in the two orders, so the statement is an instance of
symmetry of the second derivative. -/

section Commutation

/-- The time-`t` spatial slice of a space-time map. -/
def spatialSlice (Φ : ℝ × E₁ → E) (t : ℝ) : E₁ → E := fun y => Φ (t, y)

/-- The velocity of a space-time map: the partial derivative in the time direction. -/
noncomputable def timeVelocity (Φ : ℝ × E₁ → E) (t : ℝ) : E₁ → E :=
  fun y => fderiv ℝ Φ (t, y) (1, 0)

/-- A spatial derivative of a slice is a partial derivative of the joint map. -/
lemma fderiv_spatialSlice
    {Φ : ℝ × E₁ → E} (hΦ : Differentiable ℝ Φ) (t : ℝ) (x v : E₁) :
    fderiv ℝ (spatialSlice Φ t) x v = fderiv ℝ Φ (t, x) (0, v) := by
  have h : HasFDerivAt (spatialSlice Φ t)
      ((fderiv ℝ Φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E₁)) x :=
    (hΦ (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  rw [h.fderiv]
  rfl

/-- **Commutation of the spatial and time derivatives.**

Discharges the `hcomm` hypothesis of `hasDerivAt_inducedGramMatrix` for a jointly
twice-differentiable space-time map. -/
theorem hasDerivAt_fderiv_spatialSlice
    {Φ : ℝ × E₁ → E} (hΦ : ContDiff ℝ 2 Φ) (t : ℝ) (x v : E₁) :
    HasDerivAt (fun s => fderiv ℝ (spatialSlice Φ s) x v)
      (fderiv ℝ (timeVelocity Φ t) x v) t := by
  have hΦ1 : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hd1 : ∀ p : ℝ × E₁, HasFDerivAt Φ (fderiv ℝ Φ p) p := fun p => (hΦ1 p).hasFDerivAt
  have hΦ2 : ContDiff ℝ 1 (fderiv ℝ Φ) := (contDiff_succ_iff_fderiv.mp hΦ).2.2
  have hd2 : ∀ p : ℝ × E₁,
      HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) p) p :=
    fun p => (hΦ2.differentiable (by norm_num) p).hasFDerivAt
  -- The second derivative, as a bilinear object on `ℝ × E₁`.
  set D := fderiv ℝ (fderiv ℝ Φ) (t, x) with hD
  -- Left side: differentiate `s ↦ dΦ_{(s,x)}(0, v)` in `s`.
  have hLinner : HasFDerivAt (fun p : ℝ × E₁ => fderiv ℝ Φ p (0, v))
      (D.flip (0, v)) (t, x) := by
    simpa using (hd2 (t, x)).clm_apply (hasFDerivAt_const ((0 : ℝ), v) (t, x))
  have hLcomp : HasFDerivAt
      ((fun p : ℝ × E₁ => fderiv ℝ Φ p (0, v)) ∘ fun s : ℝ => (s, x))
      ((D.flip (0, v)).comp (ContinuousLinearMap.inl ℝ ℝ E₁)) t :=
    hLinner.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)
  have hL : HasFDerivAt (fun s : ℝ => fderiv ℝ Φ (s, x) (0, v))
      ((D.flip (0, v)).comp (ContinuousLinearMap.inl ℝ ℝ E₁)) t := hLcomp
  have hLd := hL.hasDerivAt
  -- Rewrite the function on the left into the slice form.
  have hfun : (fun s : ℝ => fderiv ℝ (spatialSlice Φ s) x v)
      = fun s : ℝ => fderiv ℝ Φ (s, x) (0, v) := by
    funext s
    exact fderiv_spatialSlice hΦ1 s x v
  rw [hfun]
  -- Right side: differentiate `y ↦ dΦ_{(t,y)}(1, 0)` in `y`.
  have hRinner : HasFDerivAt (fun p : ℝ × E₁ => fderiv ℝ Φ p (1, 0))
      (D.flip ((1 : ℝ), (0 : E₁))) (t, x) := by
    simpa using (hd2 (t, x)).clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : E₁)) (t, x))
  have hRcomp : HasFDerivAt
      ((fun p : ℝ × E₁ => fderiv ℝ Φ p (1, 0)) ∘ fun y : E₁ => (t, y))
      ((D.flip ((1 : ℝ), (0 : E₁))).comp (ContinuousLinearMap.inr ℝ ℝ E₁)) x :=
    hRinner.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  have hR : HasFDerivAt (timeVelocity Φ t)
      ((D.flip ((1 : ℝ), (0 : E₁))).comp (ContinuousLinearMap.inr ℝ ℝ E₁)) x := hRcomp
  have hRv : fderiv ℝ (timeVelocity Φ t) x v = D ((0 : ℝ), v) ((1 : ℝ), (0 : E₁)) := by
    rw [hR.fderiv]
    rfl
  -- The two agree by symmetry of the second derivative.
  have hsymm : D ((1 : ℝ), (0 : E₁)) ((0 : ℝ), v) = D ((0 : ℝ), v) ((1 : ℝ), (0 : E₁)) :=
    second_derivative_symmetric hd1 (hd2 (t, x)) _ _
  rw [hRv, ← hsymm]
  convert hLd using 1
  rfl

/-- **Commutation of the spatial and time derivatives, local form.**

Only `ContDiffAt` at the point is required. This matters for manifold data: a chart
representation `fun y => f ((extChartAt I x).symm y)` is smooth on the chart target and
nowhere else, so a global hypothesis would be unusable.

Both sides are the mixed second derivative of `Φ` in the two orders, so the proof is
`second_derivative_symmetric_of_eventually`. -/
theorem hasDerivAt_fderiv_spatialSlice_of_contDiffAt
    {Φ : ℝ × E₁ → E} {t : ℝ} {x : E₁} (hΦ : ContDiffAt ℝ 2 Φ (t, x)) (v : E₁) :
    HasDerivAt (fun s => fderiv ℝ (spatialSlice Φ s) x v)
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
  have hLinner : HasFDerivAt (fun p : ℝ × E₁ => fderiv ℝ Φ p (0, v))
      (D.flip (0, v)) (t, x) := by
    simpa using hd2.clm_apply (hasFDerivAt_const ((0 : ℝ), v) (t, x))
  have hLcomp : HasFDerivAt
      ((fun p : ℝ × E₁ => fderiv ℝ Φ p (0, v)) ∘ fun s : ℝ => (s, x))
      ((D.flip (0, v)).comp (ContinuousLinearMap.inl ℝ ℝ E₁)) t :=
    hLinner.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)
  have hL : HasFDerivAt (fun s : ℝ => fderiv ℝ Φ (s, x) (0, v))
      ((D.flip (0, v)).comp (ContinuousLinearMap.inl ℝ ℝ E₁)) t := hLcomp
  have hLd := hL.hasDerivAt
  -- Near `t` the slice derivative agrees with that partial derivative.
  have hmap : Filter.Tendsto (fun s : ℝ => ((s, x) : ℝ × E₁)) (nhds t)
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
  have hRinner : HasFDerivAt (fun p : ℝ × E₁ => fderiv ℝ Φ p (1, 0))
      (D.flip ((1 : ℝ), (0 : E₁))) (t, x) := by
    simpa using hd2.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : E₁)) (t, x))
  have hRcomp : HasFDerivAt
      ((fun p : ℝ × E₁ => fderiv ℝ Φ p (1, 0)) ∘ fun y : E₁ => (t, y))
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
    HasDerivAt (fun s : ℝ => fderiv ℝ Φ (s, x) ((0 : ℝ), v))
      (fderiv ℝ (fderiv ℝ Φ) (t, x) ((1 : ℝ), (0 : E₁)) ((0 : ℝ), v)) t := by
  have hΦ2 : ContDiffAt ℝ 1 (fderiv ℝ Φ) (t, x) := hΦ.fderiv_right (by norm_num)
  have hd2 : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (t, x)) (t, x) :=
    (hΦ2.differentiableAt (by norm_num)).hasFDerivAt
  set D := fderiv ℝ (fderiv ℝ Φ) (t, x) with hD
  have hinner : HasFDerivAt (fun p : ℝ × E₁ => fderiv ℝ Φ p ((0 : ℝ), v))
      (D.flip ((0 : ℝ), v)) (t, x) := by
    simpa using hd2.clm_apply (hasFDerivAt_const ((0 : ℝ), v) (t, x))
  have hcomp : HasFDerivAt
      ((fun p : ℝ × E₁ => fderiv ℝ Φ p ((0 : ℝ), v)) ∘ fun s : ℝ => (s, x))
      ((D.flip ((0 : ℝ), v)).comp (ContinuousLinearMap.inl ℝ ℝ E₁)) t :=
    hinner.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)
  have hL : HasFDerivAt (fun s : ℝ => fderiv ℝ Φ (s, x) ((0 : ℝ), v))
      ((D.flip ((0 : ℝ), v)).comp (ContinuousLinearMap.inl ℝ ℝ E₁)) t := hcomp
  convert hL.hasDerivAt using 1
  rfl

end Commutation

end HuiskenMonotonicity
