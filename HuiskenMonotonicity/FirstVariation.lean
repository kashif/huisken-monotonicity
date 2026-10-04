/-
**The first-variation integrand for the backward heat kernel.**

Huisken's monotonicity proof applies the divergence theorem to the test field

  `Y = ρ F / τ`,

where `ρ` is the backward heat kernel and `τ = t₀ - t`. This file computes the pointwise
tangential divergence of that field, which is the integrand the divergence theorem is
applied to.

The computation has two inputs, both already available: the product rule
`tangentialDivergence_smul` together with `div_M F = n`, and the spatial gradient of
the kernel, `dρ_x(v) = -(ρ(x)/(2τ)) ⟪x, v⟫`. The result is

  `div_M (ρ • F) = ρ (n - ‖F^⊥‖²_T / (2τ))`,

where the tangential squared norm appears through `tangentialNormSq`, so no orthogonal
projection is constructed anywhere.

Combining this with the divergence theorem `∫ div_M Y dμ = -∫ ⟪Y, Hvec⟫ dμ` yields the
first-variation identity

  `∫ ρ (n - ‖F^T‖²/(2τ) + ⟪Hvec, F⟫) dμ = 0`,

which is the hypothesis `hFirstVar` of `Monotonicity.lean`.
-/

import HuiskenMonotonicity.TangentialCalculus
import HuiskenMonotonicity.HeatKernel

namespace HuiskenMonotonicity

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-! ## The spatial gradient of the kernel, in Fréchet form -/

/-- The spatial differential of the backward heat kernel:

  `dρ_x(v) = -(ρ(x)/(2τ)) ⟪x, v⟫`.

`hasDerivAt_backwardHeatKernel_dir` gives this as a derivative along a line; this is the
same fact as a Fréchet derivative, obtained by composing with that line. -/
theorem fderiv_backwardHeatKernel
    (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀) (x v : E) :
    fderiv ℝ (fun y : E => backwardHeatKernel m t₀ t y) x v =
      -(backwardHeatKernel m t₀ t x / (2 * (t₀ - t))) * @inner ℝ E _ x v := by
  have hdiff : HasFDerivAt (fun y : E => backwardHeatKernel m t₀ t y)
      (fderiv ℝ (fun y : E => backwardHeatKernel m t₀ t y) x) x :=
    ((contDiff_backwardHeatKernel m t₀ hτ).differentiable (by norm_num) x).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hbase : x + (0 : ℝ) • v = x := by simp
  have hdiff' : HasFDerivAt (fun y : E => backwardHeatKernel m t₀ t y)
      (fderiv ℝ (fun y : E => backwardHeatKernel m t₀ t y) x) (x + (0 : ℝ) • v) := by
    rw [hbase]; exact hdiff
  have hcomp := hdiff'.comp_hasDerivAt 0 hline
  exact hcomp.unique (hasDerivAt_backwardHeatKernel_dir m t₀ hτ x v)

/-- The kernel pulled back along `F`, differentiated in a coordinate direction. -/
theorem fderiv_backwardHeatKernel_comp
    (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀)
    {F : E₁ → E} (b : Idx → E₁) (x : E₁)
    (hF : DifferentiableAt ℝ F x) (i : Idx) :
    fderiv ℝ (fun y => backwardHeatKernel m t₀ t (F y)) x (b i) =
      -(backwardHeatKernel m t₀ t (F x) / (2 * (t₀ - t))) *
        @inner ℝ E _ (F x) (frameTangent F b x i) := by
  have hρ : DifferentiableAt ℝ (fun y : E => backwardHeatKernel m t₀ t y) (F x) :=
    (contDiff_backwardHeatKernel m t₀ hτ).differentiable (by norm_num) (F x)
  have h : HasFDerivAt (fun y => backwardHeatKernel m t₀ t (F y))
      ((fderiv ℝ (fun y : E => backwardHeatKernel m t₀ t y) (F x)).comp (fderiv ℝ F x)) x :=
    hρ.hasFDerivAt.comp x hF.hasFDerivAt
  rw [h.fderiv]
  simpa using fderiv_backwardHeatKernel m t₀ hτ (F x) (frameTangent F b x i)

/-! ## The divergence of the test field -/

/-- Contracting the tangential gradient of the kernel against the position vector produces
the tangential squared norm:

  `⟪∇_M ρ, F⟫ = -(ρ/(2τ)) ‖F^T‖²`. -/
theorem inner_tangentialGradient_backwardHeatKernel
    (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀)
    {F : E₁ → E} (b : Idx → E₁) (gInv : Idx → Idx → ℝ) (x : E₁)
    (hF : DifferentiableAt ℝ F x) :
    @inner ℝ E _
        (tangentialGradient F (fun y => backwardHeatKernel m t₀ t (F y)) b gInv x)
        (F x) =
      -(backwardHeatKernel m t₀ t (F x) / (2 * (t₀ - t))) *
        tangentialNormSq F b gInv x (F x) := by
  rw [inner_tangentialGradient, tangentialNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_backwardHeatKernel_comp m t₀ hτ b x hF i,
    real_inner_comm (frameTangent F b x j) (F x)]
  ring

/-- **The divergence of Huisken's test field.**

  `div_M (ρ • F) = ρ (n - ‖F^T‖² / (2τ))`.

This is the integrand to which the divergence theorem is applied. The tangential squared
norm enters through `tangentialNormSqAlong`, so no orthogonal projection is constructed. -/
theorem tangentialDivergence_backwardHeatKernel_smul_position
    (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀)
    {F : E₁ → E} (b : Idx → E₁) {gInv : Idx → Idx → ℝ} (x : E₁)
    (hF : DifferentiableAt ℝ F x)
    (hinv : IsFrameInverse F b x gInv) :
    tangentialDivergence F
        (fun y => backwardHeatKernel m t₀ t (F y) • F y) b gInv x =
      backwardHeatKernel m t₀ t (F x) *
        ((Fintype.card Idx : ℝ) -
          tangentialNormSq F b gInv x (F x) / (2 * (t₀ - t))) := by
  have hρF : DifferentiableAt ℝ (fun y => backwardHeatKernel m t₀ t (F y)) x :=
    ((contDiff_backwardHeatKernel m t₀ hτ).differentiable (by norm_num)
      (F x)).comp x hF
  rw [tangentialDivergence_smul F b gInv hρF hF,
    tangentialDivergence_self F b hinv,
    inner_tangentialGradient_backwardHeatKernel m t₀ hτ b gInv x hF]
  ring

end HuiskenMonotonicity
