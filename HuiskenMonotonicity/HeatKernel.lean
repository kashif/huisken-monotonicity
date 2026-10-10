/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The backward heat kernel

The backward heat kernel used in Huisken's monotonicity formula.

For a hypersurface dimension `n`, base time `t₀`, current time `t < t₀`, and ambient point
`x` in an inner product space, define

  ρ(x, t) = (4π(t₀ - t))^(-n/2) · exp(-‖x‖² / (4(t₀ - t))).

Note that the exponent `-n/2` matches the *hypersurface* dimension, not the ambient
dimension; this is what makes ∫ ρ dμ ≡ 1 over an `n`-plane through the origin and is the
normalisation used in Huisken (1990), J. Differential Geom. 31, 285–299.
-/

namespace HuiskenMonotonicity

open Real

/-- Backward heat kernel for `n`-dimensional hypersurface flow, centred at `(0, t₀)`,
evaluated at `(x, t)`. For `t < t₀`,

  `backwardHeatKernel n t₀ t x = (4π(t₀-t))^(-n/2) · exp(-‖x‖² / (4(t₀-t)))`.

For `t ≥ t₀` the formula becomes singular; we still write down the same algebraic
expression and only assert non-trivial properties under `t < t₀`. -/
noncomputable def backwardHeatKernel
    {E : Type*} [SeminormedAddCommGroup E] (n : ℕ) (t₀ t : ℝ) (x : E) : ℝ :=
  (4 * π * (t₀ - t)) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * (t₀ - t)))

section Positivity

variable {E : Type*} [SeminormedAddCommGroup E] {n : ℕ} {t₀ t : ℝ}

lemma backwardHeatKernel_pos (hτ : t < t₀) (x : E) :
    0 < backwardHeatKernel n t₀ t x := by
  unfold backwardHeatKernel
  have h : (0 : ℝ) < 4 * π * (t₀ - t) := by
    have : 0 < t₀ - t := sub_pos.mpr hτ
    positivity
  exact mul_pos (Real.rpow_pos_of_pos h _) (Real.exp_pos _)

end Positivity

/-! ## Derivative identities

These are the analytic facts Huisken uses in §3:

* the gradient in the spatial variable is `∇_x ρ = -ρ · x / (2τ)`;
* the partial time derivative is `∂_t ρ = ρ · (n/(2τ) - ‖x‖²/(4τ²))`;
* hence `ρ` satisfies the *backward* heat equation `∂_t ρ + Δ_x ρ = 0`.

The combinatorial identity used in the rescaled monotonicity formula (Corollary 3.2) is
the algebraic content

  `∂_t ρ + ⟨H, ∇_x ρ⟩ - H² ρ = -ρ · |H + F^⊥/(2τ)|² + ρ · |F^T|²/(4τ²) - ρ · n/(2τ)`,

evaluated along the immersed surface; the tangential `|F^T|²/(4τ²)` is then absorbed by
the divergence theorem on `M_t` (first variation formula) to leave the clean form

  `(d/dt) ∫_{M_t} ρ dμ_t = -∫_{M_t} ρ · |H + F^⊥/(2τ)|² dμ_t`.

Only the first three statements are about the kernel itself; the fourth is the
geometric step, carried out in `MeanCurvatureFlow.lean`. -/

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (n : ℕ) (t₀ : ℝ)

omit [InnerProductSpace ℝ E] in
/-- Time-derivative of the backward heat kernel at fixed `x`. -/
theorem hasDerivAt_backwardHeatKernel_time {t : ℝ} (hτ : t < t₀) (x : E) :
    HasDerivAt (fun t' => backwardHeatKernel n t₀ t' x)
      (backwardHeatKernel n t₀ t x *
        ((n : ℝ) / (2 * (t₀ - t)) - ‖x‖ ^ 2 / (4 * (t₀ - t) ^ 2))) t := by
  -- Decomposition: ρ(t') = A(t') · B(t') with
  --   A(t') = (4π(t₀-t'))^(-n/2),  B(t') = exp(-‖x‖²/(4(t₀-t'))).
  have hτ_pos : (0 : ℝ) < t₀ - t := sub_pos.mpr hτ
  have hτ_ne : (t₀ - t) ≠ 0 := ne_of_gt hτ_pos
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have hu_pos : (0 : ℝ) < 4 * π * (t₀ - t) := by positivity
  have hu_ne : 4 * π * (t₀ - t) ≠ 0 := ne_of_gt hu_pos
  -- u(t') = 4π(t₀-t'),  u'(t) = -4π.
  have hu : HasDerivAt (fun t' : ℝ => 4 * π * (t₀ - t')) (-(4 * π)) t := by
    have h1 : HasDerivAt (fun t' : ℝ => t₀ - t') (-1 : ℝ) t :=
      (hasDerivAt_id t).const_sub t₀
    simpa using h1.const_mul (4 * π)
  -- A(t') = u(t')^c with c = -n/2; chain rule via `Real.hasDerivAt_rpow_const`.
  set c : ℝ := -(n : ℝ) / 2 with hc_def
  have hA :
      HasDerivAt (fun t' : ℝ => (4 * π * (t₀ - t')) ^ c)
        (c * (4 * π * (t₀ - t)) ^ (c - 1) * -(4 * π)) t := by
    have hrp :
        HasDerivAt (fun y : ℝ => y ^ c)
          (c * (4 * π * (t₀ - t)) ^ (c - 1)) (4 * π * (t₀ - t)) :=
      Real.hasDerivAt_rpow_const (Or.inl hu_ne)
    exact hrp.comp t hu
  -- v(t') = -‖x‖² / (4(t₀-t')),  v'(t) = -‖x‖² / (4(t₀-t)²).
  have hw_ne : (4 : ℝ) * (t₀ - t) ≠ 0 := by positivity
  have hw : HasDerivAt (fun t' : ℝ => 4 * (t₀ - t')) (-(4 : ℝ)) t := by
    have h1 : HasDerivAt (fun t' : ℝ => t₀ - t') (-1 : ℝ) t :=
      (hasDerivAt_id t).const_sub t₀
    simpa using h1.const_mul (4 : ℝ)
  have hv :
      HasDerivAt (fun t' : ℝ => -‖x‖ ^ 2 / (4 * (t₀ - t')))
        (-‖x‖ ^ 2 / (4 * (t₀ - t) ^ 2)) t := by
    have hc' : HasDerivAt (fun _ : ℝ => -‖x‖ ^ 2) (0 : ℝ) t := hasDerivAt_const _ _
    have hd := hc'.div hw hw_ne
    convert hd using 1
    field_simp
    ring
  -- B(t') = exp(v(t')),  B'(t) = exp(v(t)) · v'(t).
  have hB :
      HasDerivAt (fun t' : ℝ => Real.exp (-‖x‖ ^ 2 / (4 * (t₀ - t'))))
        (Real.exp (-‖x‖ ^ 2 / (4 * (t₀ - t))) *
          (-‖x‖ ^ 2 / (4 * (t₀ - t) ^ 2))) t :=
    hv.exp
  -- Product rule.
  have h_prod := hA.mul hB
  -- Match function and derivative to the target.
  have h_fun :
      (fun t' : ℝ => backwardHeatKernel n t₀ t' x) =
        fun t' : ℝ =>
          (4 * π * (t₀ - t')) ^ c *
            Real.exp (-‖x‖ ^ 2 / (4 * (t₀ - t'))) := by
    funext t'; rfl
  rw [h_fun]
  convert h_prod using 1
  -- Reduce `(4π(t₀-t))^(c-1)` to `(4π(t₀-t))^c / (4π(t₀-t))`.
  have h_pow :
      (4 * π * (t₀ - t)) ^ (c - 1) =
        (4 * π * (t₀ - t)) ^ c / (4 * π * (t₀ - t)) :=
    Real.rpow_sub_one hu_ne c
  unfold backwardHeatKernel
  rw [h_pow, hc_def]
  field_simp
  ring

/-- Directional derivative of the backward heat kernel at fixed `t`, in the form
of a derivative along the parameterised line `s ↦ x + s • v`.

The directional derivative in direction `v` equals `-(1/(2(t₀-t))) · ⟨x, v⟩ · ρ(x, t)`;
the gradient (as an element of `E`) is therefore `-x/(2(t₀-t)) · ρ(x,t)`. -/
theorem hasDerivAt_backwardHeatKernel_dir {t : ℝ} (hτ : t < t₀) (x v : E) :
    HasDerivAt (fun s : ℝ => backwardHeatKernel n t₀ t (x + s • v))
      (- (backwardHeatKernel n t₀ t x / (2 * (t₀ - t))) * @inner ℝ E _ x v) 0 := by
  have hτ_pos : (0 : ℝ) < t₀ - t := sub_pos.mpr hτ
  have hτ_ne : (t₀ - t) ≠ 0 := ne_of_gt hτ_pos
  -- Polynomial expansion ‖x + s•v‖² = ‖x‖² + 2⟨x,v⟩·s + ‖v‖²·s²
  have h_norm_sq : ∀ s : ℝ,
      ‖x + s • v‖ ^ 2 = ‖x‖ ^ 2 + 2 * @inner ℝ E _ x v * s + ‖v‖ ^ 2 * s ^ 2 := by
    intro s
    rw [@norm_add_sq_real E _ _ x (s • v), real_inner_smul_right,
        norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  -- Step 1: derivative of the exponent  s ↦ -‖x + s•v‖² / (4(t₀-t))  at 0.
  have h_expo :
      HasDerivAt (fun s : ℝ => -‖x + s • v‖ ^ 2 / (4 * (t₀ - t)))
        (-(@inner ℝ E _ x v) / (2 * (t₀ - t))) 0 := by
    have h_eq :
        (fun s : ℝ => -‖x + s • v‖ ^ 2 / (4 * (t₀ - t))) =
          fun s : ℝ =>
            -‖x‖ ^ 2 / (4 * (t₀ - t)) +
              -(@inner ℝ E _ x v) / (2 * (t₀ - t)) * s +
                -‖v‖ ^ 2 / (4 * (t₀ - t)) * s ^ 2 := by
      funext s
      rw [h_norm_sq s]
      field_simp
      ring
    rw [h_eq]
    have h_const : HasDerivAt (fun _ : ℝ => -‖x‖ ^ 2 / (4 * (t₀ - t))) 0 0 :=
      hasDerivAt_const _ _
    have h_lin :
        HasDerivAt (fun s : ℝ => -(@inner ℝ E _ x v) / (2 * (t₀ - t)) * s)
          (-(@inner ℝ E _ x v) / (2 * (t₀ - t))) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul
        (-(@inner ℝ E _ x v) / (2 * (t₀ - t)))
    have h_quad :
        HasDerivAt (fun s : ℝ => -‖v‖ ^ 2 / (4 * (t₀ - t)) * s ^ 2) 0 0 := by
      have hp : HasDerivAt (fun s : ℝ => s ^ 2) ((2 : ℕ) * (0 : ℝ) ^ (2 - 1)) 0 :=
        hasDerivAt_pow 2 0
      have := hp.const_mul (-‖v‖ ^ 2 / (4 * (t₀ - t)))
      simpa using this
    convert (h_const.add h_lin).add h_quad using 1
    all_goals
      try rfl
      try simp only [Pi.add_apply]
      try ring
  -- Step 2: compose with exp.
  have h_exp :
      HasDerivAt (fun s : ℝ => Real.exp (-‖x + s • v‖ ^ 2 / (4 * (t₀ - t))))
        (Real.exp (-‖x‖ ^ 2 / (4 * (t₀ - t))) *
          (-(@inner ℝ E _ x v) / (2 * (t₀ - t)))) 0 := by
    have hk := h_expo.exp
    -- value at 0: -‖x + 0•v‖² / … = -‖x‖² / …
    have h0 : -‖x + (0 : ℝ) • v‖ ^ 2 / (4 * (t₀ - t)) = -‖x‖ ^ 2 / (4 * (t₀ - t)) := by
      simp
    rw [h0] at hk
    exact hk
  -- Step 3: multiply by the constant prefactor C = (4π(t₀-t))^(-n/2).
  have h_prod :
      HasDerivAt
        (fun s : ℝ =>
          (4 * π * (t₀ - t)) ^ (-(n : ℝ) / 2) *
            Real.exp (-‖x + s • v‖ ^ 2 / (4 * (t₀ - t))))
        ((4 * π * (t₀ - t)) ^ (-(n : ℝ) / 2) *
          (Real.exp (-‖x‖ ^ 2 / (4 * (t₀ - t))) *
            (-(@inner ℝ E _ x v) / (2 * (t₀ - t))))) 0 :=
    h_exp.const_mul _
  -- Match the target expression.
  have h_fun :
      (fun s : ℝ => backwardHeatKernel n t₀ t (x + s • v)) =
        fun s : ℝ =>
          (4 * π * (t₀ - t)) ^ (-(n : ℝ) / 2) *
            Real.exp (-‖x + s • v‖ ^ 2 / (4 * (t₀ - t))) := by
    funext s; rfl
  rw [h_fun]
  convert h_prod using 1
  unfold backwardHeatKernel
  field_simp

/-- First derivative of `ρ` along the line `s' ↦ x + s'•v`, evaluated at *any* point
`s`, not just `s = 0`. The value at the base point shifts to `x + s•v`, but the formula
is otherwise identical to `hasDerivAt_backwardHeatKernel_dir`. Obtained from the latter
by reparametrising `s' ↦ s' - s`. -/
theorem hasDerivAt_backwardHeatKernel_along {t : ℝ} (hτ : t < t₀) (x v : E) (s : ℝ) :
    HasDerivAt (fun s' : ℝ => backwardHeatKernel n t₀ t (x + s' • v))
      (- (backwardHeatKernel n t₀ t (x + s • v) / (2 * (t₀ - t))) *
        @inner ℝ E _ (x + s • v) v) s := by
  -- Apply the at-zero lemma at the translated base point `x + s • v`.
  have h := hasDerivAt_backwardHeatKernel_dir n t₀ hτ (x + s • v) v
  -- Reparametrise: `s' ↦ s' - s` has derivative 1 at `s` and maps `s` to `0`.
  have h_sub : HasDerivAt (fun s' : ℝ => s' - s) 1 s :=
    (hasDerivAt_id s).sub_const s
  have h_comp := HasDerivAt.comp_of_eq s h h_sub (sub_self s).symm
  -- `(x + s•v) + (s' - s)•v = x + s'•v` — collapse the composed function.
  have h_fun_eq :
      (fun s_1 : ℝ => backwardHeatKernel n t₀ t (x + s • v + s_1 • v)) ∘
          (fun s' : ℝ => s' - s) =
        fun s' : ℝ => backwardHeatKernel n t₀ t (x + s' • v) := by
    funext s'
    change backwardHeatKernel n t₀ t (x + s • v + (s' - s) • v) =
        backwardHeatKernel n t₀ t (x + s' • v)
    congr 1
    rw [sub_smul]
    abel
  rw [h_fun_eq, mul_one] at h_comp
  exact h_comp

/-- Second directional derivative of `ρ` at `s = 0` along the line `s' ↦ x + s'•v`.

Differentiating `s' ↦ ρ(x + s'•v)` twice and evaluating at `0` gives

  `ρ(x) · (⟨x, v⟩² / (4τ²) − ‖v‖² / (2τ))`,

which (when `v` ranges over an orthonormal basis and we sum) is exactly `−Δρ`. The
proof is the product rule applied to phase-1's first-derivative formula. -/
theorem iteratedDeriv_two_backwardHeatKernel_along {t : ℝ} (hτ : t < t₀) (x v : E) :
    iteratedDeriv 2 (fun s' : ℝ => backwardHeatKernel n t₀ t (x + s' • v)) 0 =
      backwardHeatKernel n t₀ t x *
        ((@inner ℝ E _ x v) ^ 2 / (4 * (t₀ - t) ^ 2) -
          ‖v‖ ^ 2 / (2 * (t₀ - t))) := by
  have hτ_pos : (0 : ℝ) < t₀ - t := sub_pos.mpr hτ
  have hτ_ne : (t₀ - t) ≠ 0 := ne_of_gt hτ_pos
  -- Step 1: identify `deriv (fun s' => ρ(x + s'•v))` with the explicit function `G`.
  set G : ℝ → ℝ := fun s =>
    -(backwardHeatKernel n t₀ t (x + s • v) / (2 * (t₀ - t))) *
      @inner ℝ E _ (x + s • v) v with hG_def
  have h_first_at : ∀ s : ℝ,
      HasDerivAt (fun s' : ℝ => backwardHeatKernel n t₀ t (x + s' • v)) (G s) s :=
    fun s => hasDerivAt_backwardHeatKernel_along n t₀ hτ x v s
  have h_deriv_eq :
      deriv (fun s' : ℝ => backwardHeatKernel n t₀ t (x + s' • v)) = G :=
    funext (fun s => (h_first_at s).deriv)
  -- Step 2: differentiate `G` at `0`. Combine: derivative of `s ↦ ρ(x + s•v)` (phase 1
  -- at `s = 0`) and derivative of `s ↦ ⟨x + s•v, v⟩` (linear in `s` with slope `‖v‖²`).
  have h_rho0 :
      HasDerivAt (fun s : ℝ => backwardHeatKernel n t₀ t (x + s • v))
        (-(backwardHeatKernel n t₀ t x / (2 * (t₀ - t))) * @inner ℝ E _ x v) 0 :=
    hasDerivAt_backwardHeatKernel_dir n t₀ hτ x v
  have h_inner :
      HasDerivAt (fun s : ℝ => @inner ℝ E _ (x + s • v) v) (‖v‖ ^ 2) 0 := by
    -- ⟨x + s•v, v⟩ = ⟨x, v⟩ + s · ‖v‖²; derivative of the affine RHS in `s` is `‖v‖²`.
    have h_lin : HasDerivAt (fun s : ℝ => s * ‖v‖ ^ 2) (‖v‖ ^ 2) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (‖v‖ ^ 2)
    have h_affine :
        HasDerivAt (fun s : ℝ => @inner ℝ E _ x v + s * ‖v‖ ^ 2) (‖v‖ ^ 2) 0 :=
      h_lin.const_add (@inner ℝ E _ x v)
    -- Transport along the pointwise identity.
    have h_eq :
        (fun s : ℝ => @inner ℝ E _ x v + s * ‖v‖ ^ 2) =
          fun s : ℝ => @inner ℝ E _ (x + s • v) v := by
      funext s
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [h_eq] at h_affine
    exact h_affine
  -- Product rule on `s ↦ ρ(x + s•v) · ⟨x + s•v, v⟩`.
  have h_prod := h_rho0.mul h_inner
  -- Multiply by the constant `-1/(2(t₀ - t))` to get `G`.
  have h_G_zero : HasDerivAt G
      (backwardHeatKernel n t₀ t x *
        ((@inner ℝ E _ x v) ^ 2 / (4 * (t₀ - t) ^ 2) -
          ‖v‖ ^ 2 / (2 * (t₀ - t)))) 0 := by
    have h_factor :
        G = fun s : ℝ =>
          (-1 / (2 * (t₀ - t))) *
            (backwardHeatKernel n t₀ t (x + s • v) * @inner ℝ E _ (x + s • v) v) := by
      funext s
      rw [hG_def]
      ring
    rw [h_factor]
    have h_scaled := h_prod.const_mul (-1 / (2 * (t₀ - t)))
    convert h_scaled using 1
    -- value at 0: x + 0•v = x.
    simp only [zero_smul, add_zero]
    field_simp
    ring
  -- Step 3: assemble via `iteratedDeriv 2 = deriv ∘ deriv`.
  have h_iter :
      iteratedDeriv 2 (fun s' : ℝ => backwardHeatKernel n t₀ t (x + s' • v)) =
        deriv (deriv (fun s' : ℝ => backwardHeatKernel n t₀ t (x + s' • v))) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h_iter, h_deriv_eq]
  exact h_G_zero.deriv

end Derivatives

/-! ## Bridge: line second derivative ↔ iterated Fréchet derivative

For a `C²` real-valued function `f` on a real normed space `V`, the second derivative of
the curve `s ↦ f(x + s · v)` at `s = 0` equals the iterated Fréchet derivative
`(D²f)(x)` applied to the pair `(v, v)`. This generic fact is the link between our
line-based computation (`iteratedDeriv_two_backwardHeatKernel_along`) and mathlib's
abstract Laplacian (`InnerProductSpace.laplacian`), which is built on
`iteratedFDeriv ℝ 2 f x ![eᵢ, eᵢ]`. -/

section LaplacianBridge

/-- For a `C²` function `f : V → F`, the second derivative of `s ↦ f(x + s·v)` at
`s = 0` equals `iteratedFDeriv ℝ 2 f x` applied to `(v, v)`. -/
theorem iteratedDeriv_two_along_eq_iteratedFDeriv_two
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : V → F) (hf : ContDiff ℝ 2 f) (x v : V) :
    iteratedDeriv 2 (fun s : ℝ => f (x + s • v)) 0 =
      iteratedFDeriv ℝ 2 f x ![v, v] := by
  -- Line map S : ℝ →L[ℝ] V, s ↦ s • v.
  let S : ℝ →L[ℝ] V := (1 : ℝ →L[ℝ] ℝ).smulRight v
  have hS_apply : ∀ s : ℝ, S s = s • v := fun s => by simp [S]
  have hS_zero : S 0 = 0 := by simp [hS_apply]
  have hS_one : S 1 = v := by simp [hS_apply]
  -- The shifted function g(z) = f(x + z) is `C²` if `f` is.
  have h_shift_contDiff : ContDiff ℝ 2 (fun z : V => f (x + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  -- Rewrite the curve as `(g) ∘ S`.
  have h_curve_eq : (fun s : ℝ => f (x + s • v)) = (fun z : V => f (x + z)) ∘ S := by
    funext s
    change f (x + s • v) = f (x + S s)
    rw [hS_apply]
  -- Unfold `iteratedDeriv 2 = iteratedFDeriv ℝ 2 ... applied at (1, 1)`.
  rw [h_curve_eq, iteratedDeriv_eq_iteratedFDeriv,
      ContinuousLinearMap.iteratedFDeriv_comp_right S h_shift_contDiff 0 le_rfl,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      iteratedFDeriv_comp_add_left, hS_zero, add_zero]
  -- Goal: `(iteratedFDeriv ℝ 2 f x) (fun i => S 1) = (iteratedFDeriv ℝ 2 f x) ![v, v]`.
  congr 1
  funext i
  fin_cases i <;> simp [hS_one]

end LaplacianBridge

/-! ## Backward heat equation in coordinates

Combining the time and second-directional-derivative identities, we show that on
`EuclideanSpace ℝ (Fin n)` the kernel satisfies

  `∂_t ρ + Σᵢ ∂²ᵢ ρ = 0`,

where the spatial sum runs over the standard orthonormal basis. With the bridge
lemma above, this can also be stated as `∂_t ρ + Δρ = 0` against mathlib's
coordinate-free Laplacian. -/

section HeatEquation

open Finset

/-- Backward heat equation: `∂_t ρ + Σᵢ ∂²ᵢ ρ = 0` on `EuclideanSpace ℝ (Fin n)`,
where the spatial sum runs over the standard orthonormal basis. -/
theorem backwardHeatEquation_euclidean
    {n : ℕ} {t₀ t : ℝ} (hτ : t < t₀) (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun t' : ℝ => backwardHeatKernel n t₀ t' x) t +
        ∑ i : Fin n,
          iteratedDeriv 2
            (fun s : ℝ =>
              backwardHeatKernel n t₀ t (x + s • EuclideanSpace.single i (1 : ℝ)))
            0 = 0 := by
  have hτ_pos : (0 : ℝ) < t₀ - t := sub_pos.mpr hτ
  have hτ_ne : (t₀ - t) ≠ 0 := ne_of_gt hτ_pos
  -- ∂_t ρ.
  have h_time :=
    (hasDerivAt_backwardHeatKernel_time n t₀ hτ x).deriv
  -- Each second partial along eᵢ: substitute v = single i 1 in phase 2,
  -- then use ⟨x, eᵢ⟩ = x i and ‖eᵢ‖ = 1.
  have h_part : ∀ i : Fin n,
      iteratedDeriv 2
          (fun s : ℝ =>
            backwardHeatKernel n t₀ t (x + s • EuclideanSpace.single i (1 : ℝ)))
          0 =
        backwardHeatKernel n t₀ t x *
          ((x i) ^ 2 / (4 * (t₀ - t) ^ 2) - 1 / (2 * (t₀ - t))) := by
    intro i
    rw [iteratedDeriv_two_backwardHeatKernel_along n t₀ hτ x
          (EuclideanSpace.single i (1 : ℝ))]
    have h_inner : @inner ℝ _ _ x (EuclideanSpace.single i (1 : ℝ)) = x i := by
      simpa using (EuclideanSpace.inner_single_right (𝕜 := ℝ) i 1 x)
    have h_norm_sq : ‖EuclideanSpace.single i (1 : ℝ)‖ ^ 2 = 1 := by simp
    rw [h_inner, h_norm_sq]
  rw [h_time, sum_congr rfl (fun i _ => h_part i)]
  -- Pull ρ out of the sum and split into the `xᵢ²/(4τ²)` and `1/(2τ)` pieces.
  rw [← mul_sum, sum_sub_distrib]
  -- ∑ᵢ xᵢ²/(4τ²) = (∑ᵢ xᵢ²)/(4τ²) = ‖x‖²/(4τ²);  ∑ᵢ 1/(2τ) = n/(2τ).
  rw [← sum_div, ← sum_div, sum_const, card_univ, Fintype.card_fin]
  rw [show ∑ i : Fin n, (x i) ^ 2 = ‖x‖ ^ 2 from (EuclideanSpace.real_norm_sq_eq x).symm]
  -- Final algebra: ρ · (n/(2τ) − ‖x‖²/(4τ²)) + ρ · (‖x‖²/(4τ²) − n · 1/(2τ)) = 0.
  field_simp
  ring

/-- Smoothness of the kernel in the spatial variable: for any inner product space `V`
and any `t < t₀`, `x ↦ ρ(x, t)` is `C^∞`. Used to invoke the bridge lemma. -/
theorem contDiff_backwardHeatKernel
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (n : ℕ) (t₀ : ℝ) {t : ℝ} (_hτ : t < t₀) :
    ContDiff ℝ ⊤ (fun x : V => backwardHeatKernel n t₀ t x) := by
  unfold backwardHeatKernel
  -- (4πτ)^(-n/2) · exp(-‖x‖²/(4τ)) — constant times an exp of a smooth function.
  exact contDiff_const.mul
    (Real.contDiff_exp.comp (((contDiff_norm_sq ℝ).neg).div_const _))

end HeatEquation

/-! ## Backward heat equation against mathlib's Laplacian

Bridging the coordinate computation above to mathlib's coordinate-free
`InnerProductSpace.laplacian Δ`. -/

section LaplacianForm

open InnerProductSpace
open scoped InnerProductSpace

/-- The Laplacian of the backward heat kernel on `EuclideanSpace ℝ (Fin n)`. -/
theorem laplacian_backwardHeatKernel
    {n : ℕ} {t₀ t : ℝ} (hτ : t < t₀) (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => backwardHeatKernel n t₀ t y) x =
      backwardHeatKernel n t₀ t x *
        (‖x‖ ^ 2 / (4 * (t₀ - t) ^ 2) - (n : ℝ) / (2 * (t₀ - t))) := by
  have hτ_pos : (0 : ℝ) < t₀ - t := sub_pos.mpr hτ
  have hτ_ne : (t₀ - t) ≠ 0 := ne_of_gt hτ_pos
  -- Express Δ via the orthonormal basis formula, using the standard basis of EuclideanSpace.
  rw [show Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => backwardHeatKernel n t₀ t y) x
        = ∑ i,
            iteratedFDeriv ℝ 2
              (fun y : EuclideanSpace ℝ (Fin n) => backwardHeatKernel n t₀ t y) x
              ![EuclideanSpace.basisFun (Fin n) ℝ i,
                EuclideanSpace.basisFun (Fin n) ℝ i] from
      congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _
        (EuclideanSpace.basisFun (Fin n) ℝ)) x]
  -- Each term: bridge to the line second derivative, then phase 2 + simplification.
  have h_term : ∀ i : Fin n,
      iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => backwardHeatKernel n t₀ t y)
          x ![EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ i] =
        backwardHeatKernel n t₀ t x *
          ((x i) ^ 2 / (4 * (t₀ - t) ^ 2) - 1 / (2 * (t₀ - t))) := by
    intro i
    have hbasis : (EuclideanSpace.basisFun (Fin n) ℝ i : EuclideanSpace ℝ (Fin n)) =
        EuclideanSpace.single i (1 : ℝ) := by simp
    rw [hbasis]
    rw [← iteratedDeriv_two_along_eq_iteratedFDeriv_two _
          ((contDiff_backwardHeatKernel n t₀ hτ).of_le (by exact_mod_cast le_top)) x
          (EuclideanSpace.single i (1 : ℝ))]
    rw [iteratedDeriv_two_backwardHeatKernel_along n t₀ hτ x
          (EuclideanSpace.single i (1 : ℝ))]
    have h_inner : @inner ℝ _ _ x (EuclideanSpace.single i (1 : ℝ)) = x i := by
      simpa using (EuclideanSpace.inner_single_right (𝕜 := ℝ) i 1 x)
    have h_norm_sq : ‖EuclideanSpace.single i (1 : ℝ)‖ ^ 2 = 1 := by simp
    rw [h_inner, h_norm_sq]
  rw [Finset.sum_congr rfl (fun i _ => h_term i)]
  -- Same algebra as `backwardHeatEquation_euclidean`: collapse Σᵢ xᵢ² = ‖x‖² and Σᵢ 1 = n.
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [show ∑ i : Fin n, (x i) ^ 2 = ‖x‖ ^ 2 from (EuclideanSpace.real_norm_sq_eq x).symm]
  field_simp
  ring

/-- **Backward heat equation** in mathlib's `Δ` form:
`∂_t ρ + Δρ = 0` on `EuclideanSpace ℝ (Fin n)` for `t < t₀`. -/
theorem backwardHeatEquation_laplacian
    {n : ℕ} {t₀ t : ℝ} (hτ : t < t₀) (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun t' : ℝ => backwardHeatKernel n t₀ t' x) t +
      Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => backwardHeatKernel n t₀ t y) x
      = 0 := by
  rw [(hasDerivAt_backwardHeatKernel_time n t₀ hτ x).deriv,
      laplacian_backwardHeatKernel hτ]
  ring

end LaplacianForm

section Normalisation

open MeasureTheory

/-- Total mass of the backward heat kernel over an `n`-dimensional inner product space.

For any finite-dimensional real inner product space `V` with `Module.finrank ℝ V = n`,

  `∫ x : V, ρ(x, t) dx = 1`,

i.e. the kernel `ρ(·, t) = (4πτ)^(-n/2) exp(-‖·‖²/(4τ))` is a probability density on `V`
for every `t < t₀` (with `τ = t₀ - t > 0`). The exponent `-n/2` is precisely the
normalisation that makes this hold. Reduces to `GaussianFourier.integral_rexp_neg_mul_sq_norm`
applied with `b = 1/(4τ)`. -/
theorem integral_backwardHeatKernel
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {n : ℕ} (hn : Module.finrank ℝ V = n)
    {t₀ t : ℝ} (hτ : t < t₀) :
    ∫ x : V, backwardHeatKernel n t₀ t x = 1 := by
  have hτ_pos : (0 : ℝ) < t₀ - t := sub_pos.mpr hτ
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have hu_pos : (0 : ℝ) < 4 * π * (t₀ - t) := by positivity
  have hb_pos : (0 : ℝ) < 1 / (4 * (t₀ - t)) := by positivity
  -- Pull the constant prefactor out of the integral and normalise the integrand into
  -- the form `exp(-b * ‖x‖²)` expected by `GaussianFourier.integral_rexp_neg_mul_sq_norm`.
  have h_integrand :
      (fun x : V => backwardHeatKernel n t₀ t x) =
        fun x : V =>
          (4 * π * (t₀ - t)) ^ (-(n : ℝ) / 2) *
            Real.exp (-(1 / (4 * (t₀ - t))) * ‖x‖ ^ 2) := by
    funext x
    unfold backwardHeatKernel
    congr 1
    congr 1
    field_simp
  rw [h_integrand, integral_const_mul]
  -- Mathlib's multidim Gaussian: `∫ exp(-b‖x‖²) = (π/b)^(finrank/2)`.
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb_pos, hn]
  -- Simplify `π / (1 / (4(t₀-t))) = 4π(t₀-t)`, then `(4πτ)^(-n/2) · (4πτ)^(n/2) = 1`.
  have h_div : π / (1 / (4 * (t₀ - t))) = 4 * π * (t₀ - t) := by
    rw [div_div_eq_mul_div]; ring
  rw [h_div, ← Real.rpow_add hu_pos]
  rw [show (-(n : ℝ) / 2 + (n : ℝ) / 2 : ℝ) = 0 by ring, Real.rpow_zero]

end Normalisation

section JointSmoothness

/-- **Joint smoothness of the kernel in time and space**, on `{t < t₀}`.

`contDiff_backwardHeatKernel` gives smoothness in the spatial variable at a fixed time.
This is the joint statement, which is what a transport formula needs: its regularity
hypotheses are about the integrand as a function on `ℝ × M`.

The restriction to `{t < t₀}` is essential rather than technical: at `t = t₀` the prefactor
`(4π(t₀-t))^(-n/2)` is singular, so no joint statement holds on a neighbourhood of `t₀`. -/
theorem contDiffOn_backwardHeatKernel_prod
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (n : ℕ) (t₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun p : ℝ × V => backwardHeatKernel n t₀ p.1 p.2)
      {p : ℝ × V | p.1 < t₀} := by
  intro p hp
  have hτpos : (0 : ℝ) < t₀ - p.1 := sub_pos.mpr hp
  -- the prefactor
  have hbase : ContDiffAt ℝ ⊤ (fun q : ℝ × V => 4 * π * (t₀ - q.1)) p := by
    exact contDiffAt_const.mul ((contDiffAt_const).sub (contDiff_fst.contDiffAt))
  have hbase_ne : (fun q : ℝ × V => 4 * π * (t₀ - q.1)) p ≠ 0 := by
    have : (0 : ℝ) < 4 * π * (t₀ - p.1) := by positivity
    exact ne_of_gt this
  have hpre : ContDiffAt ℝ ⊤
      (fun q : ℝ × V => (4 * π * (t₀ - q.1)) ^ (-(n : ℝ) / 2)) p :=
    hbase.rpow_const_of_ne hbase_ne
  -- the exponent
  have hden : ContDiffAt ℝ ⊤ (fun q : ℝ × V => 4 * (t₀ - q.1)) p :=
    contDiffAt_const.mul ((contDiffAt_const).sub (contDiff_fst.contDiffAt))
  have hden_ne : (fun q : ℝ × V => 4 * (t₀ - q.1)) p ≠ 0 := by
    have : (0 : ℝ) < 4 * (t₀ - p.1) := by positivity
    exact ne_of_gt this
  have hnum : ContDiffAt ℝ ⊤ (fun q : ℝ × V => -‖q.2‖ ^ 2) p :=
    (contDiff_norm_sq (𝕜 := ℝ)).contDiffAt.comp p contDiff_snd.contDiffAt |>.neg
  have hexparg : ContDiffAt ℝ ⊤
      (fun q : ℝ × V => -‖q.2‖ ^ 2 / (4 * (t₀ - q.1))) p := hnum.div hden hden_ne
  have hexp : ContDiffAt ℝ ⊤
      (fun q : ℝ × V => Real.exp (-‖q.2‖ ^ 2 / (4 * (t₀ - q.1)))) p :=
    Real.contDiff_exp.contDiffAt.comp p hexparg
  exact (hpre.mul hexp).contDiffWithinAt

/-- The set on which the kernel is jointly smooth is open. -/
theorem isOpen_lt_fst_backwardHeatKernel
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (t₀ : ℝ) :
    IsOpen {p : ℝ × V | p.1 < t₀} :=
  isOpen_lt continuous_fst continuous_const

end JointSmoothness

/-! ## The spatial gradient, in Fréchet form -/

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

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

end Gradient

/-! ## The rescaled kernel

Under Huisken's rescaling `F̃ = (2(T - t))^(-1/2) F`, the kernel centred at `(0, T)` becomes,
up to its normalising constant, the time-independent Gaussian `ρ̃(x) = exp(-‖x‖²/2)`
(Huisken 1990, before Corollary 3.2). It is the kernel at `τ = 1/2`. -/

section Rescaled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rescaled kernel `ρ̃(x) = exp(-‖x‖² / 2)`. -/
noncomputable def rescaledHeatKernel (x : E) : ℝ :=
  Real.exp (-‖x‖ ^ 2 / 2)

omit [InnerProductSpace ℝ E] in
lemma rescaledHeatKernel_pos (x : E) : 0 < rescaledHeatKernel x :=
  Real.exp_pos _

omit [InnerProductSpace ℝ E] in
/-- `ρ̃` is the backward heat kernel at `τ = 1/2`, up to the constant `(2π)^(n/2)`. -/
theorem rescaledHeatKernel_eq (n : ℕ) (x : E) :
    rescaledHeatKernel x = (2 * Real.pi) ^ ((n : ℝ) / 2) * backwardHeatKernel n (1 / 2) 0 x := by
  have h4 : (4 * Real.pi * (1 / 2 - 0) : ℝ) = 2 * Real.pi := by ring
  have h2 : (4 * (1 / 2 - 0) : ℝ) = 2 := by norm_num
  rw [rescaledHeatKernel, backwardHeatKernel, h4, h2, ← mul_assoc,
    ← Real.rpow_add (by positivity)]
  rw [show (n : ℝ) / 2 + -(n : ℝ) / 2 = 0 by ring, Real.rpow_zero, one_mul]

open scoped ContDiff in
theorem contDiff_rescaledHeatKernel : ContDiff ℝ ∞ (rescaledHeatKernel (E := E)) :=
  Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).neg.div_const 2)

/-- **`ρ̃` along a moving point**: `d/ds ρ̃(γ s) = -ρ̃(γ) ⟪γ, γ'⟫`. -/
theorem hasDerivAt_rescaledHeatKernel_curve {γ : ℝ → E} {γ' : E} {t : ℝ}
    (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => rescaledHeatKernel (γ s))
      (-rescaledHeatKernel (γ t) * @inner ℝ E _ (γ t) γ') t := by
  have h := ((hγ.norm_sq).neg.div_const 2).exp
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, rescaledHeatKernel]
  ring

end Rescaled

end HuiskenMonotonicity
