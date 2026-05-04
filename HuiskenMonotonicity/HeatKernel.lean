/-
The backward heat kernel used in Huisken's monotonicity formula.

For a hypersurface dimension `n`, base time `t₀`, current time `t < t₀`, and ambient point
`x` in an inner product space, define

  ρ(x, t) = (4π(t₀ - t))^(-n/2) · exp(-‖x‖² / (4(t₀ - t))).

Note that the exponent `-n/2` matches the *hypersurface* dimension, not the ambient
dimension; this is what makes ∫ ρ dμ ≡ 1 over an `n`-plane through the origin and is the
normalisation used in Huisken (1990), J. Differential Geom. 31, 285–299.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic

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

/-- Convenience abbreviation for the time-to-go `τ = t₀ - t`. -/
noncomputable def heatKernelTau (t₀ t : ℝ) : ℝ := t₀ - t

@[simp] lemma heatKernelTau_def (t₀ t : ℝ) : heatKernelTau t₀ t = t₀ - t := rfl

section Positivity

variable {E : Type*} [SeminormedAddCommGroup E] {n : ℕ} {t₀ t : ℝ}

lemma backwardHeatKernel_pos (hτ : t < t₀) (x : E) :
    0 < backwardHeatKernel n t₀ t x := by
  unfold backwardHeatKernel
  have h : (0 : ℝ) < 4 * π * (t₀ - t) := by
    have : 0 < t₀ - t := sub_pos.mpr hτ
    positivity
  exact mul_pos (Real.rpow_pos_of_pos h _) (Real.exp_pos _)

lemma backwardHeatKernel_ne_zero (hτ : t < t₀) (x : E) :
    backwardHeatKernel n t₀ t x ≠ 0 :=
  (backwardHeatKernel_pos hτ x).ne'

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
geometric step that requires mathlib infrastructure mathlib does not yet provide
(see `HuiskenMonotonicity.Flow`). -/

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
    have := (h_const.add h_lin).add h_quad
    simpa using this
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

end Derivatives

/-- Backward heat equation `∂_t ρ + Δ_x ρ = 0`.

This follows from the time and directional-derivative identities by computing the
Hessian and taking the trace. The Laplacian on a general inner product space is not
available in the current mathlib release; the statement is left at this informal level
until that scaffolding lands. -/
example : True := trivial  -- placeholder; replace with the literal heat-equation
                            -- statement when `Δ_x` is available on inner product spaces

end HuiskenMonotonicity
