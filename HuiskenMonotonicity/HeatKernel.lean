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
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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

/-! ## Backward heat equation in coordinates

Combining the time and second-directional-derivative identities, we show that on
`EuclideanSpace ℝ (Fin n)` the kernel satisfies

  `∂_t ρ + Σᵢ ∂²ᵢ ρ = 0`,

where the spatial sum runs over the standard orthonormal basis. This is the heat
equation in coordinates; matching it up with mathlib's coordinate-free Laplacian
(`InnerProductSpace.laplacian`) is left for follow-up work. -/

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

end HeatEquation

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

end HuiskenMonotonicity
