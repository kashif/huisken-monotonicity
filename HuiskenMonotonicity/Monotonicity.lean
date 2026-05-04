/-
Statement and (axiom-conditional) proof of Huisken's monotonicity formula.

Huisken (1990), Theorem 3.1:

  Let `Mₜ = F(·, t)(M)` evolve by mean curvature in `ℝⁿ⁺¹`, and let
  `ρ(x, t) = (4π(t₀-t))^(-n/2) exp(-‖x‖²/(4(t₀-t)))` be the backward heat kernel
  centred at `(0, t₀)`. Then for `t < t₀`,

      d/dt ∫_{Mₜ} ρ(x, t) dμ_t  =  - ∫_{Mₜ} ρ(x, t) · ‖H + F^⊥/(2τ)‖² dμ_t.

Mathlib v4.30.0-rc2 does not yet contain the second fundamental form, the surface
measure of an immersion, the moving-measure chain rule, or the first variation
formula. Rather than build all four, we **axiomatise** them at the level needed for
this single application:

  * `MonotonicityData` carries the surface measure `μ_t`, the mean curvature vector
    field `H`, and the normal-component map `F^⊥`, together with two purely geometric
    coherence axioms (orthogonality of the tangential and normal parts of `F`, and
    `H ⟂ F^T`).
  * `huisken_monotonicity` then takes two analytic hypotheses corresponding to
    Huisken's two non-trivial steps: the chain-rule expansion of `(d/dt) ∫ ρ dμ_t`
    (which packages the moving-measure chain rule together with our heat-kernel
    derivative identities) and the first-variation identity for `Y = ρ F / τ`
    (which packages the divergence theorem on `Mₜ`).

Given those four axioms, the theorem becomes a piece of pure algebra: complete the
square against `H + F^⊥/(2τ)`, use the orthogonal decomposition to identify
`‖F‖² − ‖F^⊥‖² = ‖F^T‖²` and `⟨F, H⟩ = ⟨F^⊥, H⟩`, and absorb the residue using
the first-variation identity.

When the missing geometric primitives land in mathlib, the analytic hypotheses can
be discharged for any genuine MCF, recovering Huisken's theorem unconditionally.
-/

import HuiskenMonotonicity.HeatKernel
import HuiskenMonotonicity.Flow
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace HuiskenMonotonicity

open MeasureTheory

/-- Geometric data needed to state Huisken's formula:
the surface measures `μ_t`, the mean curvature vector field `H`, the
normal-component map `F^⊥` of the position vector, and two coherence axioms
(orthogonality of the tangential and normal parts of `F`, and `H ⟂ F^T`). -/
structure MonotonicityData
    {M E : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : ImmersionFamily M E) where
  /-- Surface measure `μ_t` on the parameter space `M`. -/
  surface : SurfaceMeasure F
  /-- Mean curvature vector field `H : M × [0, T) → E`. -/
  meanCurvature : M → ℝ → E
  /-- Normal component of the position vector, `F^⊥ : M × [0, T) → E`. -/
  normalPos : M → ℝ → E
  /-- The position vector decomposes orthogonally: `F = F^T + F^⊥` with `F^T ⟂ F^⊥`. -/
  posDecomp : ∀ p t, @inner ℝ E _ (F p t - normalPos p t) (normalPos p t) = 0
  /-- The mean curvature vector is orthogonal to the tangential component of `F`. -/
  meanCurvature_normal : ∀ p t,
    @inner ℝ E _ (meanCurvature p t) (F p t - normalPos p t) = 0

/-! ## Pointwise algebraic identity

Pure algebra in the inner product space `E`: if `F^T ⟂ F^⊥` and `H ⟂ F^T`, then the
chain-rule integrand differs from the squared-norm integrand by a multiple of the
first-variation integrand. -/

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pointwise identity: the chain-rule integrand equals the negated squared-norm
integrand plus `(1/(2τ))` times the first-variation integrand. Uses only the two
orthogonality axioms. -/
lemma huisken_pointwise_identity
    (n : ℕ) (τ : ℝ) (hτ : τ ≠ 0)
    (Fpt Fperp H : E) (ρ : ℝ)
    (hPosDecomp : @inner ℝ E _ (Fpt - Fperp) Fperp = 0)
    (hMCNormal : @inner ℝ E _ H (Fpt - Fperp) = 0) :
    ρ * ((n : ℝ) / (2 * τ) - ‖Fpt‖ ^ 2 / (4 * τ ^ 2)
          - @inner ℝ E _ Fpt H / (2 * τ) - ‖H‖ ^ 2) =
      -(ρ * ‖H + (1 / (2 * τ)) • Fperp‖ ^ 2)
        + (1 / (2 * τ)) *
            (ρ * ((n : ℝ) - ‖Fpt - Fperp‖ ^ 2 / (2 * τ) + @inner ℝ E _ H Fpt)) := by
  -- Expand ‖H + (1/(2τ)) • F^⊥‖² = ‖H‖² + ⟨H, F^⊥⟩/τ + ‖F^⊥‖²/(4τ²).
  have h_norm_sq :
      ‖H + (1 / (2 * τ)) • Fperp‖ ^ 2 =
        ‖H‖ ^ 2 + @inner ℝ E _ H Fperp / τ + ‖Fperp‖ ^ 2 / (4 * τ ^ 2) := by
    rw [@norm_add_sq_real E _ _ H ((1 / (2 * τ)) • Fperp), real_inner_smul_right,
        norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  -- Expand ‖F‖² = ‖F^T‖² + ‖F^⊥‖². From posDecomp, ⟨F^T, F^⊥⟩ = 0, so
  -- ‖F‖² = ‖F^T + F^⊥‖² = ‖F^T‖² + 2⟨F^T, F^⊥⟩ + ‖F^⊥‖² = ‖F^T‖² + ‖F^⊥‖².
  have hFsplit : Fpt = (Fpt - Fperp) + Fperp := by abel
  have h_F_norm :
      ‖Fpt‖ ^ 2 = ‖Fpt - Fperp‖ ^ 2 + ‖Fperp‖ ^ 2 := by
    conv_lhs => rw [hFsplit]
    rw [@norm_add_sq_real E _ _ (Fpt - Fperp) Fperp, hPosDecomp]
    ring
  -- From `H ⟂ F^T`: ⟨H, F⟩ = ⟨H, F^T + F^⊥⟩ = 0 + ⟨H, F^⊥⟩ = ⟨H, F^⊥⟩.
  have h_inner_split :
      @inner ℝ E _ H Fpt = @inner ℝ E _ H Fperp := by
    conv_lhs => rw [hFsplit]
    rw [inner_add_right, hMCNormal, zero_add]
  have h_inner_sym : @inner ℝ E _ Fpt H = @inner ℝ E _ H Fpt := real_inner_comm _ _
  rw [h_norm_sq, h_F_norm, h_inner_sym, h_inner_split]
  field_simp
  ring

end Algebra

/-- **Huisken's monotonicity formula** (Theorem 3.1, axiom-conditional).

For `t < t₀ < T`,
  `d/dt ∫_{M} ρ(F(p,t), t) dμ_t(p) = - ∫_{M} ρ(F(p,t), t) · ‖H(p,t) + F^⊥(p,t)/(2τ)‖² dμ_t(p)`.

The two analytic hypotheses (`hChainRule`, `hFirstVar`) package the moving-measure
chain rule for our specific integrand and the first variation formula for the test
field `Y = ρ F / τ`, respectively. The MCF assumption `∂_t F = H` is encoded in
the form of `hChainRule`, where `H = data.meanCurvature` appears as the velocity
in the chain-rule integrand; no separate `IsMeanCurvatureFlow` hypothesis is
needed. The hypotheses will be discharged for any actual MCF once mathlib has
the underlying geometric infrastructure. -/
theorem huisken_monotonicity
    (n : ℕ)
    {M E : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : ImmersionFamily M E)
    (data : MonotonicityData F)
    (t₀ : ℝ) {t : ℝ} (hτ : t < t₀) (_ht : 0 ≤ t) (_htT : t < F.T)
    (hChainRule :
      HasDerivAt
        (fun s => ∫ p, backwardHeatKernel n t₀ s (F p s) ∂(data.surface.μ s))
        (∫ p, backwardHeatKernel n t₀ t (F p t) *
              ((n : ℝ) / (2 * (t₀ - t)) - ‖F p t‖ ^ 2 / (4 * (t₀ - t) ^ 2)
                - @inner ℝ E _ (F p t) (data.meanCurvature p t) / (2 * (t₀ - t))
                - ‖data.meanCurvature p t‖ ^ 2)
              ∂(data.surface.μ t)) t)
    (hFirstVar :
      ∫ p, backwardHeatKernel n t₀ t (F p t) *
        ((n : ℝ) - ‖F p t - data.normalPos p t‖ ^ 2 / (2 * (t₀ - t))
          + @inner ℝ E _ (data.meanCurvature p t) (F p t))
        ∂(data.surface.μ t) = 0)
    (hIntSqNorm : Integrable
      (fun p => backwardHeatKernel n t₀ t (F p t) *
        ‖data.meanCurvature p t + (1 / (2 * (t₀ - t))) • data.normalPos p t‖ ^ 2)
      (data.surface.μ t))
    (hIntFirstVar : Integrable
      (fun p => backwardHeatKernel n t₀ t (F p t) *
        ((n : ℝ) - ‖F p t - data.normalPos p t‖ ^ 2 / (2 * (t₀ - t))
          + @inner ℝ E _ (data.meanCurvature p t) (F p t))) (data.surface.μ t)) :
    HasDerivAt
      (fun s => ∫ p, backwardHeatKernel n t₀ s (F p s) ∂(data.surface.μ s))
      (- ∫ p, backwardHeatKernel n t₀ t (F p t) *
              ‖data.meanCurvature p t + (1 / (2 * (t₀ - t))) • data.normalPos p t‖ ^ 2
              ∂(data.surface.μ t)) t := by
  have hτ_ne : (t₀ - t) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hτ)
  -- Name the three integrands.
  set A : M → ℝ := fun p =>
    backwardHeatKernel n t₀ t (F p t) *
      ‖data.meanCurvature p t + (1 / (2 * (t₀ - t))) • data.normalPos p t‖ ^ 2 with hA_def
  set B : M → ℝ := fun p =>
    backwardHeatKernel n t₀ t (F p t) *
      ((n : ℝ) - ‖F p t - data.normalPos p t‖ ^ 2 / (2 * (t₀ - t))
        + @inner ℝ E _ (data.meanCurvature p t) (F p t)) with hB_def
  set C : M → ℝ := fun p =>
    backwardHeatKernel n t₀ t (F p t) *
      ((n : ℝ) / (2 * (t₀ - t)) - ‖F p t‖ ^ 2 / (4 * (t₀ - t) ^ 2)
        - @inner ℝ E _ (F p t) (data.meanCurvature p t) / (2 * (t₀ - t))
        - ‖data.meanCurvature p t‖ ^ 2) with hC_def
  -- Pointwise: chain-rule integrand = -squared-norm + (1/(2τ)) · first-variation.
  have h_pt : ∀ p, C p = -A p + (1 / (2 * (t₀ - t))) * B p := fun p =>
    huisken_pointwise_identity n (t₀ - t) hτ_ne (F p t) (data.normalPos p t)
      (data.meanCurvature p t) (backwardHeatKernel n t₀ t (F p t))
      (data.posDecomp p t) (data.meanCurvature_normal p t)
  -- Lift to integrals using linearity of integration.
  have h_int : ∫ p, C p ∂(data.surface.μ t) = -∫ p, A p ∂(data.surface.μ t) := by
    calc ∫ p, C p ∂(data.surface.μ t)
        = ∫ p, -A p + (1 / (2 * (t₀ - t))) * B p ∂(data.surface.μ t) :=
          integral_congr_ae (Filter.Eventually.of_forall h_pt)
      _ = ∫ p, -A p ∂(data.surface.μ t)
            + ∫ p, (1 / (2 * (t₀ - t))) * B p ∂(data.surface.μ t) :=
          integral_add hIntSqNorm.neg (hIntFirstVar.const_mul _)
      _ = -∫ p, A p ∂(data.surface.μ t)
            + (1 / (2 * (t₀ - t))) * ∫ p, B p ∂(data.surface.μ t) := by
          rw [integral_neg, integral_const_mul]
      _ = -∫ p, A p ∂(data.surface.μ t) := by rw [hFirstVar]; ring
  -- Conclude.
  rw [h_int] at hChainRule
  exact hChainRule

/-- **Rescaled monotonicity formula** (Huisken Cor 3.2, axiom-conditional).

After the parabolic rescaling `Ft(p, s) = (2(T-t))^(-1/2) F(p, t)`, `s = -½ log(T-t)`,
the rescaled surfaces `M̃_s` satisfy `∂_s Ft = H̃ + Ft` and the simpler formula

  (d/ds) ∫_{M̃_s} ρ̃(Ft) dμ̃_s = - ∫_{M̃_s} ρ̃(Ft) · ‖H̃ + Ft^⊥‖² dμ̃_s,

where `ρ̃(x) = exp(-‖x‖²/2)`. The kernel has no `(4πτ)^(-n/2)` prefactor, the
`1/(2τ)` weight on `Ft^⊥` collapses, and `ρ̃` is time-independent.

Algebraically this is the τ = 1/2 specialisation of `huisken_pointwise_identity`,
so the proof reuses the unrescaled algebra. The two analytic hypotheses
(`hChainRule`, `hFirstVar`) package the rescaled-flow chain rule and first
variation, with the rescaled MCF equation `∂_s Ft = H̃ + Ft` providing the extra
`-‖Ft‖²` term that compensates for the absence of a time-dependent prefactor. -/
theorem huisken_monotonicity_rescaled
    (n : ℕ)
    {M E : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ft : ImmersionFamily M E)
    (data : MonotonicityData Ft)
    {s : ℝ} (_hs : 0 ≤ s) (_hsT : s < Ft.T)
    (hChainRule :
      HasDerivAt
        (fun s' => ∫ p, rescaledHeatKernel (Ft p s') ∂(data.surface.μ s'))
        (∫ p, rescaledHeatKernel (Ft p s) *
              ((n : ℝ) - ‖Ft p s‖ ^ 2
                - @inner ℝ E _ (Ft p s) (data.meanCurvature p s)
                - ‖data.meanCurvature p s‖ ^ 2)
              ∂(data.surface.μ s)) s)
    (hFirstVar :
      ∫ p, rescaledHeatKernel (Ft p s) *
        ((n : ℝ) - ‖Ft p s - data.normalPos p s‖ ^ 2
          + @inner ℝ E _ (data.meanCurvature p s) (Ft p s))
        ∂(data.surface.μ s) = 0)
    (hIntSqNorm : Integrable
      (fun p => rescaledHeatKernel (Ft p s) *
        ‖data.meanCurvature p s + data.normalPos p s‖ ^ 2)
      (data.surface.μ s))
    (hIntFirstVar : Integrable
      (fun p => rescaledHeatKernel (Ft p s) *
        ((n : ℝ) - ‖Ft p s - data.normalPos p s‖ ^ 2
          + @inner ℝ E _ (data.meanCurvature p s) (Ft p s))) (data.surface.μ s)) :
    HasDerivAt
      (fun s' => ∫ p, rescaledHeatKernel (Ft p s') ∂(data.surface.μ s'))
      (- ∫ p, rescaledHeatKernel (Ft p s) *
              ‖data.meanCurvature p s + data.normalPos p s‖ ^ 2
              ∂(data.surface.μ s)) s := by
  -- Specialise `huisken_pointwise_identity` at τ = 1/2: the factor `1/(2τ)` becomes 1.
  have hτ_ne : (1 / 2 : ℝ) ≠ 0 := by norm_num
  set A : M → ℝ := fun p =>
    rescaledHeatKernel (Ft p s) *
      ‖data.meanCurvature p s + data.normalPos p s‖ ^ 2 with _hA_def
  set B : M → ℝ := fun p =>
    rescaledHeatKernel (Ft p s) *
      ((n : ℝ) - ‖Ft p s - data.normalPos p s‖ ^ 2
        + @inner ℝ E _ (data.meanCurvature p s) (Ft p s)) with _hB_def
  set C : M → ℝ := fun p =>
    rescaledHeatKernel (Ft p s) *
      ((n : ℝ) - ‖Ft p s‖ ^ 2
        - @inner ℝ E _ (Ft p s) (data.meanCurvature p s)
        - ‖data.meanCurvature p s‖ ^ 2) with _hC_def
  -- Pointwise identity at τ = 1/2 (note: `1/(2·(1/2)) = 1` and `4·(1/2)² = 1`).
  have h_pt : ∀ p, C p = -A p + 1 * B p := by
    intro p
    have key := huisken_pointwise_identity n (1 / 2 : ℝ) hτ_ne
      (Ft p s) (data.normalPos p s) (data.meanCurvature p s)
      (rescaledHeatKernel (Ft p s)) (data.posDecomp p s) (data.meanCurvature_normal p s)
    -- key : ρ̃ · (n/(2·1/2) - ‖Ft‖²/(4·(1/2)²) - ⟨Ft,H⟩/(2·(1/2)) - ‖H‖²)
    --       = -(ρ̃ · ‖H + (1/(2·(1/2)))•F⊥‖²)
    --         + (1/(2·(1/2))) · (ρ̃ · (n - ‖Ft-F⊥‖²/(2·(1/2)) + ⟨H, Ft⟩))
    -- Simplify each `2 * (1/2)`-style factor to `1`.
    simp only [show (2 : ℝ) * (1 / 2) = 1 by norm_num,
               show (4 : ℝ) * (1 / 2) ^ 2 = 1 by norm_num,
               div_one, one_smul] at key
    convert key using 2
  -- Lift to integrals using linearity (mirrors the unrescaled proof).
  have h_int : ∫ p, C p ∂(data.surface.μ s) = -∫ p, A p ∂(data.surface.μ s) := by
    calc ∫ p, C p ∂(data.surface.μ s)
        = ∫ p, -A p + 1 * B p ∂(data.surface.μ s) :=
          integral_congr_ae (Filter.Eventually.of_forall h_pt)
      _ = ∫ p, -A p ∂(data.surface.μ s) + ∫ p, 1 * B p ∂(data.surface.μ s) :=
          integral_add hIntSqNorm.neg (hIntFirstVar.const_mul _)
      _ = -∫ p, A p ∂(data.surface.μ s) + 1 * ∫ p, B p ∂(data.surface.μ s) := by
          rw [integral_neg, integral_const_mul]
      _ = -∫ p, A p ∂(data.surface.μ s) := by rw [hFirstVar]; ring
  rw [h_int] at hChainRule
  exact hChainRule

end HuiskenMonotonicity
