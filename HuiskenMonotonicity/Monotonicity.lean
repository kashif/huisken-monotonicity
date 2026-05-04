/-
Statement of Huisken's monotonicity formula.

Huisken (1990), Theorem 3.1:

  Let `Mₜ = F(·, t)(M)` evolve by mean curvature in `ℝⁿ⁺¹`, and let
  `ρ(x, t) = (4π(t₀-t))^(-n/2) exp(-‖x‖²/(4(t₀-t)))` be the backward heat kernel
  centred at `(0, t₀)`. Then for `t < t₀`,

      d/dt ∫_{Mₜ} ρ(x, t) dμ_t  =  - ∫_{Mₜ} ρ(x, t) · ‖H + F^⊥/(2τ)‖² dμ_t,

  where `τ = t₀ - t`, `H` is the mean curvature vector, and `F^⊥` is the normal
  component of the position vector.

Because mathlib does not yet contain mean curvature, the surface measure of an
immersion, or the first variation of area, the statement below is intentionally
abstract: the hypothesis `IsMeanCurvatureFlow F` is opaque and the geometric quantities
appear as fields of `MonotonicityData`. The proof follows Huisken's two-step argument
(differentiate under the integral; complete the square against `F^⊥/(2τ)`; absorb the
tangential term via the divergence theorem). It is left as `sorry` and the cited
geometric primitives are itemised in comments.
-/

import HuiskenMonotonicity.HeatKernel
import HuiskenMonotonicity.Flow
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace HuiskenMonotonicity

open MeasureTheory

/-- Geometric data needed to state Huisken's formula:
the surface measures `μ_t`, the mean curvature vector field `H`, and the
normal-component map `F^⊥` of the position vector. All three are
opaque placeholders until mathlib has the underlying definitions. -/
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

/-- Huisken's monotonicity formula (statement only).

For `t < t₀ < T`,
  `d/dt ∫_{M} ρ(F(p,t), t) dμ_t(p) = - ∫_{M} ρ(F(p,t), t) · ‖H(p,t) + F^⊥(p,t)/(2τ)‖² dμ_t(p)`.

The proof requires:
  1. evolution of the area element `(d/dt) dμ_t = -‖H‖² dμ_t`;
  2. the chain rule `(d/dt) ρ(F(p,t), t) = ∂_t ρ + ⟨H, ∇_x ρ⟩`;
  3. the first variation formula `∫ div_M Y dμ = -∫ ⟨H, Y⟩ dμ`
     applied to `Y = ρ F / τ`, which converts the cross term into
     `n/(2τ) - ‖F^T‖²/(4τ²)`.
None of these three primitives are presently in mathlib. -/
theorem huisken_monotonicity
    (n : ℕ)
    {M E : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : ImmersionFamily M E) [IsMeanCurvatureFlow F]
    (data : MonotonicityData F)
    (t₀ : ℝ) {t : ℝ} (_hτ : t < t₀) (_ht : 0 ≤ t) (_htT : t < F.T) :
    HasDerivAt
      (fun s => ∫ p, backwardHeatKernel n t₀ s (F p s) ∂(data.surface.μ s))
      (- ∫ p, backwardHeatKernel n t₀ t (F p t) *
              ‖data.meanCurvature p t + (1 / (2 * (t₀ - t))) • data.normalPos p t‖ ^ 2
              ∂(data.surface.μ t)) t := by
  -- See module docstring. The proof requires:
  --   * evolution of dμ_t under MCF (`(d/dt) dμ_t = -H² dμ_t`);
  --   * differentiation under the integral with a moving measure;
  --   * the first variation formula on `M_t`.
  sorry

/-- Rescaled monotonicity (Corollary 3.2). After the parabolic rescaling
`F̃(p, s) = (2(T-t))^(-1/2) F(p, t)`, `s = -½ log(T-t)`, the surfaces `M̃_s` satisfy

  (d/ds) ∫ ρ̃ dμ̃_s = - ∫ ρ̃ · ‖H̃ + F̃^⊥‖² dμ̃_s,

where `ρ̃(x) = exp(-‖x‖²/2)`. Stated as a target; relies on `huisken_monotonicity` plus
the reparameterisation identity. -/
theorem huisken_monotonicity_rescaled : True := by
  -- Placeholder — replace with the rescaled statement once `huisken_monotonicity`
  -- carries a usable proof.
  trivial

end HuiskenMonotonicity
