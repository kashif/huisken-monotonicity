/-
**Sanity-check example**: a stationary `n`-dimensional hyperplane through the origin
in `ℝⁿ⁺¹`.

Geometrically the simplest non-degenerate MCF: the hyperplane is flat (`H = 0`), the
position vector `F(p, t) = (p, 0)` is entirely tangential to the surface (`F^⊥ = 0`),
and the surface is stationary (`∂_t F = 0 = H`). The two coherence axioms in
`MonotonicityData` then hold trivially.

The point of this file is to exhibit a concrete `MonotonicityData` whose geometric
hypotheses are non-vacuously satisfied — confirming that the axiomatised version of
`huisken_monotonicity` is consistent and applicable to a real geometric setup.

The two analytic hypotheses (`hChainRule`, `hFirstVar`) are not constructed here:
they require differentiation under the integral and explicit Gaussian moment
calculations, which are outside the scope of this example. With both `H = 0` and
`F^⊥ = 0` the conclusion reduces trivially to `(d/dt) ∫ ρ dμ_t = 0`, and indeed
`∫ ρ dμ_t = 1` for every `t < t₀` by `integral_backwardHeatKernel`.
-/

import HuiskenMonotonicity.Monotonicity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace HuiskenMonotonicity.Hyperplane

open MeasureTheory

variable (n : ℕ)

/-- The inclusion `ℝⁿ ↪ ℝⁿ⁺¹` placing `p` at zero in the last coordinate, lifted
through the `EuclideanSpace` type aliases. -/
noncomputable def embedding (p : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (Fin.snoc ((EuclideanSpace.equiv (Fin n) ℝ) p) (0 : ℝ))

lemma continuous_embedding : Continuous (embedding n) := by
  -- Continuity of `f ↦ Fin.snoc f 0`: componentwise, each entry is either a projection or 0.
  have h_snoc : Continuous
      (fun f : Fin n → ℝ => (Fin.snoc f (0 : ℝ) : Fin (n + 1) → ℝ)) := by
    refine continuous_pi (fun i => ?_)
    rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
    · simpa using continuous_apply j
    · simpa using continuous_const
  exact (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp
    (h_snoc.comp (EuclideanSpace.equiv (Fin n) ℝ).continuous)

/-- The stationary `n`-hyperplane through the origin as an `ImmersionFamily`. -/
noncomputable def immersion :
    ImmersionFamily (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (n + 1))) where
  T := 1
  T_pos := zero_lt_one
  toFun := fun p _ => embedding n p
  continuous_toFun := (continuous_embedding n).comp continuous_fst

/-- A stationary hyperplane satisfies the MCF equation with zero mean curvature. -/
theorem isMeanCurvatureFlow_immersion :
    IsMeanCurvatureFlow (immersion n) (fun _ _ => 0) := by
  intro p t _ _
  -- The function `s ↦ embedding p` is constant in `s`; its derivative is `0`.
  exact hasDerivAt_const _ _

/-- The complete `MonotonicityData` for the stationary hyperplane: zero mean curvature,
zero normal-position projection, Lebesgue surface measure (constant in time). -/
noncomputable def data : MonotonicityData (immersion n) where
  surface := { μ := fun _ => volume }
  meanCurvature := fun _ _ => 0
  normalPos := fun _ _ => 0
  posDecomp := by
    intro p t
    -- ⟨F p t - 0, 0⟩ = 0
    simp
  meanCurvature_normal := by
    intro p t
    -- ⟨0, F p t - 0⟩ = 0
    simp

end HuiskenMonotonicity.Hyperplane
