/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.IntervalFlow
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The shrinking sphere

The round sphere of radius `√(1 - 2nt)` moves by mean curvature, `Sⁿ_t = √(1 - 2nt) Sⁿ` for
`2nt < 1`: it is the basic self-similarly shrinking solution, the model Huisken's paper
compares singularities with. This file proves that it satisfies the hypotheses of the
monotonicity formula, so that the formula is not vacuous.

The mean curvature vector of a sphere of radius `R` is computed from the results already
proved, without second fundamental forms: when `|F| = R` is constant, the tangential part of
the position vector vanishes, so Beltrami's formula `div_M Fᵀ = n + ⟪F, Hvec⟫` gives
`⟪F, Hvec⟫ = -n`; and `Hvec`, being normal, is a multiple of `F`. Hence
`Hvec = -(n / R²) F` (`SmoothImmersion.meanCurvature_eq_of_norm_eq`).
-/

open scoped Manifold ContDiff RealInnerProductSpace

open Set Metric Module

noncomputable section

namespace HuiskenMonotonicity

open MeasureTheory Manifold DifferentialGeometry DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Geometry.Operator

section MeanCurvature

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]
variable [T2Space M] [I.Boundaryless]

/-- **The mean curvature vector of a sphere.** If `|f| = R ≠ 0` everywhere and the normal
space at each point is spanned by the position vector, then `Hvec = -(n / R²) f`. -/
theorem SmoothImmersion.meanCurvature_eq_of_norm_eq (f : SmoothImmersion I M E) {R : ℝ}
    (hR : R ≠ 0) (hnorm : ∀ p, ‖f p‖ = R)
    (hnormal : ∀ p (v : E), (∀ w, ⟪v, mvfderiv I f p w⟫ = 0) → v ∈ ℝ ∙ f p)
    (p : M) :
    f.meanCurvature p = -((finrank ℝ E₁ : ℝ) / R ^ 2) • f p := by
  set y := extChartAt I p p with hy_def
  set Fc := f.chartRep p
  have hy : y ∈ (extChartAt I p).target := mem_extChartAt_target p
  have hopen := isOpen_extChartAt_target (I := I) p
  have hpt : Fc y = f p := by
    change f ((extChartAt I p).symm y) = f p
    rw [extChartAt_to_inv]
  -- `|Fc|²` is constant, so the position vector is orthogonal to the tangent vectors
  have horth : ∀ z ∈ (extChartAt I p).target, ∀ v, ⟪Fc z, fderiv ℝ Fc z v⟫ = 0 := by
    intro z hz v
    have hd := ((f.contDiffAt_chartRep p hz).differentiableAt (by norm_num)).hasFDerivAt
    have hconst : (fun z ↦ ‖Fc z‖ ^ 2) = fun _ ↦ R ^ 2 := by
      funext z
      change ‖f ((extChartAt I p).symm z)‖ ^ 2 = R ^ 2
      rw [hnorm]
    have h := hd.norm_sq
    rw [hconst] at h
    have h0 := congrArg (fun L : E₁ →L[ℝ] ℝ ↦ L v) ((hasFDerivAt_const (R ^ 2) z).unique h)
    simp at h0
    change ⟪f.chartRep p z, fderiv ℝ (f.chartRep p) z v⟫ = 0
    linarith
  -- so the tangential part of the position vector vanishes near `y`
  have hT : (fun z ↦ tangentialPart Fc (chartModelBasis E₁)
        (fun k l ↦ chartInvGramOnE f.inducedMetric p k l z) z (Fc z)) =ᶠ[nhds y]
      fun _ ↦ (0 : E) := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    simp only [tangentialPart, frameTangent, horth z hz, mul_zero, zero_smul,
      Finset.sum_const_zero]
  -- and Beltrami's formula gives `⟪F, Hvec⟫ = -n`
  have hbel := f.tangentialDivergence_tangentialPart_chartRep p hy
  have hzero : tangentialDivergence Fc (fun z ↦ tangentialPart Fc (chartModelBasis E₁)
      (fun k l ↦ chartInvGramOnE f.inducedMetric p k l z) z (Fc z)) (chartModelBasis E₁)
      (fun k l ↦ chartInvGramOnE f.inducedMetric p k l y) y = 0 := by
    simp only [tangentialDivergence, hT.fderiv_eq, fderiv_fun_const, Pi.zero_apply,
      zero_apply, inner_zero_left, mul_zero, Finset.sum_const_zero]
  have hFH : ⟪f p, f.meanCurvature p⟫ = -(finrank ℝ E₁ : ℝ) := by
    have h := hzero.symm.trans hbel
    rw [show f.chartRep p y = f p from hpt] at h
    change (0 : ℝ) = (finrank ℝ E₁ : ℝ) + ⟪f p, f.meanCurvature p⟫ at h
    linarith
  -- `Hvec` is normal, hence a multiple of the position vector
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (hnormal p _ fun w ↦ f.inner_meanCurvature_mvfderiv p w)
  rw [← hc] at hFH ⊢
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm] at hFH
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  congr 1
  field_simp
  linarith

end MeanCurvature

/-! ## The shrinking sphere -/

variable (n : ℕ)

/-- `EuclideanSpace ℝ (Fin (n + 1))` has dimension `n + 1`. -/
local instance factFinrankEuclidean : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The Borel σ-algebra on the sphere. -/
local instance instMeasurableSpaceSphere :
    MeasurableSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := borel _

local instance instBorelSpaceSphere :
    BorelSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := ⟨rfl⟩

/-- The times at which the shrinking sphere exists, `2nt < 1`. -/
def shrinkingSphereTimes : Set ℝ := {t | 2 * n * t < 1}

theorem isOpen_shrinkingSphereTimes : IsOpen (shrinkingSphereTimes n) :=
  isOpen_lt (continuous_const.mul continuous_id) continuous_const

theorem convex_shrinkingSphereTimes : Convex ℝ (shrinkingSphereTimes n) := by
  intro a ha b hb μ ν hμ hν hμν
  simp only [shrinkingSphereTimes, mem_ofPred_eq, smul_eq_mul] at *
  have hsplit : 2 * n * (μ * a + ν * b) = μ * (2 * n * a) + ν * (2 * n * b) := by ring
  rw [hsplit]
  rcases hμ.eq_or_lt with rfl | hμ'
  · simp only [zero_add] at hμν
    subst hμν
    linarith
  · nlinarith [mul_lt_mul_of_pos_left ha hμ', mul_le_mul_of_nonneg_left hb.le hν]

/-- The radius `√(1 - 2nt)`. -/
def shrinkingSphereRadius (t : ℝ) : ℝ := Real.sqrt (1 - 2 * n * t)

theorem shrinkingSphereRadius_pos {t : ℝ} (ht : t ∈ shrinkingSphereTimes n) :
    0 < shrinkingSphereRadius n t :=
  Real.sqrt_pos.mpr (by simp only [shrinkingSphereTimes, mem_ofPred_eq] at ht; linarith)

/-- The derivative of the radius, `d/dt √(1 - 2nt) = -n / √(1 - 2nt)`. -/
theorem hasDerivAt_shrinkingSphereRadius {t : ℝ} (ht : t ∈ shrinkingSphereTimes n) :
    HasDerivAt (shrinkingSphereRadius n) (-(n : ℝ) / shrinkingSphereRadius n t) t := by
  have h1 : (1 - 2 * n * t : ℝ) ≠ 0 := by
    simp only [shrinkingSphereTimes, mem_ofPred_eq] at ht; linarith
  have h := (((hasDerivAt_id' t).const_mul (2 * (n : ℝ))).const_sub 1).sqrt h1
  refine h.congr_deriv ?_
  have hR := shrinkingSphereRadius_pos n ht
  rw [shrinkingSphereRadius] at hR ⊢
  field_simp

theorem contDiffAt_shrinkingSphereRadius {t : ℝ} (ht : t ∈ shrinkingSphereTimes n) :
    ContDiffAt ℝ ∞ (shrinkingSphereRadius n) t := by
  have h1 : (1 - 2 * n * t : ℝ) ≠ 0 := by
    simp only [shrinkingSphereTimes, mem_ofPred_eq] at ht; linarith
  exact (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).sqrt h1

/-- The differential of the scaled inclusion of the sphere. -/
theorem mvfderiv_smul_coe_sphere (R : ℝ) (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    mvfderiv (𝓡 n)
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦ R • (q : EuclideanSpace ℝ
          (Fin (n + 1)))) p =
      R • mvfderiv (𝓡 n)
        ((↑) : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin (n + 1)))
        p :=
  (((contMDiff_coe_sphere (m := ∞) p).mdifferentiableAt (by simp)).hasMFDerivAt.const_smul
    R).mfderiv

/-- **The shrinking sphere** `F(p, t) = √(1 - 2nt) p`, a family of immersions of the unit
sphere `Sⁿ ⊂ ℝⁿ⁺¹` for `2nt < 1`. -/
def shrinkingSphere :
    ImmersionFlowOn (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (EuclideanSpace ℝ (Fin (n + 1))) (shrinkingSphereTimes n) where
  isOpen := isOpen_shrinkingSphereTimes n
  toFun p t := shrinkingSphereRadius n t • (p : EuclideanSpace ℝ (Fin (n + 1)))
  contMDiffOn := by
    rintro ⟨p, t⟩ ⟨-, ht⟩
    have hR : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × ℝ ↦
          shrinkingSphereRadius n q.2) (p, t) :=
      (contDiffAt_shrinkingSphereRadius n ht).contMDiffAt.comp (p, t) contMDiffAt_snd
    have hp : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × ℝ ↦
          (q.1 : EuclideanSpace ℝ (Fin (n + 1)))) (p, t) :=
      (contMDiff_coe_sphere (p, t).1).comp (p, t) contMDiffAt_fst
    exact (hR.smul hp).contMDiffWithinAt
  mfderiv_injective t ht p v w hvw :=
    injective_mvfderiv_subtypeVal_sphere p <|
      smul_right_injective (EuclideanSpace ℝ (Fin (n + 1))) (shrinkingSphereRadius_pos n ht).ne' <|
        (DFunLike.congr_fun (mvfderiv_smul_coe_sphere n _ p) v).symm.trans
          (hvw.trans (DFunLike.congr_fun (mvfderiv_smul_coe_sphere n _ p) w))

/-- The mean curvature vector of the sphere of radius `R(t)` is `-(n / R(t)²) F`. -/
theorem shrinkingSphere_meanCurvature {t : ℝ} (ht : t ∈ shrinkingSphereTimes n)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ((shrinkingSphere n).slice t ht).meanCurvature p =
      -((n : ℝ) / shrinkingSphereRadius n t) • (p : EuclideanSpace ℝ (Fin (n + 1))) := by
  have hR := (shrinkingSphereRadius_pos n ht)
  have hnorm : ∀ q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      ‖(shrinkingSphere n).slice t ht q‖ = shrinkingSphereRadius n t := by
    intro q
    change ‖shrinkingSphereRadius n t • (q : EuclideanSpace ℝ (Fin (n + 1)))‖ = _
    rw [norm_smul, Real.norm_of_nonneg hR.le, norm_eq_of_mem_sphere q, mul_one]
  have hnormal : ∀ (q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (v : EuclideanSpace ℝ (Fin (n + 1))),
      (∀ w, ⟪v, mvfderiv (𝓡 n) ((shrinkingSphere n).slice t ht) q w⟫ = 0) →
        v ∈ ℝ ∙ ((shrinkingSphere n).slice t ht q) := by
    intro q v hv
    change v ∈ ℝ ∙ (shrinkingSphereRadius n t • (q : EuclideanSpace ℝ (Fin (n + 1))))
    rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hR.ne'),
      ← Submodule.orthogonal_orthogonal (ℝ ∙ (q : EuclideanSpace ℝ (Fin (n + 1)))),
      Submodule.mem_orthogonal]
    intro u hu
    rw [← range_mvfderiv_subtypeVal (n := n) q] at hu
    obtain ⟨w, rfl⟩ := hu
    have h := hv w
    change ⟪v, mvfderiv (𝓡 n)
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
        shrinkingSphereRadius n t • (q : EuclideanSpace ℝ (Fin (n + 1)))) q w⟫ = 0 at h
    rw [mvfderiv_smul_coe_sphere, smul_apply, real_inner_smul_right,
      mul_eq_zero] at h
    exact (real_inner_comm _ _).trans (h.resolve_left hR.ne')
  rw [SmoothImmersion.meanCurvature_eq_of_norm_eq _ hR.ne' hnorm hnormal p,
    finrank_euclideanSpace_fin]
  change -((n : ℝ) / shrinkingSphereRadius n t ^ 2) •
      (shrinkingSphereRadius n t • (p : EuclideanSpace ℝ (Fin (n + 1)))) = _
  rw [smul_smul]
  congr 1
  field_simp

/-- **The shrinking sphere moves by mean curvature.** -/
theorem shrinkingSphere_isMeanCurvatureFlow : (shrinkingSphere n).IsMeanCurvatureFlow := by
  intro t ht p
  rw [shrinkingSphere_meanCurvature n ht p]
  have h := (hasDerivAt_shrinkingSphereRadius n ht).smul_const
    (p : EuclideanSpace ℝ (Fin (n + 1)))
  refine h.congr_deriv ?_
  rw [neg_div]

/-- **Huisken's monotonicity for the shrinking sphere**: the hypotheses of the monotonicity
formula are satisfied by a genuine mean curvature flow, and its Gaussian density
`t ↦ ∫_{Sⁿ} ρ_{x₀,t₀}(F, t) dμ_t` is non-increasing before `t₀`. -/
theorem shrinkingSphere_antitoneOn_integral (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (t₀ : ℝ) :
    AntitoneOn
      (fun s ↦ ∫ p, backwardHeatKernel n t₀ s ((shrinkingSphere n) p s - x₀)
        ∂((shrinkingSphere n).surfaceMeasure s))
      (shrinkingSphereTimes n ∩ Iio t₀) := by
  have h := (shrinkingSphere n).antitoneOn_integral (convex_shrinkingSphereTimes n)
    (shrinkingSphere_isMeanCurvatureFlow n) x₀ t₀
  rwa [finrank_euclideanSpace_fin] at h

end HuiskenMonotonicity
