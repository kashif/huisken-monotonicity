/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.FirstVariationIntegral
import HuiskenMonotonicity.TransportFormula
import HuiskenMonotonicity.MetricEvolution

/-!
# Huisken's monotonicity formula for a mean curvature flow

For a smooth family of immersions `F : M × ℝ → E` of a closed manifold moving by mean
curvature, `∂_t F = Hvec`, and the backward heat kernel `ρ` centred at `(0, t₀)`,

  `d/dt ∫_M ρ(F, t) dμ_t = -∫_M ρ(F, t) ‖Hvec + F^⊥ / (2(t₀ - t))‖² dμ_t`

for `t < t₀` (Huisken 1990, Theorem 3.1).

The proof follows Huisken's:

* the transport formula (`hasDerivAt_integral_backwardHeatKernel`) differentiates the
  integral, with weight `½ tr(g⁻¹ ∂_t g) = -‖Hvec‖²` under the flow
  (`traceTimeDerivMetric_of_isMeanCurvatureFlow`);
* the chain rule along the flow gives `∂_t ρ + ⟨∇ρ, Hvec⟩`
  (`hasDerivAt_backwardHeatKernel_curve`);
* the resulting integrand is `-ρ ‖Hvec + F^⊥/(2τ)‖²` plus a multiple of the first-variation
  integrand (`huisken_pointwise_identity`), whose integral vanishes
  (`integral_firstVariation`).

The mean curvature vector is read in the chart at each point. Under the flow it is the time
velocity, hence continuous, which is what makes the integrands integrable. The one
geometric input beyond the first variation is that the velocity is normal in *every* chart,
not just in the chart at the point (`inner_meanCurvature_fderiv_chartRep`); the library's
`fderiv_fixed_chart_eq_trivialization_comp_mfderiv` reduces this to normality against the
manifold derivative.
-/

open scoped Manifold ContDiff

noncomputable section

namespace HuiskenMonotonicity

open MeasureTheory Manifold DifferentialGeometry DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator

/-! ## The kernel along a curve -/

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The backward heat kernel along a moving point.** For a curve `γ` with velocity `γ'`,

  `d/ds ρ(γ s, s) = ρ (n/(2τ) - ‖γ‖²/(4τ²) - ⟪γ, γ'⟫/(2τ))`,

the sum of the time derivative and of the spatial gradient `-ρ γ/(2τ)` paired with `γ'`. -/
theorem hasDerivAt_backwardHeatKernel_curve (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀)
    {γ : ℝ → E} {γ' : E} (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => backwardHeatKernel m t₀ s (γ s))
      (backwardHeatKernel m t₀ t (γ t) *
        ((m : ℝ) / (2 * (t₀ - t)) - ‖γ t‖ ^ 2 / (4 * (t₀ - t) ^ 2) -
          @inner ℝ E _ (γ t) γ' / (2 * (t₀ - t)))) t := by
  set K : ℝ × E → ℝ := fun q => backwardHeatKernel m t₀ q.1 q.2
  have hK : DifferentiableAt ℝ K (t, γ t) :=
    ((contDiffOn_backwardHeatKernel_prod m t₀).contDiffAt
      ((isOpen_lt_fst_backwardHeatKernel t₀).mem_nhds
        (show (t, γ t) ∈ {q : ℝ × E | q.1 < t₀} from hτ))).differentiableAt (by simp)
  set D := fderiv ℝ K (t, γ t)
  have h₁ : D ((1 : ℝ), (0 : E)) = backwardHeatKernel m t₀ t (γ t) *
      ((m : ℝ) / (2 * (t₀ - t)) - ‖γ t‖ ^ 2 / (4 * (t₀ - t) ^ 2)) := by
    have hc : HasDerivAt (K ∘ fun s => (s, γ t)) (D ((1 : ℝ), (0 : E))) t :=
      hK.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t (γ t)))
    exact hc.unique (hasDerivAt_backwardHeatKernel_time m t₀ hτ (γ t))
  have h₂ : D ((0 : ℝ), γ') =
      -(backwardHeatKernel m t₀ t (γ t) / (2 * (t₀ - t))) * @inner ℝ E _ (γ t) γ' := by
    have hsp : HasFDerivAt (fun y : E => K (t, y)) (D.comp (ContinuousLinearMap.inr ℝ ℝ E))
        (γ t) := hK.hasFDerivAt.comp (γ t) (hasFDerivAt_prodMk_right t (γ t))
    have happ := congrArg (fun L : E →L[ℝ] ℝ => L γ') hsp.fderiv
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inr_apply] at happ
    rw [← happ]
    exact fderiv_backwardHeatKernel m t₀ hτ (γ t) γ'
  have hmain : HasDerivAt (K ∘ fun s => (s, γ s)) (D ((1 : ℝ), γ')) t :=
    hK.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk hγ)
  have hsplit : D ((1 : ℝ), γ') = D ((1 : ℝ), (0 : E)) + D ((0 : ℝ), γ') := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  refine hmain.congr_deriv ?_
  rw [hsplit, h₁, h₂]
  ring

end Kernel

/-! ## Huisken's pointwise identity

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

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

/-- The Borel σ-algebra, matching the one under which `surfaceMeasure` is stated. -/
local instance instMeasurableSpaceMeanCurvatureFlow : MeasurableSpace M := borel M

local instance instBorelSpaceMeanCurvatureFlow : BorelSpace M := ⟨rfl⟩

namespace SmoothImmersion

variable [T2Space M] [I.Boundaryless]

/-! ## Normality of the mean curvature vector in every chart -/

/-- The mean curvature vector is orthogonal to every tangent vector `df(w)`. -/
theorem inner_meanCurvature_mfderiv (f : SmoothImmersion I M E) (p : M)
    (w : TangentSpace I p) :
    @inner ℝ E _ (f.meanCurvature p) (mfderiv I 𝓘(ℝ, E) f p w) = 0 := by
  have hmd : MDifferentiableAt I 𝓘(ℝ, E) f p := f.contMDiff.mdifferentiableAt (by simp)
  have h := DifferentialGeometry.Manifold.mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint I hmd
    BoundarylessManifold.isInteriorPoint
  rw [show mfderiv I 𝓘(ℝ, E) f p w =
      fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) w from
    congrArg (fun L : E₁ →L[ℝ] E => L w) h]
  exact inner_normalPart_fderiv (chartModelBasis E₁).span_eq
    (f.isFrameInverse_chartInvGramOnE p (mem_extChartAt_target p))
    (fun i j => chartInvGramOnE_symm (I := I) _ p i j _) _ w

/-- The mean curvature vector at a point is orthogonal to the tangent vectors of the chart
representation in *any* chart containing it. -/
theorem inner_meanCurvature_fderiv_chartRep (f : SmoothImmersion I M E)
    (α : M) {z : E₁} (hz : z ∈ (extChartAt I α).target) (v : E₁) :
    @inner ℝ E _ (f.meanCurvature ((extChartAt I α).symm z))
      (fderiv ℝ (f.chartRep α) z v) = 0 := by
  set x := (extChartAt I α).symm z
  have hx : x ∈ (extChartAt I α).source := (extChartAt I α).map_target hz
  have hzx : extChartAt I α x = z := (extChartAt I α).right_inv hz
  have hcont : ContinuousAt f x := f.contMDiff.continuous.continuousAt
  have hfx : f x ∈ (extChartAt 𝓘(ℝ, E) (f x)).source := by simp
  have h := DifferentialGeometry.Topology.Manifold.fderiv_fixed_chart_eq_trivialization_comp_mfderiv
    (I := I) (J := 𝓘(ℝ, E)) f α (f x) x hx hfx hcont
  rw [extChartAt_model_space_eq_id, TangentBundle.continuousLinearMapAt_model_space] at h
  have happ := DFunLike.congr_fun h v
  simp only [PartialEquiv.refl_coe, Function.comp_def, id_eq] at happ
  rw [hzx] at happ
  change @inner ℝ E _ _ (fderiv ℝ (fun y => f ((extChartAt I α).symm y)) z v) = 0
  rw [happ]
  exact f.inner_meanCurvature_mfderiv x _

end SmoothImmersion

namespace SmoothImmersionFamily

variable [T2Space M] [I.Boundaryless]

/-! ## Mean curvature flow at a time -/

/-- `F` moves by **mean curvature flow at time `t`**: `∂_t F = Hvec` at every point, at the
time `t`. The monotonicity formula at `t` needs the flow equation at `t` only. -/
def IsMeanCurvatureFlowAt (F : SmoothImmersionFamily I M E) (t : ℝ) : Prop :=
  ∀ p, HasDerivAt (fun s => F p s) ((F.slice t).meanCurvature p) t

omit [T2Space M] in
/-- The time velocity of the space-time chart representation is differentiable on the chart
target. -/
theorem differentiableAt_timeVelocity_spaceTimeChartRep (F : SmoothImmersionFamily I M E)
    (α : M) (t : ℝ) {z : E₁} (hz : z ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ (timeVelocity (F.spaceTimeChartRep α) t) z := by
  have hs := isOpen_univ_prod_extChartAt_target (I := I) α
  have hΦ : ContDiffAt ℝ 2 (F.spaceTimeChartRep α) (t, z) :=
    ((F.contDiffOn_spaceTimeChartRep α).contDiffAt
      (hs.mem_nhds ⟨Set.mem_univ _, hz⟩)).of_le (by simp)
  have h1 : DifferentiableAt ℝ (fderiv ℝ (F.spaceTimeChartRep α)) (t, z) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (h1.comp z ((differentiableAt_const t).prodMk differentiableAt_id)).clm_apply
    (differentiableAt_const _)

/-- Under mean curvature flow at `t`, the time velocity read in a chart is the mean
curvature vector. -/
theorem timeVelocity_spaceTimeChartRep (F : SmoothImmersionFamily I M E) {t : ℝ}
    (hmcf : F.IsMeanCurvatureFlowAt t) (α : M) {z : E₁}
    (hz : z ∈ (extChartAt I α).target) :
    timeVelocity (F.spaceTimeChartRep α) t z =
      (F.slice t).meanCurvature ((extChartAt I α).symm z) := by
  have hs := isOpen_univ_prod_extChartAt_target (I := I) α
  have hd : DifferentiableAt ℝ (F.spaceTimeChartRep α) (t, z) :=
    ((F.contDiffOn_spaceTimeChartRep α).contDiffAt
      (hs.mem_nhds ⟨Set.mem_univ _, hz⟩)).differentiableAt (by simp)
  have hc : HasDerivAt (F.spaceTimeChartRep α ∘ fun s => (s, z))
      (fderiv ℝ (F.spaceTimeChartRep α) (t, z) ((1 : ℝ), (0 : E₁))) t :=
    hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t z))
  exact hc.unique (hmcf ((extChartAt I α).symm z))

/-- Under mean curvature flow at `t`, the mean curvature vector is continuous: it is the time
velocity, read in a chart. -/
theorem continuous_meanCurvature (F : SmoothImmersionFamily I M E) {t : ℝ}
    (hmcf : F.IsMeanCurvatureFlowAt t) : Continuous (F.slice t).meanCurvature := by
  rw [continuous_iff_continuousAt]
  intro p
  have hc : ContinuousAt (timeVelocity (F.spaceTimeChartRep p) t) (extChartAt I p p) :=
    (F.differentiableAt_timeVelocity_spaceTimeChartRep p t
      (mem_extChartAt_target p)).continuousAt
  refine (hc.comp (continuousAt_extChartAt p)).congr ?_
  filter_upwards [extChartAt_source_mem_nhds (I := I) p] with q hq
  change timeVelocity _ t (extChartAt I p q) = (F.slice t).meanCurvature q
  rw [F.timeVelocity_spaceTimeChartRep hmcf p ((extChartAt I p).map_source hq),
    (extChartAt I p).left_inv hq]

/-- **The volume element under mean curvature flow.** The transport weight is
`tr(g⁻¹ ∂_t g) = -2 ‖Hvec‖²`, i.e. `∂_t dμ = -‖Hvec‖² dμ`. -/
theorem traceTimeDerivMetric_of_isMeanCurvatureFlowAt (F : SmoothImmersionFamily I M E)
    {t : ℝ} (hmcf : F.IsMeanCurvatureFlowAt t) (x : M) :
    traceTimeDerivMetric (I := I) F.inducedMetricFamily t x =
      -2 * ‖(F.slice t).meanCurvature x‖ ^ 2 := by
  set f := F.slice t
  set y := extChartAt I x x with hy_def
  set b := chartModelBasis E₁ with hb_def
  set Φ := F.spaceTimeChartRep x
  set gInv : Fin (Module.finrank ℝ E₁) → Fin (Module.finrank ℝ E₁) → ℝ :=
    fun i j => chartInvGramOnE f.inducedMetric x i j y with hgInv
  have hy : y ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hsymm : (extChartAt I x).symm y = x := extChartAt_to_inv x
  have hs := isOpen_univ_prod_extChartAt_target (I := I) x
  have hΦ : ContDiffAt ℝ 2 Φ (t, y) :=
    ((F.contDiffOn_spaceTimeChartRep x).contDiffAt
      (hs.mem_nhds ⟨Set.mem_univ _, hy⟩)).of_le (by simp)
  have hF2 : ContDiffAt ℝ 2 (F.chartRep t x) y := f.contDiffAt_chartRep x hy
  have hV := F.differentiableAt_timeVelocity_spaceTimeChartRep x t hy
  have hnormal : IsNormalAlongNear (F.chartRep t x) (timeVelocity Φ t) y := by
    filter_upwards [(isOpen_extChartAt_target (I := I) x).mem_nhds hy] with z hz v
    rw [F.timeVelocity_spaceTimeChartRep hmcf x hz]
    exact f.inner_meanCurvature_fderiv_chartRep x hz v
  have hcomm : ∀ k, HasDerivAt (fun s => frameTangent (F.chartRep s x) b y k)
      (frameTangent (timeVelocity Φ t) b y k) t := fun k =>
    hasDerivAt_fderiv_spatialSlice_of_contDiffAt hΦ (b k)
  have hderiv : ∀ i j, deriv (fun s => chartGramMatrix (I := I)
      (F.inducedMetricFamily s) x x i j) t =
      -2 * @inner ℝ E _ (timeVelocity Φ t y)
        (secondDerivative (F.chartRep t x) y (b i) (b j)) := by
    intro i j
    have hfun : (fun s => chartGramMatrix (I := I) (F.inducedMetricFamily s) x x i j) =
        fun s => frameGram (F.chartRep s x) b y i j := by
      funext s
      rw [inducedMetricFamily_apply]
      exact chartGramMatrix_inducedMetric_eq_frameGram_modelBasis F s x
        (mem_extChartAt_source x) i j
    rw [hfun]
    exact (hasDerivAt_frameGram_of_isNormalAlong (F := fun s => F.chartRep s x)
      (V := timeVelocity Φ) b i j hF2 hV hnormal hcomm).deriv
  have hinv : (chartGramMatrix (I := I) (F.inducedMetricFamily t) x x)⁻¹ = Matrix.of gInv := by
    ext i j
    change chartInvGramMatrix (I := I) f.inducedMetric x x i j =
      chartInvGramOnE f.inducedMetric x i j y
    rw [chartInvGramOnE_def, hsymm]
  -- the trace is `-2 ⟪V, g^{ij} D²F(b_i, b_j)⟫`
  have htrace : traceTimeDerivMetric (I := I) F.inducedMetricFamily t x =
      -2 * @inner ℝ E _ (timeVelocity Φ t y)
        (meanCurvatureVectorFrame (F.chartRep t x) b gInv y) := by
    rw [traceTimeDerivMetric_eq, hinv, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [← trace_metricEvolution (F := F.chartRep t x) (V := timeVelocity Φ t) (x := y) b gInv]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hderiv j i, secondDerivative_symm_of_contDiffAt hF2]
  -- the velocity is the mean curvature vector, which sees only the normal part of the trace
  have hVH : timeVelocity Φ t y = f.meanCurvature x := by
    rw [F.timeVelocity_spaceTimeChartRep hmcf x hy, hsymm]
  have hinvF : IsFrameInverse (F.chartRep t x) b y gInv := f.isFrameInverse_chartInvGramOnE x hy
  have hsymmG : ∀ i j, gInv i j = gInv j i := fun i j =>
    chartInvGramOnE_symm (I := I) _ x i j _
  have hzero : ∀ l, @inner ℝ E _ (f.meanCurvature x)
      (frameTangent (F.chartRep t x) b y l) = 0 := fun l =>
    inner_normalPart_frameTangent hinvF hsymmG _ l
  have hT0 : tangentialPart (F.chartRep t x) b gInv y (f.meanCurvature x) = 0 := by
    simp only [tangentialPart, hzero, mul_zero, zero_smul, Finset.sum_const_zero]
  have hN : normalPart (F.chartRep t x) b gInv y (f.meanCurvature x) = f.meanCurvature x := by
    rw [normalPart, hT0, sub_zero]
  have hHH := inner_meanCurvatureNormal_eq hinvF hsymmG (f.meanCurvature x)
  rw [hN] at hHH
  rw [htrace, hVH, ← hHH]
  exact congrArg (fun r => -2 * r) (real_inner_self_eq_norm_sq _)

/-! ## The monotonicity formula -/

/-- **Huisken's monotonicity formula** (Huisken 1990, Theorem 3.1), centred at the origin.
For a family of immersions of a closed `n`-manifold moving by mean curvature at time `t < t₀`,

  `d/dt ∫_M ρ(F, t) dμ_t = -∫_M ρ(F, t) ‖Hvec + F^⊥ / (2(t₀ - t))‖² dμ_t`. -/
theorem huisken_monotonicity_origin [CompactSpace M] (F : SmoothImmersionFamily I M E)
    (t₀ : ℝ) {t : ℝ} (hτ : t < t₀) (hmcf : F.IsMeanCurvatureFlowAt t) :
    HasDerivAt
      (fun s => ∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ s (F p s)
        ∂(F.surfaceMeasure s))
      (-∫ p, backwardHeatKernel (Module.finrank ℝ E₁) t₀ t (F p t) *
          ‖(F.slice t).meanCurvature p + (1 / (2 * (t₀ - t))) • (F.slice t).normalPosition p‖ ^ 2
        ∂(F.surfaceMeasure t)) t := by
  set n := Module.finrank ℝ E₁
  set f := F.slice t
  have hτ0 : t₀ - t ≠ 0 := (sub_pos.mpr hτ).ne'
  have hρ : Continuous fun p => backwardHeatKernel n t₀ t (F p t) :=
    (f.contMDiff_backwardHeatKernel_comp n t₀ hτ).continuous
  have hFc : Continuous fun p => F p t := (F.contMDiff_timeSlice t).continuous
  have hHc : Continuous f.meanCurvature := F.continuous_meanCurvature hmcf
  -- the transport formula, with the integrand evaluated along the flow
  have hT := hasDerivAt_integral_backwardHeatKernel F n hτ
  have hC : ∀ p, deriv (fun s => backwardHeatKernel n t₀ s (F p s)) t +
        (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) F.inducedMetricFamily t p *
          backwardHeatKernel n t₀ t (F p t) =
      backwardHeatKernel n t₀ t (F p t) *
        ((n : ℝ) / (2 * (t₀ - t)) - ‖F p t‖ ^ 2 / (4 * (t₀ - t) ^ 2) -
          @inner ℝ E _ (F p t) (f.meanCurvature p) / (2 * (t₀ - t)) -
          ‖f.meanCurvature p‖ ^ 2) := by
    intro p
    rw [(hasDerivAt_backwardHeatKernel_curve n t₀ hτ (hmcf p)).deriv,
      F.traceTimeDerivMetric_of_isMeanCurvatureFlowAt hmcf p]
    ring
  -- Huisken's pointwise identity: chain-rule integrand = -(squared norm) + first variation
  have hsplit : ∀ p, backwardHeatKernel n t₀ t (F p t) *
        ((n : ℝ) / (2 * (t₀ - t)) - ‖F p t‖ ^ 2 / (4 * (t₀ - t) ^ 2) -
          @inner ℝ E _ (F p t) (f.meanCurvature p) / (2 * (t₀ - t)) -
          ‖f.meanCurvature p‖ ^ 2) =
      -(backwardHeatKernel n t₀ t (F p t) *
          ‖f.meanCurvature p + (1 / (2 * (t₀ - t))) • f.normalPosition p‖ ^ 2) +
        (1 / (2 * (t₀ - t))) * (backwardHeatKernel n t₀ t (F p t) *
          ((n : ℝ) - f.tangentialSqNorm p / (2 * (t₀ - t)) +
            @inner ℝ E _ (F p t) (f.meanCurvature p))) := by
    intro p
    have h := huisken_pointwise_identity n (t₀ - t) hτ0 (F p t) (f.normalPosition p)
      (f.meanCurvature p) (backwardHeatKernel n t₀ t (F p t))
      (f.inner_sub_normalPosition p) (f.inner_meanCurvature_sub_normalPosition p)
    rwa [show ‖F p t - f.normalPosition p‖ ^ 2 = f.tangentialSqNorm p from
      f.norm_sub_normalPosition_sq p, real_inner_comm (F p t) (f.meanCurvature p)] at h
  have hFV : Integrable (fun p => backwardHeatKernel n t₀ t (F p t) *
      ((n : ℝ) - f.tangentialSqNorm p / (2 * (t₀ - t)) +
        @inner ℝ E _ (F p t) (f.meanCurvature p))) (F.surfaceMeasure t) :=
    f.integrable_firstVariation n t₀ hτ
  have hFV0 : ∫ p, backwardHeatKernel n t₀ t (F p t) *
      ((n : ℝ) - f.tangentialSqNorm p / (2 * (t₀ - t)) +
        @inner ℝ E _ (F p t) (f.meanCurvature p)) ∂(F.surfaceMeasure t) = 0 :=
    f.integral_firstVariation n t₀ hτ
  have hCint : Integrable (fun p => backwardHeatKernel n t₀ t (F p t) *
      ((n : ℝ) / (2 * (t₀ - t)) - ‖F p t‖ ^ 2 / (4 * (t₀ - t) ^ 2) -
        @inner ℝ E _ (F p t) (f.meanCurvature p) / (2 * (t₀ - t)) -
        ‖f.meanCurvature p‖ ^ 2)) (F.surfaceMeasure t) :=
    f.integrable_of_continuous (by fun_prop)
  have hS : Integrable (fun p => backwardHeatKernel n t₀ t (F p t) *
      ‖f.meanCurvature p + (1 / (2 * (t₀ - t))) • f.normalPosition p‖ ^ 2)
      (F.surfaceMeasure t) := by
    refine ((hFV.const_mul (1 / (2 * (t₀ - t)))).sub hCint).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply, hsplit p]
    ring
  have hval : ∫ p, (deriv (fun s => backwardHeatKernel n t₀ s (F p s)) t +
        (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) F.inducedMetricFamily t p *
          backwardHeatKernel n t₀ t (F p t)) ∂(F.surfaceMeasure t) =
      -∫ p, backwardHeatKernel n t₀ t (F p t) *
          ‖f.meanCurvature p + (1 / (2 * (t₀ - t))) • f.normalPosition p‖ ^ 2
        ∂(F.surfaceMeasure t) := by
    have hS' : Integrable (fun p => -(backwardHeatKernel n t₀ t (F p t) *
        ‖f.meanCurvature p + (1 / (2 * (t₀ - t))) • f.normalPosition p‖ ^ 2))
        (F.surfaceMeasure t) := hS.neg
    have hFV' : Integrable (fun p => (1 / (2 * (t₀ - t))) * (backwardHeatKernel n t₀ t (F p t) *
        ((n : ℝ) - f.tangentialSqNorm p / (2 * (t₀ - t)) +
          @inner ℝ E _ (F p t) (f.meanCurvature p)))) (F.surfaceMeasure t) :=
      hFV.const_mul _
    simp only [hC, hsplit]
    rw [integral_add hS' hFV', integral_neg, integral_const_mul, hFV0]
    ring
  rw [hval] at hT
  exact hT

end SmoothImmersionFamily

end HuiskenMonotonicity
