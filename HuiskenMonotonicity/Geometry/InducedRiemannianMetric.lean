/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.SmoothImmersionFamily
import HuiskenMonotonicity.MetricEvolution
import DifferentialGeometry.Topology.Manifold.MFDeriv.Interior
import DifferentialGeometry.Topology.Manifold.ChartDifferential
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Analysis.Integration.Measure.Family.VolumeVariation
import DifferentialGeometry.Analysis.Integration.Measure.Family.Regularity

/-!
# The induced Riemannian metric and surface measure of an immersion family

The metric induced on `M` by a time slice `F_t` is the pullback of the ambient Euclidean
metric,

`g_t(v, w) = ⟪dF_t v, dF_t w⟫`.

Bundling it as a Riemannian metric needs smooth dependence of the form on the base point in
manifold charts. `DifferentialGeometry` supplies that. Its
`SmoothRiemannianMetric.pullback` bundles the pullback of a metric along an immersion, with
the chart-smoothness discharged by `SmoothRiemannianMetric.pullbackInner_contMDiff`. This
file applies it to the Euclidean metric on the ambient space to obtain

* `SmoothImmersion.inducedMetric` — the bundled `SmoothRiemannianMetric I M` of an
  immersion, and `SmoothImmersionFamily.inducedMetric` for a time slice;
* `inducedMetricFamily` — the time-indexed family, in the shape
  `ℝ → SmoothRiemannianMetric I M` required by
  `DifferentialGeometry.Integral.Measure.volume_variation_formula`;
* `surfaceMeasure` — the Riemannian volume measure `dμ_t`.

## The global-in-time immersion hypothesis

`volume_variation_formula` differentiates the metric family in time at *every* real time
(see `MetricFamilyRegularAt`), so it needs a family defined on all of `ℝ`. The
immersion condition of `SmoothImmersionFamily` is therefore quantified over every time.

## Measurable structure

`DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure` is stated with the Borel
σ-algebra of `M` installed as a local instance, so this file installs the same one. Any
downstream statement about `surfaceMeasure` must use that σ-algebra, which is why the
measurable structure is *not* taken as an instance parameter here.
-/

open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace

open MeasureTheory

noncomputable section

namespace HuiskenMonotonicity

open Manifold DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator (chartGramOnE)

universe u v w

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H : Type v} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E₁ H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]

/-- The Borel σ-algebra, matching the local instance under which
`DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure` is stated. -/
local instance : MeasurableSpace M := borel M

local instance : BorelSpace M := ⟨rfl⟩

namespace SmoothImmersion

section Metric

variable [T2Space M]

/-- The Riemannian metric induced on `M` by a smooth immersion `f`, bundled as a
`SmoothRiemannianMetric`.

This is the pullback of the ambient Euclidean metric along `f`. The smooth dependence on
the base point comes from `DifferentialGeometry.SmoothRiemannianMetric.pullbackInner_contMDiff`. -/
def inducedMetric (f : SmoothImmersion I M E) : SmoothRiemannianMetric I M :=
  (euclideanMetric (E := E)).pullback (I := I) f f.contMDiff f.mfderiv_injective

@[simp]
theorem inducedMetric_inner (f : SmoothImmersion I M E) (p : M) (v w : TangentSpace I p) :
    f.inducedMetric.inner p v w =
      ⟪mvfderiv I f p v, mvfderiv I f p w⟫_ℝ :=
  rfl

/-- The chart Gram matrix of the induced metric is the Gram matrix of the chart frame pushed
forward by `df`. -/
theorem chartGramMatrix_inducedMetric (f : SmoothImmersion I M E)
    (x₀ x : M) (i j : Fin (Module.finrank ℝ E₁)) :
    Tensor.Coordinates.chartGramMatrix (I := I) f.inducedMetric x₀ x i j =
      ⟪mvfderiv I f x (Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i x),
        mvfderiv I f x (Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j x)⟫_ℝ := by
  rw [Tensor.Coordinates.chartGramMatrix_apply, inducedMetric_inner]

/-! ### The chart representation

`mfderiv` of `f`, viewed on the model space, is the `fderiv` of the chart representation
`f ∘ (extChartAt I x).symm`. That identification turns the entries of the chart Gram matrix
into `frameGram` of the chart representation against the model basis. -/

/-- The chart representation of `f` around `x`, as a map between model spaces. -/
def chartRep (f : SmoothImmersion I M E) (x : M) : E₁ → E :=
  fun y ↦ f ((extChartAt I x).symm y)

omit [T2Space M] in
/-- The chart representation is smooth on the chart target. -/
theorem contDiffOn_chartRep (f : SmoothImmersion I M E) (x₀ : M) :
    ContDiffOn ℝ ∞ (f.chartRep x₀) (extChartAt I x₀).target :=
  (f.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm x₀)).contDiffOn

omit [T2Space M] in
/-- The chart representation is `C²` at points of the chart target. -/
theorem contDiffAt_chartRep [I.Boundaryless] (f : SmoothImmersion I M E) (α : M) {y : E₁}
    (hy : y ∈ (extChartAt I α).target) : ContDiffAt ℝ 2 (f.chartRep α) y :=
  ((f.contDiffOn_chartRep α).contDiffAt
    ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)).of_le (by simp)

/-- In the chart fixed at `x₀`, the chart Gram entries are the `frameGram` of the chart
representation against the *constant* model basis, evaluated at the chart coordinate of `x`.

The work is done by the library's
`Topology.Manifold.fderiv_fixed_chart_eq_trivialization_comp_mfderiv`, specialised to a
vector-space target, where the outer chart and trivialization are trivial. -/
theorem chartGramMatrix_inducedMetric_eq_frameGram_modelBasis [I.Boundaryless]
    (f : SmoothImmersion I M E)
    (x₀ : M) {x : M} (hx : x ∈ (extChartAt I x₀).source)
    (i j : Fin (Module.finrank ℝ E₁)) :
    Tensor.Coordinates.chartGramMatrix (I := I) f.inducedMetric x₀ x i j =
      frameGram (f.chartRep x₀) (Tensor.Coordinates.chartModelBasis E₁)
        (extChartAt I x₀ x) i j := by
  have hcont : ContinuousAt f x := f.contMDiff.continuous.continuousAt
  have hfx : f x ∈ (extChartAt 𝓘(ℝ, E) (f x)).source := by simp
  have h := DifferentialGeometry.Topology.Manifold.fderiv_fixed_chart_eq_trivialization_comp_mfderiv
    (I := I) (J := 𝓘(ℝ, E)) f x₀ (f x) x hx hfx hcont
  -- the outer chart and trivialization are trivial for a vector-space target
  rw [extChartAt_model_space_eq_id, TangentBundle.continuousLinearMapAt_model_space] at h
  have key : ∀ k : Fin (Module.finrank ℝ E₁),
      fderiv ℝ (f.chartRep x₀) (extChartAt I x₀ x)
          (Tensor.Coordinates.chartModelBasis E₁ k) =
        mvfderiv I f x (Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ k x) := by
    intro k
    have happ := DFunLike.congr_fun h (Tensor.Coordinates.chartModelBasis E₁ k)
    simp only [PartialEquiv.refl_coe, Function.comp_def, id_eq] at happ
    exact happ
  rw [chartGramMatrix_inducedMetric, frameGram, frameTangent_apply, frameTangent_apply,
    key i, key j]

/-- The chart-representation form of the chart Gram entries. -/
theorem chartGramOnE_inducedMetric [I.Boundaryless] (f : SmoothImmersion I M E)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E₁)) {y : E₁}
    (hy : y ∈ (extChartAt I x₀).target) :
    chartGramOnE (I := I) f.inducedMetric x₀ i j y =
      frameGram (f.chartRep x₀) (Tensor.Coordinates.chartModelBasis E₁) y i j := by
  have hmem : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hy
  have hyy : extChartAt I x₀ ((extChartAt I x₀).symm y) = y := (extChartAt I x₀).right_inv hy
  rw [chartGramOnE, f.chartGramMatrix_inducedMetric_eq_frameGram_modelBasis x₀ hmem i j, hyy]

end Metric

/-- The surface measure of `f`: the Riemannian volume measure of the induced metric. -/
def surfaceMeasure [T2Space M] [SigmaCompactSpace M] (f : SmoothImmersion I M E) :
    Measure M :=
  riemannianVolumeMeasure I M f.inducedMetric

end SmoothImmersion

namespace SmoothImmersionFamily

section Metric

variable [T2Space M]

/-- The Riemannian metric induced on `M` by the time slice `F_t`. -/
def inducedMetric (F : SmoothImmersionFamily I M E) (t : ℝ) : SmoothRiemannianMetric I M :=
  (F.slice t).inducedMetric

/-- The time-indexed family of induced metrics, in the shape consumed by
`DifferentialGeometry.Integral.Measure.volume_variation_formula`. -/
def inducedMetricFamily (F : SmoothImmersionFamily I M E) :
    ℝ → SmoothRiemannianMetric I M :=
  fun t ↦ F.inducedMetric t

@[simp]
theorem inducedMetricFamily_apply (F : SmoothImmersionFamily I M E)
    (t : ℝ) :
    F.inducedMetricFamily t = F.inducedMetric t :=
  rfl

/-- The chart representation of the time slice `F_t` around `x`. -/
def chartRep (F : SmoothImmersionFamily I M E) (t : ℝ) (x : M) : E₁ → E :=
  (F.slice t).chartRep x

/-! ### Smoothness of the space-time chart representation

Everything the regularity hypothesis needs is a statement about the chart representation of
the space-time map, as an honest map `ℝ × E₁ → E`. It is smooth on the chart target, and
the proof is mathlib's chart API composed with `contMDiff_spaceTime`:
`contMDiffOn_extChartAt_symm` for the inverse chart, `ContMDiff.comp_contMDiffOn` for the
composite, and `contMDiffOn_iff_contDiffOn` to land back in Fréchet calculus. -/

/-- The space-time chart representation around `x₀`, as a map `ℝ × E₁ → E`. -/
def spaceTimeChartRep (F : SmoothImmersionFamily I M E) (x₀ : M) : ℝ × E₁ → E :=
  fun p ↦ F.chartRep p.1 x₀ p.2

omit [T2Space M] in
/-- The space-time chart representation is smooth on the chart target. -/
theorem contDiffOn_spaceTimeChartRep (F : SmoothImmersionFamily I M E) (x₀ : M) :
    ContDiffOn ℝ ∞ (F.spaceTimeChartRep x₀)
      (Set.univ ×ˢ (extChartAt I x₀).target) := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E₁) I ∞ (extChartAt I x₀).symm (extChartAt I x₀).target :=
    contMDiffOn_extChartAt_symm x₀
  have hmaps : Set.MapsTo (fun p : ℝ × E₁ ↦ p.2)
      (Set.univ ×ˢ (extChartAt I x₀).target) (extChartAt I x₀).target :=
    fun _ hp ↦ hp.2
  -- Build the inner map with the self-model on `ℝ × E₁`, avoiding the product
  -- charted-space structure, whose instances do not match `chartedSpaceSelf`.
  have hsnd : ContMDiff 𝓘(ℝ, ℝ × E₁) 𝓘(ℝ, E₁) ∞ (fun p : ℝ × E₁ ↦ p.2) :=
    (contDiff_snd (𝕜 := ℝ)).contMDiff
  have hfst : ContMDiff 𝓘(ℝ, ℝ × E₁) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × E₁ ↦ p.1) :=
    (contDiff_fst (𝕜 := ℝ)).contMDiff
  have hg : ContMDiffOn 𝓘(ℝ, ℝ × E₁) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × E₁ ↦ ((extChartAt I x₀).symm p.2, p.1))
      (Set.univ ×ˢ (extChartAt I x₀).target) :=
    (hsymm.comp hsnd.contMDiffOn hmaps).prodMk hfst.contMDiffOn
  exact (F.contMDiff_spaceTime.comp_contMDiffOn hg).contDiffOn

/-- In the chart fixed at `x₀`, the chart Gram entries of `F_t` are the `frameGram` of its
chart representation against the model basis. -/
theorem chartGramMatrix_inducedMetric_eq_frameGram_modelBasis [I.Boundaryless]
    (F : SmoothImmersionFamily I M E) (t : ℝ)
    (x₀ : M) {x : M} (hx : x ∈ (extChartAt I x₀).source)
    (i j : Fin (Module.finrank ℝ E₁)) :
    Tensor.Coordinates.chartGramMatrix (I := I) (F.inducedMetric t) x₀ x i j =
      frameGram (F.chartRep t x₀) (Tensor.Coordinates.chartModelBasis E₁)
        (extChartAt I x₀ x) i j :=
  (F.slice t).chartGramMatrix_inducedMetric_eq_frameGram_modelBasis x₀ hx i j

/-! ### The regularity hypothesis, in chart-representation form

`MetricFamilyRegularAt.of_chartGramOnE` consumes the chart Gram entries as a function on
`ℝ × E₁`, namely `chartGramOnE`. For the induced metric family that function is a
`frameGram` of the space-time chart representation against the constant model basis. -/

/-- The chart-representation form of the chart Gram entries of the induced metric family. -/
theorem chartGramOnE_inducedMetricFamily [I.Boundaryless]
    (F : SmoothImmersionFamily I M E)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E₁)) (t : ℝ) {y : E₁}
    (hy : y ∈ (extChartAt I x₀).target) :
    chartGramOnE (I := I) (F.inducedMetricFamily t) x₀ i j y =
      frameGram (F.chartRep t x₀) (Tensor.Coordinates.chartModelBasis E₁) y i j :=
  (F.slice t).chartGramOnE_inducedMetric x₀ i j hy

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E₁] [T2Space M] in
/-- The chart target, crossed with all times, is open. -/
lemma isOpen_univ_prod_extChartAt_target [I.Boundaryless] (x₀ : M) :
    IsOpen ((Set.univ : Set ℝ) ×ˢ (extChartAt I x₀).target) :=
  isOpen_univ.prod (isOpen_extChartAt_target (I := I) x₀)

omit [T2Space M] in
/-- A spatial derivative of the chart representation is a partial derivative of the
space-time chart representation, at points of the chart target. -/
theorem fderiv_chartRep_eq_fderiv_spaceTimeChartRep [I.Boundaryless]
    (F : SmoothImmersionFamily I M E) (x₀ : M) {p : ℝ × E₁}
    (hp : p ∈ Set.univ ×ˢ (extChartAt I x₀).target) (v : E₁) :
    fderiv ℝ (F.chartRep p.1 x₀) p.2 v =
      fderiv ℝ (F.spaceTimeChartRep x₀) p ((0 : ℝ), v) := by
  have hs := isOpen_univ_prod_extChartAt_target (I := I) x₀
  have hΦ : HasFDerivAt (F.spaceTimeChartRep x₀)
      (fderiv ℝ (F.spaceTimeChartRep x₀) p) p :=
    (((F.contDiffOn_spaceTimeChartRep x₀).differentiableOn (by norm_num)).differentiableAt
      (hs.mem_nhds hp)).hasFDerivAt
  have hcomp : HasFDerivAt ((F.spaceTimeChartRep x₀) ∘ fun z : E₁ ↦ (p.1, z))
      ((fderiv ℝ (F.spaceTimeChartRep x₀) p).comp
        (ContinuousLinearMap.inr ℝ ℝ E₁)) p.2 :=
    hΦ.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  have hslice : HasFDerivAt (F.chartRep p.1 x₀)
      ((fderiv ℝ (F.spaceTimeChartRep x₀) p).comp
        (ContinuousLinearMap.inr ℝ ℝ E₁)) p.2 := hcomp
  rw [hslice.fderiv]
  rfl

/-- **Joint continuity of the chart Gram entries.** The second field of
`MetricFamilyRegularAt.of_chartGramOnE`. -/
theorem continuousOn_chartGramOnE_inducedMetricFamily [I.Boundaryless]
    (F : SmoothImmersionFamily I M E)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E₁)) :
    ContinuousOn
      (fun p : ℝ × E₁ ↦
        chartGramOnE (I := I) (F.inducedMetricFamily p.1) x₀ i j p.2)
      (Set.univ ×ˢ (extChartAt I x₀).target) := by
  have hs := isOpen_univ_prod_extChartAt_target (I := I) x₀
  have hfd : ContinuousOn (fderiv ℝ (F.spaceTimeChartRep x₀))
      (Set.univ ×ˢ (extChartAt I x₀).target) :=
    (F.contDiffOn_spaceTimeChartRep x₀).continuousOn_fderiv_of_isOpen hs (by norm_num)
  have hev : ∀ v : E₁, ContinuousOn
      (fun p : ℝ × E₁ ↦ fderiv ℝ (F.spaceTimeChartRep x₀) p ((0 : ℝ), v))
      (Set.univ ×ˢ (extChartAt I x₀).target) := fun v ↦
    ((ContinuousLinearMap.apply ℝ E ((0 : ℝ), v)).continuous).comp_continuousOn hfd
  refine ((hev (Tensor.Coordinates.chartModelBasis E₁ i)).inner
    (hev (Tensor.Coordinates.chartModelBasis E₁ j))).congr ?_
  intro p hp
  dsimp only
  rw [chartGramOnE_inducedMetricFamily F x₀ i j p.1 hp.2, frameGram,
    frameTangent_apply, frameTangent_apply,
    fderiv_chartRep_eq_fderiv_spaceTimeChartRep F x₀ hp
      (Tensor.Coordinates.chartModelBasis E₁ i),
    fderiv_chartRep_eq_fderiv_spaceTimeChartRep F x₀ hp
      (Tensor.Coordinates.chartModelBasis E₁ j)]

/-! ### The derivative of the chart Gram entries, and its continuity

The derivative needs neither the velocity nor any normality hypothesis: it is the plain
product rule applied to `⟪∂_i Φ, ∂_j Φ⟫`, with the time derivative of a spatial partial
derivative given by `hasDerivAt_fderiv_partial_time`. So all three fields of
`of_chartGramOnE` follow from smoothness of the space-time chart representation alone. The
velocity and the normality enter only later, when the *value* of the trace is evaluated. -/

/-- The time derivative of the chart Gram entries, in chart-representation form. -/
noncomputable def chartGramDeriv (F : SmoothImmersionFamily I M E) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E₁)) (t : ℝ) (y : E₁) : ℝ :=
  ⟪fderiv ℝ (F.spaceTimeChartRep x₀) (t, y) ((0 : ℝ), Tensor.Coordinates.chartModelBasis E₁ i),
      fderiv ℝ (fderiv ℝ (F.spaceTimeChartRep x₀)) (t, y) ((1 : ℝ), (0 : E₁))
        ((0 : ℝ), Tensor.Coordinates.chartModelBasis E₁ j)⟫_ℝ +
    ⟪fderiv ℝ (fderiv ℝ (F.spaceTimeChartRep x₀)) (t, y) ((1 : ℝ), (0 : E₁))
        ((0 : ℝ), Tensor.Coordinates.chartModelBasis E₁ i),
      fderiv ℝ (F.spaceTimeChartRep x₀) (t, y) ((0 : ℝ), Tensor.Coordinates.chartModelBasis E₁ j)⟫_ℝ

/-- **The derivative property.** The first field of
`MetricFamilyRegularAt.of_chartGramOnE`. -/
theorem hasDerivAt_chartGramMatrix_chartGramDeriv [I.Boundaryless]
    (F : SmoothImmersionFamily I M E)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E₁)) (t : ℝ) {x : M}
    (hx : x ∈ (trivializationAt E₁ (TangentSpace I) x₀).baseSet) :
    HasDerivAt
      (fun s : ℝ ↦ Tensor.Coordinates.chartGramMatrix (I := I)
        (F.inducedMetricFamily s) x₀ x i j)
      (F.chartGramDeriv x₀ i j t (extChartAt I x₀ x)) t := by
  have hxs : x ∈ (extChartAt I x₀).source :=
    baseSet_subset_extChartAt_source (I := I) x₀ hx
  have hy : extChartAt I x₀ x ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hxs
  have hmem : ((t, extChartAt I x₀ x) : ℝ × E₁) ∈
      (Set.univ : Set ℝ) ×ˢ (extChartAt I x₀).target := ⟨Set.mem_univ _, hy⟩
  have hs := isOpen_univ_prod_extChartAt_target (I := I) x₀
  have hΦ : ContDiffAt ℝ 2 (F.spaceTimeChartRep x₀) (t, extChartAt I x₀ x) :=
    ((F.contDiffOn_spaceTimeChartRep x₀).contDiffAt (hs.mem_nhds hmem)).of_le (by norm_num)
  -- rewrite the function of `s` into chart-representation form
  have hfun : (fun s : ℝ ↦ Tensor.Coordinates.chartGramMatrix (I := I)
        (F.inducedMetricFamily s) x₀ x i j)
      = fun s : ℝ ↦
        ⟪fderiv ℝ (F.spaceTimeChartRep x₀) (s, extChartAt I x₀ x)
            ((0 : ℝ), Tensor.Coordinates.chartModelBasis E₁ i),
          fderiv ℝ (F.spaceTimeChartRep x₀) (s, extChartAt I x₀ x)
            ((0 : ℝ), Tensor.Coordinates.chartModelBasis E₁ j)⟫_ℝ := by
    funext s
    rw [inducedMetricFamily_apply,
      chartGramMatrix_inducedMetric_eq_frameGram_modelBasis F s x₀ hxs i j,
      frameGram, frameTangent_apply, frameTangent_apply,
      fderiv_chartRep_eq_fderiv_spaceTimeChartRep F x₀
        (p := (s, extChartAt I x₀ x)) ⟨Set.mem_univ _, hy⟩
        (Tensor.Coordinates.chartModelBasis E₁ i),
      fderiv_chartRep_eq_fderiv_spaceTimeChartRep F x₀
        (p := (s, extChartAt I x₀ x)) ⟨Set.mem_univ _, hy⟩
        (Tensor.Coordinates.chartModelBasis E₁ j)]
  rw [hfun]
  exact HasDerivAt.inner ℝ
    (hasDerivAt_fderiv_partial_time hΦ (Tensor.Coordinates.chartModelBasis E₁ i))
    (hasDerivAt_fderiv_partial_time hΦ (Tensor.Coordinates.chartModelBasis E₁ j))

omit [T2Space M] in
/-- **Joint continuity of the derivative.** The third field of
`MetricFamilyRegularAt.of_chartGramOnE`. -/
theorem continuousOn_chartGramDeriv [I.Boundaryless]
    (F : SmoothImmersionFamily I M E) (x₀ : M) (i j : Fin (Module.finrank ℝ E₁)) :
    ContinuousOn (fun p : ℝ × E₁ ↦ F.chartGramDeriv x₀ i j p.1 p.2)
      ((Set.univ : Set ℝ) ×ˢ (extChartAt I x₀).target) := by
  have hs := isOpen_univ_prod_extChartAt_target (I := I) x₀
  have hfd : ContinuousOn (fderiv ℝ (F.spaceTimeChartRep x₀))
      ((Set.univ : Set ℝ) ×ˢ (extChartAt I x₀).target) :=
    (F.contDiffOn_spaceTimeChartRep x₀).continuousOn_fderiv_of_isOpen hs (by norm_num)
  have hfd2 : ContinuousOn (fderiv ℝ (fderiv ℝ (F.spaceTimeChartRep x₀)))
      ((Set.univ : Set ℝ) ×ˢ (extChartAt I x₀).target) :=
    ((F.contDiffOn_spaceTimeChartRep x₀).fderiv_of_isOpen hs
      (m := 1) (by simp)).continuousOn_fderiv_of_isOpen hs (by norm_num)
  have hev : ∀ v : E₁, ContinuousOn
      (fun p : ℝ × E₁ ↦ fderiv ℝ (F.spaceTimeChartRep x₀) p ((0 : ℝ), v))
      ((Set.univ : Set ℝ) ×ˢ (extChartAt I x₀).target) := fun v ↦
    ((ContinuousLinearMap.apply ℝ E ((0 : ℝ), v)).continuous).comp_continuousOn hfd
  have hev2 : ∀ v : E₁, ContinuousOn
      (fun p : ℝ × E₁ ↦ fderiv ℝ (fderiv ℝ (F.spaceTimeChartRep x₀)) p
        ((1 : ℝ), (0 : E₁)) ((0 : ℝ), v))
      ((Set.univ : Set ℝ) ×ˢ (extChartAt I x₀).target) := fun v ↦
    ((ContinuousLinearMap.apply ℝ E ((0 : ℝ), v)).continuous).comp_continuousOn
      (((ContinuousLinearMap.apply ℝ ((ℝ × E₁) →L[ℝ] E) ((1 : ℝ), (0 : E₁))).continuous)
        |>.comp_continuousOn hfd2)
  exact ((hev (Tensor.Coordinates.chartModelBasis E₁ i)).inner
      (hev2 (Tensor.Coordinates.chartModelBasis E₁ j))).add
    ((hev2 (Tensor.Coordinates.chartModelBasis E₁ i)).inner
      (hev (Tensor.Coordinates.chartModelBasis E₁ j)))

/-- **The induced metric family is regular.**

Discharges the regularity hypothesis of
`DifferentialGeometry.Integral.Measure.volume_variation_formula` for the induced metric
family of a smooth immersion family, from smoothness alone. The library assumes this
hypothesis wherever it needs it and never constructs it. -/
theorem metricFamilyRegularAt_inducedMetricFamily [I.Boundaryless]
    (F : SmoothImmersionFamily I M E)
    (t₀ : ℝ) :
    MetricFamilyRegularAt (I := I) (F.inducedMetricFamily) t₀ :=
  MetricFamilyRegularAt.of_chartGramOnE (I := I)
    (fun x₀ i j ↦ F.chartGramDeriv x₀ i j)
    (fun x₀ i j t _ hx ↦
      hasDerivAt_chartGramMatrix_chartGramDeriv F x₀ i j t hx)
    (fun x₀ i j ↦ continuousOn_chartGramOnE_inducedMetricFamily F x₀ i j)
    (fun x₀ i j ↦ continuousOn_chartGramDeriv F x₀ i j)

end Metric

section SurfaceMeasure

variable [T2Space M] [SigmaCompactSpace M]

/-- The surface measure `dμ_t` of the time slice `F_t`. -/
def surfaceMeasure (F : SmoothImmersionFamily I M E) (t : ℝ) : Measure M :=
  (F.slice t).surfaceMeasure

/-- The surface measure is the Riemannian measure family of the induced metric family. This
is the form in which `volume_variation_formula` expects the measure. -/
theorem surfaceMeasure_eq_riemannianMeasureFamily (F : SmoothImmersionFamily I M E) :
    F.surfaceMeasure =
      riemannianMeasureFamily (I := I) (M := M) (F.inducedMetricFamily) :=
  rfl

end SurfaceMeasure

end SmoothImmersionFamily

end HuiskenMonotonicity
