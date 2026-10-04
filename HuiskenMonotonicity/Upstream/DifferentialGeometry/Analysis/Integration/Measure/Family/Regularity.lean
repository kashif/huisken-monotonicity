import DifferentialGeometry.Analysis.Integration.Measure.Family.Defs

/-!
# A chart-local constructor for `MetricFamilyRegularAt`

`MetricFamilyRegularAt` is the regularity hypothesis of
`Integral.Measure.volume_variation_formula`. Its only constructor,
`MetricFamilyRegularAt.of_chartGram_timeDeriv`, asks for continuity of the chart Gram
entries and of their time derivative as functions on `ℝ × M`, restricted to
`Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet`.

That shape is awkward to verify, because the data one actually has is usually a function of
`(t, y) ∈ ℝ × E`: a chart representation. This file reduces the hypothesis to exactly that,
by transporting along `extChartAt I x₀`:

* `chartGramMatrixOnE` reads the chart Gram entries as a function on `ℝ × E`;
* `MetricFamilyRegularAt.of_chartGramOnE` builds `MetricFamilyRegularAt` from the
  derivative property together with continuity *on the chart target*, where ordinary
  Fréchet calculus applies.

The transport is possible because `(trivializationAt E (TangentSpace I) x₀).baseSet` is the
chart source, on which `extChartAt I x₀` is continuous, maps into the chart target and is
inverted by its symm.

Intended upstream location:
`DifferentialGeometry/Analysis/Integration/Measure/Family/Regularity.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart Gram entries of a metric family, read as a function of a time and a point of
the model space. -/
def chartGramMatrixOnE (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) (t : ℝ) (y : E) : ℝ :=
  DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₀
    ((extChartAt I x₀).symm y) i j

/-- On the chart source, the chart-representation form agrees with the chart Gram entry. -/
lemma chartGramMatrixOnE_extChartAt
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) (t : ℝ) {x : M}
    (hx : x ∈ (extChartAt I x₀).source) :
    chartGramMatrixOnE (I := I) g_fam x₀ i j t (extChartAt I x₀ x) =
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₀ x i j := by
  rw [chartGramMatrixOnE, (extChartAt I x₀).left_inv hx]

/-- The trivialization base set is contained in the source of the extended chart. -/
lemma baseSet_subset_extChartAt_source (x₀ : M) :
    (trivializationAt E (TangentSpace I) x₀).baseSet ⊆ (extChartAt I x₀).source := by
  rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
  exact subset_of_eq
    (DifferentialGeometry.Tensor.Coordinates.trivializationAt_baseSet_eq_chartAt_source
      (I := I) x₀)

/-- **Chart-local constructor for `MetricFamilyRegularAt`.**

The time derivative is supplied as a function `D` of a time and a point of the model space,
and the two continuity conditions are imposed on the chart target, where they are ordinary
statements about functions on `ℝ × E`. -/
theorem MetricFamilyRegularAt.of_chartGramOnE
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t₀ : ℝ}
    (D : M → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ → E → ℝ)
    (hderiv : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)) (t : ℝ) {x : M},
      x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      HasDerivAt
        (fun s : ℝ =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j)
        (D x₀ i j t (extChartAt I x₀ x)) t)
    (hcontG : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × E => chartGramMatrixOnE (I := I) g_fam x₀ i j p.1 p.2)
        (univ ×ˢ (extChartAt I x₀).target))
    (hcontD : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × E => D x₀ i j p.1 p.2)
        (univ ×ˢ (extChartAt I x₀).target)) :
    MetricFamilyRegularAt (I := I) g_fam t₀ := by
  refine MetricFamilyRegularAt.of_chartGram_timeDeriv (I := I) ?_
  intro x₀ i j
  refine ⟨fun t x => D x₀ i j t (extChartAt I x₀ x), ?_, ?_, ?_⟩
  · intro t x hx
    exact hderiv x₀ i j t hx
  · -- continuity of the Gram entries, transported from the chart target
    have hmap : ContinuousOn (fun p : ℝ × M => (p.1, extChartAt I x₀ p.2))
        (univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      refine ContinuousOn.prodMk (continuous_fst.continuousOn) ?_
      exact (continuousOn_extChartAt (I := I) x₀).comp continuousOn_snd
        (fun p hp => baseSet_subset_extChartAt_source (I := I) x₀ hp.2)
    have hmaps : MapsTo (fun p : ℝ × M => (p.1, extChartAt I x₀ p.2))
        (univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
        (univ ×ˢ (extChartAt I x₀).target) := by
      intro p hp
      exact ⟨mem_univ _,
        (extChartAt I x₀).map_source (baseSet_subset_extChartAt_source (I := I) x₀ hp.2)⟩
    have hcomp := (hcontG x₀ i j).comp hmap hmaps
    refine hcomp.congr ?_
    intro p hp
    exact (chartGramMatrixOnE_extChartAt (I := I) g_fam x₀ i j p.1
      (baseSet_subset_extChartAt_source (I := I) x₀ hp.2)).symm
  · -- continuity of the derivative, transported the same way
    have hmap : ContinuousOn (fun p : ℝ × M => (p.1, extChartAt I x₀ p.2))
        (univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      refine ContinuousOn.prodMk (continuous_fst.continuousOn) ?_
      exact (continuousOn_extChartAt (I := I) x₀).comp continuousOn_snd
        (fun p hp => baseSet_subset_extChartAt_source (I := I) x₀ hp.2)
    have hmaps : MapsTo (fun p : ℝ × M => (p.1, extChartAt I x₀ p.2))
        (univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
        (univ ×ˢ (extChartAt I x₀).target) := by
      intro p hp
      exact ⟨mem_univ _,
        (extChartAt I x₀).map_source (baseSet_subset_extChartAt_source (I := I) x₀ hp.2)⟩
    exact (hcontD x₀ i j).comp hmap hmaps

end DifferentialGeometry.Integral.Measure
