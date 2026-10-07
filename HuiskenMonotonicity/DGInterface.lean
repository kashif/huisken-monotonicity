import HuiskenMonotonicity.FirstVariation
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Coordinates.Frame.Coordinate
import DifferentialGeometry.Tensor.Coordinates.ModelBasis

/-!
# Interface check against DifferentialGeometry's chart conventions

The tangential calculus is stated for an arbitrary frame `b : Idx → E₁` and an arbitrary
matrix `gInv` of inverse-metric components. This file checks that those parameters accept
`DifferentialGeometry`'s own chart conventions directly: the index type
`Tensor.Coordinates.CoordinateIdx E₁` and the frame `Tensor.Coordinates.chartModelBasis E₁`.

Each example below is the corresponding general theorem applied with no bridging lemma;
the only rewriting is `Fintype.card_fin`, turning the cardinality of the index type into
the model-space dimension. The point is that adopting the library's conventions costs
nothing here, so no translation layer between a local coordinate development and the
library's chart frame is needed.

A manifold derivative reduces to a Fréchet derivative of the chart representation
`f ∘ (extChartAt I x).symm`, which is a map between model spaces, by
`mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint`. That is why these statements apply to
manifold data without change.
-/

open DifferentialGeometry

namespace HuiskenMonotonicity

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normal divergence identity, stated at DG's chart index type and model basis. -/
example {F ξ : E₁ → E} {x : E₁} (hF : ContDiffAt ℝ 2 F x) (hξ : DifferentiableAt ℝ ξ x)
    (hnormal : IsNormalAlongNear F ξ x)
    (gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := ℝ) E₁ →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := ℝ) E₁ → ℝ) :
    tangentialDivergence F ξ (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₁) gInv x =
      -@inner ℝ E _ (ξ x)
        (meanCurvatureVectorFrame F (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₁) gInv x) :=
  tangentialDivergence_of_isNormalAlong hF hξ hnormal _ gInv

/-- `div_M F` at DG's chart frame is the model-space dimension, on the nose. -/
example {F : E₁ → E}
    {gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := ℝ) E₁ →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := ℝ) E₁ → ℝ} {x : E₁}
    (hinv : IsFrameInverse F (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₁) x gInv) :
    tangentialDivergence F F (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₁) gInv x =
      (Module.finrank ℝ E₁ : ℝ) := by
  rw [tangentialDivergence_self F _ hinv, Fintype.card_fin]

/-- Huisken's test-field divergence, at DG's chart frame. -/
example (m : ℕ) (t₀ : ℝ) {t : ℝ} (hτ : t < t₀) {F : E₁ → E}
    {gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := ℝ) E₁ →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := ℝ) E₁ → ℝ} (x : E₁)
    (hF : DifferentiableAt ℝ F x)
    (hinv : IsFrameInverse F (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₁) x gInv) :
    tangentialDivergence F (fun y => backwardHeatKernel m t₀ t (F y) • F y)
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₁) gInv x =
      backwardHeatKernel m t₀ t (F x) *
        ((Module.finrank ℝ E₁ : ℝ) -
          tangentialNormSq F (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₁) gInv x (F x)
            / (2 * (t₀ - t))) := by
  rw [tangentialDivergence_backwardHeatKernel_smul_position m t₀ hτ _ x hF hinv,
    Fintype.card_fin]

end HuiskenMonotonicity
