/-
Copyright (c) 2026 Kashif Rasul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kashif Rasul
-/

import HuiskenMonotonicity.GraphMeanCurvature
import HuiskenMonotonicity.Monotonicity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coordinate hypersurfaces in Euclidean space

This file starts the concrete hypersurface layer for graphs

`X_f(x) = (x, f x) : ℝⁿ → ℝⁿ⁺¹`.

The goal is deliberately modest: define the basic geometric terms that occur in Huisken's formula
for coordinate graphs, and prove the orthogonality lemmas needed by `MonotonicityData`. This gives a
first route for replacing the abstract geometric axioms in `Monotonicity.lean` by actual coordinate
calculations.
-/

namespace HuiskenMonotonicity

open MeasureTheory
open scoped ENNReal Gradient

/-- Base coordinates for a graph hypersurface. -/
abbrev GraphBase (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Ambient coordinates for a graph hypersurface. -/
abbrev GraphAmbient (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

/-- Append a height coordinate to a base vector. -/
noncomputable def graphVector {n : ℕ} (u : GraphBase n) (a : ℝ) : GraphAmbient n :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (Fin.snoc ((EuclideanSpace.equiv (Fin n) ℝ) u) a)

@[simp] lemma graphVector_last {n : ℕ} (u : GraphBase n) (a : ℝ) :
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ (graphVector u a)) (Fin.last n) = a := by
  simp [graphVector]

@[simp] lemma graphVector_castSucc {n : ℕ} (u : GraphBase n) (a : ℝ) (i : Fin n) :
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ (graphVector u a)) i.castSucc =
      (EuclideanSpace.equiv (Fin n) ℝ u) i := by
  simp [graphVector]

/-- Inner product of two appended graph vectors. -/
lemma inner_graphVector_graphVector {n : ℕ} (u v : GraphBase n) (a b : ℝ) :
    @inner ℝ (GraphAmbient n) _ (graphVector u a) (graphVector v b) =
      @inner ℝ (GraphBase n) _ u v + a * b := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  rw [Fin.sum_univ_castSucc]
  simp [graphVector, mul_comm]

/-- The graph embedding `x ↦ (x, f x)`. -/
noncomputable def graphPosition {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) : GraphAmbient n :=
  graphVector x (f x)

/-- The unnormalised lower normal `(∇f, -1)`. -/
noncomputable def graphNormalVector {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) : GraphAmbient n :=
  graphVector (∇ f x) (-1)

/-- A coordinate tangent vector to the graph. -/
noncomputable def graphTangentVector {n : ℕ}
    (f : GraphBase n → ℝ) (x v : GraphBase n) : GraphAmbient n :=
  graphVector v (@inner ℝ (GraphBase n) _ (∇ f x) v)

/-- The metric induced on a graph by its coordinate tangent vectors. -/
lemma inner_graphTangentVector_graphTangentVector {n : ℕ}
    (f : GraphBase n → ℝ) (x v w : GraphBase n) :
    @inner ℝ (GraphAmbient n) _
        (graphTangentVector f x v) (graphTangentVector f x w) =
      @inner ℝ (GraphBase n) _ v w +
        @inner ℝ (GraphBase n) _ (∇ f x) v * @inner ℝ (GraphBase n) _ (∇ f x) w := by
  simp [graphTangentVector, inner_graphVector_graphVector]

/-- In the standard basis, the graph metric is
`g_ij = delta_ij + (partial_i f) * (partial_j f)`. -/
lemma inner_graphTangentVector_single {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) (i j : Fin n) :
    @inner ℝ (GraphAmbient n) _
        (graphTangentVector f x (EuclideanSpace.single i 1))
        (graphTangentVector f x (EuclideanSpace.single j 1)) =
      (if i = j then 1 else 0) + (∇ f x) i * (∇ f x) j := by
  rw [inner_graphTangentVector_graphTangentVector]
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    EuclideanSpace.inner_single_right]
  simp only [conj_trivial, PiLp.single_apply, mul_ite, mul_one, mul_zero, one_mul]

/-- The matrix of the metric induced on the graph in standard coordinates. -/
noncomputable def graphMetricMatrix {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    @inner ℝ (GraphAmbient n) _
      (graphTangentVector f x (EuclideanSpace.single i 1))
      (graphTangentVector f x (EuclideanSpace.single j 1))

@[simp] lemma graphMetricMatrix_apply {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) (i j : Fin n) :
    graphMetricMatrix f x i j =
      (if i = j then 1 else 0) + (∇ f x) i * (∇ f x) j := by
  exact inner_graphTangentVector_single f x i j

/-- The explicit candidate inverse of the graph metric matrix. -/
noncomputable def graphInverseMetricMatrix {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    (if i = j then 1 else 0) -
      (∇ f x) i * (∇ f x) j / (1 + ‖∇ f x‖ ^ 2)

/-- The squared Euclidean norm of the gradient is the sum of its squared coordinates. -/
lemma sum_sq_gradient {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    ∑ j : Fin n, (∇ f x j) ^ 2 = ‖∇ f x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [PiLp.inner_apply]
  simp [pow_two]

/-- The explicit inverse graph metric is a right inverse of the graph metric. -/
theorem graphMetricMatrix_mul_graphInverseMetricMatrix {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    graphMetricMatrix f x * graphInverseMetricMatrix f x = 1 := by
  ext i k
  have hsum :
      (∑ j : Fin n, (∇ f x) i * (∇ f x) j *
          ((∇ f x) j * (∇ f x) k / (1 + ‖∇ f x‖ ^ 2))) =
        ((∇ f x) i * (∇ f x) k / (1 + ‖∇ f x‖ ^ 2)) * ‖∇ f x‖ ^ 2 := by
    calc
      _ = ∑ j : Fin n,
          ((∇ f x) i * (∇ f x) k / (1 + ‖∇ f x‖ ^ 2)) * (∇ f x j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ((∇ f x) i * (∇ f x) k / (1 + ‖∇ f x‖ ^ 2)) *
          ∑ j : Fin n, (∇ f x j) ^ 2 := by rw [Finset.mul_sum]
      _ = _ := by rw [sum_sq_gradient]
  have hdenom : 1 + ‖∇ f x‖ ^ 2 ≠ 0 := by positivity
  simp only [Matrix.mul_apply, graphMetricMatrix_apply, graphInverseMetricMatrix,
    Matrix.one_apply, add_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, reduceIte,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, hsum]
  field_simp [hdenom]
  ring_nf

/-- The explicit inverse graph metric is a left inverse of the graph metric. -/
theorem graphInverseMetricMatrix_mul_graphMetricMatrix {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    graphInverseMetricMatrix f x * graphMetricMatrix f x = 1 :=
  mul_eq_one_comm.mp (graphMetricMatrix_mul_graphInverseMetricMatrix f x)

/-- The explicit graph inverse metric agrees with mathlib's matrix inverse. -/
theorem graphMetricMatrix_inv {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    (graphMetricMatrix f x)⁻¹ = graphInverseMetricMatrix f x :=
  Matrix.inv_eq_right_inv (graphMetricMatrix_mul_graphInverseMetricMatrix f x)

/-- The graph metric matrix has nonzero determinant. -/
theorem graphMetricMatrix_det_ne_zero {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    (graphMetricMatrix f x).det ≠ 0 := by
  have hdet :
      (graphMetricMatrix f x).det * (graphInverseMetricMatrix f x).det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using
      congrArg Matrix.det (graphMetricMatrix_mul_graphInverseMetricMatrix f x)
  intro hzero
  rw [hzero, zero_mul] at hdet
  norm_num at hdet

/-- The graph metric is the identity plus the rank-one matrix `(∇f)(∇f)ᵀ`. -/
theorem graphMetricMatrix_eq_one_add_vecMulVec {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    graphMetricMatrix f x =
      1 + Matrix.vecMulVec (fun i : Fin n => (∇ f x) i) (fun i : Fin n => (∇ f x) i) := by
  ext i j
  simp [Matrix.one_apply, Matrix.vecMulVec_apply]

/-- The determinant of the graph metric is `1 + ‖∇f‖²`. -/
theorem graphMetricMatrix_det {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    (graphMetricMatrix f x).det = 1 + ‖∇ f x‖ ^ 2 := by
  rw [graphMetricMatrix_eq_one_add_vecMulVec, Matrix.vecMulVec_eq Unit]
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simpa only [dotProduct, pow_two] using sum_sq_gradient f x

/-- The determinant of the graph metric is the square of the graph area factor. -/
theorem graphMetricMatrix_det_eq_graphAreaFactor_sq {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    (graphMetricMatrix f x).det = graphAreaFactor f x ^ 2 := by
  rw [graphMetricMatrix_det]
  unfold graphAreaFactor
  rw [Real.sq_sqrt]
  positivity

/-- The volume density defined by the graph metric matrix. -/
noncomputable def graphMetricVolumeElement {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) : ℝ :=
  Real.sqrt (graphMetricMatrix f x).det

/-- The metric volume density of a graph is its explicit area factor. -/
theorem graphMetricVolumeElement_eq_graphAreaFactor {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    graphMetricVolumeElement f x = graphAreaFactor f x := by
  rw [graphMetricVolumeElement, graphMetricMatrix_det_eq_graphAreaFactor_sq]
  apply Real.sqrt_sq
  exact Real.sqrt_nonneg _

lemma graphAreaFactor_pos {n : ℕ} (f : GraphBase n → ℝ) (x : GraphBase n) :
    0 < graphAreaFactor f x := by
  unfold graphAreaFactor
  exact Real.sqrt_pos.2 (by positivity)

lemma graphAreaFactor_ne_zero {n : ℕ} (f : GraphBase n → ℝ) (x : GraphBase n) :
    graphAreaFactor f x ≠ 0 :=
  ne_of_gt (graphAreaFactor_pos f x)

lemma graphNormalVector_ne_zero {n : ℕ} (f : GraphBase n → ℝ) (x : GraphBase n) :
    graphNormalVector f x ≠ 0 := by
  intro h
  have hlast : (-1 : ℝ) = 0 := by
    simpa [graphNormalVector, graphVector] using congrArg
      (fun y : GraphAmbient n =>
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ y) (Fin.last n)) h
  norm_num at hlast

/-- The unnormalised graph normal has norm `sqrt(1 + ‖∇f‖²)`. -/
lemma norm_graphNormalVector {n : ℕ} (f : GraphBase n → ℝ) (x : GraphBase n) :
    ‖graphNormalVector f x‖ = graphAreaFactor f x := by
  have hsqN : ‖graphNormalVector f x‖ ^ 2 = ‖∇ f x‖ ^ 2 + 1 := by
    have h := inner_graphVector_graphVector (∇ f x) (∇ f x) (-1 : ℝ) (-1 : ℝ)
    rw [← real_inner_self_eq_norm_sq (graphNormalVector f x), graphNormalVector, h]
    rw [real_inner_self_eq_norm_sq]
    ring
  have hsqA : graphAreaFactor f x ^ 2 = ‖∇ f x‖ ^ 2 + 1 := by
    unfold graphAreaFactor
    rw [Real.sq_sqrt]
    · ring
    · positivity
  have hsquares : ‖graphNormalVector f x‖ ^ 2 = graphAreaFactor f x ^ 2 := by
    rw [hsqN, hsqA]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with h | h
  · exact h
  · have hn : 0 ≤ ‖graphNormalVector f x‖ := norm_nonneg _
    have ha : 0 < graphAreaFactor f x := graphAreaFactor_pos f x
    linarith

/-- The lower unit normal `(∇f, -1) / sqrt(1 + ‖∇f‖²)`. -/
noncomputable def graphUnitNormal {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) : GraphAmbient n :=
  (graphAreaFactor f x)⁻¹ • graphNormalVector f x

lemma norm_graphUnitNormal {n : ℕ} (f : GraphBase n → ℝ) (x : GraphBase n) :
    ‖graphUnitNormal f x‖ = 1 := by
  unfold graphUnitNormal
  rw [norm_smul, norm_graphNormalVector]
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt (graphAreaFactor_pos f x)))]
  field_simp [graphAreaFactor_ne_zero f x]

lemma graphUnitNormal_ne_zero {n : ℕ} (f : GraphBase n → ℝ) (x : GraphBase n) :
    graphUnitNormal f x ≠ 0 := by
  intro h
  have hn := congrArg norm h
  simp [norm_graphUnitNormal f x] at hn

/-- Coordinate tangent vectors are orthogonal to the graph normal. -/
lemma graphNormalVector_orthogonal_tangent {n : ℕ}
    (f : GraphBase n → ℝ) (x v : GraphBase n) :
    @inner ℝ (GraphAmbient n) _
      (graphNormalVector f x) (graphTangentVector f x v) = 0 := by
  simp [graphNormalVector, graphTangentVector, inner_graphVector_graphVector]

lemma graphUnitNormal_orthogonal_tangent {n : ℕ}
    (f : GraphBase n → ℝ) (x v : GraphBase n) :
    @inner ℝ (GraphAmbient n) _
      (graphUnitNormal f x) (graphTangentVector f x v) = 0 := by
  rw [graphUnitNormal, real_inner_smul_left]
  rw [graphNormalVector_orthogonal_tangent, mul_zero]

/-! ## Normal projection -/

/-- Orthogonal projection of `Y` to the line spanned by a nonzero normal `N`. -/
noncomputable def normalProjectionAlong {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (N Y : E) : E :=
  (@inner ℝ E _ Y N / ‖N‖ ^ 2) • N

lemma normalProjectionAlong_normal_orthogonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (N Y : E) (hN : N ≠ 0) :
    @inner ℝ E _ N (Y - normalProjectionAlong N Y) = 0 := by
  let a : ℝ := @inner ℝ E _ Y N / ‖N‖ ^ 2
  change @inner ℝ E _ N (Y - a • N) = 0
  calc
    @inner ℝ E _ N (Y - a • N)
        = @inner ℝ E _ N Y - a * @inner ℝ E _ N N := by
          rw [inner_sub_right, real_inner_smul_right]
    _ = 0 := by
      rw [real_inner_comm Y N, real_inner_self_eq_norm_sq]
      have hnorm : ‖N‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hN)
      subst a
      field_simp [hnorm]
      ring

lemma normalProjectionAlong_tangent_orthogonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (N Y : E) (hN : N ≠ 0) :
    @inner ℝ E _ (Y - normalProjectionAlong N Y) (normalProjectionAlong N Y) = 0 := by
  let a : ℝ := @inner ℝ E _ Y N / ‖N‖ ^ 2
  change @inner ℝ E _ (Y - a • N) (a • N) = 0
  calc
    @inner ℝ E _ (Y - a • N) (a • N)
        = a * @inner ℝ E _ (Y - a • N) N := by
          rw [real_inner_smul_right]
    _ = a * @inner ℝ E _ N (Y - a • N) := by
          rw [real_inner_comm N (Y - a • N)]
    _ = 0 := by
      have horth : @inner ℝ E _ N (Y - a • N) = 0 := by
        change @inner ℝ E _ N (Y - normalProjectionAlong N Y) = 0
        exact normalProjectionAlong_normal_orthogonal N Y hN
      rw [horth, mul_zero]

lemma normalProjectionAlong_smul_normal_orthogonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (N Y : E) (c : ℝ) (hN : N ≠ 0) :
    @inner ℝ E _ (c • N) (Y - normalProjectionAlong N Y) = 0 := by
  rw [real_inner_smul_left, normalProjectionAlong_normal_orthogonal N Y hN, mul_zero]

/-- Normal projection of an ambient vector along the graph unit normal. -/
noncomputable def graphNormalProjection {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) (Y : GraphAmbient n) : GraphAmbient n :=
  normalProjectionAlong (graphUnitNormal f x) Y

lemma graphNormalProjection_posDecomp {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) (Y : GraphAmbient n) :
    @inner ℝ (GraphAmbient n) _
      (Y - graphNormalProjection f x Y) (graphNormalProjection f x Y) = 0 := by
  exact normalProjectionAlong_tangent_orthogonal
    (graphUnitNormal f x) Y (graphUnitNormal_ne_zero f x)

/-! ## Graph mean curvature vector -/

/-- Mean curvature vector of a graph, using the lower-normal convention. -/
noncomputable def graphMeanCurvatureVector {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) : GraphAmbient n :=
  -(meanCurvatureGraph f x) • graphUnitNormal f x

lemma graphMeanCurvatureVector_normal {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) (Y : GraphAmbient n) :
    @inner ℝ (GraphAmbient n) _
      (graphMeanCurvatureVector f x) (Y - graphNormalProjection f x Y) = 0 := by
  exact normalProjectionAlong_smul_normal_orthogonal
    (graphUnitNormal f x) Y (-(meanCurvatureGraph f x)) (graphUnitNormal_ne_zero f x)

/-- A purely vertical vector in the ambient space. -/
noncomputable def graphVerticalVector {n : ℕ} (a : ℝ) : GraphAmbient n :=
  graphVector 0 a

lemma inner_graphVerticalVector_unitNormal {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) (a : ℝ) :
    @inner ℝ (GraphAmbient n) _
      (graphVerticalVector (n := n) a) (graphUnitNormal f x) =
      -a / graphAreaFactor f x := by
  unfold graphVerticalVector graphUnitNormal graphNormalVector
  rw [real_inner_smul_right, inner_graphVector_graphVector]
  simp
  field_simp [graphAreaFactor_ne_zero f x]

/--
If the graph height evolves by `f_t = v H`, where
`v = sqrt(1 + ‖∇f‖²)` and `H = meanCurvatureGraph f`, then the normal projection
of the vertical velocity is exactly the graph mean-curvature vector.
-/
lemma graphNormalProjection_vertical_mcfVelocity {n : ℕ}
    (f : GraphBase n → ℝ) (x : GraphBase n) :
    graphNormalProjection f x
        (graphVerticalVector (n := n) (graphAreaFactor f x * meanCurvatureGraph f x)) =
      graphMeanCurvatureVector f x := by
  unfold graphNormalProjection normalProjectionAlong graphMeanCurvatureVector
  rw [inner_graphVerticalVector_unitNormal, norm_graphUnitNormal]
  rw [show -(graphAreaFactor f x * meanCurvatureGraph f x) /
      graphAreaFactor f x = -meanCurvatureGraph f x by
        field_simp [graphAreaFactor_ne_zero f x]]
  simp

/-! ## Coordinate graph families -/

/-- A time-dependent coordinate graph as an `ImmersionFamily`.

The continuity proof is supplied by the caller; later modules can build it from
regularity assumptions on `f`. -/
noncomputable def coordinateGraphFamily {n : ℕ}
    (f : ℝ → GraphBase n → ℝ) (T : ℝ) (hT : 0 < T)
    (hcont : Continuous fun xt : GraphBase n × ℝ => graphPosition (f xt.2) xt.1) :
    ImmersionFamily (GraphBase n) (GraphAmbient n) where
  T := T
  T_pos := hT
  toFun := fun x t => graphPosition (f t) x
  continuous_toFun := hcont

/-- The induced graph surface measure, represented on the base coordinates by
`sqrt(1 + ‖∇f‖²) dx`. -/
noncomputable def graphSurfaceMeasure {n : ℕ}
    (f : ℝ → GraphBase n → ℝ)
    (F : ImmersionFamily (GraphBase n) (GraphAmbient n)) :
    SurfaceMeasure F where
  μ := fun t => volume.withDensity
    (fun x => ENNReal.ofReal (graphAreaFactor (f t) x))

/-- The scalar graphical mean curvature flow equation `∂ₜ f = v H`.

This is the coordinate version of mean curvature flow for graphs: the embedding
velocity is vertical, but its normal projection is the mean-curvature vector by
`graphNormalProjection_vertical_mcfVelocity`. -/
def IsCoordinateGraphMeanCurvatureFlow {n : ℕ}
    (f : ℝ → GraphBase n → ℝ) (T : ℝ) : Prop :=
  ∀ x : GraphBase n, ∀ t : ℝ, 0 ≤ t → t < T →
    HasDerivAt (fun s => f s x)
      (graphAreaFactor (f t) x * meanCurvatureGraph (f t) x) t

/-- Differentiating `s ↦ graphVector u (g s)` at fixed base `u`: the result is a
purely vertical vector with last coordinate `g'`, the time derivative of `g`. -/
lemma hasDerivAt_graphVector_const_height {n : ℕ} (u : GraphBase n)
    {g : ℝ → ℝ} {g' t : ℝ} (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => graphVector u (g s)) (graphVerticalVector (n := n) g') t := by
  -- The Pi-version: derivative of `s ↦ Fin.snoc (constant) (g s)` is `Fin.snoc 0 g'`.
  set u' : Fin n → ℝ := EuclideanSpace.equiv (Fin n) ℝ u with _hu'_def
  have h_pi : HasDerivAt
      (fun s : ℝ => (Fin.snoc u' (g s) : Fin (n + 1) → ℝ))
      (Fin.snoc (0 : Fin n → ℝ) g') t := by
    rw [hasDerivAt_pi]
    intro i
    rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
    · simpa using hasDerivAt_const t (u' j)
    · simpa using hg
  -- Wrap with the continuous linear equiv `(EuclideanSpace.equiv).symm` via `clm_apply`.
  have h_const : HasDerivAt
      (fun _ : ℝ => (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.toContinuousLinearMap)
      (0 : (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) t :=
    hasDerivAt_const _ _
  have h := h_const.clm_apply h_pi
  -- Clean up the value: the constant-derivative term collapses.
  simp only [zero_apply, zero_add] at h
  have h_fun :
      (fun y => (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (Fin.snoc u' (g y))) =
        fun s => graphVector u (g s) := by
    funext s
    simp [graphVector, _hu'_def]
  have h_deriv :
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (Fin.snoc 0 g') =
        graphVerticalVector (n := n) g' := by
    simp [graphVerticalVector, graphVector]
  rw [← h_fun, ← h_deriv]
  exact h

/-- Under graphical MCF (`∂_t f = v · H`), the time derivative of the graph
position is a *vertical* vector with magnitude `v · H`. The normal projection
of this velocity is the geometric mean curvature vector
(see `graphNormalProjection_vertical_mcfVelocity`). -/
lemma hasDerivAt_graphPosition_of_isCoordMCF {n : ℕ}
    (f : ℝ → GraphBase n → ℝ) (T : ℝ) (hf : IsCoordinateGraphMeanCurvatureFlow f T)
    (x : GraphBase n) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivAt (fun s => graphPosition (f s) x)
      (graphVerticalVector (n := n)
        (graphAreaFactor (f t) x * meanCurvatureGraph (f t) x)) t :=
  hasDerivAt_graphVector_const_height x (hf x t ht htT)

/-- Combined connection: under graphical MCF, the *normal projection* of the time
derivative of the graph position equals the geometric mean curvature vector.
This is the precise sense in which the scalar PDE `∂_t f = v H` is a faithful
parametrisation of mean curvature flow. -/
theorem graphNormalProjection_velocity_eq_meanCurvatureVector {n : ℕ}
    (f : ℝ → GraphBase n → ℝ) (T : ℝ) (hf : IsCoordinateGraphMeanCurvatureFlow f T)
    (x : GraphBase n) {t : ℝ} (ht : 0 ≤ t) (htT : t < T)
    {v : GraphAmbient n}
    (hv : HasDerivAt (fun s => graphPosition (f s) x) v t) :
    graphNormalProjection (f t) x v = graphMeanCurvatureVector (f t) x := by
  have h_unique := (hasDerivAt_graphPosition_of_isCoordMCF f T hf x ht htT).unique hv
  rw [← h_unique]
  exact graphNormalProjection_vertical_mcfVelocity (f t) x

/-- Concrete `MonotonicityData` for a coordinate graph family.

This discharges the two geometric coherence axioms in `MonotonicityData`.  The
analytic hypotheses in `huisken_monotonicity` are still separate: for graphs they
should be proved by rewriting the moving surface integral as a fixed-coordinate
integral with density `graphAreaFactor`. -/
noncomputable def coordinateGraphMonotonicityData {n : ℕ}
    (f : ℝ → GraphBase n → ℝ) (T : ℝ) (hT : 0 < T)
    (hcont : Continuous fun xt : GraphBase n × ℝ => graphPosition (f xt.2) xt.1) :
    MonotonicityData (coordinateGraphFamily f T hT hcont) where
  surface := graphSurfaceMeasure f (coordinateGraphFamily f T hT hcont)
  meanCurvature := fun x t => graphMeanCurvatureVector (f t) x
  normalPos := fun x t => graphNormalProjection (f t) x (graphPosition (f t) x)
  posDecomp := by
    intro x t
    exact graphNormalProjection_posDecomp (f t) x (graphPosition (f t) x)
  meanCurvature_normal := by
    intro x t
    exact graphMeanCurvatureVector_normal (f t) x (graphPosition (f t) x)

end HuiskenMonotonicity
