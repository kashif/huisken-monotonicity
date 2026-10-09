# huisken-monotonicity

A Lean 4 / mathlib formalization of Huisken's monotonicity formula for mean curvature
flow ([Huisken 1990][huisken1990]).

## What's in here

Huisken's monotonicity formula (Huisken 1990, Theorem 3.1), with its corollaries, proved
with no hypotheses beyond the flow itself. Huisken works with a closed manifold `Mⁿ`
("compact without boundary"), and so does this formalisation. It holds in any codimension,
in any finite-dimensional inner product space, and without a unit normal.

For a smooth family of immersions `F : M × J → E` of a closed manifold of dimension `n`,
defined for times in an open set `J` and moving by mean curvature (`∂ₜ F = Hvec`), and the
backward heat kernel centred at `(x₀, t₀)`,
`ρ(x, t) = (4π(t₀-t))^(-n/2) exp(-‖x - x₀‖²/(4(t₀-t)))`, for every `t ∈ J` with `t < t₀`:

```text
d/dt ∫_M ρ(F, t) dμ_t  =  -∫_M ρ(F, t) · ‖Hvec + (F - x₀)^⊥/(2(t₀-t))‖² dμ_t.
```

| Result | Lean |
| --- | --- |
| Theorem 3.1, at one time of a smooth family | `SmoothImmersionFamily.huisken_monotonicity` |
| Theorem 3.1 for a flow on an open set of times | `ImmersionFlowOn.huisken_monotonicity` |
| monotonicity of the Gaussian density on an interval before `t₀` | `ImmersionFlowOn.antitoneOn_integral` |
| Corollary 3.2, the rescaled flow `∂ₛF̃ = H̃ + F̃` with `ρ̃ = exp(-‖x‖²/2)` | `SmoothImmersionFamily.huisken_monotonicity_rescaled`, `ImmersionFlowOn.huisken_monotonicity_rescaled` |
| monotonicity under the rescaled flow | `ImmersionFlowOn.antitoneOn_integral_rescaled` |
| §2: the rescaling `F̃ = (2(T-t))^(-1/2) F`, `s = -½ log(T-t)` of a flow on `(a, T)` satisfies `∂ₛF̃ = H̃ + F̃` (Huisken (4)), so Corollary 3.2 applies to it | `ImmersionFlowOn.IsMeanCurvatureFlow.rescale`, `ImmersionFlowOn.antitoneOn_integral_rescale` |
| the shrinking sphere `√(1 - 2nt) Sⁿ` moves by mean curvature, so the hypotheses are met | `shrinkingSphere_isMeanCurvatureFlow`, `shrinkingSphere_antitoneOn_integral` |

The differential geometry (Riemannian metrics, volume measures and their variation,
gradient, divergence, Laplacian, integration by parts) comes from the
[`DifferentialGeometry`](https://github.com/qinz1yang/differential-geometry) library and
mathlib; the extrinsic calculus of an immersion into a Euclidean space is developed here.

| Module | Content |
| --- | --- |
| [`HeatKernel`](HuiskenMonotonicity/HeatKernel.lean) | the backward heat kernel and the rescaled kernel: derivatives, heat equation, total mass `1`, joint smoothness |
| [`SmoothImmersionFamily`](HuiskenMonotonicity/SmoothImmersionFamily.lean) | smooth immersions, and smooth space-time families of them |
| [`Geometry/InducedRiemannianMetric`](HuiskenMonotonicity/Geometry/InducedRiemannianMetric.lean) | induced metric and surface measure, chart representation, regularity for the library's volume variation formula |
| [`Weingarten`](HuiskenMonotonicity/Weingarten.lean) | orientation-free Weingarten equation |
| [`TangentialCalculus`](HuiskenMonotonicity/TangentialCalculus.lean) | tangential divergence, tangential and normal parts, mean curvature vector, `div_M F = n`, Beltrami's formula for `\|F\|²/2` |
| [`GaussFormula`](HuiskenMonotonicity/GaussFormula.lean) | divergence of a tangential field in coordinates |
| [`VossWeyl`](HuiskenMonotonicity/VossWeyl.lean) | the library's Voss-Weyl divergence is the extrinsic divergence |
| [`MetricEvolution`](HuiskenMonotonicity/MetricEvolution.lean) | evolution of the induced metric, and its trace |
| [`TransportFormula`](HuiskenMonotonicity/TransportFormula.lean) | `d/dt ∫ ρ dμ_t` via the library's volume variation formula |
| [`FirstVariationIntegral`](HuiskenMonotonicity/FirstVariationIntegral.lean) | `Δ(\|F\|²/2) = n + ⟪F, Hvec⟫`, and `∫ ρ (n - ‖Fᵀ‖²/(2τ) + ⟪F, Hvec⟫) dμ = 0` |
| [`MeanCurvatureFlow`](HuiskenMonotonicity/MeanCurvatureFlow.lean) | `∂ₜ dμ = -‖Hvec‖² dμ`, Theorem 3.1 at the origin |
| [`Translation`](HuiskenMonotonicity/Translation.lean) | arbitrary centre `x₀` |
| [`RescaledFlow`](HuiskenMonotonicity/RescaledFlow.lean) | `dμₛ/ds = (n - H²) μₛ`, Corollary 3.2 |
| [`IntervalFlow`](HuiskenMonotonicity/IntervalFlow.lean) | flows on an open set of times; monotonicity |
| [`Rescaling`](HuiskenMonotonicity/Rescaling.lean) | `H(cF) = c⁻¹ H(F)`; Huisken's rescaling and equation (4) |
| [`Examples/ShrinkingSphere`](HuiskenMonotonicity/Examples/ShrinkingSphere.lean) | the shrinking sphere |
| [`Upstream`](HuiskenMonotonicity/Upstream/) | API intended for `DifferentialGeometry` |

### The proof

It follows Huisken's.

1. **Transport.** `hasDerivAt_integral_backwardHeatKernel` differentiates the integral
   through the library's `volume_variation_formula`, with weight `½ tr(g⁻¹ ∂ₜ g)`. The
   kernel is singular at `t₀`, so the integrand is cut off in time away from `t₀`.
2. **The volume element.** Under the flow the weight is `-‖Hvec‖²`
   (`traceTimeDerivMetric_of_isMeanCurvatureFlowAt`), Huisken's `∂ₜ dμ = -H² dμ`: the metric
   evolves by `∂ₜ g_ij = -2⟪Hvec, ∂_i∂_j F⟫` because the velocity is normal.
3. **Chain rule.** `hasDerivAt_backwardHeatKernel_curve` gives `∂ₜ ρ + ⟨∇ρ, Hvec⟩`.
4. **First variation.** On a closed manifold
   `∫ ρ (n - ‖Fᵀ‖²/(2τ) + ⟪F, Hvec⟫) dμ = 0` (`integral_firstVariation`): Huisken applies
   the first variation formula to `Y = ρF/τ`. Here this is the library's integration by
   parts `∫ X(ρ) dμ = -∫ ρ div X dμ` with `X = ∇(|F|²/2)`, where
   `div X = Δ(|F|²/2) = n + ⟪F, Hvec⟫` is Beltrami's formula, proved by splitting
   `F = Fᵀ + F^⊥`: `div F = n`, and the Weingarten equation gives
   `div F^⊥ = -⟪F^⊥, Hvec⟫`.
5. **Algebra.** `huisken_pointwise_identity` rewrites the integrand of step 1 as
   `-ρ ‖Hvec + F^⊥/(2τ)‖²` plus `1/(2τ)` times the first-variation integrand.

The arbitrary centre (Huisken's Remark (i)) is a translation. Corollary 3.2 follows
Huisken's own proof: "`dμₛ/ds = (n - H²) μₛ` and a calculation analogous to the proof of
Theorem 3.1", with the rescaled kernel the backward heat kernel at `τ = 1/2`. Equation (4)
for the rescaled surfaces follows, as in Huisken's §2, from `H(cF) = c⁻¹ H(F)`.

The mean curvature vector is read in the chart at each point. Under the flow it equals
the time velocity (minus the position, for the rescaled flow), hence is continuous, which
makes every integrand integrable on a closed manifold.

`lake build` passes with no `sorry`, and every result depends only on Lean's standard
axioms `propext`, `Classical.choice`, `Quot.sound`.

## Build

```sh
lake build
```

Requires the toolchain pinned in [`lean-toolchain`](lean-toolchain).

## Blueprint

A LaTeX/HTML blueprint mixing prose math with Lean references is in
[`blueprint/src/content.tex`](blueprint/src/content.tex). Each statement carries
`\lean{...}` and `\leanok` macros tying it to the corresponding Lean declaration;
`leanblueprint checkdecls` verifies every reference resolves.

```sh
pip install leanblueprint  # one-time, plus a graphviz system install
leanblueprint pdf          # builds blueprint/print/print.pdf
leanblueprint web          # builds blueprint/web/ HTML site
leanblueprint checkdecls   # verifies every \lean{...} ref exists in the build
```

## Reference

Gerhard Huisken, *Asymptotic behavior for singularities of the mean curvature flow*,
J. Differential Geom. **31** (1990), no. 1, 285–299.
[doi:10.4310/jdg/1214444099](https://doi.org/10.4310/jdg/1214444099)

```bibtex
@article{huisken1990,
  author    = {Gerhard Huisken},
  title     = {Asymptotic behavior for singularities of the mean curvature flow},
  journal   = {Journal of Differential Geometry},
  volume    = {31},
  number    = {1},
  pages     = {285--299},
  year      = {1990},
  publisher = {Lehigh University},
  doi       = {10.4310/jdg/1214444099},
  url       = {https://doi.org/10.4310/jdg/1214444099}
}
```

[huisken1990]: https://doi.org/10.4310/jdg/1214444099
