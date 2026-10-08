# huisken-monotonicity

A Lean 4 / mathlib formalization of Huisken's monotonicity formula for mean curvature
flow ([Huisken 1990][huisken1990]).

## What's in here

Theorem 3.1 of Huisken (1990), proved with no hypotheses beyond the flow itself.
For a smooth family of immersions `F : M × ℝ → E` of a closed manifold `M` of dimension
`n` into a finite-dimensional inner product space, moving by mean curvature
(`∂ₜ F = Hvec`), and the backward heat kernel
`ρ(x, t) = (4π(t₀-t))^(-n/2) exp(-‖x‖²/(4(t₀-t)))`, for every `t < t₀`:

```text
d/dt ∫_M ρ(F, t) dμ_t  =  -∫_M ρ(F, t) · ‖Hvec + F^⊥/(2(t₀-t))‖² dμ_t.
```

This is `SmoothImmersionFamily.huisken_monotonicity` in
[`MeanCurvatureFlow.lean`](HuiskenMonotonicity/MeanCurvatureFlow.lean). It holds in any
codimension, and on non-orientable submanifolds: no unit normal is chosen anywhere.

The differential geometry (Riemannian metrics, volume measures and their variation,
gradient, divergence, Laplacian, integration by parts) comes from the
[`DifferentialGeometry`](https://github.com/qinz1yang/differential-geometry) library; the
extrinsic calculus of an immersion into a Euclidean space is developed here.

| Module | Content |
| --- | --- |
| [`HeatKernel`](HuiskenMonotonicity/HeatKernel.lean) | the backward heat kernel: derivatives, heat equation, total mass `1`, joint smoothness |
| [`SmoothImmersionFamily`](HuiskenMonotonicity/SmoothImmersionFamily.lean) | smooth space-time families of immersions |
| [`Geometry/InducedRiemannianMetric`](HuiskenMonotonicity/Geometry/InducedRiemannianMetric.lean) | induced metric family and surface measure, chart representation, regularity for the library's volume variation formula |
| [`Weingarten`](HuiskenMonotonicity/Weingarten.lean) | orientation-free Weingarten equation |
| [`TangentialCalculus`](HuiskenMonotonicity/TangentialCalculus.lean) | tangential divergence, tangential and normal parts, mean curvature vector, `div_M F = n`, Beltrami's formula for `\|F\|²/2` |
| [`GaussFormula`](HuiskenMonotonicity/GaussFormula.lean) | divergence of a tangential field in coordinates |
| [`VossWeyl`](HuiskenMonotonicity/VossWeyl.lean) | the library's Voss-Weyl divergence is the extrinsic divergence |
| [`MetricEvolution`](HuiskenMonotonicity/MetricEvolution.lean) | evolution of the induced metric under a normal velocity |
| [`TransportFormula`](HuiskenMonotonicity/TransportFormula.lean) | `d/dt ∫ ρ dμ_t` via the library's volume variation formula |
| [`FirstVariationIntegral`](HuiskenMonotonicity/FirstVariationIntegral.lean) | `Δ(\|F\|²/2) = n + ⟪F, Hvec⟫`, and `∫ ρ (n - ‖Fᵀ‖²/(2τ) + ⟪F, Hvec⟫) dμ = 0` |
| [`MeanCurvatureFlow`](HuiskenMonotonicity/MeanCurvatureFlow.lean) | mean curvature flow, `∂ₜ dμ = -‖Hvec‖² dμ`, Theorem 3.1 |
| [`Upstream`](HuiskenMonotonicity/Upstream/) | API intended for `DifferentialGeometry` and mathlib |

### The proof

It follows Huisken's.

1. **Transport.** `hasDerivAt_integral_backwardHeatKernel` differentiates the integral
   through the library's `volume_variation_formula`, with weight `½ tr(g⁻¹ ∂ₜ g)`. The
   kernel is singular at `t₀`, so the integrand is cut off in time away from `t₀`.
2. **The volume element.** Under the flow the weight is `-‖Hvec‖²`
   (`traceTimeDerivMetric_of_isMeanCurvatureFlow`): the metric evolves by
   `∂ₜ g_ij = -2⟪Hvec, ∂_i∂_j F⟫` because the velocity is normal. Normality in every chart
   comes from the library's fixed-chart differential.
3. **Chain rule.** `hasDerivAt_backwardHeatKernel_curve` gives `∂ₜ ρ + ⟨∇ρ, Hvec⟩`.
4. **First variation.** On a closed manifold
   `∫ ρ (n - ‖Fᵀ‖²/(2τ) + ⟪F, Hvec⟫) dμ = 0` (`integral_firstVariation`). This is the
   library's integration by parts `∫ X(ρ) dμ = -∫ ρ div X dμ` with `X = ∇(|F|²/2)`, where
   `div X = Δ(|F|²/2) = n + ⟪F, Hvec⟫` is Beltrami's formula, proved by splitting
   `F = Fᵀ + F^⊥`: `div F = n`, and the Weingarten equation gives
   `div F^⊥ = -⟪F^⊥, Hvec⟫`.
5. **Algebra.** `huisken_pointwise_identity` rewrites the integrand of step 1 as
   `-ρ ‖Hvec + F^⊥/(2τ)‖²` plus `1/(2τ)` times the first-variation integrand.

The mean curvature vector is read in the chart at each point. Under the flow it equals
the time velocity, hence is continuous, which makes every integrand integrable on a closed
manifold.

`lake build` passes with no `sorry` and no axioms beyond Lean's standard three.

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
