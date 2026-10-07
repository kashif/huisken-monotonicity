# huisken-monotonicity

A Lean 4 / mathlib formalization of Huisken's monotonicity formula for mean curvature
flow ([Huisken 1990][huisken1990]).

## What's in here

The target is Theorem 3.1 of Huisken (1990): for a hypersurface family `Mₜ ⊂ ℝⁿ⁺¹`
evolving by mean curvature, and the backward heat kernel
`ρ(x, t) = (4π(t₀-t))^(-n/2) exp(-‖x‖²/(4(t₀-t)))`,

```text
d/dt ∫_{Mₜ} ρ(x, t) dμ_t  =  -∫_{Mₜ} ρ(x, t) · ‖H + F^⊥/(2τ)‖² dμ_t.
```

The repository is organised around these modules:

| Module | Status |
| --- | --- |
| [`HuiskenMonotonicity.HeatKernel`](HuiskenMonotonicity/HeatKernel.lean) | proved |
| [`HuiskenMonotonicity.Flow`](HuiskenMonotonicity/Flow.lean) | scaffolding |
| [`HuiskenMonotonicity.SmoothImmersionFamily`](HuiskenMonotonicity/SmoothImmersionFamily.lean) | proved |
| [`HuiskenMonotonicity.Monotonicity`](HuiskenMonotonicity/Monotonicity.lean) | proved (axiom-conditional) |
| [`HuiskenMonotonicity.GraphMeanCurvature`](HuiskenMonotonicity/GraphMeanCurvature.lean) | definition |
| [`HuiskenMonotonicity.CoordinateHypersurface`](HuiskenMonotonicity/CoordinateHypersurface.lean) | proved (graph axioms discharged) |
| [`HuiskenMonotonicity.InducedMetric`](HuiskenMonotonicity/InducedMetric.lean) | definition + basic properties |
| [`HuiskenMonotonicity.SecondFundamentalForm`](HuiskenMonotonicity/SecondFundamentalForm.lean) | definition + symmetry |
| [`HuiskenMonotonicity.Upstream`](HuiskenMonotonicity/Upstream/) | minimal ports from open mathlib PRs |
| [`HuiskenMonotonicity.Weingarten`](HuiskenMonotonicity/Weingarten.lean) | proved (orientation-free Weingarten) |
| [`HuiskenMonotonicity.TangentialCalculus`](HuiskenMonotonicity/TangentialCalculus.lean) | proved (normal divergence identity, `div_M F = n`, Beltrami for `\|F\|²/2`) |
| [`HuiskenMonotonicity.MetricEvolution`](HuiskenMonotonicity/MetricEvolution.lean) | proved (metric evolution, trace, derivative commutation) |
| [`HuiskenMonotonicity.FirstVariation`](HuiskenMonotonicity/FirstVariation.lean) | proved (kernel gradient, test-field divergence) |
| [`HuiskenMonotonicity.FirstVariationIntegral`](HuiskenMonotonicity/FirstVariationIntegral.lean) | proved (`Δ(\|F\|²/2) = n + ⟪F, H⟫`, first variation identity on a closed manifold; `hFirstVar` in native form) |
| [`HuiskenMonotonicity.TransportFormula`](HuiskenMonotonicity/TransportFormula.lean) | proved (transport formula; `hChainRule` discharged) |
| [`HuiskenMonotonicity.DGInterface`](HuiskenMonotonicity/DGInterface.lean) | interface check against DG chart conventions |
| [`DifferentialGeometry.Integral.Measure.Regularity`](HuiskenMonotonicity/Upstream/DifferentialGeometry/Analysis/Integration/Measure/Family/Regularity.lean) | new API for upstreaming to `DifferentialGeometry` |
| [`DifferentialGeometry.Geometry.MeanCurvature`](HuiskenMonotonicity/Upstream/DifferentialGeometry/Geometry/Submanifold/MeanCurvature.lean) | new API for upstreaming to `DifferentialGeometry` |

### Heat kernel — proved

`backwardHeatKernel n t₀ t x` is defined for any inner product space, with:

- `backwardHeatKernel_pos`, `backwardHeatKernel_ne_zero` — positivity for `t < t₀`;
- `hasDerivAt_backwardHeatKernel_time` — `∂_t ρ = ρ · (n/(2τ) − ‖x‖²/(4τ²))`;
- `hasDerivAt_backwardHeatKernel_dir` — directional derivative at `0`,
  `d/ds ρ(x + s·v)|₀ = -ρ/(2τ) · ⟨x, v⟩`;
- `hasDerivAt_backwardHeatKernel_along` — same, at any point `s` along the line;
- `iteratedDeriv_two_backwardHeatKernel_along` — second directional derivative at `0`,
  `d²/ds² ρ(x + s·v)|₀ = ρ · (⟨x, v⟩²/(4τ²) − ‖v‖²/(2τ))`;
- `backwardHeatEquation_euclidean` — heat equation in coordinates on
  `EuclideanSpace ℝ (Fin n)`, `∂_t ρ + Σᵢ ∂²ᵢ ρ = 0`;
- `iteratedDeriv_two_along_eq_iteratedFDeriv_two` — generic bridge between line
  second derivatives and `iteratedFDeriv ℝ 2 f x ![v, v]` for `C²` functions;
- `contDiff_backwardHeatKernel` — `x ↦ ρ(x, t)` is `C^∞` for `t < t₀`;
- `laplacian_backwardHeatKernel` — `Δρ x = ρ · (‖x‖²/(4τ²) − n/(2τ))`;
- `backwardHeatEquation_laplacian` — heat equation in mathlib's coordinate-free
  Laplacian form on `EuclideanSpace ℝ (Fin n)`, `∂_t ρ + Δρ = 0`;
- `integral_backwardHeatKernel` — total mass `∫_V ρ(x, t) dx = 1` over any
  finite-dimensional inner product space `V` with `Module.finrank ℝ V = n`.

These statements stand on their own and are candidates for upstreaming to mathlib
(`Mathlib.Analysis.SpecialFunctions.Gaussian.HeatKernel`).

### Coordinate hypersurfaces — graph geometry

`CoordinateHypersurface.lean` starts replacing abstract geometric assumptions with
concrete graph calculations for `X_f(x) = (x, f x)`.

- `graphPosition`, `graphNormalVector`, `graphUnitNormal` define the graph embedding,
  lower normal `(∇f, -1)`, and unit normal.
- `norm_graphNormalVector`, `norm_graphUnitNormal` prove the normal has length
  `sqrt(1 + ‖∇f‖²)` and the normalized normal has length `1`.
- `graphTangentVector`, `graphNormalVector_orthogonal_tangent`,
  `graphUnitNormal_orthogonal_tangent` prove the coordinate tangent vectors are
  orthogonal to the normal.
- `secondFundamentalFormMatrix_graphPosition` proves
  `h_ij = partial_i partial_j f / sqrt(1 + ||grad f||^2)` for the lower normal.
- `meanCurvatureGraph_eq_metricTrace` proves that the divergence definition is
  `sum_i,j g^ij h_ij`; `meanCurvatureGraph_eq_inducedMetricTrace` states the
  same identity using the generic induced Gram and second fundamental form matrices.
- `graphSecondFundamentalFormVectorTrace_eq_meanCurvatureVector` and its
  induced-Gram-matrix variant prove that tracing the normal-valued form gives
  the orientation-independent vector `-H * nu`.
- `graphNormalProjection`, `graphMeanCurvatureVector`,
  `graphNormalProjection_posDecomp`, and `graphMeanCurvatureVector_normal`
  discharge the two geometric coherence axioms required by `MonotonicityData`.
- `coordinateGraphMonotonicityData` packages the graph surface measure
  `sqrt(1 + ‖∇f‖²) dx`, mean-curvature vector, and normal projection for a
  time-dependent graph family.
- `graphNormalProjection_vertical_mcfVelocity` proves that the scalar graph MCF
  equation `∂ₜ f = sqrt(1 + ‖∇f‖²) · meanCurvatureGraph f` has normal velocity equal
  to the graph mean-curvature vector.

### Flow — abstract scaffolding

The pinned mathlib snapshot does *not* yet contain an integrated second fundamental form, the mean
curvature vector, the induced volume measure on an immersion, or the first variation
of area. `Flow.lean` therefore defines `ImmersionFamily` and a placeholder
`SurfaceMeasure`, so that the statement of Huisken's theorem can be written; these are
interfaces to be filled in once the underlying geometry lands in mathlib.

`SmoothImmersionFamily.lean` supplies the geometric replacement for the
continuity-only family: its space-time map is smooth on the product manifold,
every valid time slice is a genuine mathlib `Manifold.IsImmersion`, and the
source and ambient model spaces are finite-dimensional. It exposes smooth
slices and trajectories, spatial `mfderiv`, canonical time velocity,
hypersurface dimensions, and an adapter to the conditional `ImmersionFamily`
API. The local compatibility theorem in `Upstream/ImmersionInjective.lean`,
ported from mathlib PRs `#41796` and `#42012`, proves that this spatial
differential is injective at every valid time.

`Geometry/InducedMetric.lean` pulls the ambient Euclidean inner product back
along the spatial differential. The result is bundled as a continuous bilinear
form on each tangent space, with proved symmetry, bilinearity, non-negativity,
and positive definiteness. Smooth dependence in charts and packaging as a
mathlib `RiemannianBundle` remain to be proved.

`IsMeanCurvatureFlow F H` is a real predicate asserting `∂/∂s F(p, s)|_{s = t} = H(p, t)`
for every `p` and every `t ∈ [0, T)`. Because mean curvature itself is not yet in
mathlib, the velocity field `H : M → ℝ → E` is taken as **explicit data** rather than
derived from `F`; the geometric content (that `H` actually equals the mean curvature
vector of `F(·, t)(M)`) is the caller's responsibility until the second fundamental
form lands.

### Monotonicity — proved, axiom-conditional

`huisken_monotonicity` is **proved**, conditional on four axioms covering the
geometric primitives mathlib still lacks:

- **Geometric coherence** (fields of `MonotonicityData`):
  - `posDecomp` — orthogonal decomposition `⟨F − F^⊥, F^⊥⟩ = 0`.
  - `meanCurvature_normal` — `H ⟂ F^T`, i.e. `⟨H, F − F^⊥⟩ = 0`.
- **Analytic** (theorem hypotheses):
  - `hChainRule` — packages the moving-measure chain rule with the kernel's
    `∂_t ρ` and `∇_x ρ` formulas, giving `(d/dt) ∫ ρ ∂μ_s` as a single
    integral over the chain-rule expansion.
  - `hFirstVar` — the first variation formula applied to `Y = ρ F / τ`,
    `∫ ρ · [n − ‖F^T‖²/(2τ) + ⟨H, F⟩] dμ_t = 0`.

Given those, the proof is the pointwise algebraic identity
`huisken_pointwise_identity` plus integral linearity. When mathlib gains the
surface measure of an immersion, the moving-measure chain rule, and the first
variation formula, the analytic hypotheses can be discharged for any genuine
MCF, recovering Huisken's theorem unconditionally.

`huisken_monotonicity_rescaled` (Cor 3.2) is proved in the same axiom-conditional
style. Under the parabolic rescaling `F̃ = (2(T-t))^(-1/2) F`, the surfaces
satisfy `∂_s F̃ = H̃ + F̃` (`IsRescaledMeanCurvatureFlow`) and the simpler formula
`(d/ds) ∫ ρ̃ dμ̃_s = -∫ ρ̃ · ‖H̃ + F̃^⊥‖² dμ̃_s`, where the rescaled kernel
`ρ̃(x) = exp(-‖x‖²/2)` carries no `(4πτ)^(-n/2)` prefactor. The proof reuses
the unrescaled algebra by specialising `huisken_pointwise_identity` at τ = 1/2.

`lake build` passes with **zero `sorry`**.

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
