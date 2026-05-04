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

The repository is organised in three layers:

| Module | Status |
| --- | --- |
| [`HuiskenMonotonicity.HeatKernel`](HuiskenMonotonicity/HeatKernel.lean) | proved |
| [`HuiskenMonotonicity.Flow`](HuiskenMonotonicity/Flow.lean) | scaffolding |
| [`HuiskenMonotonicity.Monotonicity`](HuiskenMonotonicity/Monotonicity.lean) | proved (axiom-conditional) |
| [`HuiskenMonotonicity.GraphMeanCurvature`](HuiskenMonotonicity/GraphMeanCurvature.lean) | definition |

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

### Flow — abstract scaffolding

mathlib (v4.30.0-rc2) does *not* yet contain the second fundamental form, the mean
curvature vector, the induced volume measure on an immersion, or the first variation
of area. `Flow.lean` therefore defines `ImmersionFamily` and a placeholder
`SurfaceMeasure`, so that the statement of Huisken's theorem can be written; these are
interfaces to be filled in once the underlying geometry lands in mathlib.

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

`lake build` passes with **zero `sorry`**.

## Build

```sh
lake build
```

Requires the toolchain pinned in [`lean-toolchain`](lean-toolchain).

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
