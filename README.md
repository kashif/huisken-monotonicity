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
| [`HuiskenMonotonicity.Monotonicity`](HuiskenMonotonicity/Monotonicity.lean) | statement only |

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

### Monotonicity — statement only

`huisken_monotonicity` takes an `ImmersionFamily F`, geometric data
`MonotonicityData F` (surface measure, mean curvature vector field, normal-position
projection), and an explicit hypothesis `IsMeanCurvatureFlow F data.meanCurvature`
linking the two. The proof is left as `sorry`. The intended proof structure follows
Huisken §3:

1. evolution of the area element `(d/dt) dμ_t = -‖H‖² dμ_t`;
2. chain rule for `(d/dt) ρ(F(p, t), t) = ∂_t ρ + ⟨H, ∇_x ρ⟩`;
3. first variation formula on `Mₜ` to absorb the cross term `⟨F, H⟩/(2τ)`.

All three primitives are presently outside mathlib.

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
