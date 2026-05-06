# Vendored mathlib content

This directory holds mathlib content from **open PRs** copied verbatim (mathlib
is Apache 2.0). Each vendored file carries the original copyright header and a
`VENDORED` note pointing to the source PR. Once the upstream PR lands, the
file should be removed and downstream imports redirected to the upstream
location.

## Current vendored content

| Local file | Source PR | Mathlib path | Lines |
|---|---|---|---|
| `MFDerivPatch.lean` | [#36299](https://github.com/leanprover-community/mathlib4/pull/36299) | `Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean` (+14 line patch) | 14 |
| `CovariantDerivativeMetric.lean` | [#36299](https://github.com/leanprover-community/mathlib4/pull/36299) | `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Metric.lean` | 281 |
| `CovariantDerivativeLeviCivita.lean` | [#36845](https://github.com/leanprover-community/mathlib4/pull/36845) | `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean` | 868 |

Total: ~1163 lines of vendored work-in-progress mathlib content.

## Known issues

`CovariantDerivativeLeviCivita.lean` has **one upstream `sorry`** (line ~568,
inside the auxiliary lemma `aux`). It's a known Lean elaboration issue —
a synthesised typeclass instance not being definitionally equal to the
expected one. The PR author left it as `sorry` with a note. This single
`sorry` is in vendored upstream-in-progress code; the rest of the project is
sorry-free.

## Status of the vendored content in this project

Currently **not imported** into the root `HuiskenMonotonicity.lean` — the
files are present and build clean (modulo the one upstream `sorry`), but
nothing in the rest of the project depends on them yet. The intent is to
build the connection-based abstract layer (tangential divergence,
Laplace-Beltrami, first variation formula on submanifolds) on top of the
vendored Levi-Civita connection.
