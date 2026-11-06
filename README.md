# Robust SPR Synthesis for Polynomial Polytopes

[简体中文](README.zh-CN.md)

A Lean 4 / mathlib formalization classifying universal robust strictly positive-real (SPR) synthesis by denominator order, vertex bound, and exact numerator degree.

## What this repository proves

For a nonempty finite family of real monic degree-`n` denominators, assume that the **entire convex hull is strictly Hurwitz stable**. A common SPR numerator must work with the original denominators throughout that hull at every finite real frequency:

$$
\mathrm{Re}\left(\frac{b(i\omega)}{a(i\omega)}\right)>0.
$$

For every positive order `n` and vertex bound `m`, universal existence is classified as follows:

| Exact numerator degree | Necessary and sufficient condition |
| --- | --- |
| `n − 1` | `n ≤ 2` or `m ≤ 2` |
| `n` | `n ≤ 2` or `m ≤ 2` |
| `n + 1` | `n ≤ 2`, `m ≤ 2`, or `n = m = 3` |

Here `m` bounds the number of listed vertices. The zero bound is vacuous. The cubic triangle is the additional positive case for degree `n + 1`. These are statements about all stable polytopes in each class; failure of universal existence does not mean that every individual polytope fails.

The public theorem is [`SPR.Polytope.Direct.classification`](Lean/PolytopeSPR.lean); the precise predicate is in [Definitions.lean](Lean/SPR/Polytope/Common/Definitions.lean).

## Setup and build

Install Git and [elan](https://github.com/leanprover/elan), the Lean toolchain manager, and make sure `elan`, `lean`, and `lake` are on your PATH. The commands below work in a macOS, Linux, or Windows WSL shell and run from the repository root.

```sh
git clone https://github.com/dgjszy/polytope-spr-proof.git
cd polytope-spr-proof
lake exe cache get
lake build
```

`lean-toolchain` pins Lean **4.30.0**; mathlib is pinned to **v4.30.0**, with exact dependency commits in `lake-manifest.json`. The first run needs internet access to download the toolchain, dependencies, and compiled cache. Keep the lockfile; a normal build does not require `lake update`. The cache speeds up dependency builds; Lean checks the project proof sources.

This repository is used as a local proof library. No server or database deployment is needed. The formal build requires neither Python nor an external solver.

## Verify and use

```sh
lake env lean Lean/PolytopeAudit.lean
```

The default build includes a transitive axiom audit that permits only `propext`, `Classical.choice`, and `Quot.sound`; any other axiom causes an error.

Within this project's Lean environment:

```lean
import PolytopeSPR

#check SPR.Polytope.Direct.classification
#print axioms SPR.Polytope.Direct.classification
```

## Repository layout

- [`Lean/PolytopeSPR.lean`](Lean/PolytopeSPR.lean): public theorem.
- [`Lean/SPR/Polytope/Classification.lean`](Lean/SPR/Polytope/Classification.lean): classification assembly.
- [`CubicSynthesis/`](Lean/SPR/Polytope/CubicSynthesis/): cubic triangle existence proof.
- [`Transfer/`](Lean/SPR/Polytope/Transfer/): transfer across orders.
- [`Lean/PolytopeAudit.lean`](Lean/PolytopeAudit.lean): axiom audit.
