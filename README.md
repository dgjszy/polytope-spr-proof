# Robust SPR synthesis for polynomial polytopes

Lean proofs of the classification by denominator order, vertex count and actual numerator degree. The public theorem is `SPR.Polytope.Direct.classification` in `Lean/PolytopeSPR.lean`. Its hypotheses require strict Hurwitz stability of the entire convex hull. A single numerator works at every finite real frequency for every original denominator.

For all positive orders n and vertex bounds m, universal synthesis at degree n−1 or n holds exactly when n≤2 or m≤2. Degree n+1 also admits the cubic triangle (n=m=3).

With Elan installed, run:

```sh
lake exe cache get
lake build
```

The toolchain and mathlib revision are pinned. The default build checks the public theorem and audits the imported SPR proofs for transitive axioms. The cubic triangle existence proof is under `Lean/SPR/Polytope/CubicSynthesis/`, and the order transfer is under `Lean/SPR/Polytope/Transfer/`.
