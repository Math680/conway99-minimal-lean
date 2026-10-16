# Codex development

Lean `v4.24.0`; Mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

Complete theorem: [`Conway99.graph_minimal_article_theorem`](lean/CanonicalDet49LiftComplete.lean).
Its only mathematical input is `G.IsSRGWith 99 14 1 2`.

```sh
lake exe cache get
lake build
lake env lean lean/CanonicalDet49LiftComplete.lean
```

The zero-point branch contains a potentially high-memory kernel-checked
finite certificate. Allow sufficient resources for a cold build.

The general `CanonicalThetaPoisson` interface is retained historically;
the final theorem does not assume it. The completed route uses actual
orthogonal coordinates, one-dimensional Gaussian identities and exact gluing.

See the repository [proof map](../docs/PROOF_MAP.md) and
[Opus's cross-review](../verification/opus-on-codex.md).
