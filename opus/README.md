# Opus development

Lean `v4.34.1`; Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Complete theorem: [`Conway99.theorem_1_1`](Conway99Audit/Main.lean).
Its only mathematical input is `G.IsSRGWith 99 14 1 2`.

```sh
lake exe cache get
lake build
lake env lean Conway99Audit/CheckAll.lean
```

`CheckAll` prints the final statement and the axiom dependencies of the
main results. `Zero.lean` supplies the short combinatorial argument which
discharges the historical `Sec8` interface. Milgram and the determinant-49
construction are proved in `Gauss1`, `Milgram`, `Iso`, `NHat`, and `NHatFinal`.

See the repository [proof map](../docs/PROOF_MAP.md) and
[Codex's cross-review](../verification/codex-on-opus.md).
