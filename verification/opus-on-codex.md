# Independent authentication of the Codex Lean formalization

*Claude Opus — October 16, 2026*

I have reviewed the Lean 4 development produced by Codex in `research_99graph/authentification_minimale_codex_20261011`. I authenticate its final theorem, `Conway99.graph_minimal_article_theorem` (file `lean/CanonicalDet49LiftComplete.lean`), as a faithful and complete formalization of the main theorem of the 25-page minimal proof.

## What the theorem states

The theorem's only mathematical hypothesis is that `G` is a strongly regular graph with parameters (99, 14, 1, 2), plus the standard finiteness and decidability instances. From this it derives:

- N₂ + 3N₃ = 4158 and δ = N₂ − 693 = 3465 − 3N₃ ∈ 3ℤ, with δ ≥ 165.
- An explicit even, integral, positive lattice N̂ containing the triangle lattice Λ, defined as the preimage of an isotropic subspace of the discriminant group of N. It has:
  - rank 44;
  - an integral basis whose Gram matrix has determinant 49;
  - minimum of its dual N̂* at least 2.
- For the roots of N̂: any two distinct, non-opposite roots are orthogonal (Φ(N̂) = A₁^ρ), and the roots span a space of dimension at most 3 (ρ ≤ 3).

I read the definitions behind this statement in the sources and found each of them faithful to the paper:

- the triangle-pair counts N_m and the defect δ;
- the vertex Gram matrix G₀ = 27I − 9A + J;
- the pairing x·y/63;
- the lattices Λ, N, N* and N̂;
- the Gram matrix of the basis and the dual of N̂;
- the root subspace.

The determinant-49 step uses an unconditional Milgram computation (`canonicalDiscriminant_gauss_sum`). The older conditional Poisson-based route (`CanonicalThetaPoisson`) is not used by the final theorem.

## Checks I actually performed

- **Hashes and source scan.** The SHA-256 hashes of the closing files match the values Codex published. A scan of all 136 source files found no `sorry`, `admit`, added axiom, `unsafe`, `implemented_by` or `native_decide`; the only matches are two comments.
- **Full build (from caches).** With Codex's local toolchain (Lean v4.24.0, local Mathlib), `lake build` succeeded: 3518 jobs, exit code 0. This run replayed cached build results and did not recompile anything. All 539 axiom lists in the build log are restricted to `propext`, `Classical.choice` and `Quot.sound`.
- **Genuine recompilation from source** (imports from cache): the four Milgram files (`MilgramOneDimensional`, `MilgramDiagonalGauss`, `MilgramCanonicalGluing`, `MilgramCanonicalGauss`) and the closing file `CanonicalDet49LiftComplete` all compiled with exit code 0 and only the standard axioms.

I did not run a cold rebuild of the whole project, nor Codex's `Verify-Lean.ps1` script.

## Cross-confirmation and caveats

I separately produced my own Lean formalization of the same theorem (`theorem_1_1`, about 7,550 lines), which relies only on the same three standard axioms. The two developments were written independently and take partly different routes:

- **Case z = 0:** Codex uses a kernel-checked finite certificate; I use a short combinatorial argument.
- **Milgram's formula:** Codex goes through rational diagonalization and exact gluing; I go through an orthogonal sublattice and one-dimensional theta functions.

Both formalizations nevertheless model the paper's ℝ⁴⁴ by rational vectors indexed by the vertices, with the pairing x·y/63. Rank, Gram determinant and norms are intrinsic to this model, but the two developments are not independent on this modelling choice.

**Scope.** This authenticates the conclusions of the minimal article: δ ≥ 165, the existence of N̂ with determinant 49, and ρ ≤ 3. **It does not resolve Conway's 99-graph problem.** No non-existence result is claimed.
