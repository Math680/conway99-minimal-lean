# Proof map and coordinate conventions

## Common mathematical model

The paper's rank-44 Euclidean space is represented by vertex-indexed profile
vectors in the `−4` eigenspace of the adjacency matrix. The pairing is
`x · y / 63`, with vertex Gram `G₀ = 27I − 9A + J`. Rank, Gram determinant
and norms are intrinsic to this model. Neither implementation assumes a
graph exists; its results are implications from the SRG hypothesis.

Both final theorems explicitly construct a lattice and a genuine integral
basis of size 44 with Gram determinant 49. The rank assertion is not merely
a universal statement over potentially nonexistent bases. Orthogonal roots
are distinct directions modulo sign; the dual minimum uses squared norms.

## Codex

- Counting and `δ ≥ 165`: `TriangleSecondMoments`, `DeltaBound`.
- Canonical lattice, dual, discriminant: `RationalLattice`, `Lattice*`,
  `Discriminant*`.
- Milgram: one-dimensional shifted Poisson, diagonal theta products and an
  exact three-point S/T cycle (`MilgramOneDimensional`, `MilgramCyclicPhase`,
  `MilgramDiagonalGauss`); actual orthogonal sublattice coordinates and finite
  isotropic gluing (`MilgramOrthogonal*`, `MilgramFiniteGluing`,
  `MilgramCanonicalGluing`, `MilgramCanonicalGauss`).
- Determinant 49: finite quadratic Gauss/Witt reduction and determinant/index
  identities; assembled in `CanonicalDet49LiftComplete`.
- Roots: `DualMinimum`, `RootOrthogonality`, Hoffman and four-direction modules.
- Four-direction exclusions: the one-zero-point argument and the kernel-checked
  finite-certificate zero-point branch; closed by `RootRankThree`.
- Final complete statement: `graph_minimal_article_theorem`.

The general property `CanonicalThetaPoisson` remains an unproved *alternative
interface*. It is **not required by the completed final theorem**; the actual
canonical Gauss sum is proved through diagonalization and exact gluing.

## Opus

- Counting: `Basic`, `Frame`, `Quad`, `Delta`, `Count`.
- Dual minimum and roots: `Eig`, `Biplane`, `Roots`, `Orth`, `Part`, `Hoff`, `Ceiling`.
- Root bound: `Cover`, `Profile`, `One1`–`One3`, `Final`, `Zero`.
- Zero-point case: a short combinatorial weight argument, without exhaustive
  packing enumeration. The old `Sec8` interface is discharged by `Zero.sec8`.
- Milgram: signed one-dimensional Gauss evaluation from theta functional
  equations and a dominated limit (`Gauss1`), finite discriminant algebra
  (`GaussLat`, `FinGauss`), and sublattice invariance/diagonalization (`Milgram`).
- Determinant 49: integral dual coordinates and `7N* ⊆ N` (`NHat`), nonzero
  isotropic extension over the 7-primary discriminant (`Iso`), and strict
  determinant descent (`NHatFinal`).
- Final complete statement: `Main.theorem_1_1`.

## Deliberate differences

Codex works mainly in rational submodules; Opus uses integral profiles and
divisibility by 63 and 126. In both, an integer Gram division is used only
when exactness has been proved. Codex bounds the dimension of the root span;
Opus forbids a family of four roots distinct modulo sign. Together with the
proved orthogonality, these express the same root-direction bound.

Both developments use proofs equivalent to, but not always line-by-line
translations of, the paper. This repository verifies the article's stated
constraints; it does not verify the entire historical research corpus.
