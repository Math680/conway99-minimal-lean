# Lean formalizations of structural constraints for Conway's 99-graph

Two independently developed Lean formalizations accompanying the forthcoming
article by **Mathieu RANNOU** (mathieu.rannou@imt-atlantique.net).

**This repository does not resolve Conway's 99-graph problem.** It formalizes
necessary structural constraints on a hypothetical strongly regular graph with
parameters `(99, 14, 1, 2)`.

The repository is private while the article is being prepared. Its visibility
must not be changed without the author's explicit approval.

## Verified conclusions

From the strongly regular graph parameters alone, both developments establish:

- `N₂ + 3N₃ = 4158`, and `δ = N₂ − 693 = 3465 − 3N₃ ∈ 3ℤ`;
- `δ ≥ 165`, hence `N₂ ≥ 858` and `N₃ ≤ 1100`;
- an even integral positive lattice containing the triangle lattice, of rank
  `44`, with an integral Gram matrix of determinant `49`;
- dual minimum at least `2` (squared norms);
- pairwise orthogonal root directions, with root system `A₁^ρ`, `ρ ≤ 3`.

Here `N_m` counts unordered pairs of disjoint triangles joined by exactly `m`
edges. No non-existence conclusion is claimed.

## The two developments

| Project | Lean | Mathlib commit | Final theorem |
| --- | --- | --- | --- |
| [Codex](codex/) | `v4.24.0` | `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` | `Conway99.graph_minimal_article_theorem` |
| [Opus](opus/) | `v4.34.1` | `d13f23b723b8a846827a245b89c10fc7d3f11612` | `Conway99.theorem_1_1` |

These are **separate Lake projects** with separate toolchains and dependency
locks. Do not combine their imports or upgrade one to match the other.

Entry points:

- [Codex's complete theorem](codex/lean/CanonicalDet49LiftComplete.lean).
- [Opus's complete theorem](opus/Conway99Audit/Main.lean).
- [Proof map and modelling conventions](docs/PROOF_MAP.md).
- [Verification scope and cross-reviews](verification/README.md).

## Reproduce the checks

Install Git and [elan](https://github.com/leanprover/elan). Each project's
`lean-toolchain` selects its own Lean version. Download the Mathlib cache once:

```sh
cd codex
lake exe cache get
cd ../opus
lake exe cache get
cd ..
```

Then use Python 3 to check source integrity, build each project, and validate
the printed axiom dependencies of its final theorem:

```sh
python3 scripts/verify.py --project codex
python3 scripts/verify.py --project opus
```

On Windows, `python` can be used in place of `python3`. The corresponding
direct checks are:

```sh
# Within codex/
lake build
lake env lean lean/CanonicalDet49LiftComplete.lean

# Within opus/
lake build
lake env lean Conway99Audit/CheckAll.lean
```

The Codex finite-certificate branch can require substantial memory and time
on a cold build. Use a high-memory machine for a full reproduction; prior
local measurements are documented in [verification](verification/README.md).
Build logs from the verification script are written to ignored `artifacts/`.

## Trust and scope

The accepted axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, added axiom, native proof computation or kernel bypass is
accepted. `python3 scripts/verify.py --source-only` performs the lightweight
integrity and source-policy checks, **not** a Lean proof check.

Both formalizations were developed with substantial AI autonomy and were
cross-reviewed after their independent developments were completed. They
share the paper's mathematics and a profile-coordinate model; they should not
be described as independent discoveries of the underlying theorem. The
cross-review statements are AI-generated technical assessments, not human
peer-review or an absolute guarantee.

Some intermediate lemmas retain explicit hypotheses for historical or modular
reasons. The **final theorem statements above have no open analytic or
combinatorial premise**. See the proof map for the completed Milgram routes.

## Automation, citation and contributions

Pushes and pull requests run lightweight integrity checks. Full Lean checks
are available through a manually triggered workflow, so a push does not
silently start an expensive proof rebuild. See
[CONTRIBUTING.md](CONTRIBUTING.md).

The paper title, arXiv identifier and DOI will be added after publication.
[CITATION.cff](CITATION.cff) currently describes this software companion only.
Do not cite an unpublished arXiv identifier or claim the Conway problem is solved.

## License

The repository's Lean code and documentation are provided under the
[MIT License](LICENSE). Mathlib and other dependencies retain their own
licenses and are downloaded separately; their caches are not redistributed.
