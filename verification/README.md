# Verification records

## Cross-review statements

- [Codex's review of Opus](codex-on-opus.md).
- [Opus's review of Codex](opus-on-codex.md).

These statements are preserved verbatim from the completed cross-review,
dated 16 October 2026. A historical source-directory reference in a statement
does not refer to a directory in this release. Use the project paths in the
root README instead. These are AI-generated technical assessments, not human
peer-review certifications.

## Checks recorded before packaging

Codex's development passed a grouped build (3518 tasks) and checks of 539
printed axiom lists. Opus's grouped build passed (8952 tasks); the final
statement and five axiom lists were checked, and `Main.lean` was explicitly
recompiled. A subsequent focused review recompiled `Gauss1`, `Milgram`, `Iso`
and `NHatFinal`, and checked thirteen critical theorem interfaces/axiom lists.
All reported axioms were `propext`, `Classical.choice`, and `Quot.sound`.

Those builds reused Mathlib/import caches. They are **not cold rebuilds** and
the task counts are historical diagnostics, not measures of proof coverage.
The source-level modelling review included actual duals, Gram exactness,
non-vacuous rank, isotropic extension, determinant descent and Milgram's sign.
No line-by-line review of every historical source file is claimed.

## Packaging and integrity

Lean proof sources and toolchain files are copied without modification from
the audited developments. Codex's local Mathlib path dependency was converted
to a portable Git dependency at **the same audited commit**; its locked
transitive dependency revisions are unchanged. Opus's Lake configuration and
lock are preserved. No toolchain, dependency checkout or compiled cache is
committed.

`sources.sha256` records the packaged proof files, toolchains, dependency
configuration/locks and cross-review statements. `scripts/verify.py` checks
these hashes before running Lean. Hashes establish identity, not correctness.

The Codex kernel-reduced packing certificate was observed to use roughly
20 GB of memory locally in an earlier run. Platform/compiler differences can
affect this substantially. Use a sufficiently large machine for that branch;
do not mistake an out-of-memory failure for a disproof or a verification pass.

## Limits

The trust base includes the Lean kernel, the pinned Mathlib developments,
standard axioms, and correct interpretation of the final statements.
Source scanning alone is not a proof check. Cached builds alone should not
be called independent cold reconstruction. Neither statement claims that
Conway's 99-graph cannot exist.
