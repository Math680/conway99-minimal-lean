# Contributing

- Keep contributions focused on the accompanying paper and its formalizations.
- Preserve the two projects and pinned toolchains separately.
- Never replace a proved interface with an added hypothesis in a final theorem.
- No `sorry`, `admit`, custom axiom, `native_decide`, unsafe proof computation
  or kernel bypass is accepted.
- State whether checks used cached imports or a cold rebuild.
- Run `python3 scripts/verify.py --source-only` and the affected project's
  full verification command before proposing a source change.
- A deliberate source change requires updating `verification/sources.sha256`
  and explaining the changed proof/definition; changing hashes is not verification.
- Do not rewrite the historical cross-review statements. Add a dated addendum
  if a later version requires a revised review.
- Never commit `.lake`, credentials, local runtimes, personal workstation paths
  or unrelated research. Keep generated logs in ignored `artifacts/`.

The lightweight GitHub workflow does not compile Lean. The full Lean workflow
is manually triggered and permits an explicitly selected runner. For Codex,
choose a runner with enough memory for the kernel-checked finite certificate.
Do not silently downgrade the checks when resources are insufficient.
