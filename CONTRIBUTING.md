# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively
solicited collaborative project, but issues and pull requests are welcome.

The general theory of Markov processes comes from the separate
[`MarkovProcess`](https://github.com/scottnarmstrong/MarkovProcess) library,
which `lakefile.lean` requires as a `git` dependency pinned to an exact
commit; Lake materializes it under `.lake/packages/MarkovProcess`. It is
read-only for this project: extensions belong under `Algsuperdiff/Process`,
and contributors must not edit the dependency's sources.

## Building locally

```bash
lake exe cache get   # prebuilt mathlib oleans
lake build           # build the dependencies and the project
```

The production build is required to emit no Lean or linter warnings.  The
three Mathlib-only files under `SuperdiffusionAudit/*/Challenge.lean` are the
sole exception: each contains one documented statement-level `sorry`, checked
against its completed solution by `leanprover/comparator`.

A few practical notes for working with a development of this size:

- **Never run `lake clean`.**  It wipes the `mathlib` and `CoarseGraining`
  oleans and forces a multi-hour rebuild from source.  To force a
  project-only rebuild, remove the project build artifacts under
  `.lake/build/lib/lean/Algsuperdiff` (and the corresponding
  `.lake/build/ir/Algsuperdiff`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.

- **The main results** are in `Algsuperdiff/MainTheorems.lean`.  The axiom
  report is `lake build Algsuperdiff.Meta.AxiomsAudit`.  That module is
  deliberately not imported by the library root — a `#print axioms` command
  re-runs on every rebuild of the module that carries it — so it is built
  only as an explicit target, as the `Axiom audit` step of the CI workflow
  does; the step fails on `sorryAx` or on any axiom outside `propext`,
  `Classical.choice`, `Quot.sound`.

## Elaboration policy for new files

These rules come from measured elaboration passes over this repository; each one
moved a profile, and the counter-examples were measured too.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with
  `nlinarith`. When a nonlinear fact is needed, hoist it into a small `private`
  lemma over abstract real variables so that `Real.rpow` and `Real.exp` terms
  never enter a numeric tactic. This was the single largest lever measured.
- Prefer the explicit `mul_le_mul_of_nonneg_*` / `add_le_add_*` lemmas to
  `gcongr` on goals over `ℝ`: each such `gcongr` call raises a fixed set of
  failing instance searches. Over `ℝ≥0∞` or `ℕ` the tactic is cheap and fine.
- Use `positivity` for sign goals only; a chain of fourteen `positivity` closers
  in one proof cost more than the explicit terms.
- Before `ring` or `field_simp` on an expression built with `set`, run
  `clear_value` on the bound names; otherwise the let-bodies are unfolded inside
  the tactic.
- Do not split a file, narrow its imports, or add an instance cache "for
  performance" without a warm profile before and after
  (`lake env lean --profile <file>`); on this code base import narrowing and
  head-class caches were tried and did not pay. Note that the profiler's
  default 100 ms floor hides diffuse costs; use `-D profiler.threshold=1` when
  hunting them.
- Never raise `maxHeartbeats`. A default-budget failure is a design signal
  (usually a wrong lemma orientation or a `set`-bound term), not a budget
  problem.
- Keep Lean files under 1500 lines.
