# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively
solicited collaborative project, but issues and pull requests are welcome.

## Building locally

```bash
lake exe cache get   # prebuilt mathlib oleans
lake build           # build the CoarseGraining dependency and the project
```

The production build is required to emit no Lean or linter warnings.  The two
Mathlib-only files under `Audit/*/Challenge.lean` are the sole exception: each
contains one documented statement-level `sorry`, checked against its completed
solution by `leanprover/comparator`.

A few practical notes for working with a development of this size:

- **Never run `lake clean`.**  It wipes the `mathlib` and `CoarseGraining`
  oleans and forces a multi-hour rebuild from source.  To force a
  project-only rebuild, remove the project build artifacts under
  `.lake/build/lib/lean/Algsuperdiff` (and the corresponding
  `.lake/build/ir/Algsuperdiff`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.

- **The main results** are in `Algsuperdiff/MainTheorems.lean`; the axiom
  audit is `lake build Algsuperdiff.Meta.AxiomsAudit`.
