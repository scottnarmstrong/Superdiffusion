import Lake

open Lake DSL

package «superdiffusion_formalization» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

require «CoarseGraining» from git
  "https://github.com/scottnarmstrong/CoarseGraining" @ "11d802f3f6023f40568cc4511f55cf251aaa974f"

require «MarkovProcess» from git
  "https://github.com/scottnarmstrong/MarkovProcess.git" @ "dbade0d12c4f84179441a9df7d7147df7a8bcaa0"

/-- The comparator audit surfaces (`SuperdiffusionAudit/*/Challenge.lean`, `SolutionBasic.lean`,
`Solution.lean`).  Deliberately **not** a default target: it builds only on demand
(`lake build SuperdiffusionAudit`), so the ordinary project build is unchanged. -/
lean_lib «SuperdiffusionAudit» where
  globs := #[.submodules `SuperdiffusionAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩,
    ⟨`warn.classDefReducibility, false⟩
  ]

@[default_target]
lean_lib «Algsuperdiff» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩,
    ⟨`warn.classDefReducibility, false⟩
  ]
