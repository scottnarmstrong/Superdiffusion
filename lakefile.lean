import Lake

open Lake DSL

package «superdiffusion_formalization» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

require «CoarseGraining» from git
  "https://github.com/scottnarmstrong/CoarseGraining" @ "c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4"

require «MarkovProcess» from git
  "https://github.com/scottnarmstrong/MarkovProcess.git" @ "5d4a2a7c07d982f9425ce09e24384a20368dd501"

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
