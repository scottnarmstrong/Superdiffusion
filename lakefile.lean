import Lake

open Lake DSL

package «superdiffusion_formalization» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

require «CoarseGraining» from git
  "https://github.com/scottnarmstrong/CoarseGraining" @ "8ec687c24a78f75aa7be88cb48da28074796c670"

/-- The comparator audit surfaces (`Audit/*/Challenge.lean`, `SolutionBasic.lean`,
`Solution.lean`).  Deliberately **not** a default target: it builds only on demand
(`lake build Audit`), so the ordinary project build is unchanged. -/
lean_lib «Audit» where
  globs := #[.submodules `Audit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
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
    ⟨`linter.deprecated, true⟩
  ]
