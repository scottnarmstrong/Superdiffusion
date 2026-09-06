import Lake

open Lake DSL

package «superdiffusion_formalization» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

require «CoarseGraining» from git
  "https://github.com/scottnarmstrong/CoarseGraining" @ "8ec687c24a78f75aa7be88cb48da28074796c670"

require «MarkovProcess» from git
  "https://github.com/scottnarmstrong/MarkovProcess.git" @ "60a807e8305ae334de83d48a122ab4eb9ccc5481"

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
