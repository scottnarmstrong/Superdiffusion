import Algsuperdiff.Section3.Annealed.RunningDiffusivity.WellDefinedness
import Algsuperdiff.Section3.Observable.Comparator

/-!
# The running diffusivity

The Section 3 running diffusivity is the unique positive scalar supplied by
`existsUnique_sigmaBar`. There is no fallback value or provisional branch.

## Main definition

* `sigmaBar`: the genuine running diffusivity of the coefficient cutoff.
-/

namespace Algsuperdiff.Section3.Annealed

noncomputable section

variable {d : ℕ}

/-- The genuine positive running diffusivity of the coefficient cutoff at
scale `m`, selected from its proved unique infinite-volume characterization. -/
noncomputable def sigmaBar (M : ABKModel d) (m : ℤ) :
    Observable.PositiveScalar :=
  ⟨Classical.choose (existsUnique_sigmaBar M m),
    (Classical.choose_spec (existsUnique_sigmaBar M m)).1.1⟩

end


end Algsuperdiff.Section3.Annealed
