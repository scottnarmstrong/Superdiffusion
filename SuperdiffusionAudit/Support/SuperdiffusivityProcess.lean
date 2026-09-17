import SuperdiffusionAudit.Support.SuperdiffusivityMarginal
import SuperdiffusionAudit.Support.SuperdiffusivityMarkov
import SuperdiffusionAudit.Support.SuperdiffusivityFeller

/-!
# The full diffusion characterization of the live stream law

The canonical live law satisfies the PDE-resolvent characterization, the
conditional restart identity for its full future path, and the Feller property.
-/

namespace SuperdiffusionAudit.Support.SDProcess

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field
open Algsuperdiff.StatementAudit.Superdiffusivity
open SuperdiffusionAudit.Support.SDLiveLaw

/-- The constructed live process is the continuous Feller diffusion of the
sample's coefficient field, including its full temporal law. -/
theorem isDiffusionOf_liveLaw {d : ℕ} [NeZero d] (M : ABKModel d)
    (omega : Algsuperdiff.Section5.Field.FullSample d M.gamma) :
    IsDiffusionOf (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega)
      (liveLaw M omega) :=
  ⟨SDMarginal.hasDiffusionMarginals_liveLaw M omega,
    SDMarkov.hasMarkovRestart_liveLaw M omega,
    SDFeller.hasFellerTransitions_liveLaw M omega⟩

end SuperdiffusionAudit.Support.SDProcess
