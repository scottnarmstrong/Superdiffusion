import Algsuperdiff.Section3.Provider.Multiscale.BfaPerCube
import Algsuperdiff.Section3.Provider.Multiscale.SharpMeanLayerEnvelope
import Algsuperdiff.Section3.Provider.Multiscale.WaveTermTranslation

/-!
# Elementary properties of the sharp mean-layer envelope

This file proves the sign and measurability facts needed to turn the sharp
mean-layer domination into Orlicz lanes.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open Homogenization
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

theorem probeSharpLayerMassEnvelope_nonneg (d n : ℕ) :
    0 ≤ probeSharpLayerMassEnvelope d n := by
  rw [probeSharpLayerMassEnvelope]
  positivity


end

end Algsuperdiff.Section3.Provider.Multiscale
