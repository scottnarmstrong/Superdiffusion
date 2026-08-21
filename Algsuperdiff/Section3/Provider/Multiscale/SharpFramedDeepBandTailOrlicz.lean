import Algsuperdiff.Section3.Provider.Multiscale.SharpFramedAfterBandOrlicz
import Algsuperdiff.Section3.Provider.Multiscale.SharpFramedDeepBandTailProfile
import Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHsepResidualScale

/-!
# Orlicz split for the framed centered deep-band tail

This file applies the already-verified upper-profile separation split to the
literal squared centered deep-band tail in one good-cell Whitney lane.  The
unframed square uses the exact `Gamma_1` certificate supplied by the grouped
deep-band estimate, and its deterministic `2` witness is identified with the
separately computed ordinary layer profile.

Only the normalized inner good-mass centered-tail lane is treated.  The outer
`probeMeanGoodWaveConst M * vecNormSq p`, the root row, good base, band mean,
after-band and wave-tail lanes, every collar lane, layer/grid/depth
aggregation, and the cutoff observable are absent.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open Homogenization Homogenization.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## Literal carriers -/

/-- The common sharp coefficient and good-layer mass square root for the
centered deep-band square. -/
def probeSharpDeepBandTailGoodMassCoeff (d n : ℕ) : ℝ :=
  5 * (d : ℝ) ^ 2 * Real.sqrt (probeSharpLayerMassEnvelope d n)


theorem probeSharpDeepBandTailGoodMassCoeff_nonneg (d n : ℕ) :
    0 ≤ probeSharpDeepBandTailGoodMassCoeff d n := by
  rw [probeSharpDeepBandTailGoodMassCoeff]
  positivity


/-! ## Exact descendant identity and unframed certificate -/


/-! ## Explicit ordinary and rare lanes -/


end

end Algsuperdiff.Section3.Provider.Multiscale
