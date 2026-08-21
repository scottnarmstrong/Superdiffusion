import Algsuperdiff.Section3.Provider.Multiscale.SharpFramedMeanLayerEnvelope
import Algsuperdiff.Section3.Provider.Multiscale.SharpMeanLayerProperties

/-!
# Sign and measurability of the framed sharp layer envelope

These elementary properties support later Orlicz aggregation.
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


theorem measurable_probeSharpLayerFrame
    (M : ABKModel d) (m : ℤ) (E b : ℝ) (k₀ n : ℕ) (i : ℤ) :
    Measurable (probeSharpLayerFrame M m E b k₀ n i) := by
  exact measurable_comp_hsep M m E b fun h : ℕ =>
    probeMeanLayerFrame M m (whitneyScaleSeq b h k₀) n i


end

end Algsuperdiff.Section3.Provider.Multiscale
