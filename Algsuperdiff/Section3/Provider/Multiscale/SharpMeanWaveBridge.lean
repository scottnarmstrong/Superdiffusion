import Algsuperdiff.Section3.Provider.Affine.SuperposedPotentialClosure
import Algsuperdiff.Section3.Provider.Multiscale.ConclusionSeam1PerCube
import Algsuperdiff.Section3.Provider.Multiscale.SharpSimplexMean
import Algsuperdiff.Section3.Provider.Multiscale.SuperposedConclusion

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open Homogenization Homogenization.Book Homogenization.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Affine
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}


def probeLayerWaveFactor (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ)
    (n : ℕ) (L : ℤ) (omega : CutoffSample d) : ℝ :=
  M.gamma * (3 : ℝ) ^ (-(2 * M.gamma *
      ((m - (n : ℤ) - (hn n : ℤ) : ℤ) : ℝ))) *
    Real.sqrt (layerSimplexFourthMass m hn n
      (m - (n : ℤ) - (hn n : ℤ)) L omega)


end

end Algsuperdiff.Section3.Provider.Multiscale
