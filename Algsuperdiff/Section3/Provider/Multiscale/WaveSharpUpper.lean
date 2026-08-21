import Algsuperdiff.Section3.Provider.Multiscale.WaveThirdTerm

/-!
# A macroscopic cube-averaged wave term

This internal analytic provider keeps the cube-averaged `L̲⁴` carrier for the
macroscopic increment.  It obtains the `sqrt gamma * sqrt (L-ell) *
3^(gamma*(L-ell))` `Gamma₂` scale directly from the proved increment estimate,
with no translated-cube maximum and therefore no grid penalty.
-/

set_option autoImplicit false

namespace Algsuperdiff.Section3.Provider.Multiscale

open Homogenization
open Homogenization.IndependentSums
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-- A dimension-only constant for the macroscopic `L̲⁴` term. -/
def waveSharpUpperConst (d : ℕ) : ℝ :=
  (Real.exp 1) ^ (1 / 4 : ℝ) *
    (IndependentSums.gammaMomentConst 2 *
      (IndependentSums.gammaTriangleConst 2 *
        ((d : ℝ) ^ 2 * geometricConcentrationConst))) * 2


/-- The macroscopic `L̲⁴` wave term, without a translated-cube
maximum. -/
def waveSharpUpperTerm (M : ABKModel d) (lout ell L : ℤ)
    (omega : CutoffSample d) : ℝ :=
  Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
    streamIncrementLpNorm 4 lout ell L omega.1


end

end Algsuperdiff.Section3.Provider.Multiscale
