import Algsuperdiff.StochasticProcess.Common.DivergenceForm.BoundedMeasurableLimit
import Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.InteriorContinuity

/-!
# Limits of resolvent representatives for continuous coefficients

Freezing the arbitrary-size continuous skew part supplies the local Hölder
witness required by the general representative-limit theorem.  No global
small-contrast hypothesis is used.
-/

namespace DivergenceFormProcess.Form

open Filter Homogenization MeasureTheory Set Topology

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- Continuous resolvent representatives converge pointwise when their
uniformly bounded data converge in `L²`.  This is the direct freezing
instance of `tendsto_representative_of_tendsto_norm_reg`. -/
theorem tendsto_representative_of_tendsto_norm_continuousCoeff [NeZero d]
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {alpha nu Lam : ℝ} (halpha : 0 < alpha) (hnu : 0 < nu)
    (hEll : IsEllipticFieldOn nu Lam U a)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U)
    (hd : 2 ≤ d) {F : ℕ → ScalarL2 U} {Fl : ScalarL2 U} {M : ℝ}
    (hM : 0 ≤ M)
    (hFM : ∀ k, ∀ᵐ y ∂volumeMeasureOn U, |F k y - Fl y| ≤ M)
    (hL2 : Tendsto (fun k ↦ ‖F k - Fl‖) atTop (nhds 0))
    {wk : ℕ → Vec d → ℝ} {w : Vec d → ℝ}
    (hwkcont : ∀ k, ContinuousOn (wk k) U)
    (hwkae : ∀ k, wk k =ᵐ[volumeMeasureOn U]
      alphaShiftedResolvent a halpha hnu hEll (F k))
    (hwcont : ContinuousOn w U)
    (hwae : w =ᵐ[volumeMeasureOn U]
      alphaShiftedResolvent a halpha hnu hEll Fl)
    {x : Vec d} (hx : x ∈ U) :
    Tendsto (fun k ↦ wk k x) atTop (nhds (w x)) :=
  tendsto_representative_of_tendsto_norm_reg a halpha hnu hEll
    (by norm_num) (inv_nonneg.mpr hnu.le)
    (hasLocalHolderShiftedResolvents_continuousCoeff hd a hU hnu hsymm hcont
      hnu hEll)
    hM hFM hL2 hwkcont hwkae hwcont hwae hx

end

end DivergenceFormProcess.Form
