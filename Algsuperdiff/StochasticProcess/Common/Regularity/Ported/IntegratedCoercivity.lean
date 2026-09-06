import Algsuperdiff.StochasticProcess.Common.Regularity.Ported.CoefficientBounds

/-!
# Integrated coercivity at the printed contrast

This is the measure-theoretic form of the corrected first line of the energy
test.  Integrability is kept explicit so it can be supplied by the weak-test
module without strengthening the a.e. `L^∞` coefficient carrier.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory Homogenization

noncomputable section

variable {d : ℕ}

theorem integral_half_vecNormSq_le_coefficientEnergy
    {W : Set (Vec d)} {a : CoeffField d} {G : Vec d → Vec d}
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (ha : CoefficientIdentityDistanceLE W a (smallContrastThreshold d alpha))
    (hleft : IntegrableOn (fun x => (1 / 2 : ℝ) * vecNormSq (G x)) W)
    (hright : IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (G x))) W) :
    ∫ x in W, (1 / 2 : ℝ) * vecNormSq (G x) ∂volume ≤
      ∫ x in W, vecDot (G x) (matVecMul (a x) (G x)) ∂volume := by
  apply integral_mono_ae hleft hright
  filter_upwards [ha] with x hx
  exact half_mul_vecNormSq_le_vecDot_coefficient_of_smallContrast
    halpha0 halpha1 hx (G x)

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
