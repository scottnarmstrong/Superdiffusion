import Algsuperdiff.StochasticProcess.Common.Regularity.Ported.Carrier

/-!
# Zeroth-order data for the small-contrast equation
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory Homogenization

noncomputable section

variable {d : ℕ}

/-- Weak `-div(a grad u) = g + div f` on a window. -/
def IsMatrixDivFormWeakSolutionZerothOrderOn (a : CoeffField d)
    (W : Set (Vec d)) (u : H1Function W) (g : Vec d → ℝ)
    (f : Vec d → Vec d) : Prop :=
  ∀ phi : H10Function W,
    ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume =
      (∫ x in W, g x * phi.toH1Function.toFun x ∂volume) -
        ∫ x in W, vecDot (f x) (phi.toH1Function.grad x) ∂volume

/-- Essential-supremum size of a scalar datum. -/
def scalarLInfSizeOn (W : Set (Vec d)) (g : Vec d → ℝ) : ℝ :=
  (eLpNorm g (⊤ : ENNReal) (volume.restrict W)).toReal

/-- Scalar `L^infinity` membership on a window. -/
def MemScalarLInfOn (W : Set (Vec d)) (g : Vec d → ℝ) : Prop :=
  MemLp g (⊤ : ENNReal) (volume.restrict W)

/-- Data size for the equation with a bounded zeroth-order source. -/
def smallContrastZerothOrderDataSize (d : ℕ) (alpha : ℝ)
    (u : H1Function (smallContrastUnitBall d)) (f : Vec d → Vec d)
    (g : Vec d → ℝ) : ℝ :=
  smallContrastDataSize d alpha u f + scalarLInfSizeOn (smallContrastUnitBall d) g

theorem smallContrastZerothOrderDataSize_nonneg
    {alpha : ℝ} (halpha : alpha < 1)
    (u : H1Function (smallContrastUnitBall d)) (f : Vec d → Vec d)
    (g : Vec d → ℝ) :
    0 ≤ smallContrastZerothOrderDataSize d alpha u f g := by
  unfold smallContrastZerothOrderDataSize smallContrastDataSize scalarLInfSizeOn
  exact add_nonneg
    (add_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr halpha.le)) ENNReal.toReal_nonneg))
    ENNReal.toReal_nonneg

end


end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
