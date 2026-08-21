import Algsuperdiff.Section4.Support.Events

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

/-!
# The translated good event — [ABK] `d.good.event.for.lambda`

`goodEventAt M Ccg m y s ep` is the good event of the coarse-graining scheme
at scale `m`, seen from the base point `y`: the pullback of the centred good
event along the translation of the cutoff sample by `y`.  The parameters `s`
and `ep` are the fractional exponent and the smallness level.

Definition; no proof obligation.
-/

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Section4.goodEventAt
    {d : ℕ} (M : Algsuperdiff.Section3.ABKModel d) (Ccg : ℝ) (m : ℤ)
    (y : Homogenization.Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Set (Algsuperdiff.Section3.Cutoff.CutoffSample d) :=
  Algsuperdiff.Section3.Cutoff.translateCutoffSample y ⁻¹'
    Algsuperdiff.Section4.Support.goodEventBase M Ccg m s ep
-- FROZEN-STATEMENT-END
