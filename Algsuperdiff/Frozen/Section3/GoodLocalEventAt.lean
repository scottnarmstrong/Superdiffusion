import Algsuperdiff.Section3.Provider.BadEvents.GoodLocalEvents
import Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Section3.goodLocalEventAt
    {d : ℕ} (M : Algsuperdiff.Section3.ABKModel d) (Ccg : ℝ) (m n : ℤ)
    (z : Homogenization.Vec d) :
    Set (Algsuperdiff.Section3.Cutoff.CutoffSample d) :=
  Algsuperdiff.Section3.Cutoff.translateCutoffSample z ⁻¹'
    Algsuperdiff.Section3.Provider.BadEvents.goodLocalEvent M Ccg
      (Homogenization.originCube d m) n
-- FROZEN-STATEMENT-END
