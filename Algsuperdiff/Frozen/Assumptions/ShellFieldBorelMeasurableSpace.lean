import Algsuperdiff.Frozen.Assumptions.ShellFieldCompactOpenTopology
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

-- FROZEN-STATEMENT-BEGIN
noncomputable def
    Algsuperdiff.Frozen.Assumptions.shellFieldBorelMeasurableSpace
    (d : ℕ) :
    MeasurableSpace
      (Algsuperdiff.Frozen.Assumptions.ShellField d) :=
  @borel
    (Algsuperdiff.Frozen.Assumptions.ShellField d)
    (Algsuperdiff.Frozen.Assumptions.shellFieldCompactOpenTopology d)
-- FROZEN-STATEMENT-END
