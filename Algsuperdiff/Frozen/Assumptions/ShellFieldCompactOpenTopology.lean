import Algsuperdiff.Frozen.Assumptions.ShellField

-- FROZEN-STATEMENT-BEGIN
noncomputable def
    Algsuperdiff.Frozen.Assumptions.shellFieldCompactOpenTopology
    (d : ℕ) :
    TopologicalSpace
      (Algsuperdiff.Frozen.Assumptions.ShellField d) := by
  unfold Algsuperdiff.Frozen.Assumptions.ShellField
  infer_instance
-- FROZEN-STATEMENT-END
