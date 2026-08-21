import Homogenization.Ambient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.CompactOpen

open scoped Matrix.Norms.Elementwise

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Assumptions.ShellField (d : ℕ) :=
  { p :
      ContinuousMap (Homogenization.Vec d) (Homogenization.Mat d) ×
        (ContinuousMap (Homogenization.Vec d)
            (Homogenization.Vec d →L[ℝ] Homogenization.Mat d) ×
          ContinuousMap (Homogenization.Vec d)
            (Homogenization.Vec d →L[ℝ]
              (Homogenization.Vec d →L[ℝ] Homogenization.Mat d))) //
    (∀ x, HasFDerivAt p.1 (p.2.1 x) x) ∧
      (∀ x, HasFDerivAt p.2.1 (p.2.2 x) x) ∧
      ∀ x i j, p.1 x i j = -p.1 x j i }
-- FROZEN-STATEMENT-END
