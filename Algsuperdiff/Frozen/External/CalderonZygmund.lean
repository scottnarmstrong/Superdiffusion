import Homogenization.PDE.DirichletRHS
import Homogenization.PDE.NeumannRHS
import Homogenization.Multiscale.NormalizedNorms
import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.DirichletNeumannEndpoint

open Homogenization MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.External.calderon_zygmund
    {d : ℕ} (dimension : 2 ≤ d)
    (p : ℝ≥0∞) (one_lt_p : 1 < p) (p_lt_top : p < ∞) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (f : Vec d → Vec d),
        MemLp f p (normalizedCubeMeasure Q) →
          (∀ u : H10Function (openCubeSet Q),
              IsZeroTraceDirichletRhsWeakSolution
                  (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                  (openCubeSet Q) u (fun x => -f x) →
                MemLp u.toH1Function.grad p
                    (normalizedCubeMeasure Q) ∧
                  cubeLpNorm Q p u.toH1Function.grad ≤
                    C * cubeLpNorm Q p f) ∧
          (∀ u : H1MeanZeroFunction (openCubeSet Q),
              IsMeanZeroNeumannRhsWeakSolution
                  (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                  (openCubeSet Q) u (fun x => -f x) →
                MemLp u.toH1Function.grad p
                    (normalizedCubeMeasure Q) ∧
                  cubeLpNorm Q p u.toH1Function.grad ≤
                    C * cubeLpNorm Q p f)
-- FROZEN-STATEMENT-END
    := by
  exact Homogenization.CubeCalderonZygmund.exists_cubeDirichletNeumannDivergence_cz
    dimension p one_lt_p p_lt_top
