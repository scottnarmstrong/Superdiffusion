import Algsuperdiff.Assumptions.ShellField.SequenceLaw

open Homogenization MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- ABK26 (J3): the joint law of the entire shell sequence is
invariant under every hyperoctahedral conjugation and, separately, under
whole-sequence negation. -/
structure Algsuperdiff.Frozen.Assumptions.ShellLawJ3
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d)) : Prop where
  hyperoctahedral : ∀ (R : Mat d)
      (hR : Homogenization.IsSignedPermutationMatrix R),
    P.map
        (Algsuperdiff.Frozen.Assumptions.ShellField.measurable_rotateSequence
          R hR).aemeasurable = P
  negation :
    P.map
        (Algsuperdiff.Frozen.Assumptions.ShellField.measurable_negateSequence
          (d := d)).aemeasurable = P
-- FROZEN-STATEMENT-END
