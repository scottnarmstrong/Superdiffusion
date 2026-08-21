import Algsuperdiff.Frozen.Assumptions.ShellLawJ3
import Algsuperdiff.Frozen.Assumptions.ShellLawJ4
import Algsuperdiff.Frozen.Assumptions.ShellLawPrefix

/-!
# The standing ABK model

This file packages precisely the paper data used throughout Section 3.

## Main definitions

* `Algsuperdiff.Section3.ABKModel`: molecular diffusivity, the canonical shell
  sequence law, and the exact prefix and (J1)--(J4) assumptions of ABK26.

## References

* ABK26.
-/

namespace Algsuperdiff.Section3

open MeasureTheory

/-- The complete standing probabilistic model of ABK26.

The dimension is an external parameter.  Its lower bound and the complete
admissible range for `gamma` belong exactly to `prefix`; this aggregate adds
only molecular diffusivity positivity and the four separately frozen shell-law
assumptions. -/
structure ABKModel (d : ℕ) where
  /-- The molecular diffusivity from ABK26. -/
  nu : ℝ
  /-- Molecular diffusivity is strictly positive. -/
  nu_pos : 0 < nu
  /-- The scale parameter from ABK26. -/
  gamma : ℝ
  /-- The canonical probability law of the bi-infinite shell sequence. -/
  P : ProbabilityMeasure (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d)
  /-- The exact dimension, scale, independence, and marginal-scaling prefix. -/
  shellPrefix : Algsuperdiff.Frozen.Assumptions.ShellLawPrefix d gamma P
  /-- The exact mean-zero, stationarity, and finite-range assumption (J1). -/
  J1 : Algsuperdiff.Frozen.Assumptions.ShellLawJ1 d P
  /-- The exact local regularity and Gaussian-tail assumption (J2). -/
  J2 : Algsuperdiff.Frozen.Assumptions.ShellLawJ2 d P
  /-- The exact joint hyperoctahedral and negation invariance assumption (J3). -/
  J3 : Algsuperdiff.Frozen.Assumptions.ShellLawJ3 d P
  /-- The exact stationary potential-projection nondegeneracy assumption (J4). -/
  J4 : Algsuperdiff.Frozen.Assumptions.ShellLawJ4 d P shellPrefix.dimension J1 J2

end Algsuperdiff.Section3
