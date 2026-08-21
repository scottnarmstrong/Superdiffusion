import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# The natural spatial range of the actual cutoff law

ABK26 records that the lower-infinite cutoff `k_m`, and hence the actual
coefficient `a_m = nu I + k_m`, has dependence range `sqrt(d) * 3^m`.  This file
owns that literal scale vocabulary.  The proof of independence itself is
intentionally downstream of the local-limit A: it must show that the *actual*
`Cutoff.coefficientCutoffLaw` reads only the lower-shell restriction
sigma-field, and then combine J1 with the prefix's cross-shell independence.  It
must not be replaced by an assumption on a free coefficient law.  -/

namespace Algsuperdiff.Section3.Cutoff

open Homogenization

noncomputable section

/-- The exact spatial dependence range of the actual cutoff at shell scale `m`, as
stated in ABK26.  This is the Euclidean range used by J1; the later proof converts
it to CoarseGraining's ambient unit-range condition only after a triadic scale
normalization. -/
def cutoffNaturalRange (d : ℕ) (m : ℤ) : ℝ :=
  Real.sqrt (d : ℝ) * (3 : ℝ) ^ m

/-- At scale zero the natural range is exactly `sqrt d`, matching the J1
normalization of the zero shell. -/
@[simp]
theorem cutoffNaturalRange_zero (d : ℕ) : cutoffNaturalRange d 0 = Real.sqrt d := by
  simp [cutoffNaturalRange]

end

end Algsuperdiff.Section3.Cutoff
