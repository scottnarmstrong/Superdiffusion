import Algsuperdiff.Section3.Observable.Comparator
import Homogenization.Book.Ch04.Theorems.Expectations

/-!
# Section 3 normalized response observable

This file defines the genuine scalar response observable on the centered cube
`square_m`.  For a positive comparator `sigma` and a direction `e`, its loads
are exactly `sigma^(-1/2) e` and `sigma^(1/2) e`.  The coefficient argument is
an actual CoarseGraining `RegCoeffField`; later cutoff-specific declarations
merely compose this map with the genuine cutoff field.

## References

* ABK26, (2.4), definition of `J(U,p,q;a)`.
* ABK26, Section 2.5 and Section 3 response normalizations.
-/

namespace Algsuperdiff.Section3.Observable

open Homogenization Homogenization.Book.Ch04 MeasureTheory

noncomputable section

/-- The response observable
`a ↦ J(square_m, sigma^(-1/2)e, sigma^(1/2)e; a)`. -/
noncomputable def responseJAtScale {d : ℕ} (m : ℤ)
    (sigma : PositiveScalar) (e : Vec d) : RegCoeffField d → ℝ :=
  restrictionResponseJObservableCubeSet (originCube d m)
    (inverseSqrtLoad sigma e) (sqrtLoad sigma e)

/-- The normalized scalar response is pointwise nonnegative. -/
theorem responseJAtScale_nonneg {d : ℕ} (m : ℤ)
    (sigma : PositiveScalar) (e : Vec d) (a : RegCoeffField d) :
    0 ≤ responseJAtScale m sigma e a :=
  restrictionResponseJObservableCubeSet_nonneg (originCube d m)
    (inverseSqrtLoad sigma e) (sqrtLoad sigma e) a

end

end Algsuperdiff.Section3.Observable
