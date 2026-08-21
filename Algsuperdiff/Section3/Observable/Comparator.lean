import Algsuperdiff.Section3.Observable.Scaling

/-!
# Positive scalar comparators for Section 3

Section 3 compares the random coefficient cutoff with the constant isotropic
matrix `sigmaBar_m Id`.  This file records that literal matrix and the two
scalar load normalizations used in the response functional.  Positivity is
part of the scalar's type, so the inverse-square-root load is meaningful on
the whole public carrier.
-/

namespace Algsuperdiff.Section3.Observable

open Homogenization

noncomputable section

/-- A strictly positive scalar, used for the running-diffusivity comparator. -/
abbrev PositiveScalar := {sigma : ℝ // 0 < sigma}

/-- The constant isotropic coefficient `sigma Id`. -/
noncomputable def isotropicComparatorMatrix {d : ℕ} (sigma : PositiveScalar) : Mat d :=
  (sigma : ℝ) • (1 : Mat d)

/-- The primal load `sigma^(-1/2) e`, written using the positive square root. -/
noncomputable def inverseSqrtLoad {d : ℕ} (sigma : PositiveScalar) (e : Vec d) : Vec d :=
  (Real.sqrt (sigma : ℝ))⁻¹ • e

/-- The dual load `sigma^(1/2) e`. -/
noncomputable def sqrtLoad {d : ℕ} (sigma : PositiveScalar) (e : Vec d) : Vec d :=
  Real.sqrt (sigma : ℝ) • e

end

end Algsuperdiff.Section3.Observable
