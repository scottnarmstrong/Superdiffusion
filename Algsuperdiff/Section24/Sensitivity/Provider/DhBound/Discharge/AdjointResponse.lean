import Homogenization.Book.Ch02.Theorems.MagicIdentities
import Homogenization.Book.Ch02.Theorems.MatrixExtractionProofs

/-!
# The adjoint response identity

Source: ABK26.  The proof of `l.Dh.bound` needs the energy of the *adjoint*
half `w* = ½ v(·, □₀, p, -q; aᵗ)` expressed through the primal response
functional.  In the coarse-matrix coordinates the two response functionals
differ only by the sign of the `κ` term, so

```
J(U, aᵗ, p, -q) = J(U, a, p, q) + 2 p · q .
```

Both sides are unconditional: the canonical coarse-matrix formula
`responseJ_eq_coarseMatrices_formula_canonical` and the adjoint formula
`ResponseMagicIdentitiesTheory.adjoint_quadratic` hold at every Chapter 2 domain
and coefficient.

The identity is what converts the adjoint energy `(P · 𝐀 P)/2 - 2J` of the
source proof into the frozen budget shape `√J + √|p · q|`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open Homogenization Homogenization.Book Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## Sign bookkeeping for the quadratic form -/

theorem matVecMul_neg (M : Mat d) (v : Vec d) :
    matVecMul M (-v) = -(matVecMul M v) := by
  funext i
  simp [matVecMul, Finset.sum_neg_distrib, mul_neg]

theorem vecDot_neg_neg (v w : Vec d) : vecDot (-v) (-w) = vecDot v w := by
  simp [vecDot]

theorem vecDot_neg_right (v w : Vec d) : vecDot v (-w) = -vecDot v w := by
  simp [vecDot, Finset.sum_neg_distrib, mul_neg]

/-! ## The adjoint response identity -/

/-- **Adjoint response identity.**  Flipping the coefficient to its transpose and
the second loading to its negative shifts the response functional by `2 p · q`. -/
theorem responseJ_transpose_neg_right (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    responseJ U a.transpose p (-q) = responseJ U a p q + 2 * vecDot p q := by
  have hadj := (responseMagicIdentitiesTheory U a).adjoint_quadratic p (-q)
  have hcan := responseJ_eq_coarseMatrices_formula_canonical U a p q
  have hneg : (-q) - matVecMul (Ch02.kappaCoarse U a) p =
      -(q + matVecMul (Ch02.kappaCoarse U a) p) := by
    funext i
    simp [sub_eq_add_neg]
    ring
  rw [hneg, matVecMul_neg, vecDot_neg_neg, vecDot_neg_right] at hadj
  rw [hadj, hcan]
  ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
