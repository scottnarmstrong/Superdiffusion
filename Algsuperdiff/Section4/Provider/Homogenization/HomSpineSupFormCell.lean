/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineSupFormClause

/-!
# The D1 re-cut, fork (iii), PER CELL: the print's own `sup_k max_z` carrier

## Why per cell, and not per depth

`HomSpineSupFormClause` replaced the `ℓ^p`-over-depths aggregate by the sup over
depths, keeping the `ℓ^p` MEAN OVER CELLS inside each depth.  Its duality input
is therefore a depth-`j` GLOBAL test (one test seeing all `3^{jd}` cells of the
depth), and the machine result kills that route: the global test carries a
far-band Gagliardo cost `Σ_{i<j} 3^{-i s p'} ≍ min(j, (s p')⁻¹)`, saturating at
`≈ |log γ|^{1/p'}` once the depth range reaches `⌈10|log γ|⌉` — worse than the
retired banded lane, and machine-witnessed (alternating `±e₁`), not an estimate
artifact.

The manuscript's own display does not ask for that test.  In the printed
display the aggregation is

```text
  sup_{k ≤ n} 3^{-(s-s₁)(n-k)} max_{z ∈ 3^k ℤ^d ∩ □_m}  (per-CELL quantity),
```

a sup over depths AND a max over CELLS of a per-cell quantity — the `p = ∞`
member of the family whose finite-`p` members are the `negBesovLpPartialNorm`.
(The left-hand symbol `Ŵ̲^{-s,∞}` is itself undefined in the print —— so this
is the reading, taken from the print's own displayed weights, not a printed
definition.)  A carrier of that shape is certified ONE CELL AT A TIME, and the
dual test that certifies it is supported on that single cell, where the far
bands do not exist.

## What this file gives

* `negBesovCellDepthMax`, `negBesovSupCellPartialNorm` — the print's carrier:
  `sup_{j ≤ N} 3^{-sj} max_{R ∈ D_j} ‖(F)_R‖`, at the print's own weights.
* `NegBesovCellGaugeBound` — its unbounded-`N` reading, `∀ j, ∀ R ∈ D_j`, which
  is EXACTLY the per-cell descendant datum the whole Step-3c chain consumes.
* `GridCellSmoothDualConverseAt` — THE NAMED DUALITY INPUT, per cube AND per
  cell: `3^{s(m-j)}‖(F)_R‖ ≤ CA · ‖F‖_{smooth dual}`.  No cell count, no depth
  sum, no band.
* `GridDualCellTestFamily` (and its single-cell-SUPPORTED refinement
  `GridDualCellSupportedTestFamily`, which implies it) — the test-side statement
  the pairing needs: one unit-`W̲^{s,p'}(□_m)` test per cube/cell whose
  normalized pairing with `F` sees the weighted cell average.
* `CoarseGrainingSupCellMultiscale` + `exists_…_of_cellConverseOn` — the clause
  at the print's carrier, PRODUCED from the per-cell input plus the `CoarseGraining`
  machinery, at the constant `CA · C(p,d)` (not even a `√d`: the carrier is
  stated in the Euclidean norm the pairing produces).
-/

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The print's carrier: sup over depths, max over cells -/

/-- **The depth-`j` cell maximum**, `3^{-sj} max_{R ∈ D_j} ‖(F)_R‖` — the
`p = ∞` member of the family whose finite-`p` member is
`negBesovLpDepthSeminorm`. -/
def negBesovCellDepthMax (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  (3 : ℝ) ^ (-s * (j : ℝ)) *
    (descendantsAtDepth Q j).sup' (descendantsAtDepth_nonempty Q j) fun R =>
      ‖cubeAverageVec R F‖

/-- **The print's sup-over-depths, max-over-cells partial gauge**. -/
def negBesovSupCellPartialNorm (Q : TriadicCube d) (s : ℝ) (N : ℕ) (F : Vec d → Vec d) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun j =>
    negBesovCellDepthMax Q s F j

theorem negBesovCellDepthMax_def (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    negBesovCellDepthMax Q s F j =
      (3 : ℝ) ^ (-s * (j : ℝ)) *
        (descendantsAtDepth Q j).sup' (descendantsAtDepth_nonempty Q j) fun R =>
          ‖cubeAverageVec R F‖ := rfl

theorem negBesovSupCellPartialNorm_def (Q : TriadicCube d) (s : ℝ) (N : ℕ)
    (F : Vec d → Vec d) :
    negBesovSupCellPartialNorm Q s N F =
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun j =>
        negBesovCellDepthMax Q s F j := rfl

/-- The depth maximum is realized at one cell — the fact that makes the carrier
certifiable per cell. -/
theorem negBesovCellDepthMax_eq_cell (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d)
    (j : ℕ) : ∃ R ∈ descendantsAtDepth Q j,
      negBesovCellDepthMax Q s F j = (3 : ℝ) ^ (-s * (j : ℝ)) * ‖cubeAverageVec R F‖ := by
  obtain ⟨R, hR, hEq⟩ := Finset.exists_mem_eq_sup' (descendantsAtDepth_nonempty Q j)
    fun R => ‖cubeAverageVec R F‖
  exact ⟨R, hR, by rw [negBesovCellDepthMax_def, hEq]⟩

theorem negBesovCellDepthMax_le {Q : TriadicCube d} {s B : ℝ} {F : Vec d → Vec d} {j : ℕ}
    (h : ∀ R ∈ descendantsAtDepth Q j, (3 : ℝ) ^ (-s * (j : ℝ)) * ‖cubeAverageVec R F‖ ≤ B) :
    negBesovCellDepthMax Q s F j ≤ B := by
  obtain ⟨R, hR, hEq⟩ := negBesovCellDepthMax_eq_cell Q s F j
  rw [hEq]
  exact h R hR

theorem negBesovSupCellPartialNorm_le {Q : TriadicCube d} {s B : ℝ} {N : ℕ}
    {F : Vec d → Vec d}
    (h : ∀ j ≤ N, ∀ R ∈ descendantsAtDepth Q j,
      (3 : ℝ) ^ (-s * (j : ℝ)) * ‖cubeAverageVec R F‖ ≤ B) :
    negBesovSupCellPartialNorm Q s N F ≤ B :=
  Finset.sup'_le _ _ fun j hj =>
    negBesovCellDepthMax_le (h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))

theorem negBesovCellDepthMax_nonneg (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    0 ≤ negBesovCellDepthMax Q s F j := by
  obtain ⟨R, _, hEq⟩ := negBesovCellDepthMax_eq_cell Q s F j
  rw [hEq]
  exact mul_nonneg (three_rpow_nonneg _) (norm_nonneg _)

theorem negBesovSupCellPartialNorm_nonneg (Q : TriadicCube d) (s : ℝ) (N : ℕ)
    (F : Vec d → Vec d) : 0 ≤ negBesovSupCellPartialNorm Q s N F :=
  le_trans (negBesovCellDepthMax_nonneg Q s F 0)
    (Finset.le_sup' (f := fun j => negBesovCellDepthMax Q s F j)
      (Finset.mem_range.mpr (Nat.succ_pos N)))

/-! ## 2. The unbounded reading — the per-cell descendant datum -/

/-- **The print's gauge bound at level `A`**: every cell of every depth obeys
`3^{-sj}‖(F)_R‖ ≤ A`.  This is `sup_j max_z ≤ A` written out, and it is
verbatim the per-cell datum the Step-3c chain consumes. -/
def NegBesovCellGaugeBound (Q : TriadicCube d) (s A : ℝ) (F : Vec d → Vec d) : Prop :=
  ∀ (j : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth Q j →
    (3 : ℝ) ^ (-s * (j : ℝ)) * ‖cubeAverageVec R F‖ ≤ A

theorem negBesovCellGaugeBound_iff_forall_partial {Q : TriadicCube d} {s A : ℝ}
    {F : Vec d → Vec d} :
    NegBesovCellGaugeBound Q s A F ↔ ∀ N : ℕ, negBesovSupCellPartialNorm Q s N F ≤ A := by
  constructor
  · intro h N
    exact negBesovSupCellPartialNorm_le fun j _ R hR => h j R hR
  · intro h j R hR
    refine le_trans ?_ (h j)
    refine le_trans ?_ (Finset.le_sup' (f := fun i => negBesovCellDepthMax Q s F i)
      (Finset.mem_range.mpr (Nat.lt_succ_self j)))
    rw [negBesovCellDepthMax_def]
    refine mul_le_mul_of_nonneg_left ?_ (three_rpow_nonneg _)
    exact Finset.le_sup' (f := fun R => ‖cubeAverageVec R F‖) hR

theorem NegBesovCellGaugeBound.nonneg {Q : TriadicCube d} {s A : ℝ} {F : Vec d → Vec d}
    (h : NegBesovCellGaugeBound Q s A F) : 0 ≤ A := by
  obtain ⟨R, hR⟩ := descendantsAtDepth_nonempty Q 0
  exact le_trans (mul_nonneg (three_rpow_nonneg _) (norm_nonneg _)) (h 0 R hR)

/-- **The `ℓ^p` gauge gives the per-cell one, at the SHIFTED order.**

The cell count `3^{jd}` is what separates the two readings: an `ℓ^p` mean over
the depth-`j` cells controls one cell only after paying `3^{jd/p}`, i.e. at the
order `s + d/p`.  This is `HomFinitePGauge`'s own extraction, restated as the
carrier comparison, and it is the honest regression direction: the print's
carrier at order `s` is STRONGER than the carrier at order `s`. -/
theorem negBesovCellGaugeBound_of_negBesovLp (Q : TriadicCube d) {s p A : ℝ} (hp : 0 < p)
    {F : Vec d → Vec d} (h : ∀ N : ℕ, negBesovLpPartialNorm Q s p N F ≤ A) :
    NegBesovCellGaugeBound Q (s + (d : ℝ) / p) A F := by
  intro j R hR
  have hcell := sqrt_vecNormSq_cubeAverageVec_le_of_depthBound hp
    (negBesovLpDepthSeminorm_le_of_partialBound Q hp F h j) hR
  have hnorm : ‖cubeAverageVec R F‖ ≤ Real.sqrt (vecNormSq (cubeAverageVec R F)) :=
    norm_le_sqrt_vecNormSq _
  have hA : 0 ≤ A := le_trans (negBesovLpDepthSeminorm_nonneg Q s p F 0)
    (negBesovLpDepthSeminorm_le_of_partialBound Q hp F h 0)
  have hw : (0 : ℝ) < (3 : ℝ) ^ (-(s + (d : ℝ) / p) * (j : ℝ)) := three_rpow_pos _
  have hstep : ‖cubeAverageVec R F‖ ≤ A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (j : ℝ)) :=
    hnorm.trans hcell
  have hmul := mul_le_mul_of_nonneg_left hstep hw.le
  refine hmul.trans (le_of_eq ?_)
  rw [← mul_assoc, mul_comm ((3 : ℝ) ^ (-(s + (d : ℝ) / p) * (j : ℝ))) A, mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hzero : -(s + (d : ℝ) / p) * (j : ℝ) + (s + (d : ℝ) / p) * (j : ℝ) = 0 := by ring
  rw [hzero, Real.rpow_zero, mul_one]

/-! ## 3. THE NAMED DUALITY INPUT: one cell at a time -/

/-- **The single-cell grid/smooth-dual comparison.**

The depth-`j` GLOBAL comparison (`HomSpineSupFormClause`'s
`NegativeBesovGridSmoothDualConverseAtDepth`, the
`NegativeBesovGridDepthSmoothDualConverse`) asks one test to see the whole
depth-`j` grid, and pays the far-band cost.  The print's carrier asks only
this: the weighted average on ONE cell, against the smooth dual.

THIS IS A HYPOTHESIS, and it is the ONLY external input of the producer in §4.
`3^{s(m-j)}` is `CoarseGraining`'s running-scale weight (`m = Q.scale`), so the
constant is directly comparable to the. -/
def GridCellSmoothDualConverseAt (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (j : ℕ) (CA : ℝ≥0∞) : Prop :=
  ∀ (F : CubeEuclideanLpField Q FiniteLpExponent.two) (R : TriadicCube d),
    R ∈ descendantsAtDepth Q j →
      ENNReal.ofReal ((3 : ℝ) ^ (s.1 * (((Q.scale : ℤ) : ℝ) - (j : ℝ))) *
          ‖cubeAverageVec R F.toField‖) ≤
        CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F

/-- **The single-cell dual test family** — the test-side statement the pairing
needs: per cube, order, field, depth and CELL, one `W̲^{s,p'}(Q) ∩ L²(Q)` field
of full norm at most one whose normalized pairing with `F` sees the weighted
average on that cell. -/
def GridDualCellTestFamily (d : ℕ) (p : FiniteLpExponent) (CA : ℝ≥0∞) : Prop :=
  ∀ (Q : TriadicCube d) (s : FractionalOrder),
    s.1 * p.conjugate.exponent.toReal ≤ 1 / 2 →
    ∀ (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtDepth Q j →
        ∃ G : CubeEuclideanWspL2Field Q s p.conjugate,
          cubeEuclideanWspFullENorm Q s p.conjugate G.toField ≤ 1 ∧
            ENNReal.ofReal ((3 : ℝ) ^ (s.1 * (((Q.scale : ℤ) : ℝ) - (j : ℝ))) *
                ‖cubeAverageVec R F.toField‖) ≤
              CA * ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G|

/-- **The single-cell-SUPPORTED refinement** — the construction the print's
carrier actually wants: the test vanishes off the cell `R`, so no coarser band
of `W̲^{s,p'}` mass is ever created and the far-band sum has no terms. -/
def GridDualCellSupportedTestFamily (d : ℕ) (p : FiniteLpExponent) (CA : ℝ≥0∞) : Prop :=
  ∀ (Q : TriadicCube d) (s : FractionalOrder),
    s.1 * p.conjugate.exponent.toReal ≤ 1 / 2 →
    ∀ (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtDepth Q j →
        ∃ G : CubeEuclideanWspL2Field Q s p.conjugate,
          (∀ x, x ∉ cubeSet R → G.toField x = 0) ∧
            cubeEuclideanWspFullENorm Q s p.conjugate G.toField ≤ 1 ∧
              ENNReal.ofReal ((3 : ℝ) ^ (s.1 * (((Q.scale : ℤ) : ℝ) - (j : ℝ))) *
                  ‖cubeAverageVec R F.toField‖) ≤
                CA * ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G|

/-- The supported family is a family: the producer never uses the support, so
the constructor may target the stronger, geometrically honest statement. -/
theorem gridDualCellTestFamily_of_supported {p : FiniteLpExponent} {CA : ℝ≥0∞}
    (h : GridDualCellSupportedTestFamily d p CA) : GridDualCellTestFamily d p CA := by
  intro Q s hband F j R hR
  obtain ⟨G, _, hG1, hG2⟩ := h Q s hband F j R hR
  exact ⟨G, hG1, hG2⟩

/-- **The per-cell comparison from the per-cell test family** — the exact
analogue of the `negativeBesovGridDepthSmoothDualConverse_of_depthTestFamily`,
one CELL at a time. -/
theorem gridCellSmoothDualConverseAt_of_cellTestFamily {p : FiniteLpExponent} {CA : ℝ≥0∞}
    (h : GridDualCellTestFamily d p CA) (Q : TriadicCube d) (s : FractionalOrder)
    (hband : s.1 * p.conjugate.exponent.toReal ≤ 1 / 2) (j : ℕ) :
    GridCellSmoothDualConverseAt Q s p j CA := by
  intro F R hR
  obtain ⟨G, hG1, hG2⟩ := h Q s hband F j R hR
  refine hG2.trans ?_
  calc CA * ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G|
      ≤ CA * (cubeEuclideanNegativeWspSmoothDualENorm Q s p F *
          cubeEuclideanWspFullENorm Q s p.conjugate G.toField) :=
        mul_le_mul' le_rfl (ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le F G)
    _ ≤ CA * (cubeEuclideanNegativeWspSmoothDualENorm Q s p F * 1) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hG1)
    _ = CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F := by rw [mul_one]

/-- **THE PRINT'S CARRIER, FROM THE PER-CELL COMPARISON ALONE.**

No cell count, no depth sum, no geometric factor: the sup over depths and the
max over cells are both realized at ONE cell, and the comparison is applied
there. -/
theorem ofReal_negBesovSupCellPartialNorm_le_of_cellConverse (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) {CA : ℝ≥0∞} (N : ℕ)
    (hconv : ∀ j : ℕ, GridCellSmoothDualConverseAt Q s p j CA)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    ENNReal.ofReal (negBesovSupCellPartialNorm Q s.1 N F.toField) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * ((Q.scale : ℤ) : ℝ))) *
        (CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F) := by
  classical
  set B : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * ((Q.scale : ℤ) : ℝ))) *
    (CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F) with hB
  by_cases hBtop : B = ⊤
  · rw [hBtop]; exact le_top
  have hreal : ∀ (j : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth Q j →
      (3 : ℝ) ^ (-s.1 * (j : ℝ)) * ‖cubeAverageVec R F.toField‖ ≤ B.toReal := by
    intro j R hR
    have hsplit : (3 : ℝ) ^ (-s.1 * (j : ℝ)) =
        (3 : ℝ) ^ (-s.1 * ((Q.scale : ℤ) : ℝ)) *
          (3 : ℝ) ^ (s.1 * (((Q.scale : ℤ) : ℝ) - (j : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have hstep : ENNReal.ofReal
        ((3 : ℝ) ^ (-s.1 * (j : ℝ)) * ‖cubeAverageVec R F.toField‖) ≤ B := by
      rw [hsplit, mul_assoc,
        ENNReal.ofReal_mul (three_rpow_nonneg (-s.1 * ((Q.scale : ℤ) : ℝ))), hB]
      exact mul_le_mul' le_rfl (hconv j F R hR)
    have hmono := ENNReal.toReal_mono hBtop hstep
    rwa [ENNReal.toReal_ofReal
      (mul_nonneg (three_rpow_nonneg _) (norm_nonneg _))] at hmono
  have hsup : negBesovSupCellPartialNorm Q s.1 N F.toField ≤ B.toReal :=
    negBesovSupCellPartialNorm_le fun j _ R hR => hreal j R hR
  calc ENNReal.ofReal (negBesovSupCellPartialNorm Q s.1 N F.toField)
      ≤ ENNReal.ofReal B.toReal := ENNReal.ofReal_le_ofReal hsup
    _ = B := ENNReal.ofReal_toReal hBtop

/-! ## 4. The clause at the print's carrier, and its production -/

/-- **THE MULTISCALE CLAUSE AT THE PRINT'S OWN CARRIER.**

`HomSpineSupFormClause.CoarseGrainingSupMultiscale` with the per-depth `ℓ^p`
cell mean replaced by the print's max over cells.  The energy
slot is unchanged (the D3 site; see `HomSpineSupFormClause` §5).

THIS IS A HYPOTHESIS.  It is never proved in this repository. -/
def CoarseGrainingSupCellMultiscale (Q : TriadicCube d) (jn : ℕ)
    (Ccg s s1 s2 p sigma E1 E2 Dg : ℝ)
    (Gen : TriadicCube d → ℝ) (Fgrad Fflux : Vec d → Vec d) : Prop :=
  ∀ S : ℝ, (∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S) →
    ∀ N : ℕ,
      sigma * negBesovSupCellPartialNorm Q s N Fgrad +
          negBesovSupCellPartialNorm Q s N Fflux ≤
        coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))

/-- **The Step-3c leg of the per-cell clause**: the flux leg discarded, the printed `σ̄_m` weight stripped, output in the per-cell reading the
Step-3c chain consumes. -/
theorem CoarseGrainingSupCellMultiscale.gradGauge {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d}
    (h : CoarseGrainingSupCellMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux)
    {S : ℝ} (hS : ∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S)
    (hsigma : 0 < sigma) :
    NegBesovCellGaugeBound Q s
      (sigma⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)))
      Fgrad := by
  refine negBesovCellGaugeBound_iff_forall_partial.mpr fun N => ?_
  have hmain := h S hS N
  have hflux : (0 : ℝ) ≤ negBesovSupCellPartialNorm Q s N Fflux :=
    negBesovSupCellPartialNorm_nonneg Q s N Fflux
  have hstep : sigma * negBesovSupCellPartialNorm Q s N Fgrad ≤
      coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) := by
    linarith only [hmain, hflux]
  have hne : sigma ≠ 0 := ne_of_gt hsigma
  calc negBesovSupCellPartialNorm Q s N Fgrad
      = sigma⁻¹ * (sigma * negBesovSupCellPartialNorm Q s N Fgrad) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ ≤ sigma⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) :=
        mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hsigma.le)

/-- **THE CLAUSE AT THE PRINT'S CARRIER, PRODUCED.**

`HomSpineSupFormClause.exists_coarseGrainingSupMultiscale_of_depthConverseOn`
re-cut per cell: the single input is the SINGLE-CELL comparison, at the
constant `CA · C(p,d)` with `C(p,d)` the constant of
`exists_printedCoarseGrainingFiniteP_smoothDual`.  Neither the depth-summed
`(★)` nor the depth-global test occurs, and no cell-count factor is paid. -/
theorem exists_coarseGrainingSupCellMultiscale_of_cellConverseOn (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    {CA : ℝ≥0∞} (hCA : CA ≠ ⊤) (Pred : FractionalOrder → Prop)
    (hconv : ∀ (m : ℤ) (j : ℕ) (s : FractionalOrder), Pred s →
      GridCellSmoothDualConverseAt (originCube d m) s p j CA) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Ccg : ℝ, 0 ≤ Ccg ∧
      ∀ (m : ℤ) (jn : ℕ), 0 < jn →
      ∀ (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 → Pred s →
      ∀ (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ) (hsigma0 : 0 < sigma0) (g : Vec d → Vec d)
        (u v : H1Function (openCubeSet (originCube d m))),
        MemCubeEuclideanFullWsp (originCube d m) s2 p g →
        IsForcedEquation (originCube d m) a u g →
        IsScalarForcedEquation (originCube d m) sigma0 v g →
        HasH10Difference (originCube d m) u v →
      ∀ (E1 E2 Dg : ℝ) (Gen : TriadicCube d → ℝ) (Fgrad Fflux : Vec d → Vec d),
        0 ≤ E1 → 0 ≤ E2 → 0 ≤ Dg →
        (∀ R, 0 ≤ Gen R) →
        (∀ R, printedLocalEnergy a u R ≤ Gen R) →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (by omega) a sigma0 hsigma0 s1 ≤
          ENNReal.ofReal E1 →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (by omega) a sigma0 hsigma0
            (fractionalOrderHalf s1) ≤ ENNReal.ofReal E2 →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g ≤
          ENNReal.ofReal Dg →
        Fgrad = (centeredCubeGradientDifferenceL2Field m u v).toField →
        Fflux = (centeredCubeFluxDifferenceL2Field m a sigma0 u v).toField →
          CoarseGrainingSupCellMultiscale (originCube d m) jn Ccg s.1 s1.1 s2.1
            p.exponent.toReal sigma0 E1 E2 Dg Gen Fgrad Fflux := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCtop, hsd⟩ := exists_printedCoarseGrainingFiniteP_smoothDual d hd p hp
  have hCAC : CA * C ≠ ⊤ := ENNReal.mul_ne_top hCA hCtop.ne
  refine ⟨(CA * C).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro m jn hjn s1 s s2 hs1s hss2 hband a sigma0 hsigma0 g u v hg hu hv hzero
    E1 E2 Dg Gen Fgrad Fflux hE10 hE20 hDg0 hGen0 hGen hE1 hE2 hDg hFg hFf S hS N
  have hms : (originCube d m).scale = m := rfl
  have hn : (originCube d m).scale - (jn : ℤ) ≤ (originCube d m).scale := by omega
  have hnm : (originCube d m).scale - (jn : ℤ) < m := by rw [hms]; omega
  have hS0 : (0 : ℝ) ≤ S := by
    have hge := hS 0
    have h0 : (0 : ℝ) ≤ coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal
        (s.1 - s1.1) jn 0 Gen := by
      rw [coarseGrainingEnergyPartial_def]
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
        mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (descendantsAverage_nonneg _ _ _ fun R _ => Real.rpow_nonneg (hGen0 R) _)) _
    linarith only [hge, h0]
  have hSlot : weightedLocalSymmetricEnergyLp (originCube d m)
      ((originCube d m).scale - (jn : ℤ)) hn a u s1 s p ≤ ENNReal.ofReal S :=
    weightedLocalSymmetricEnergyLp_le_ofReal hn a u s1 s p (wgap := s.1 - s1.1) le_rfl
      (by omega) hGen0 hGen hS0 hS
  have hdisplay := hsd m ((originCube d m).scale - (jn : ℤ)) hnm s1 s s2 hs1s hss2 a
    sigma0 hsigma0 g hg u v hu hv hzero
  set Ggrad := centeredCubeGradientDifferenceL2Field m u v with hGgrad
  set Gflux := centeredCubeFluxDifferenceL2Field m a sigma0 u v with hGflux
  set W : ℝ≥0∞ := ENNReal.ofReal
    ((3 : ℝ) ^ (-s.1 * (((originCube d m).scale : ℤ) : ℝ))) with hW
  have hCgrad := ofReal_negBesovSupCellPartialNorm_le_of_cellConverse (originCube d m) s p N
    (fun j => hconv m j s hband) Ggrad
  have hCflux := ofReal_negBesovSupCellPartialNorm_le_of_cellConverse (originCube d m) s p N
    (fun j => hconv m j s hband) Gflux
  have hchain : ENNReal.ofReal
      (sigma0 * negBesovSupCellPartialNorm (originCube d m) s.1 N Fgrad +
        negBesovSupCellPartialNorm (originCube d m) s.1 N Fflux) ≤
      ENNReal.ofReal (coarseGrainingFinitePRHS (CA * C).toReal s.1 s2.1 sigma0 E1 E2 Dg S
        ((originCube d m).scale - (jn : ℤ))) := by
    rw [hFg, hFf,
      ENNReal.ofReal_add (mul_nonneg hsigma0.le (negBesovSupCellPartialNorm_nonneg _ _ _ _))
        (negBesovSupCellPartialNorm_nonneg _ _ _ _),
      ENNReal.ofReal_mul hsigma0.le]
    calc ENNReal.ofReal sigma0 *
          ENNReal.ofReal
            (negBesovSupCellPartialNorm (originCube d m) s.1 N Ggrad.toField) +
          ENNReal.ofReal
            (negBesovSupCellPartialNorm (originCube d m) s.1 N Gflux.toField)
        ≤ ENNReal.ofReal sigma0 *
            (W * (CA * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p Ggrad)) +
            W * (CA * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p Gflux) :=
          add_le_add (mul_le_mul' le_rfl hCgrad) hCflux
      _ = CA * (W * centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p) := by
          simp only [centeredCubeFluxComparisonSmoothDualLHS, ← hGgrad, ← hGflux]
          ring
      _ ≤ CA * localCoarseGrainingLpRHS C (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) hn a sigma0 hsigma0 g u s1 s s2 p :=
          mul_le_mul' le_rfl hdisplay
      _ = localCoarseGrainingLpRHS (CA * C) (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) hn a sigma0 hsigma0 g u s1 s s2 p :=
          localCoarseGrainingLpRHS_const_mul CA C (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) hn a sigma0 hsigma0 g u s1 s s2 p
      _ ≤ ENNReal.ofReal (coarseGrainingFinitePRHS (CA * C).toReal s.1 s2.1 sigma0 E1 E2 Dg S
            ((originCube d m).scale - (jn : ℤ))) :=
          localCoarseGrainingLpRHS_le_ofReal hn a hsigma0 g u s1 s s2 p hss2
            ENNReal.toReal_nonneg hE10 hE20 hDg0 hS0
            (le_of_eq (ENNReal.ofReal_toReal hCAC).symm) hE1 hE2 hDg hSlot
  exact (ENNReal.ofReal_le_ofReal_iff
    (coarseGrainingFinitePRHS_nonneg ENNReal.toReal_nonneg s.2.1 hss2 hE10 hE20 hDg0
      hS0)).mp hchain

end

end Algsuperdiff.Section4.Provider.Homogenization
