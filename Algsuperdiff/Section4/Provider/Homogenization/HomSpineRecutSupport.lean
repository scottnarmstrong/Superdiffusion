/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomCGCarrierLegs

/-!
# Support for the bundle re-cut: the multiscale clause alone, the printed
# carriers' finiteness, the two produced constants, and the numeral pin

## What this file supplies

Route (i) is closed, leaving ONE mechanical step: re-cut the spine's per-`ω`
bundle so that the transcribed source hypothesis appears with its MULTISCALE
clause alone, and the Step-4 output `hC4ex` is PRODUCED rather than assumed.
This file gives the four ingredients that step needs.

1. `CoarseGrainingFinitePMultiscale` — clause 1 of
   `HomFinitePSource.GeneralCoarseGrainingFiniteP`, standing alone, with the
   projection `gradPartial` the Step-3c leg actually consumes and the forgetful
   bridge `GeneralCoarseGrainingFiniteP.toMultiscale` (so the re-cut bundle is
   IMPLIED by the one on this conjunct — the regression direction).
2. **THE FINITENESS CHECK** (the CHECK-FIRST item).  The re-cut carries four
   slot dominations; each is a genuine hypothesis only if its printed carrier
   can be `⊤`.  The verdict, machine-checked below:
   * `parentTruncatedHomogenizationErrorInfinityOneScalar` — NEVER `⊤`
     (`CoarseGraining`'s `…_eq_ofReal` exhibits it as an `ENNReal.ofReal`), UNCONDITIONALLY;
   * `parentTruncatedHomogenizationErrorInfinityTwoScalar` — the same;
   * `cubeEuclideanPositiveBesovOverlapESeminorm` — never `⊤` on the printed
     data class `MemCubeEuclideanFullWsp`, which the root's own `C^{0,1/2}`
     binder supplies (`HomCGFinalDatum.memCubeEuclideanFullWsp_of_holderHalf`).
   So all three dominations are PINNABLE: at `E:= carrier.toReal` they hold by
   `ENNReal.ofReal_toReal`, and no printed finiteness requirement has to be
   added to the bundle.  The three `…_dominates_self` lemmas below are that
   pinning, and they are what makes the re-cut bundle demonstrably non-vacuous.
3. The two constants the re-cut must NAME.  The bundle's `Ccg` slot is tied to
   the printed constant `C(p,d)` of `HomCGCarrierLegs`, and the bundle's
   Schauder slot to the external's `C_sch(d,s)`; both are produced by
   existential theorems, so the re-cut names them
   (`cgDualBoundConst`, `stepFourSchauderConst`) and recovers their defining
   property through `Classical.choose_spec`.
4. The numeral pin.  At the printed §4.5 exponent `p = 4d` and the display pin
   `s₁′ = s/8`, `s′ = 7s/8`, the joint conjunction
   `s₁′ < s′ < s₂`, `s₂ < 1/2`, `1/2 - d/p < s₂`, `s + d/p ≤ 1/2`
   is satisfied at `s₂ = 3/8`, for EVERY admissible `s` — and the guard itself
   is satisfiable (`s = 1/8`).
-/

open Homogenization Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The multiscale clause, standing alone -/

/-- **Clause 1 of the transcribed source hypothesis, ALONE.**

`HomFinitePSource.GeneralCoarseGrainingFiniteP` asserts the printed display at
BOTH readings of its undefined negative-norm symbol.  Step 3c consumes only the
MULTISCALE reading; the two DUALITY readings are proved from the
root's own binders, so the re-cut bundle carries this clause and no other.

THIS IS A HYPOTHESIS.  It is never proved in this repository. -/
def CoarseGrainingFinitePMultiscale (Q : TriadicCube d) (jn : ℕ)
    (Ccg s s1 s2 p sigma E1 E2 Dg : ℝ)
    (Gen : TriadicCube d → ℝ) (Fgrad Fflux : Vec d → Vec d) : Prop :=
  ∀ S : ℝ, (∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S) →
    ∀ N : ℕ,
      sigma * negBesovLpPartialNorm Q s p N Fgrad +
          negBesovLpPartialNorm Q s p N Fflux ≤
        coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))

/-- **The regression direction.**  The bundle's conjunct implies the
re-cut bundle's conjunct: the re-cut only forgets. -/
theorem GeneralCoarseGrainingFiniteP.toMultiscale {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d}
    (h : GeneralCoarseGrainingFiniteP Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux) :
    CoarseGrainingFinitePMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux :=
  fun _ hS N => h.multiscale hS N

/-- The single gradient leg, with the flux leg discarded — the source's own
route (ii) in the paper, "we just discarded it".  This is the ONLY consequence
of the transcribed hypothesis the Step-3c leg uses. -/
theorem CoarseGrainingFinitePMultiscale.gradPartial {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d}
    (h : CoarseGrainingFinitePMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux)
    {S : ℝ} (hS : ∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S)
    (hsigma : 0 < sigma) (N : ℕ) :
    negBesovLpPartialNorm Q s p N Fgrad ≤
      sigma⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) := by
  have hflux : (0 : ℝ) ≤ negBesovLpPartialNorm Q s p N Fflux :=
    negBesovLpPartialNorm_nonneg Q s p N Fflux
  have hmain := h S hS N
  have hstep : sigma * negBesovLpPartialNorm Q s p N Fgrad ≤
      coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) := by
    linarith only [hmain, hflux]
  have hne : sigma ≠ 0 := ne_of_gt hsigma
  calc negBesovLpPartialNorm Q s p N Fgrad
      = sigma⁻¹ * (sigma * negBesovLpPartialNorm Q s p N Fgrad) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ ≤ sigma⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) :=
        mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hsigma.le)

/-! ## 2. THE FINITENESS CHECK, and the pinning it licenses -/

/-- **The `𝓔₁` carrier is never `⊤`** — unconditionally.  `CoarseGraining`'s
`parentTruncatedHomogenizationErrorInfinityOneScalar_eq_ofReal` exhibits it as
an `ENNReal.ofReal`. -/
theorem parentErrorOne_ne_top [NeZero d] (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (s1 : FractionalOrder) :
    Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0
        hsigma0 s1 ≠ ⊤ := by
  rw [parentTruncatedHomogenizationErrorInfinityOneScalar_eq_ofReal Q n hn a sigma0
    hsigma0 s1]
  exact ENNReal.ofReal_ne_top

/-- **The `𝓔₂` carrier is never `⊤`** — unconditionally. -/
theorem parentErrorTwo_ne_top [NeZero d] (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (s1 : FractionalOrder) :
    Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
        hsigma0 s1 ≠ ⊤ := by
  rw [parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_ofReal Q n hn a sigma0
    hsigma0 s1]
  exact ENNReal.ofReal_ne_top

/-- **The `[𝐠]` carrier is never `⊤` on the printed data class.**

The overlap seminorm is below the dimension constant times the fractional
seminorm, and both factors are finite on `MemCubeEuclideanFullWsp`. -/
theorem overlapSeminorm_ne_top [NeZero d] (Q : TriadicCube d) (s2 : FractionalOrder)
    (p : FiniteLpExponent) {g : Vec d → Vec d} (hg : MemCubeEuclideanFullWsp Q s2 p g) :
    ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g ≠ ⊤ := by
  let F : CubeEuclideanLpField Q p := { toField := g, euclideanMemLp := hg.1 }
  have hcomp := cubeEuclideanOverlap_le_dimensionConstant_mul_wsp Q s2 p F
  have hright : cubeEuclideanWspOverlapDimensionConstant d *
      cubeEuclideanWspESeminorm Q s2 p g < ∞ :=
    ENNReal.mul_lt_top (cubeEuclideanWspOverlapDimensionConstant_lt_top d)
      hg.2.eSeminorm_lt_top
  have hkey : ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g < ∞ := by
    refine lt_of_le_of_lt ?_ hright
    simpa only [F] using hcomp
  exact hkey.ne

/-- **The `𝓔₁` domination is PINNABLE**: at `E₁:= carrier.toReal` it is free. -/
theorem parentErrorOne_dominates_self [NeZero d] (Q : TriadicCube d) {n : ℤ}
    (hn : n ≤ Q.scale) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (s1 : FractionalOrder) :
    Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0
        hsigma0 s1 ≤
      ENNReal.ofReal
        (Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0
          hsigma0 s1).toReal := by
  rw [ENNReal.ofReal_toReal (parentErrorOne_ne_top Q hn a hsigma0 s1)]

/-- **The `𝓔₂` domination is PINNABLE**: at `E₂:= carrier.toReal` it is free. -/
theorem parentErrorTwo_dominates_self [NeZero d] (Q : TriadicCube d) {n : ℤ}
    (hn : n ≤ Q.scale) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (s1 : FractionalOrder) :
    Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
        hsigma0 s1 ≤
      ENNReal.ofReal
        (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
          hsigma0 s1).toReal := by
  rw [ENNReal.ofReal_toReal (parentErrorTwo_ne_top Q hn a hsigma0 s1)]

/-- **The `[𝐠]` domination is PINNABLE** on the printed data class. -/
theorem overlapSeminorm_dominates_self [NeZero d] (Q : TriadicCube d)
    (s2 : FractionalOrder) (p : FiniteLpExponent) {g : Vec d → Vec d}
    (hg : MemCubeEuclideanFullWsp Q s2 p g) :
    ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g ≤
      ENNReal.ofReal (ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g).toReal := by
  rw [ENNReal.ofReal_toReal (overlapSeminorm_ne_top Q s2 p hg)]

/-! ## 3. The two produced constants, NAMED -/

open Classical in
/-- **The printed coarse-graining constant `C(p,d)`, named.**

`HomCGCarrierLegs.exists_weakNegDualBounds_of_cutoffPair` produces it before the
model, the scale and the data; the re-cut bundle has to refer to it in the slot
condition `C(p,d) ≤ Ccg`, so it is named here. -/
def cgDualBoundConst (d : ℕ) (p : FiniteLpExponent) : ℝ≥0∞ :=
  if h : 2 ≤ d ∧ (2 : ℝ≥0∞) ≤ p.exponent then
    Classical.choose (exists_weakNegDualBounds_of_cutoffPair d h.1 p h.2)
  else 0

theorem cgDualBoundConst_eq (d : ℕ) (hd : 2 ≤ d) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    cgDualBoundConst d p =
      Classical.choose (exists_weakNegDualBounds_of_cutoffPair d hd p hp) := by
  unfold cgDualBoundConst
  rw [dif_pos (⟨hd, hp⟩ : 2 ≤ d ∧ (2 : ℝ≥0∞) ≤ p.exponent)]

/-- **The printed constant is finite**, so the bundle's `Ccg` slot is PINNABLE
at `Ccg:= (cgDualBoundConst d p).toReal`. -/
theorem cgDualBoundConst_lt_top (d : ℕ) (hd : 2 ≤ d) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) : cgDualBoundConst d p < ∞ := by
  have hspec := Classical.choose_spec (exists_weakNegDualBounds_of_cutoffPair d hd p hp)
  rw [cgDualBoundConst_eq d hd p hp]
  exact hspec.1

/-- The `Ccg` domination is free at the canonical pin. -/
theorem cgDualBoundConst_dominates_self (d : ℕ) (hd : 2 ≤ d) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    cgDualBoundConst d p ≤ ENNReal.ofReal (cgDualBoundConst d p).toReal := by
  rw [ENNReal.ofReal_toReal (cgDualBoundConst_lt_top d hd p hp).ne]

open Classical in
/-- **The Schauder external's Step-4 constant, named.**

`HomCGCarrierLegs.exists_comparator_stepFourEnergy_of_dualBounds` produces it
from `(d, s)` alone; the re-cut bundle refers to it in the absorbed-constant
condition `spineClauseConst d s p C_w C_sch ≤ K_abs`. -/
def stepFourSchauderConst (d : ℕ) (s : ℝ) : ℝ :=
  if h : 2 ≤ d ∧ 0 < s ∧ s ≤ 1 / 2 then
    Classical.choose (exists_comparator_stepFourEnergy_of_dualBounds (d := d) h.1 h.2.1 h.2.2)
  else 0

theorem stepFourSchauderConst_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsle : s ≤ 1 / 2) :
    stepFourSchauderConst d s =
      Classical.choose
        (exists_comparator_stepFourEnergy_of_dualBounds (d := d) hd hs0 hsle) := by
  unfold stepFourSchauderConst
  rw [dif_pos (⟨hd, hs0, hsle⟩ : 2 ≤ d ∧ 0 < s ∧ s ≤ 1 / 2)]

theorem stepFourSchauderConst_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsle : s ≤ 1 / 2) :
    0 < stepFourSchauderConst d s := by
  have hspec :=
    Classical.choose_spec (exists_comparator_stepFourEnergy_of_dualBounds (d := d) hd hs0 hsle)
  rw [stepFourSchauderConst_eq hd hs0 hsle]
  exact hspec.1

/-! ## 4. The numeral pin: `p = 4d`, `s₁′ = s/8`, `s′ = 7s/8`, `s₂ = 3/8` -/

/-- The printed §4.5 exponent `p = 4d`, as a `FiniteLpExponent`. -/
def recutExponent (d : ℕ) (hd : 1 ≤ d) : FiniteLpExponent where
  exponent := ((4 * d : ℕ) : ℝ≥0∞)
  one_lt := by
    have h : (1 : ℕ) < 4 * d := by omega
    exact_mod_cast (Nat.one_lt_cast (α := ℝ≥0∞)).mpr h
  lt_top := by
    exact lt_of_le_of_ne le_top (ENNReal.natCast_ne_top (4 * d))

@[simp] theorem recutExponent_toReal (d : ℕ) (hd : 1 ≤ d) :
    (recutExponent d hd).exponent.toReal = 4 * (d : ℝ) := by
  show (((4 * d : ℕ) : ℝ≥0∞)).toReal = 4 * (d : ℝ)
  rw [ENNReal.toReal_natCast]
  push_cast
  ring

/-- **THE JOINT NUMERAL CONJUNCTION AT THE NEW PIN.**

At `p = 4d` and the display pin `s₁′ = s/8`, `s′ = 7s/8`, the window `s₂ = 3/8`
satisfies every printed constraint at once, for EVERY `s` the bundle's own
guard admits. -/
theorem recutNumeralPin (d : ℕ) (hd : 1 ≤ d) {s p : ℝ} (hs0 : 0 < s)
    (hp : p = 4 * (d : ℝ)) (hguard : s + (d : ℝ) / p ≤ 1 / 2) :
    s / 8 < 7 * s / 8 ∧ 7 * s / 8 < 3 / 8 ∧ (3 : ℝ) / 8 < 1 / 2 ∧
      1 / 2 - (d : ℝ) / p < 3 / 8 ∧ s + (d : ℝ) / p ≤ 1 / 2 := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith only [hdR]
  have hquot : (d : ℝ) / p = 1 / 4 := by
    rw [hp]
    field_simp
  have hs4 : s ≤ 1 / 4 := by
    rw [hquot] at hguard
    linarith only [hguard]
  refine ⟨by linarith only [hs0], by linarith only [hs4], by norm_num, ?_, hguard⟩
  rw [hquot]
  norm_num

/-- The bundle's own guard is satisfiable at the printed pin: `s = 1/8`,
`p = 4d`. -/
theorem recutGuard_nonvacuous (d : ℕ) (hd : 1 ≤ d) :
    (0 : ℝ) < 1 / 8 ∧ (1 : ℝ) / 8 + (d : ℝ) / (4 * (d : ℝ)) ≤ 1 / 2 := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith only [hdR]
  have hquot : (d : ℝ) / (4 * (d : ℝ)) = 1 / 4 := by field_simp
  refine ⟨by norm_num, ?_⟩
  rw [hquot]
  norm_num

/-- At the printed pin the exponent clears the `2 ≤ p` threshold the display
needs. -/
theorem recutExponent_two_le (d : ℕ) (hd : 1 ≤ d) :
    (2 : ℝ≥0∞) ≤ (recutExponent d hd).exponent := by
  show (2 : ℝ≥0∞) ≤ ((4 * d : ℕ) : ℝ≥0∞)
  have h : (2 : ℕ) ≤ 4 * d := by omega
  exact_mod_cast (Nat.cast_le (α := ℝ≥0∞)).mpr h

end

end Algsuperdiff.Section4.Provider.Homogenization
