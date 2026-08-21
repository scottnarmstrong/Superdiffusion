/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineInstallPins

/-!
# The `EthmB(m)` pairing: the two printed summands, against the two level slots

## What this file supplies

`HomSpineInstallArith` reduced the §4.5 level arithmetic to three residues, of
which two — `hA`, `hB` together with the budget split `hsplit` — are the
manuscript's "comparing to the definition of `EthmB(m)`".  This
file performs that comparison at the two printed summands of `EthmB(m)`:

```text
  EthmB(m) = s^{-1} 3^{(1-α)X_m(α)} 𝓔_{s₁}(□_m,n) (1 + 𝓔_{1/4}(□_m))
               + C γ⁵ (1 + 𝓔²_{s₁/2}(□_m,n)).
```

* `ofReal_firstLeg_le` pairs the FIRST level slot `C_cg σ⁻¹ 𝓔₁ C_en` against the
  first summand.  The Step-2 constant `C_en` is taken at the shape the printed
  energy-density bound gives it — `C_en = C · (3^{(1-α)X_m}
  (1 + 𝓔_{1/4}))` — which is what makes the pairing an inequality between the
  SAME two random factors.
* `ofReal_gapLeg_le` pairs the SECOND level slot against the `γ⁵` summand,
  through `HomSpineInstallData.homGapAbsorbAt` at any `s₂`
  admitting the absorption, in particular the corrected pin `s₂ = 49/100`.
* `ofReal_add_le_ethmB` adds the two, and `le_toReal_of_ofReal_le` converts the
  `[0,∞]` domination into the REAL budget inequality `A + B ≤ C_w · E_B` that
  the bundle's `hsplit` conjunct is, at `E_B:= (EthmB(m))(ω).toReal`.

The two `𝓔`-dominations are the file's inputs, stated at the own
carriers; see the disclosure below.

## Scope

The two hypotheses `hdom1`, `hdom2` compare the coarse-graining bundle's error
slots with `EthmB(m)`'s own factors.  At the CURRENT pins these two
are NOT the same object, in three independent respects, and no bridge between
them exists in the tree:

1. **the coefficient** — the bundle's slots dominate
   `parentTruncatedHomogenizationErrorInfinity{One,Two}Scalar` at the CUTOFF
   field `a_L` (`HomCGCarrierLegs.exists_weakNegDualBounds_of_cutoffPair`,
   `Cutoff.coefficientCutoffCoeffOn`), while `EthmB(m)` and BOTH printed
   displays carry the FLUX-CORRECTED field
   `ã_{L,m}`;
2. **the order** — the bundle pins the dual low order at `s₁′ = s/8` (and its
   half `s/16`), while `EthmB(m)` carries `s₁ = s/2` (and `s₁/2 = s/4`), the
   print's own choice the §4.5 parameter choices.  `𝓔` is a weighted average
   with normalized weights and is NOT monotone in the order, so neither
   direction is free;
3. **the `q` index** — the first slot's carrier is the `q = 1` functional,
   `EthmB(m)`'s first factor the `q = 2` one (the print has the same asymmetry
   between the two printed displays, where it is a Jensen step).

Nothing in this file asserts those inputs; they are named, and the arithmetic
above them is proved outright.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The two summands of `EthmB(m)`, named -/

/-- The FIRST summand of `EthmB(m)`: the minimal-scale factor
times the two printed `𝓔` factors, weighted by `s^{-1}`. -/
def ethmBFirst (M : ABKModel d) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m n : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ENNReal.ofReal ((s : ℝ)⁻¹) *
    (Y omega *
      (fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega *
        (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)))

/-- The SECOND summand of `EthmB(m)`: the `γ⁵` gap term. -/
def ethmBGap (M : ABKModel d) (Cgap : ℝ) (m n : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ENNReal.ofReal (Cgap * M.gamma ^ (5 : ℕ)) *
    (1 +
      fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 : ℝ))

/-- `EthmB(m)` IS the sum of its two named summands. -/
theorem ethmB_eq_first_add_gap (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m n : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) :
    ethmB M Cgap Y m n s omega =
      ethmBFirst M Y m n s omega + ethmBGap M Cgap m n s omega :=
  rfl

/-! ## 2. The first leg: the level's first slot against the first summand -/

/-- The abstract shape of the first pairing: a real product with one `toReal`
factor, against the `[0,∞]` product it is a `toReal` of. -/
private theorem ofReal_firstLeg_core {c Cen0 E1 sr : ℝ} (Ycar Qcar Rcar : ℝ≥0∞)
    (hc : 0 ≤ c) (hCen0 : 0 ≤ Cen0) (hE1 : 0 ≤ E1) (hsr : 0 < sr)
    (hdom : ENNReal.ofReal E1 ≤ Qcar) :
    ENNReal.ofReal (c * E1 * (Cen0 * (Ycar * Rcar).toReal)) ≤
      ENNReal.ofReal (c * Cen0 * sr) *
        (ENNReal.ofReal sr⁻¹ * (Ycar * (Qcar * Rcar))) := by
  have hcCen : (0 : ℝ) ≤ c * Cen0 := mul_nonneg hc hCen0
  have hlhs : ENNReal.ofReal (c * E1 * (Cen0 * (Ycar * Rcar).toReal)) =
      ENNReal.ofReal (c * Cen0) *
        (ENNReal.ofReal E1 * ENNReal.ofReal (Ycar * Rcar).toReal) := by
    rw [show c * E1 * (Cen0 * (Ycar * Rcar).toReal) =
        c * Cen0 * (E1 * (Ycar * Rcar).toReal) by ring,
      ENNReal.ofReal_mul hcCen, ENNReal.ofReal_mul hE1]
  have hconst : ENNReal.ofReal (c * Cen0 * sr) * ENNReal.ofReal sr⁻¹ =
      ENNReal.ofReal (c * Cen0) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hcCen hsr.le)]
    congr 1
    field_simp
  have hrhs : ENNReal.ofReal (c * Cen0 * sr) *
      (ENNReal.ofReal sr⁻¹ * (Ycar * (Qcar * Rcar))) =
      ENNReal.ofReal (c * Cen0) * (Qcar * (Ycar * Rcar)) := by
    rw [← mul_assoc, hconst]
    ring
  rw [hlhs, hrhs]
  exact mul_le_mul' le_rfl (mul_le_mul' hdom ENNReal.ofReal_toReal_le)

/-- **THE FIRST PAIRING**.

The level's first slot — the coarse-graining constant, the order weight, the
error slot and the Step-2 constant `C_en` at its printed shape
`C · (3^{(1-α)X_m}(1 + 𝓔_{1/4}))` — is below the first summand of `EthmB(m)`
times a constant that carries no randomness.

The single input is `hdom`: the error slot is dominated by `EthmB(m)`'s own
first `𝓔` factor.  See the module disclosure. -/
theorem ofReal_firstLeg_le (M : ABKModel d) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (m n : ℤ) (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d)
    {c Cen0 E1 : ℝ} (hc : 0 ≤ c) (hCen0 : 0 ≤ Cen0) (hE1 : 0 ≤ E1)
    (hdom : ENNReal.ofReal E1 ≤
      fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega) :
    ENNReal.ofReal
        (c * E1 *
          (Cen0 *
            (Y omega *
              (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)).toReal)) ≤
      ENNReal.ofReal (c * Cen0 * (s : ℝ)) * ethmBFirst M Y m n s omega :=
  ofReal_firstLeg_core _ _ _ hc hCen0 hE1 s.2 hdom

/-! ## 3. The second leg: the level's forcing slot against the `γ⁵` summand -/

/-- The gap-absorption constant is nonnegative exactly on the range where the
absorption holds. -/
theorem homGapConstAt_nonneg {s2 : ℝ} (hs2 : 5 < 10 * s2 * Real.log 3) :
    0 ≤ homGapConstAt s2 := by
  have hpos : (0 : ℝ) < 10 * s2 * Real.log 3 - 5 := by linarith only [hs2]
  rw [homGapConstAt]
  positivity

/-- The abstract shape of the gap pairing. -/
private theorem ofReal_gapLeg_core {c gap K Cgap g5 E2 : ℝ} (Ecar : ℝ≥0∞)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hCgap : 0 < Cgap) (hg5 : 0 ≤ g5) (hE2 : 0 ≤ E2)
    (hgap : gap ≤ K * g5) (hdom : ENNReal.ofReal E2 ≤ Ecar) :
    ENNReal.ofReal (c * gap * (1 + E2 ^ (2 : ℕ))) ≤
      ENNReal.ofReal (c * K / Cgap) *
        (ENNReal.ofReal (Cgap * g5) * (1 + Ecar ^ (2 : ℝ))) := by
  have hsq : (0 : ℝ) ≤ E2 ^ (2 : ℕ) := pow_nonneg hE2 2
  have hone : (0 : ℝ) ≤ 1 + E2 ^ (2 : ℕ) := by linarith only [hsq]
  have hstep : c * gap * (1 + E2 ^ (2 : ℕ)) ≤ c * (K * g5) * (1 + E2 ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap hc) hone
  have hcK : (0 : ℝ) ≤ c * K / Cgap := div_nonneg (mul_nonneg hc hK) hCgap.le
  have hCg5 : (0 : ℝ) ≤ Cgap * g5 := mul_nonneg hCgap.le hg5
  have hsplit : c * (K * g5) * (1 + E2 ^ (2 : ℕ)) =
      c * K / Cgap * (Cgap * g5) * (1 + E2 ^ (2 : ℕ)) := by
    field_simp
  have hprod : ENNReal.ofReal (c * K / Cgap * (Cgap * g5) * (1 + E2 ^ (2 : ℕ))) =
      ENNReal.ofReal (c * K / Cgap) *
        (ENNReal.ofReal (Cgap * g5) * ENNReal.ofReal (1 + E2 ^ (2 : ℕ))) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hcK hCg5), ENNReal.ofReal_mul hcK, mul_assoc]
  have hsum : ENNReal.ofReal (1 + E2 ^ (2 : ℕ)) ≤ 1 + Ecar ^ (2 : ℝ) := by
    have hrw : ENNReal.ofReal (1 + E2 ^ (2 : ℕ)) =
        1 + ENNReal.ofReal E2 ^ (2 : ℕ) := by
      rw [ENNReal.ofReal_add (by norm_num) hsq, ENNReal.ofReal_one,
        ENNReal.ofReal_pow hE2]
    have hpow : ENNReal.ofReal E2 ^ (2 : ℕ) ≤ Ecar ^ (2 : ℕ) := pow_le_pow_left' hdom 2
    have hcast : Ecar ^ (2 : ℕ) = Ecar ^ (2 : ℝ) := by
      rw [← ENNReal.rpow_natCast Ecar 2]
      norm_num
    rw [hrw, ← hcast]
    exact add_le_add le_rfl hpow
  calc ENNReal.ofReal (c * gap * (1 + E2 ^ (2 : ℕ)))
      ≤ ENNReal.ofReal (c * (K * g5) * (1 + E2 ^ (2 : ℕ))) :=
        ENNReal.ofReal_le_ofReal hstep
    _ = ENNReal.ofReal (c * K / Cgap) *
          (ENNReal.ofReal (Cgap * g5) * ENNReal.ofReal (1 + E2 ^ (2 : ℕ))) := by
        rw [hsplit, hprod]
    _ ≤ ENNReal.ofReal (c * K / Cgap) *
          (ENNReal.ofReal (Cgap * g5) * (1 + Ecar ^ (2 : ℝ))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hsum)

/-- **THE SECOND PAIRING**.

The level's forcing slot, once the mesoscale gap `s^{-9/2} 3^{s₂(n-m)}` has been
absorbed at the `γ⁵` rate (`homGapAbsorbAt`), is below the `γ⁵` summand of
`EthmB(m)` times a constant that carries no randomness.

The single input is `hdom`: the second error slot is dominated by `EthmB(m)`'s
own `𝓔` factor.  See the module disclosure. -/
theorem ofReal_gapLeg_le (M : ABKModel d) {Cgap : ℝ} (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) {c E2 s2 : ℝ}
    (hlog : 4 ≤ |Real.log M.gamma|) (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap)
    (hc : 0 ≤ c) (hE2 : 0 ≤ E2) (hs2 : 5 < 10 * s2 * Real.log 3)
    (hdom : ENNReal.ofReal E2 ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) (homQuarterOf s) omega) :
    ENNReal.ofReal
        (c *
            (homS M ^ (-(9 / 2) : ℝ) *
              (3 : ℝ) ^ (s2 * (((homN M m : ℤ)) : ℝ) - s2 * (m : ℝ))) *
          (1 + E2 ^ (2 : ℕ))) ≤
      ENNReal.ofReal (c * homGapConstAt s2 / Cgap) *
        ethmBGap M Cgap m (homN M m) s omega := by
  have hgap := homGapAbsorbAt (M := M) hlog hgamma1 m hs2
  have hexp : (3 : ℝ) ^ (s2 * (((homN M m : ℤ)) : ℝ) - s2 * (m : ℝ)) =
      (3 : ℝ) ^ (s2 * ((((homN M m : ℤ)) : ℝ) - (m : ℝ))) := by
    congr 1
    ring
  rw [hexp, ethmBGap]
  exact ofReal_gapLeg_core _ hc (homGapConstAt_nonneg hs2) hCgap
    (pow_nonneg M.shellPrefix.gamma_pos.le 5) hE2 hgap hdom

/-! ## 4. The two legs added: the budget inequality -/

/-- **THE `EthmB(m)` BUDGET, in `[0,∞]`.**  Both level slots together are below
`EthmB(m)` times the sum of the two pairing constants. -/
theorem ofReal_add_le_ethmB (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m n : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) {A B cA cB : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB)
    (hA : ENNReal.ofReal A ≤ ENNReal.ofReal cA * ethmBFirst M Y m n s omega)
    (hB : ENNReal.ofReal B ≤ ENNReal.ofReal cB * ethmBGap M Cgap m n s omega) :
    ENNReal.ofReal (A + B) ≤
      ENNReal.ofReal (cA + cB) * ethmB M Cgap Y m n s omega := by
  have hcA : ENNReal.ofReal cA ≤ ENNReal.ofReal (cA + cB) :=
    ENNReal.ofReal_le_ofReal (by linarith only [hcB0])
  have hcB : ENNReal.ofReal cB ≤ ENNReal.ofReal (cA + cB) :=
    ENNReal.ofReal_le_ofReal (by linarith only [hcA0])
  calc ENNReal.ofReal (A + B)
      = ENNReal.ofReal A + ENNReal.ofReal B := ENNReal.ofReal_add hA0 hB0
    _ ≤ ENNReal.ofReal cA * ethmBFirst M Y m n s omega +
          ENNReal.ofReal cB * ethmBGap M Cgap m n s omega := add_le_add hA hB
    _ ≤ ENNReal.ofReal (cA + cB) * ethmBFirst M Y m n s omega +
          ENNReal.ofReal (cA + cB) * ethmBGap M Cgap m n s omega :=
        add_le_add (mul_le_mul' hcA le_rfl) (mul_le_mul' hcB le_rfl)
    _ = ENNReal.ofReal (cA + cB) *
          (ethmBFirst M Y m n s omega + ethmBGap M Cgap m n s omega) := by ring
    _ = ENNReal.ofReal (cA + cB) * ethmB M Cgap Y m n s omega := by
        rw [ethmB_eq_first_add_gap]

/-! ## 5. The real budget: the bundle's `hsplit`, at `E_B = (EthmB(m)).toReal` -/

/-- **THE REAL CUT.**  An `[0,∞]` domination by `C_w · EthmB(m)` becomes the
bundle's own real budget inequality at `E_B:= (EthmB(m))(ω).toReal`, on the
(a.e.) event where the carrier is finite. -/
theorem le_toReal_of_ofReal_le {X Cw : ℝ} {T : ℝ≥0∞} (hCw : 0 ≤ Cw)
    (hfin : T ≠ ⊤) (h : ENNReal.ofReal X ≤ ENNReal.ofReal Cw * T) :
    X ≤ Cw * T.toReal := by
  have hT : ENNReal.ofReal Cw * T = ENNReal.ofReal (Cw * T.toReal) := by
    rw [ENNReal.ofReal_mul hCw, ENNReal.ofReal_toReal hfin]
  rw [hT] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCw ENNReal.toReal_nonneg)).1 h

/-- The real cut of `EthmB(m)` itself is a legitimate defect witness: it is
nonnegative and it is dominated by the carrier (with no finiteness needed). -/
theorem ofReal_ethmB_toReal_le (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m n : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) :
    ENNReal.ofReal (ethmB M Cgap Y m n s omega).toReal ≤
      ethmB M Cgap Y m n s omega :=
  ENNReal.ofReal_toReal_le

end

end Algsuperdiff.Section4.Provider.Homogenization
