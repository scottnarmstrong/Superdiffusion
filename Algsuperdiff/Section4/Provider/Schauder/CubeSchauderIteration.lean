/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Schauder.CubeSchauderFreezing

/-!
# Cube Schauder: the de-randomized Campanato iteration

The recursion produced by the freezing step of `CubeSchauderFreezing` at the
triadic sub-scales of a cube has the shape

```text
  E (k+1) ≤ theta * E k + F * rho ^ k ,
```

where `E k` is the excess at scale `3^{-k}`, `theta` is the contraction factor
supplied by the interior (or reflected boundary) regularity of the frozen
harmonic comparison function, `rho = 3^{-alpha}` is the freezing gain, and `F`
is the `C^{0,alpha}` seminorm of the forcing.  Whenever `theta < rho < 1` the
iteration closes at the *forcing* rate:

```text
  E k ≤ (E 0 + F / (rho - theta)) * rho ^ k ,
```

which is exactly the Campanato bound whose Morrey dual is `∇u ∈ C^{0,alpha}`.

At the development's exponent `alpha = 1/2` the rate is `rho = 3^{-1/2}`, i.e.
the `3^{-k/2}` decay of the target `ZeroDatumCubeSchauder`.

Nothing in this module is an elliptic estimate: every declaration is an
unconditional statement about real sequences, plus the triadic dictionary that
identifies `rho ^ k` with the gauge `3^{-k/2}` of the frozen conclusion.

## Main results

* `excess_le_of_recursion` — the sharp induction: the recursion propagates the
  ansatz `theta ^ k * + (F / (rho - theta)) * rho ^ k`.
* `excess_le_geometric` — the Campanato form `E k ≤ ( + F/(rho-theta)) rho^k`.
* `excess_le_geometric_triadic_half` — the same at `rho = 3^{-1/2}`, spelled in
  the frozen gauge `Real.rpow 3 (-(k/2))`.
* `excess_le_of_recursion_of_le` — the degenerate-rate variant `theta ≤ rho`
  with a strict inequality only at the reabsorption step.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`),
  Proposition `p.Schauder.C1alpha`, the display `e.Sch1a.1` and the dyadic geometric
  series preceding `e.Sch1a.2`.
* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory
open Homogenization
open Algsuperdiff.Section4.Support

/-! ## 1. The one-step recursion, iterated -/

/-- **The Campanato induction.**

If a nonnegative sequence contracts at rate `theta` with a forcing remainder
decaying at the strictly larger rate `rho`, then it is dominated by the sum of
the two geometric profiles, with the forcing amplified by the *gap* `rho - theta`
only.  This is the reabsorption at the heart of `e.Sch1a.1`. -/
theorem excess_le_of_recursion {E : ℕ → ℝ} {theta rho F : ℝ}
    (htheta : 0 ≤ theta) (hgap : theta < rho) (hF : 0 ≤ F)
    (hstep : ∀ k, E (k + 1) ≤ theta * E k + F * rho ^ k) (k : ℕ) :
    E k ≤ theta ^ k * E 0 + F / (rho - theta) * rho ^ k := by
  have hgap0 : 0 < rho - theta := by linarith only [hgap]
  have hc0 : 0 ≤ F / (rho - theta) := div_nonneg hF hgap0.le
  have hrho0 : 0 ≤ rho := le_trans htheta hgap.le
  induction k with
  | zero =>
      simp only [pow_zero, one_mul, mul_one]
      linarith only [hc0]
  | succ n ih =>
      have hmul : theta * E n ≤ theta * (theta ^ n * E 0 + F / (rho - theta) * rho ^ n) :=
        mul_le_mul_of_nonneg_left ih htheta
      have habsorb : theta * (F / (rho - theta)) + F ≤ F / (rho - theta) * rho := by
        have hid : F / (rho - theta) * (rho - theta) = F := by
          field_simp
        have hexp : F / (rho - theta) * rho - theta * (F / (rho - theta))
            = F / (rho - theta) * (rho - theta) := by ring
        linarith only [hid, hexp]
      have hpow : (0 : ℝ) ≤ rho ^ n := pow_nonneg hrho0 n
      have hrem : theta * (F / (rho - theta) * rho ^ n) + F * rho ^ n
          ≤ F / (rho - theta) * rho ^ (n + 1) := by
        have hfac : theta * (F / (rho - theta) * rho ^ n) + F * rho ^ n
            = (theta * (F / (rho - theta)) + F) * rho ^ n := by ring
        have hgoal : F / (rho - theta) * rho ^ (n + 1)
            = (F / (rho - theta) * rho) * rho ^ n := by ring
        rw [hfac, hgoal]
        exact mul_le_mul_of_nonneg_right habsorb hpow
      have hlead : theta * (theta ^ n * E 0) = theta ^ (n + 1) * E 0 := by ring
      have hstepn := hstep n
      linarith only [hstepn, hmul, hrem, hlead]

/-- **The Campanato bound.**  The iterated recursion decays at the forcing rate
`rho`, with amplitude `E 0 + F / (rho - theta)`. -/
theorem excess_le_geometric {E : ℕ → ℝ} {theta rho F : ℝ}
    (htheta : 0 ≤ theta) (hgap : theta < rho) (hF : 0 ≤ F) (hE0 : 0 ≤ E 0)
    (hstep : ∀ k, E (k + 1) ≤ theta * E k + F * rho ^ k) (k : ℕ) :
    E k ≤ (E 0 + F / (rho - theta)) * rho ^ k := by
  have hgap0 : 0 < rho - theta := by linarith only [hgap]
  have hc0 : 0 ≤ F / (rho - theta) := div_nonneg hF hgap0.le
  have hmain := excess_le_of_recursion htheta hgap hF hstep k
  have hpowle : theta ^ k ≤ rho ^ k :=
    pow_le_pow_left₀ htheta hgap.le k
  have hlead : theta ^ k * E 0 ≤ rho ^ k * E 0 :=
    mul_le_mul_of_nonneg_right hpowle hE0
  have hexp : (E 0 + F / (rho - theta)) * rho ^ k
      = rho ^ k * E 0 + F / (rho - theta) * rho ^ k := by ring
  rw [hexp]
  linarith only [hmain, hlead]

/-- The degenerate-rate variant: when the contraction rate only *matches* the
forcing rate the iteration still closes, at the cost of a linear-in-`k` factor
absorbed by any strictly larger rate.  Stated as the explicit two-profile bound
at a chosen intermediate rate `rho'`. -/
theorem excess_le_of_recursion_of_le {E : ℕ → ℝ} {theta rho rho' F : ℝ}
    (htheta : 0 ≤ theta) (hgap : theta < rho') (hrho : rho ≤ rho') (hF : 0 ≤ F)
    (hrho0 : 0 ≤ rho)
    (hstep : ∀ k, E (k + 1) ≤ theta * E k + F * rho ^ k) (k : ℕ) :
    E k ≤ theta ^ k * E 0 + F / (rho' - theta) * rho' ^ k := by
  refine excess_le_of_recursion htheta hgap hF (fun j => ?_) k
  have hpow : rho ^ j ≤ rho' ^ j := pow_le_pow_left₀ hrho0 hrho j
  have hmul : F * rho ^ j ≤ F * rho' ^ j := mul_le_mul_of_nonneg_left hpow hF
  linarith only [hstep j, hmul]

/-! ## 2. The triadic gauge -/

/-- `3^{-k/2}` as a power of the ratio `3^{-1/2}`: the dictionary between the
recursion's `rho ^ k` and the frozen statement's `Real.rpow` gauge. -/
theorem rpow_three_neg_half_pow (k : ℕ) :
    (Real.rpow 3 (-(1 / 2 : ℝ))) ^ k = Real.rpow 3 (-((k : ℝ) / 2)) := by
  show ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ k = (3 : ℝ) ^ (-((k : ℝ) / 2))
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2 : ℝ))) k,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- The freezing rate is strictly inside the unit interval. -/
theorem rpow_three_neg_half_lt_one : Real.rpow 3 (-(1 / 2 : ℝ)) < 1 := by
  show (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem rpow_three_neg_half_pos : (0 : ℝ) < Real.rpow 3 (-(1 / 2 : ℝ)) :=
  rpow_three_pos _

/-- **The Campanato bound at the development's exponent.**

At the freezing rate `rho = 3^{-1/2}` — the gain of a `C^{0,1/2}` forcing over
a triadic scale — the iterated excess obeys the `3^{-k/2}` law of the frozen
conclusion `[∇w]_{C^{0,1/2}} ≤ · KG`. -/
theorem excess_le_geometric_triadic_half {E : ℕ → ℝ} {theta F : ℝ}
    (htheta : 0 ≤ theta) (hgap : theta < Real.rpow 3 (-(1 / 2 : ℝ))) (hF : 0 ≤ F)
    (hE0 : 0 ≤ E 0)
    (hstep : ∀ k, E (k + 1) ≤ theta * E k + F * Real.rpow 3 (-((k : ℝ) / 2)))
    (k : ℕ) :
    E k ≤ (E 0 + F / (Real.rpow 3 (-(1 / 2 : ℝ)) - theta)) *
      Real.rpow 3 (-((k : ℝ) / 2)) := by
  have hstep' : ∀ j : ℕ,
      E (j + 1) ≤ theta * E j + F * (Real.rpow 3 (-(1 / 2 : ℝ))) ^ j := by
    intro j
    rw [rpow_three_neg_half_pow j]
    exact hstep j
  have h := excess_le_geometric htheta hgap hF hE0 hstep' k
  rwa [rpow_three_neg_half_pow k] at h

/-! ## 3. The sup-over-scales form -/

/-- The Campanato bound read as a uniform statement over all triadic scales: the
normalized excess `rho^{-k} E k` is bounded by one constant.  This is the shape
consumed by the Campanato characterization of `C^{0,alpha}`. -/
theorem sup_scaled_excess_le {E : ℕ → ℝ} {theta rho F : ℝ}
    (htheta : 0 ≤ theta) (hgap : theta < rho) (hF : 0 ≤ F)
    (hE0 : 0 ≤ E 0)
    (hstep : ∀ k, E (k + 1) ≤ theta * E k + F * rho ^ k) (k : ℕ) :
    (rho ^ k)⁻¹ * E k ≤ E 0 + F / (rho - theta) := by
  have hrhopos : 0 < rho := lt_of_le_of_lt htheta hgap
  have hpk : (0 : ℝ) < rho ^ k := pow_pos hrhopos k
  have h := excess_le_geometric htheta hgap hF hE0 hstep k
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.2 hpk))
  have hid : (rho ^ k)⁻¹ * ((E 0 + F / (rho - theta)) * rho ^ k)
      = E 0 + F / (rho - theta) := by
    field_simp
  rwa [hid] at hmul

end Algsuperdiff.Section4.Provider.Schauder
