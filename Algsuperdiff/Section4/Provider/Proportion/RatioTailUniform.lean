/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Proportion.RatioTailClosed

/-!
# The `𝒢₀` proportion tail with a level-uniform constant

ABK26, §4.1, `e.no.bad.scales.applied.for.lambdas` for the `𝒢₀` lane, in the
quantifier order the downstream assembly consumes.

`RatioTailClosed.exists_ratioTail_eventG0` delivers the constant `C` **after**
the level `θ`, because two of its numerical floors carry a `θ^{-1}`:
`7776 R_θ C_cg³` with `R_θ = max(4, 64 r L/θ)` and `7741440 G_θ C_cg⁷` with
`G_θ = G₀(d)/θ`.  The downstream union bound needs one `C(d)` fixed **before**
`θ`.

This module moves the `θ`-dependence out of the constant and into an explicit
coupling hypothesis between the model's `γ` and the level `θ`,

```
C⁹ γ² ≤ θ c⋆⁸ ,
```

by opening the exponential two Taylor orders further than the proved proof
does: the rate branch uses `u⁴/31104 ≤ exp(u/6)` (order 4 instead of order 3)
and the threshold branch uses `exp(−w) ≤ 8!/w⁸` (order 8 instead of order 7).
The extra power of `u = c⋆²/(C_cg C² γ)` is exactly one extra power of
`γ^{-1}`, which is what the coupling pays for.

## Main results

* `exists_ratioTail_eventG0_uniform` — the endpoint with `C(d)` quantified before
  `θ`, under the coupling `C⁹γ² ≤ θ c⋆⁸`.
* `exists_ratioTail_eventG0_of_uniform` — the **no-strength-lost certificate**:
  the proved statement's exact shape is re-derived from the uniform one, by
  absorbing the coupling into the constant `C' = max(C, 130 C⁹/θ)`.  So nothing
  was weakened: the uniform form implies the proved form verbatim.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.good.scales.ratio.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open Homogenization Homogenization.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

/-! ## 1. The order-8 opening of the exponential

The abstract-real helper; the only transcendental atom in this file that a
numeric step ever sees, and it is discharged before any carrier appears. -/

/-- `exp(−w) ≤ 40320/w⁸` for `w > 0` (the order-8 companion of
`exp_neg_le_seven`). -/
private theorem exp_neg_le_eight {w : ℝ} (hw : 0 < w) :
    Real.exp (-w) ≤ 40320 / w ^ (8 : ℕ) := by
  have hbase := Real.pow_div_factorial_le_exp (x := w) hw.le 8
  have hfac : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [hfac] at hbase
  have hwn : (0 : ℝ) < w ^ (8 : ℕ) := pow_pos hw 8
  rw [Real.exp_neg]
  have h := inv_anti₀ (div_pos hwn (by norm_num : (0 : ℝ) < 40320)) hbase
  rwa [inv_div] at h

/-! ## 2. The endpoint with a level-uniform constant -/

/-- Identical to `exists_ratioTail_eventG0` except that `C` no longer depends on `θ`;
the price is the explicit coupling `C⁹γ² ≤ θc⋆⁸`, which
`exists_ratioTail_eventG0_of_uniform` shows costs nothing.

The parameter chain is the manuscript's: `E = C c⋆^{−1}`, atom scale `A =
exp(−u)` with `u = c⋆²/(C_cg C² γ)`, `p = exp(u/6)`, so `p^{1/σ}A = exp(−u/2)`,
and normalizer `D = gammaMomentConst σ · p^{1/σ} · K`.  The two `θ`-carrying
floors of the proved proof are replaced by the `θ`-free floors

```
16174080 C_cg⁴ ,   1990656 r L C_cg⁴ ,   23224320 G₀(d) C_cg⁸ ,
```

with `L = log(3r) + r` and
`G₀(d) = 36(1+C_⋆)·gammaMomentConst(1/3)·gammaTriangleConst(1/3)·penaltyNormalizer d`,
all of which depend on `d` alone (`r = r(d)`). -/
theorem exists_ratioTail_eventG0_uniform (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ C : ℝ, 6 ≤ C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ theta : ℝ, 0 < theta → theta * ((r : ℝ) + 1) < 1 →
          C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ) ≤ theta * (Disorder.cstar M) ^ (8 : ℕ) →
            ∀ c1 : ℝ, 0 ≤ c1 → c1 * M.gamma ≤ 1 → ∀ n : ℕ,
              (Cutoff.cutoffSampleLaw M).toMeasure
                  {omega | theta < scaleProp
                    (fun k => (Support.eventG0 M (Support.cgEllipLowerConstant d) k)ᶜ) n omega}
                ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  classical
  have hCcg0 : (0 : ℝ) < Support.cgEllipLowerConstant d := Support.cgEllipLowerConstant_pos d
  have hCs0 : (0 : ℝ) < Cstar := Cstar_pos
  have hgmc0 : (0 : ℝ) < gammaMomentConst (1 / 3 : ℝ) := gammaMomentConst_pos (by norm_num)
  have hgtc0 : (0 : ℝ) < gammaTriangleConst (1 / 3 : ℝ) := gammaTriangleConst_pos
  have hPn0 : (0 : ℝ) < penaltyNormalizer d := penaltyNormalizer_pos d
  obtain ⟨r, hr1, hrgap⟩ := exists_dependence_range d
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (3 * (r : ℝ)) + (r : ℝ) := ⟨_, rfl⟩
  obtain ⟨G0d, hG0ddef⟩ : ∃ x : ℝ, x = 36 * (1 + Cstar) * gammaMomentConst (1 / 3 : ℝ) *
      gammaTriangleConst (1 / 3 : ℝ) * penaltyNormalizer d := ⟨_, rfl⟩
  -- the three `θ`-free floors
  obtain ⟨C, hC6, hCfl, hall⟩ := exists_cgExcess_atomTail_of_floor d
      (max (16174080 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ))
        (max (1990656 * (r : ℝ) * L * (Support.cgEllipLowerConstant d) ^ (4 : ℕ))
          (23224320 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ))))
  refine ⟨r, hr1, C, hC6, ?_⟩
  intro M hreg theta htheta0 hthetar hcouple c1 hc10 hc1g
  have hC0 : (0 : ℝ) < C := by linarith only [hC6]
  have hC1 : (1 : ℝ) ≤ C := by linarith only [hC6]
  have hCne : C ≠ 0 := ne_of_gt hC0
  have hCpow12 : C ≤ C ^ (12 : ℕ) := by
    calc C = C ^ (1 : ℕ) := (pow_one C).symm
      _ ≤ C ^ (12 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
  have hCpow3 : C ≤ C ^ (3 : ℕ) := by
    calc C = C ^ (1 : ℕ) := (pow_one C).symm
      _ ≤ C ^ (3 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
  have hflA : 16174080 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) ≤ C ^ (12 : ℕ) :=
    le_trans (le_trans (le_max_left _ _) hCfl) hCpow12
  have hflB : 1990656 * (r : ℝ) * L * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCfl
  have hflC : 23224320 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) ≤ C ^ (3 : ℕ) :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCfl) hCpow3
  have htheta1 : theta ≤ 1 := by
    have hstep : theta * 2 ≤ theta * ((r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrR]) htheta0.le
    linarith only [hstep, hthetar, htheta0]
  have hthetane : theta ≠ 0 := ne_of_gt htheta0
  obtain ⟨Rr, hRrdef⟩ : ∃ x : ℝ, x = max 4 (64 * (r : ℝ) * L / theta) := ⟨_, rfl⟩
  have hRr4 : (4 : ℝ) ≤ Rr := by rw [hRrdef]; exact le_max_left _ _
  have hRrL : 64 * (r : ℝ) * L / theta ≤ Rr := by rw [hRrdef]; exact le_max_right _ _
  obtain ⟨G, hGdef⟩ : ∃ x : ℝ, x = 36 * (1 + Cstar) * gammaMomentConst (1 / 3 : ℝ) *
      gammaTriangleConst (1 / 3 : ℝ) * penaltyNormalizer d / theta := ⟨_, rfl⟩
  have hG0 : 0 < G := by
    rw [hGdef]
    refine div_pos ?_ htheta0
    exact mul_pos (mul_pos (mul_pos (by linarith only [hCs0]) hgmc0) hgtc0) hPn0
  have hGtheta : G * theta = G0d := by
    rw [hGdef, hG0ddef]
    field_simp
  obtain ⟨E, hEval, hwin, hatom⟩ := hall M hreg
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg4 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
  have hgne : M.gamma ≠ 0 := ne_of_gt hg0
  have hcsne : Disorder.cstar M ≠ 0 := ne_of_gt hcs0
  have hCcgne : Support.cgEllipLowerConstant d ≠ 0 := ne_of_gt hCcg0
  obtain ⟨u, hudef⟩ : ∃ x : ℝ, x = (Support.cgEllipLowerConstant d)⁻¹ *
      (((E : ℝ))⁻¹) ^ (2 : ℕ) * M.gamma⁻¹ := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hudef]
    exact mul_pos (mul_pos (inv_pos.2 hCcg0) (pow_pos (inv_pos.2 hE0) 2)) (inv_pos.2 hg0)
  have hAu : cgTailScale M (E : ℝ) = Real.exp (-u) := by rw [hudef, cgTailScale]
  have hu' : u = (Disorder.cstar M) ^ (2 : ℕ) /
      (Support.cgEllipLowerConstant d * C ^ (2 : ℕ) * M.gamma) := by
    rw [hudef, hEval]
    field_simp
  -- the printed regime, in product form
  have hkey10 : C ^ (10 : ℕ) * M.gamma ≤ (Disorder.cstar M) ^ (10 : ℕ) := by
    have hC10 : (0 : ℝ) < C ^ (10 : ℕ) := pow_pos hC0 10
    have h := mul_le_mul_of_nonneg_left hreg hC10.le
    rw [inv_pow, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC10), one_mul] at h
    exact h
  have hgammale : M.gamma ≤ (Disorder.cstar M) ^ (10 : ℕ) / C ^ (10 : ℕ) := by
    rw [le_div_iff₀ (pow_pos hC0 10)]
    calc M.gamma * C ^ (10 : ℕ) = C ^ (10 : ℕ) * M.gamma := by ring
      _ ≤ (Disorder.cstar M) ^ (10 : ℕ) := hkey10
  have hgammasq : M.gamma ^ (2 : ℕ) ≤ (Disorder.cstar M) ^ (20 : ℕ) / C ^ (20 : ℕ) := by
    have hsq : (C ^ (10 : ℕ) * M.gamma) ^ (2 : ℕ) ≤ ((Disorder.cstar M) ^ (10 : ℕ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hkey10 2
    rw [le_div_iff₀ (pow_pos hC0 20)]
    calc M.gamma ^ (2 : ℕ) * C ^ (20 : ℕ) = (C ^ (10 : ℕ) * M.gamma) ^ (2 : ℕ) := by ring
      _ ≤ ((Disorder.cstar M) ^ (10 : ℕ)) ^ (2 : ℕ) := hsq
      _ = (Disorder.cstar M) ^ (20 : ℕ) := by ring
  have hcs2 : (Disorder.cstar M) ^ (2 : ℕ) ≤ 9 / 4 := by
    calc (Disorder.cstar M) ^ (2 : ℕ) ≤ (3 / 2 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hcs0.le hcs32 2
      _ = 9 / 4 := by norm_num
  have hcs12 : (Disorder.cstar M) ^ (12 : ℕ) ≤ 130 := by
    calc (Disorder.cstar M) ^ (12 : ℕ) ≤ (3 / 2 : ℝ) ^ (12 : ℕ) :=
        pow_le_pow_left₀ hcs0.le hcs32 12
      _ ≤ 130 := by norm_num
  -- 2: the rate branch, at Taylor order 4
  have hval4 : M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) = (Disorder.cstar M) ^ (8 : ℕ) /
      ((Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) * M.gamma ^ (2 : ℕ)) := by
    rw [hu']
    field_simp
  have hden4 : (0 : ℝ) < (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) *
      M.gamma ^ (2 : ℕ) := by positivity
  have hbranchA : (4 : ℝ) ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) / 31104 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 31104), hval4, le_div_iff₀ hden4]
    have hfrac : 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) *
        (Disorder.cstar M) ^ (12 : ℕ) / C ^ (12 : ℕ) ≤ 1 := by
      rw [div_le_one (pow_pos hC0 12)]
      calc 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * (Disorder.cstar M) ^ (12 : ℕ)
          ≤ 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * 130 :=
            mul_le_mul_of_nonneg_left hcs12 (by positivity)
        _ = 16174080 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) := by ring
        _ ≤ C ^ (12 : ℕ) := hflA
    calc (4 : ℝ) * 31104 * ((Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) *
            M.gamma ^ (2 : ℕ))
        = 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) *
            M.gamma ^ (2 : ℕ) := by ring
      _ ≤ 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) *
            ((Disorder.cstar M) ^ (20 : ℕ) / C ^ (20 : ℕ)) :=
          mul_le_mul_of_nonneg_left hgammasq (by positivity)
      _ = 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * (Disorder.cstar M) ^ (12 : ℕ) /
            C ^ (12 : ℕ) * (Disorder.cstar M) ^ (8 : ℕ) := by
          field_simp
      _ ≤ 1 * (Disorder.cstar M) ^ (8 : ℕ) :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = (Disorder.cstar M) ^ (8 : ℕ) := one_mul _
  have hbranchB : 64 * (r : ℝ) * L / theta ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) / 31104 := by
    rw [div_le_div_iff₀ htheta0 (by norm_num : (0 : ℝ) < 31104), hval4, div_mul_eq_mul_div,
      le_div_iff₀ hden4]
    calc 64 * (r : ℝ) * L * 31104 * ((Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) *
            M.gamma ^ (2 : ℕ))
        = (1990656 * (r : ℝ) * L * (Support.cgEllipLowerConstant d) ^ (4 : ℕ)) *
            (C ^ (8 : ℕ) * M.gamma ^ (2 : ℕ)) := by ring
      _ ≤ C * (C ^ (8 : ℕ) * M.gamma ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hflB (by positivity)
      _ = C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ) := by ring
      _ ≤ theta * (Disorder.cstar M) ^ (8 : ℕ) := hcouple
      _ = (Disorder.cstar M) ^ (8 : ℕ) * theta := by ring
  have hgu4 : 31104 * Rr ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) := by
    have hRrle : Rr ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) / 31104 := by
      rw [hRrdef]
      exact max_le hbranchA hbranchB
    calc 31104 * Rr ≤ 31104 * (M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) / 31104) := by
          linarith only [hRrle]
      _ = M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) := by ring
  -- 3: the threshold branch, at Taylor order 8
  have hval8 : M.gamma ^ (5 : ℕ) * u ^ (8 : ℕ) = (Disorder.cstar M) ^ (16 : ℕ) /
      ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) * M.gamma ^ (3 : ℕ)) := by
    rw [hu']
    field_simp
  have hden8 : (0 : ℝ) < (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
      M.gamma ^ (3 : ℕ) := by positivity
  have hinner : 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (7 : ℕ) *
      M.gamma ≤ (Disorder.cstar M) ^ (8 : ℕ) := by
    have hG0d0 : 0 < G0d := by
      rw [hG0ddef]
      exact mul_pos (mul_pos (mul_pos (by linarith only [hCs0]) hgmc0) hgtc0) hPn0
    have hfrac : 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) *
        (Disorder.cstar M) ^ (2 : ℕ) / C ^ (3 : ℕ) ≤ 1 := by
      rw [div_le_one (pow_pos hC0 3)]
      calc 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) *
            (Disorder.cstar M) ^ (2 : ℕ)
          ≤ 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * (9 / 4) :=
            mul_le_mul_of_nonneg_left hcs2 (by positivity)
        _ = 23224320 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) := by ring
        _ ≤ C ^ (3 : ℕ) := hflC
    calc 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (7 : ℕ) * M.gamma
        = (10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (7 : ℕ)) *
            M.gamma := by ring
      _ ≤ (10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (7 : ℕ)) *
            ((Disorder.cstar M) ^ (10 : ℕ) / C ^ (10 : ℕ)) :=
          mul_le_mul_of_nonneg_left hgammale (by positivity)
      _ = 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) *
            (Disorder.cstar M) ^ (2 : ℕ) / C ^ (3 : ℕ) * (Disorder.cstar M) ^ (8 : ℕ) := by
          field_simp
      _ ≤ 1 * (Disorder.cstar M) ^ (8 : ℕ) :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = (Disorder.cstar M) ^ (8 : ℕ) := one_mul _
  have hcore8 : 10321920 * G0d * ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
      M.gamma ^ (3 : ℕ)) ≤ theta * (Disorder.cstar M) ^ (16 : ℕ) := by
    calc 10321920 * G0d * ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
            M.gamma ^ (3 : ℕ))
        = (10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (7 : ℕ) * M.gamma) *
            (C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ)) := by ring
      _ ≤ (Disorder.cstar M) ^ (8 : ℕ) * (C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hinner (by positivity)
      _ ≤ (Disorder.cstar M) ^ (8 : ℕ) * (theta * (Disorder.cstar M) ^ (8 : ℕ)) :=
          mul_le_mul_of_nonneg_left hcouple (by positivity)
      _ = theta * (Disorder.cstar M) ^ (16 : ℕ) := by ring
  have hgu8 : 10321920 * G ≤ M.gamma ^ (5 : ℕ) * u ^ (8 : ℕ) := by
    rw [hval8, le_div_iff₀ hden8]
    refine le_of_mul_le_mul_right ?_ htheta0
    calc 10321920 * G * ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
            M.gamma ^ (3 : ℕ)) * theta
        = 10321920 * (G * theta) * ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
            M.gamma ^ (3 : ℕ)) := by ring
      _ = 10321920 * G0d * ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
            M.gamma ^ (3 : ℕ)) := by rw [hGtheta]
      _ ≤ theta * (Disorder.cstar M) ^ (16 : ℕ) := hcore8
      _ = (Disorder.cstar M) ^ (16 : ℕ) * theta := by ring
  -- from here the proved proof, verbatim
  have hA0 : 0 < cgTailScale M (E : ℝ) := cgTailScale_pos M (E : ℝ)
  have hsprime0 : (0 : ℝ) < M.gamma / 4 := by linarith only [hg0]
  have hsprime1 : M.gamma / 4 ≤ 1 := by linarith only [hg4]
  have hdom : ∀ j : ℕ, annulusPenalty d (1 / 3 : ℝ) (j + 2) * cgTailScale M (E : ℝ)
      ≤ cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2) := by
    intro j
    rw [annulusPenalty_third]
    exact le_of_eq (mul_comm _ _)
  have hapos : ∀ j : ℕ, 0 < cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2) :=
    fun j => mul_pos hA0 (annulusPenaltyThird_pos d _)
  have hsum : Summable fun j : ℕ => weightThird (M.gamma / 4) j *
      (cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2)) :=
    summable_weight_mul_annulusPenaltyThird d hsprime0 hA0.le
  obtain ⟨S0, hS0def⟩ : ∃ x : ℝ, x =
      ∑' j : ℕ, weightThird (M.gamma / 4) j * annulusPenaltyThird d (j + 2) := ⟨_, rfl⟩
  obtain ⟨Ssum, hSsumdef⟩ : ∃ x : ℝ, x = ∑' j : ℕ, weightThird (M.gamma / 4) j *
      (cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2)) := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ x : ℝ, x = gammaTriangleConst (1 / 3 : ℝ) * Ssum := ⟨_, rfl⟩
  have hSsum_eq : Ssum = cgTailScale M (E : ℝ) * S0 := by
    rw [hSsumdef, hS0def, ← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have hSsum0 : 0 < Ssum := by
    rw [hSsumdef]
    refine hsum.tsum_pos (fun j => ?_) 0 ?_
    · exact mul_nonneg (weightThird_pos j).le (hapos j).le
    · exact mul_pos (weightThird_pos 0) (hapos 0)
  have hK0 : 0 < K := by
    rw [hKdef]
    exact mul_pos hgtc0 hSsum0
  have htail : ∀ m : ℤ, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma (1 / 3 : ℝ))
      (Ycal M (Support.cgEllipLowerConstant d) (M.gamma / 4) m) K := by
    intro m
    rw [hKdef, hSsumdef]
    exact isBigOWith_Ycal M (Support.cgEllipLowerConstant d) (by norm_num) hA0.le
      hatom hapos hdom hsum m
  obtain ⟨p, hpdef⟩ : ∃ x : ℝ, x = Real.exp (u / 6) := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hpdef]; exact Real.exp_pos _
  have hp1 : 1 ≤ p := by
    rw [hpdef]
    have h := Real.add_one_le_exp (u / 6)
    linarith only [h, hu0]
  have hinv3 : ((1 / 3 : ℝ))⁻¹ = 3 := by norm_num
  have hp3 : p ^ ((1 / 3 : ℝ))⁻¹ = Real.exp (u / 2) := by
    rw [hinv3, hpdef, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  obtain ⟨D, hDdef⟩ : ∃ x : ℝ, x =
      gammaMomentConst (1 / 3 : ℝ) * p ^ ((1 / 3 : ℝ))⁻¹ * K := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    rw [hDdef]
    exact mul_pos (mul_pos hgmc0 (Real.rpow_pos_of_pos hp0 _)) hK0
  have hnorm : gammaMomentConst (1 / 3 : ℝ) * p ^ ((1 / 3 : ℝ))⁻¹ * K ≤ D := le_of_eq hDdef.symm
  have hexpprod : Real.exp (u / 2) * Real.exp (-u) = Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hDval : D = gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3 : ℝ) * S0 *
      Real.exp (-(u / 2)) := by
    rw [hDdef, hp3, hKdef, hSsum_eq, hAu, ← hexpprod]
    ring
  have hplow4 : u ^ (4 : ℕ) / 31104 ≤ p := by
    have h := Real.pow_div_factorial_le_exp (x := u / 6) (by linarith only [hu0]) 4
    have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf] at h
    rw [hpdef]
    calc u ^ (4 : ℕ) / 31104 = (u / 6) ^ (4 : ℕ) / 24 := by ring
      _ ≤ Real.exp (u / 6) := h
  have hg2p : Rr ≤ M.gamma ^ (2 : ℕ) * p := by
    calc Rr = 31104 * Rr / 31104 := by ring
      _ ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) / 31104 := by
          exact div_le_div_of_nonneg_right hgu4 (by norm_num)
      _ = M.gamma ^ (2 : ℕ) * (u ^ (4 : ℕ) / 31104) := by ring
      _ ≤ M.gamma ^ (2 : ℕ) * p := mul_le_mul_of_nonneg_left hplow4 (by positivity)
  have hgp : (4 : ℝ) ≤ M.gamma * p := by
    have hstep : 4 * M.gamma ≤ M.gamma ^ (2 : ℕ) * p := by
      have h1 : 4 * M.gamma ≤ 4 := by linarith only [hg4]
      linarith only [h1, hRr4, hg2p]
    have hstep2 := mul_le_mul_of_nonneg_right hstep (inv_nonneg.2 hg0.le)
    calc (4 : ℝ) = 4 * M.gamma * M.gamma⁻¹ := by field_simp
      _ ≤ M.gamma ^ (2 : ℕ) * p * M.gamma⁻¹ := hstep2
      _ = M.gamma * p := by field_simp
  have hsp : 1 ≤ M.gamma / 4 * p := by linarith only [hgp]
  have hrate : Real.log ((3 : ℝ) * (r : ℝ)) + c1 * (r : ℝ)
      ≤ M.gamma / 4 * p * theta / (16 * (r : ℝ)) := by
    have hlog3r : (0 : ℝ) ≤ Real.log (3 * (r : ℝ)) :=
      Real.log_nonneg (by linarith only [hrR])
    have hrnn : (0 : ℝ) ≤ (r : ℝ) := by linarith only [hrR]
    have hstepA : (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * M.gamma ≤ L := by
      rw [hLdef]
      have h1 : Real.log (3 * (r : ℝ)) * M.gamma ≤ Real.log (3 * (r : ℝ)) :=
        mul_le_of_le_one_right hlog3r (by linarith only [hg4, hg0])
      have h2 : c1 * M.gamma * (r : ℝ) ≤ 1 * (r : ℝ) :=
        mul_le_mul_of_nonneg_right hc1g hrnn
      linarith only [h1, h2]
    have h64 : 64 * (r : ℝ) * L ≤ M.gamma ^ (2 : ℕ) * p * theta := by
      calc 64 * (r : ℝ) * L = 64 * (r : ℝ) * L / theta * theta := by field_simp
        _ ≤ Rr * theta := mul_le_mul_of_nonneg_right hRrL htheta0.le
        _ ≤ M.gamma ^ (2 : ℕ) * p * theta := mul_le_mul_of_nonneg_right hg2p htheta0.le
    have hA : (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) * M.gamma
        ≤ M.gamma * p * theta * M.gamma := by
      calc (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) * M.gamma
          = (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * M.gamma * (64 * (r : ℝ)) := by ring
        _ ≤ L * (64 * (r : ℝ)) :=
            mul_le_mul_of_nonneg_right hstepA (by linarith only [hrnn])
        _ = 64 * (r : ℝ) * L := by ring
        _ ≤ M.gamma ^ (2 : ℕ) * p * theta := h64
        _ = M.gamma * p * theta * M.gamma := by ring
    have hB : (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ))
        ≤ M.gamma * p * theta := by
      calc (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ))
          = (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) * M.gamma * M.gamma⁻¹ := by
            field_simp
        _ ≤ M.gamma * p * theta * M.gamma * M.gamma⁻¹ :=
            mul_le_mul_of_nonneg_right hA (inv_nonneg.2 hg0.le)
        _ = M.gamma * p * theta := by field_simp
    rw [le_div_iff₀ (by linarith only [hrR] : (0 : ℝ) < 16 * (r : ℝ)),
      show M.gamma / 4 * p * theta = M.gamma * p * theta / 4 by ring,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    calc (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (16 * (r : ℝ)) * 4
        = (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) := by ring
      _ ≤ M.gamma * p * theta := hB
  have hS0le : S0 ≤ penaltyNormalizer d / M.gamma ^ (4 : ℕ) := by
    rw [hS0def]
    exact tsum_weightThird_mul_annulusPenaltyThird_le d hg0 hg4
  have hu20 : (0 : ℝ) < u / 2 := by linarith only [hu0]
  have hE8 : Real.exp (-(u / 2)) ≤ M.gamma ^ (5 : ℕ) / G := by
    refine le_trans (exp_neg_le_eight hu20) ?_
    rw [div_le_div_iff₀ (pow_pos hu20 8) hG0,
      show M.gamma ^ (5 : ℕ) * (u / 2) ^ (8 : ℕ) = M.gamma ^ (5 : ℕ) * u ^ (8 : ℕ) / 256 by ring,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 256)]
    linarith only [hgu8]
  have hkey : 9 * D * (1 + Cstar) ≤ M.gamma / 4 * theta := by
    have hprod : S0 * Real.exp (-(u / 2))
        ≤ penaltyNormalizer d / M.gamma ^ (4 : ℕ) * (M.gamma ^ (5 : ℕ) / G) :=
      mul_le_mul hS0le hE8 (Real.exp_pos _).le (div_pos hPn0 (pow_pos hg0 4)).le
    have hc1' : (0 : ℝ) ≤ gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3 : ℝ) :=
      (mul_pos hgmc0 hgtc0).le
    have hc2 : (0 : ℝ) ≤ 1 + Cstar := by linarith only [hCs0]
    have hstep3 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hc1')
        (by norm_num : (0 : ℝ) ≤ 9)) hc2
    have hne1 : (1 + Cstar) ≠ 0 := by
      have : (0 : ℝ) < 1 + Cstar := by linarith only [hCs0]
      exact ne_of_gt this
    have hne2 : gammaMomentConst (1 / 3 : ℝ) ≠ 0 := ne_of_gt hgmc0
    have hne3 : gammaTriangleConst (1 / 3 : ℝ) ≠ 0 := ne_of_gt hgtc0
    have hne4 : penaltyNormalizer d ≠ 0 := ne_of_gt hPn0
    have hRHS : 9 * (gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3 : ℝ) *
        (penaltyNormalizer d / M.gamma ^ (4 : ℕ) * (M.gamma ^ (5 : ℕ) / G))) * (1 + Cstar)
        = M.gamma / 4 * theta := by
      rw [hGdef]
      field_simp
      ring
    have hLHS : 9 * D * (1 + Cstar) = 9 * (gammaMomentConst (1 / 3 : ℝ) *
        gammaTriangleConst (1 / 3 : ℝ) * (S0 * Real.exp (-(u / 2)))) * (1 + Cstar) := by
      rw [hDval]
      ring
    rw [hLHS, ← hRHS]
    exact hstep3
  have hthr : 9 * (M.gamma / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) ≤ D⁻¹ :=
    threshold_le_inv hsprime0 htheta0 htheta1 hp1 hD0 hkey
  have hnull : (Cutoff.cutoffSampleLaw M).toMeasure
      (goodRowSet M (Support.cgEllipLowerConstant d) (M.gamma / 4))ᶜ = 0 :=
    measure_compl_goodRowSet M (Support.cgEllipLowerConstant d) (by norm_num) hA0.le hK0
      hsprime0 (by linarith only [hg4]) hatom hapos hdom hsum htail
  have hmain := ratioTail_Ycal M (Support.cgEllipLowerConstant d) (M.gamma / 4) D
    (fun k => Support.eventG0 M (Support.cgEllipLowerConstant d) k ∪
      (goodRowSet M (Support.cgEllipLowerConstant d) (M.gamma / 4))ᶜ)
    (by norm_num : (0 : ℝ) < 1 / 3) hK0 hD0 hp1 hsprime0 hsprime1 hsp hr1
    (by norm_num : (1 : ℝ) ≤ 3) htheta0 hthetar hc10 hrate htail hnorm
    hrgap
    (fun m => measurable_Ycal_annulusRegion_local M (Support.cgEllipLowerConstant d)
      (M.gamma / 4) m)
    (hreduce_eventG0 M (Support.cgEllipLowerConstant d) hD0 hthr)
  exact fun n => le_trans (measure_scaleProp_le_of_null_enlargement _ _ _ hnull n) (hmain n)

/-! ## 3. The no-strength-lost certificate -/

/-- **The uniform endpoint recovers the proved endpoint verbatim.**

Given the level `θ`, absorb the coupling `C⁹γ² ≤ θc⋆⁸` into the constant by
passing to `C' = max(C, 130 C⁹/θ)`: the regime `γ ≤ C'^{−10}c⋆^{10}` gives both
`γ ≤ C^{−10}c⋆^{10}` and `γ² ≤ c⋆^{20}/C'^{20}`, and with `c⋆^{12} ≤ (3/2)^{12} ≤ 130`
and `C' ≤ C'^{20}` this yields `C⁹γ² ≤ 130 C⁹ c⋆⁸/C' ≤ θ c⋆⁸`.  Hence
`exists_ratioTail_eventG0_uniform` is at least as strong as
`exists_ratioTail_eventG0`: no strength was lost by moving `C` in front of `θ`. -/
theorem exists_ratioTail_eventG0_of_uniform (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      ∀ theta : ℝ, 0 < theta → theta * ((r : ℝ) + 1) < 1 →
        ∃ C : ℝ, 6 ≤ C ∧
          ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
            ∀ c1 : ℝ, 0 ≤ c1 → c1 * M.gamma ≤ 1 → ∀ n : ℕ,
              (Cutoff.cutoffSampleLaw M).toMeasure
                  {omega | theta < scaleProp
                    (fun k => (Support.eventG0 M (Support.cgEllipLowerConstant d) k)ᶜ) n omega}
                ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  classical
  obtain ⟨r, hr1, C, hC6, huniform⟩ := exists_ratioTail_eventG0_uniform d
  refine ⟨r, hr1, ?_⟩
  intro theta htheta0 hthetar
  have hC0 : (0 : ℝ) < C := by linarith only [hC6]
  have hC1 : (1 : ℝ) ≤ C := by linarith only [hC6]
  obtain ⟨C', hC'def⟩ : ∃ x : ℝ, x = max C (130 * C ^ (9 : ℕ) / theta) := ⟨_, rfl⟩
  have hCC' : C ≤ C' := by rw [hC'def]; exact le_max_left _ _
  have hC'ratio : 130 * C ^ (9 : ℕ) / theta ≤ C' := by rw [hC'def]; exact le_max_right _ _
  have hC'6 : 6 ≤ C' := le_trans hC6 hCC'
  have hC'0 : (0 : ℝ) < C' := by linarith only [hC'6]
  have hC'1 : (1 : ℝ) ≤ C' := by linarith only [hC'6]
  refine ⟨C', hC'6, ?_⟩
  intro M hreg c1 hc10 hc1g
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  -- the regime at the smaller constant
  have hregC : M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 := by
    refine le_trans hreg ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hC0 hCC') 10
  -- (b) the coupling
  have hkey10 : C' ^ (10 : ℕ) * M.gamma ≤ (Disorder.cstar M) ^ (10 : ℕ) := by
    have hC10 : (0 : ℝ) < C' ^ (10 : ℕ) := pow_pos hC'0 10
    have h := mul_le_mul_of_nonneg_left hreg hC10.le
    rw [inv_pow, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC10), one_mul] at h
    exact h
  have hgammasq : M.gamma ^ (2 : ℕ) ≤ (Disorder.cstar M) ^ (20 : ℕ) / C' ^ (20 : ℕ) := by
    have hsq : (C' ^ (10 : ℕ) * M.gamma) ^ (2 : ℕ) ≤ ((Disorder.cstar M) ^ (10 : ℕ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hkey10 2
    rw [le_div_iff₀ (pow_pos hC'0 20)]
    calc M.gamma ^ (2 : ℕ) * C' ^ (20 : ℕ) = (C' ^ (10 : ℕ) * M.gamma) ^ (2 : ℕ) := by ring
      _ ≤ ((Disorder.cstar M) ^ (10 : ℕ)) ^ (2 : ℕ) := hsq
      _ = (Disorder.cstar M) ^ (20 : ℕ) := by ring
  have hcs12 : (Disorder.cstar M) ^ (12 : ℕ) ≤ 130 := by
    calc (Disorder.cstar M) ^ (12 : ℕ) ≤ (3 / 2 : ℝ) ^ (12 : ℕ) :=
        pow_le_pow_left₀ hcs0.le hcs32 12
      _ ≤ 130 := by norm_num
  have hC'pow : C' ≤ C' ^ (20 : ℕ) := by
    calc C' = C' ^ (1 : ℕ) := (pow_one C').symm
      _ ≤ C' ^ (20 : ℕ) := pow_le_pow_right₀ hC'1 (by norm_num)
  have hfrac : C ^ (9 : ℕ) * (Disorder.cstar M) ^ (12 : ℕ) / C' ^ (20 : ℕ) ≤ theta := by
    rw [div_le_iff₀ (pow_pos hC'0 20)]
    have hstep : 130 * C ^ (9 : ℕ) ≤ theta * C' := by
      calc 130 * C ^ (9 : ℕ) ≤ C' * theta := (div_le_iff₀ htheta0).1 hC'ratio
        _ = theta * C' := mul_comm _ _
    calc C ^ (9 : ℕ) * (Disorder.cstar M) ^ (12 : ℕ)
        ≤ C ^ (9 : ℕ) * 130 := mul_le_mul_of_nonneg_left hcs12 (by positivity)
      _ = 130 * C ^ (9 : ℕ) := by ring
      _ ≤ theta * C' := hstep
      _ ≤ theta * C' ^ (20 : ℕ) := mul_le_mul_of_nonneg_left hC'pow htheta0.le
  have hcouple : C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ) ≤ theta * (Disorder.cstar M) ^ (8 : ℕ) := by
    calc C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ)
        ≤ C ^ (9 : ℕ) * ((Disorder.cstar M) ^ (20 : ℕ) / C' ^ (20 : ℕ)) :=
          mul_le_mul_of_nonneg_left hgammasq (by positivity)
      _ = C ^ (9 : ℕ) * (Disorder.cstar M) ^ (12 : ℕ) / C' ^ (20 : ℕ) *
            (Disorder.cstar M) ^ (8 : ℕ) := by
          field_simp
      _ ≤ theta * (Disorder.cstar M) ^ (8 : ℕ) :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
  exact huniform M hregC theta htheta0 hthetar hcouple c1 hc10 hc1g

end

end Algsuperdiff.Section4.Provider.Proportion
