/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Frozen.Section4.BoundsMathcalEaL
import Algsuperdiff.Section4.Provider.Homogenization.HomStepOneArith

/-!
# Theorem B, §4.5, Step 1: consuming the anchor
# the `bounds_mathcal_E_aL` lemma at the printed parameter selection

## What this module is

This is the FIRST consumption of the eighth anchor

```
Algsuperdiff.Frozen.Section4.bounds_mathcal_E_aL
```

(`Algsuperdiff/Frozen/Section4/BoundsMathcalEaL.lean`, proved), and it
is the only place in the §4.5 lane where that anchor is applied.  It is applied
exactly THREE times — once for each `𝓔`-factor of `EthmB(m)` — at the parameter
selection the §4.5 parameter choices:

| factor of `EthmB(m)` | anchor exponent `s` | anchor gap `m − n` |
|---|---|---|
| `𝓔_{s₁,∞,2}(□_m, n; ·)`   | `s/2 = homS M / 2` | `k = homK M` |
| `𝓔_{1/4,∞,2}(□_m; ·)`     | `1/4`              | `0` (`n = m`) |
| `𝓔_{s₁/2,∞,2}(□_m, n; ·)` | `s/4 = homS M / 4` | `k = homK M` |

with `s = |log γ|⁻¹`, `k = ⌈10|log γ|⌉`, `n = m − k`.

## The instantiation, verbatim

For a factor at exponent `s'` and gap `k` the anchor delivers

```
∫⁻ (sup_{L≥m} 𝓔_{s',∞,2})^q  ≤  ( ofReal ( C 3^{s'k/2} √q (s'⁻¹ + √k) √γ ) )^q.
```

The three evaluations, discharged below:

* `s' = s/2`: `3^{s'k/2} = 3^{k/(4|log γ|)} ≤ 3³`, `s'⁻¹ + √k = 2|log γ| + √k
  ≤ 4|log γ|`, so the majorant is `≤ C |log γ| √q √γ`;
* `s' = 1/4`, `k → 0`: `3⁰ = 1`, `s'⁻¹ + √0 = 4`, so the majorant is
  `≤ C √q √γ` — with NO `|log γ|`;
* `s' = s/4`: `3^{k/(8|log γ|)} ≤ 3³`, `s'⁻¹ + √k = 4|log γ| + √k ≤ 6|log γ|`,
  so the majorant is `≤ C |log γ| √q √γ`.

The absence of a `|log γ|` in the middle line is what makes the assembled
Step-1 display carry `|log γ|²` and not `|log γ|³`: the `|log γ|` of the
`s⁻¹` prefactor of `EthmB(m)` and the one of the `𝓔_{s₁}` factor are the only
two in the product.

## Binder discharge (the anchor's five gates)

* `γ ≤ (C_A⁻¹)^{10}` — from `homGamma0`'s second branch;
* `n ≤ m` — `homN_le`;
* `m ≤ n + γ⁻¹` — `homK_le_inv_gamma` (the quartic-gauge bound
  `k ≤ 40 t⁻¹ + 1 ≤ γ⁻¹`);
* `s' ∈ [C_A² √γ, 1/4]` with the CLOSED right endpoint — the lower half from
  `absLog_mul_sqrt_le` (`|log γ|√γ ≤ 4 t`) and `homGamma0`'s first branch, the
  upper half from `homS_le_quarter` (`|log γ| ≥ 4`).  NOTE: the middle factor
  sits AT the closed endpoint `s' = 1/4` — the `s = 1/4` pin is this development
  standard and the anchor's `Set.Icc … (1/4)` admits it exactly;
* `q ∈ [2d/s', C_A⁻¹ γ⁻¹ s']` — the lower endpoint is the single hypothesis
  `8 d |log γ| ≤ q` (the BINDING one is the `s' = s/4` slot, `2d·4|log γ|`),
  the upper endpoint the single hypothesis `q ≤ C⁻¹ γ⁻¹ s` with
  `C ≥ 200 C_A ≥ 4 C_A`.

The correction is visible here and nowhere else: the lower endpoint
`8 d |log γ| ≤ q` is NOT vacuous at `q = 1`, and it is exactly the reason the
assembled Step-1 display must read `√q + √|log γ|` rather than the printed
`√q`.  This module states the constraint honestly rather than absorbing it.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The produced constants -/

/-- The `γ`-threshold of the Step-1 factor bounds, as a function of the
anchor's own constant `CA`.  Branch one is the anchor's lower `s`-endpoint
(`16 C_A² t ≤ 1` in the quartic gauge), branch two its `γ`-gate. -/
def homGamma0 (CA : ℝ) : ℝ :=
  min ((16 * max CA 1 ^ (2 : ℕ))⁻¹ ^ (4 : ℕ)) ((max CA 1)⁻¹ ^ (10 : ℕ))

/-- The produced constant of the Step-1 factor bounds: `200 max(C_A, 1)`.  The
`200` is the product of the two evaluation losses `3³ = 27` and `6` of the
third slot (`162`), rounded up. -/
def homConst (CA : ℝ) : ℝ := 200 * max CA 1

theorem one_le_maxOne (CA : ℝ) : (1 : ℝ) ≤ max CA 1 := le_max_right _ _

theorem maxOne_pos (CA : ℝ) : (0 : ℝ) < max CA 1 :=
  lt_of_lt_of_le one_pos (one_le_maxOne CA)

theorem homGamma0_pos (CA : ℝ) : 0 < homGamma0 CA := by
  have hK : (0 : ℝ) < max CA 1 := maxOne_pos CA
  refine lt_min ?_ ?_
  · have h : (0 : ℝ) < (16 * max CA 1 ^ (2 : ℕ))⁻¹ := by positivity
    exact pow_pos h 4
  · exact pow_pos (inv_pos.mpr hK) 10

theorem homConst_pos (CA : ℝ) : 0 < homConst CA := by
  have hK : (0 : ℝ) < max CA 1 := maxOne_pos CA
  rw [homConst]
  linarith only [hK]

theorem one_le_homConst (CA : ℝ) : 1 ≤ homConst CA := by
  have hK : (1 : ℝ) ≤ max CA 1 := one_le_maxOne CA
  rw [homConst]
  linarith only [hK]

/-! ## 2. `3^x ≤ 27` -/

theorem rpow_three_le_twentySeven {x : ℝ} (hx : x ≤ 3) : Real.rpow (3 : ℝ) x ≤ 27 := by
  have hcast : x ≤ ((3 : ℕ) : ℝ) := by push_cast; exact hx
  have h : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ (((3 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hcast
  have he : (3 : ℝ) ^ (((3 : ℕ) : ℝ)) = 27 := by
    rw [Real.rpow_natCast]
    norm_num
  rw [he] at h
  exact h

theorem rpow_three_zero : Real.rpow (3 : ℝ) 0 = 1 := Real.rpow_zero 3

theorem rpow_three_nonneg (x : ℝ) : (0 : ℝ) ≤ Real.rpow (3 : ℝ) x :=
  Real.rpow_nonneg (by norm_num) x

/-! ## 3. The Step-1 factor moments -/

/-- **The first consumption of the `bounds_mathcal_E_aL` anchor.**

The three `𝓔`-factor moment bounds of `EthmB(m)` at the §4.5 parameter
selection, in the `lintegral` normal form.  Every hypothesis is either the
anchor's own binder, discharged here, or the two `q`-range gates displayed in
the module docstring.

The `|log γ|`-free majorant of the middle (`s = 1/4`) factor is the point of
the whole module: it is what keeps the assembled Step-1 display at
`|log γ|²`. -/
theorem exists_ethmB_factor_moments (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 1 ≤ C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ hs : 0 < homS M, ∀ m : ℤ, ∀ q : ℝ,
          8 * (d : ℝ) * |Real.log M.gamma| ≤ q →
          q ≤ C⁻¹ * M.gamma⁻¹ * homS M →
            (∫⁻ omega,
                fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
                    (homHalf ⟨homS M, hs⟩) omega ^ q
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal
                  (C * |Real.log M.gamma| * Real.sqrt q * Real.sqrt M.gamma) ^ q ∧
            (∫⁻ omega,
                fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega ^ q
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal (C * Real.sqrt q * Real.sqrt M.gamma) ^ q ∧
            (∫⁻ omega,
                fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
                    (homQuarterOf ⟨homS M, hs⟩) omega ^ q
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal
                  (C * |Real.log M.gamma| * Real.sqrt q * Real.sqrt M.gamma) ^ q := by
  obtain ⟨CA, hCApos, hanchor⟩ := Algsuperdiff.Frozen.Section4.bounds_mathcal_E_aL d cstar hcstar
  refine ⟨homGamma0 CA, homConst CA, homGamma0_pos CA, one_le_homConst CA, ?_⟩
  intro M hcs hgamma hs m q hq_lo hq_hi
  /- ### the model's own positivi -/
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hK1 : (1 : ℝ) ≤ max CA 1 := one_le_maxOne CA
  have hKpos : (0 : ℝ) < max CA 1 := maxOne_pos CA
  have hCAK : CA ≤ max CA 1 := le_max_left _ _
  /- ### the two branches of the `γ`-ga -/
  have hg_a : M.gamma ≤ (16 * max CA 1 ^ (2 : ℕ))⁻¹ ^ (4 : ℕ) :=
    le_trans hgamma (min_le_left _ _)
  have hg_b : M.gamma ≤ (max CA 1)⁻¹ ^ (10 : ℕ) := le_trans hgamma (min_le_right _ _)
  /- ### the quartic gau -/
  have hbnn : (0 : ℝ) ≤ (16 * max CA 1 ^ (2 : ℕ))⁻¹ := by positivity
  have ht : Real.sqrt (Real.sqrt M.gamma) ≤ (16 * max CA 1 ^ (2 : ℕ))⁻¹ :=
    quarticRoot_le hgpos.le hbnn hg_a
  have hKsq : (1 : ℝ) ≤ max CA 1 ^ (2 : ℕ) := one_le_pow₀ hK1
  have h16 : (16 : ℝ) ≤ 16 * max CA 1 ^ (2 : ℕ) := by linarith only [hKsq]
  have h16pos : (0 : ℝ) < 16 * max CA 1 ^ (2 : ℕ) := by linarith only [h16]
  have htsmall : Real.sqrt (Real.sqrt M.gamma) ≤ 1 / 16 := by
    refine le_trans ht ?_
    have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) h16
    rwa [one_div (16 * max CA 1 ^ (2 : ℕ))] at hinv
  have hgsmall : M.gamma ≤ 1 / 65536 := by
    have h4 := quarticRoot_pow_four (gamma := M.gamma) hgpos.le
    rw [← h4]
    calc Real.sqrt (Real.sqrt M.gamma) ^ (4 : ℕ) ≤ (1 / 16 : ℝ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) htsmall 4
      _ = 1 / 65536 := by norm_num
  have hg1 : M.gamma < 1 := by linarith only [hgsmall]
  have hL4 : 4 ≤ |Real.log M.gamma| :=
    four_le_absLog hgpos (by linarith only [hgsmall])
  have hLpos : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hL4]
  have hs4 : homS M ≤ 1 / 4 := homS_le_quarter hL4
  /- ### the anchor's `γ`-ga -/
  have hanchor_gate : M.gamma ≤ CA⁻¹ ^ (10 : ℕ) := by
    refine le_trans hg_b (pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hKpos)) ?_ 10)
    have h := one_div_le_one_div_of_le hCApos hCAK
    rwa [one_div, one_div] at h
  /- ### the mesoscale binde -/
  have hnm : homN M m ≤ m := homN_le M m
  have hgap : ((m : ℝ)) - ((homN M m : ℤ) : ℝ) = (homK M : ℝ) := homN_gap M m
  have hmn : (m : ℝ) ≤ ((homN M m : ℤ) : ℝ) + M.gamma⁻¹ := by
    have hk := homK_le_inv_gamma M hgpos hg1 htsmall
    linarith only [hgap, hk]
  /- ### the anchor's lower `s`-endpoint, at the smallest slot `s/4` -/
  have h4L : (0 : ℝ) < 4 * |Real.log M.gamma| := by linarith only [hLpos]
  have hLsq : |Real.log M.gamma| * Real.sqrt M.gamma ≤
      4 * Real.sqrt (Real.sqrt M.gamma) := absLog_mul_sqrt_le hgpos hg1
  have hCAsq : CA ^ (2 : ℕ) ≤ max CA 1 ^ (2 : ℕ) := pow_le_pow_left₀ hCApos.le hCAK 2
  have hprod : CA ^ (2 : ℕ) * Real.sqrt M.gamma * (4 * |Real.log M.gamma|) ≤ 1 := by
    have e1 : CA ^ (2 : ℕ) * Real.sqrt M.gamma * (4 * |Real.log M.gamma|) =
        4 * CA ^ (2 : ℕ) * (|Real.log M.gamma| * Real.sqrt M.gamma) := by ring
    rw [e1]
    have hnn : (0 : ℝ) ≤ 4 * CA ^ (2 : ℕ) := by positivity
    have ht0 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt M.gamma) := Real.sqrt_nonneg _
    calc 4 * CA ^ (2 : ℕ) * (|Real.log M.gamma| * Real.sqrt M.gamma)
        ≤ 4 * CA ^ (2 : ℕ) * (4 * Real.sqrt (Real.sqrt M.gamma)) :=
          mul_le_mul_of_nonneg_left hLsq hnn
      _ = 16 * CA ^ (2 : ℕ) * Real.sqrt (Real.sqrt M.gamma) := by ring
      _ ≤ 16 * max CA 1 ^ (2 : ℕ) * Real.sqrt (Real.sqrt M.gamma) := by
          have h : 16 * CA ^ (2 : ℕ) ≤ 16 * max CA 1 ^ (2 : ℕ) := by linarith only [hCAsq]
          exact mul_le_mul_of_nonneg_right h ht0
      _ ≤ 16 * max CA 1 ^ (2 : ℕ) * (16 * max CA 1 ^ (2 : ℕ))⁻¹ :=
          mul_le_mul_of_nonneg_left ht h16pos.le
      _ = 1 := by field_simp
  have hlow4 : CA ^ (2 : ℕ) * Real.sqrt M.gamma ≤ homS M / 4 := by
    have hdiv : homS M / 4 = 1 / (4 * |Real.log M.gamma|) := by
      rw [homS]; field_simp
    rw [hdiv]
    exact (le_div_iff₀ h4L).mpr hprod
  have hlow2 : CA ^ (2 : ℕ) * Real.sqrt M.gamma ≤ homS M / 2 := by
    have : homS M / 4 ≤ homS M / 2 := by linarith only [hs]
    linarith only [hlow4, this]
  have hlowQ : CA ^ (2 : ℕ) * Real.sqrt M.gamma ≤ 1 / 4 := by
    have : homS M / 4 ≤ 1 / 4 := by linarith only [hs4, hs]
    linarith only [hlow4, this]
  /- ### the `q`-range, lower endpoin -/
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hinv2 : (homS M / 2)⁻¹ = 2 * |Real.log M.gamma| := inv_homS_half M hLpos
  have hinv4 : (homS M / 4)⁻¹ = 4 * |Real.log M.gamma| := inv_homS_quarter M hLpos
  have hdL : (0 : ℝ) ≤ (d : ℝ) * |Real.log M.gamma| := mul_nonneg hd0 hLpos.le
  have hqlo2 : 2 * (d : ℝ) * (homS M / 2)⁻¹ ≤ q := by
    rw [hinv2]
    have he1 : 2 * (d : ℝ) * (2 * |Real.log M.gamma|) =
        4 * ((d : ℝ) * |Real.log M.gamma|) := by ring
    have he2 : 8 * (d : ℝ) * |Real.log M.gamma| =
        8 * ((d : ℝ) * |Real.log M.gamma|) := by ring
    linarith only [hdL, he1, he2, hq_lo]
  have hqlo4 : 2 * (d : ℝ) * (homS M / 4)⁻¹ ≤ q := by
    rw [hinv4]
    have : 2 * (d : ℝ) * (4 * |Real.log M.gamma|) = 8 * (d : ℝ) * |Real.log M.gamma| := by
      ring
    linarith only [this, hq_lo]
  have hqloQ : 2 * (d : ℝ) * ((1 : ℝ) / 4)⁻¹ ≤ q := by
    have hprod : (0 : ℝ) ≤ (d : ℝ) * (|Real.log M.gamma| - 1) :=
      mul_nonneg hd0 (by linarith only [hL4])
    have he1 : 2 * (d : ℝ) * ((1 : ℝ) / 4)⁻¹ = 8 * (d : ℝ) := by norm_num; ring
    have he2 : 8 * (d : ℝ) * |Real.log M.gamma| - 8 * (d : ℝ) =
        8 * ((d : ℝ) * (|Real.log M.gamma| - 1)) := by ring
    have hstep : 2 * (d : ℝ) * ((1 : ℝ) / 4)⁻¹ ≤ 8 * (d : ℝ) * |Real.log M.gamma| := by
      linarith only [hprod, he1, he2]
    linarith only [hstep, hq_lo]
  /- ### the `q`-range, upper endpoin -/
  have hginv : (0 : ℝ) < M.gamma⁻¹ := inv_pos.mpr hgpos
  have hCinv : (homConst CA)⁻¹ = (200 * max CA 1)⁻¹ := by rw [homConst]
  have hKle : (max CA 1)⁻¹ ≤ CA⁻¹ := by
    have := one_div_le_one_div_of_le hCApos hCAK
    rwa [one_div, one_div] at this
  have hupper : ∀ s' : ℝ, (homConst CA)⁻¹ * homS M ≤ CA⁻¹ * s' → q ≤ CA⁻¹ * M.gamma⁻¹ * s' := by
    intro s' hle
    have hstep : (homConst CA)⁻¹ * M.gamma⁻¹ * homS M ≤ CA⁻¹ * M.gamma⁻¹ * s' := by
      have e1 : (homConst CA)⁻¹ * M.gamma⁻¹ * homS M =
          M.gamma⁻¹ * ((homConst CA)⁻¹ * homS M) := by ring
      have e2 : CA⁻¹ * M.gamma⁻¹ * s' = M.gamma⁻¹ * (CA⁻¹ * s') := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hle hginv.le
    linarith only [hq_hi, hstep]
  have hCApos' : (0 : ℝ) < CA⁻¹ := inv_pos.mpr hCApos
  have hKinvpos : (0 : ℝ) < (max CA 1)⁻¹ := inv_pos.mpr hKpos
  have hconst_le : (homConst CA)⁻¹ ≤ (max CA 1)⁻¹ / 200 := by
    rw [hCinv, mul_inv]
    have : (200 : ℝ)⁻¹ * (max CA 1)⁻¹ = (max CA 1)⁻¹ / 200 := by ring
    linarith only [this]
  have hup2 : q ≤ CA⁻¹ * M.gamma⁻¹ * (homS M / 2) := by
    refine hupper _ ?_
    have h1 : (homConst CA)⁻¹ * homS M ≤ ((max CA 1)⁻¹ / 200) * homS M :=
      mul_le_mul_of_nonneg_right hconst_le hs.le
    have h2 : ((max CA 1)⁻¹ / 200) * homS M ≤ CA⁻¹ * (homS M / 2) := by
      have hb : (max CA 1)⁻¹ * (homS M / 200) ≤ CA⁻¹ * (homS M / 2) := by
        have hstep1 : (max CA 1)⁻¹ * (homS M / 200) ≤ CA⁻¹ * (homS M / 200) :=
          mul_le_mul_of_nonneg_right hKle (by linarith only [hs])
        have hstep2 : CA⁻¹ * (homS M / 200) ≤ CA⁻¹ * (homS M / 2) :=
          mul_le_mul_of_nonneg_left (by linarith only [hs]) hCApos'.le
        linarith only [hstep1, hstep2]
      have he : ((max CA 1)⁻¹ / 200) * homS M = (max CA 1)⁻¹ * (homS M / 200) := by ring
      linarith only [hb, he]
    linarith only [h1, h2]
  have hup4 : q ≤ CA⁻¹ * M.gamma⁻¹ * (homS M / 4) := by
    refine hupper _ ?_
    have h1 : (homConst CA)⁻¹ * homS M ≤ ((max CA 1)⁻¹ / 200) * homS M :=
      mul_le_mul_of_nonneg_right hconst_le hs.le
    have h2 : ((max CA 1)⁻¹ / 200) * homS M ≤ CA⁻¹ * (homS M / 4) := by
      have hstep1 : (max CA 1)⁻¹ * (homS M / 200) ≤ CA⁻¹ * (homS M / 200) :=
        mul_le_mul_of_nonneg_right hKle (by linarith only [hs])
      have hstep2 : CA⁻¹ * (homS M / 200) ≤ CA⁻¹ * (homS M / 4) :=
        mul_le_mul_of_nonneg_left (by linarith only [hs]) hCApos'.le
      have he : ((max CA 1)⁻¹ / 200) * homS M = (max CA 1)⁻¹ * (homS M / 200) := by ring
      linarith only [hstep1, hstep2, he]
    linarith only [h1, h2]
  have hupQ : q ≤ CA⁻¹ * M.gamma⁻¹ * (1 / 4) := by
    refine hupper _ ?_
    have h1 : (homConst CA)⁻¹ * homS M ≤ ((max CA 1)⁻¹ / 200) * homS M :=
      mul_le_mul_of_nonneg_right hconst_le hs.le
    have h2 : ((max CA 1)⁻¹ / 200) * homS M ≤ CA⁻¹ * (1 / 4) := by
      have hstep1 : (max CA 1)⁻¹ * (homS M / 200) ≤ CA⁻¹ * (homS M / 200) :=
        mul_le_mul_of_nonneg_right hKle (by linarith only [hs])
      have hstep2 : CA⁻¹ * (homS M / 200) ≤ CA⁻¹ * (1 / 4) :=
        mul_le_mul_of_nonneg_left (by linarith only [hs4, hs]) hCApos'.le
      have he : ((max CA 1)⁻¹ / 200) * homS M = (max CA 1)⁻¹ * (homS M / 200) := by ring
      linarith only [hstep1, hstep2, he]
    linarith only [h1, h2]
  /- ### the exponent budgets `3^{·} ≤ 27` -/
  have hkle : (homK M : ℝ) ≤ 12 * |Real.log M.gamma| := by
    have h := homK_le M
    linarith only [h, hL4]
  have hknn : (0 : ℝ) ≤ (homK M : ℝ) := Nat.cast_nonneg _
  have hexp2 : 1 / 2 * (homS M / 2) * ((m : ℝ) - ((homN M m : ℤ) : ℝ)) ≤ 3 := by
    rw [hgap, homS]
    have hval : 1 / 2 * (|Real.log M.gamma|⁻¹ / 2) * (homK M : ℝ) =
        (homK M : ℝ) / (4 * |Real.log M.gamma|) := by field_simp; ring
    rw [hval, div_le_iff₀ h4L]
    linarith only [hkle, hLpos]
  have hexp4 : 1 / 2 * (homS M / 4) * ((m : ℝ) - ((homN M m : ℤ) : ℝ)) ≤ 3 := by
    rw [hgap, homS]
    have hval : 1 / 2 * (|Real.log M.gamma|⁻¹ / 4) * (homK M : ℝ) =
        (homK M : ℝ) / (8 * |Real.log M.gamma|) := by field_simp; ring
    have h8L : (0 : ℝ) < 8 * |Real.log M.gamma| := by linarith only [hLpos]
    rw [hval, div_le_iff₀ h8L]
    linarith only [hkle, hLpos]
  /- ### the bracket budge -/
  have hsqrtk : Real.sqrt ((homK M : ℝ)) ≤ 2 * |Real.log M.gamma| := sqrt_homK_le M hL4
  have hbr2 : (homS M / 2)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ)) ≤
      4 * |Real.log M.gamma| := by
    rw [hgap, hinv2]
    linarith only [hsqrtk]
  have hbr4 : (homS M / 4)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ)) ≤
      6 * |Real.log M.gamma| := by
    rw [hgap, hinv4]
    linarith only [hsqrtk]
  /- ### the three anchor applicatio -/
  have hqnn : (0 : ℝ) ≤ q := by
    have h := hq_lo
    have hlow : (0 : ℝ) ≤ 8 * (d : ℝ) * |Real.log M.gamma| := by positivity
    linarith only [h, hlow]
  have hsqq : (0 : ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsqg : (0 : ℝ) ≤ Real.sqrt M.gamma := Real.sqrt_nonneg _
  have hCA0 : (0 : ℝ) ≤ CA := hCApos.le
  refine ⟨?_, ?_, ?_⟩
  · /- slot (i): `s' = s/2`, gap `k` -/
    have happ := hanchor M hcs hanchor_gate m (homN M m) hnm hmn (homS M / 2)
      ⟨hlow2, by linarith only [hs4, hs]⟩ (by linarith only [hs]) q ⟨hqlo2, hup2⟩
    refine le_trans happ (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hqnn)
    have hA : Real.rpow (3 : ℝ) (1 / 2 * (homS M / 2) *
        ((m : ℝ) - ((homN M m : ℤ) : ℝ))) ≤ 27 := rpow_three_le_twentySeven hexp2
    have hA0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ)
        (1 / 2 * (homS M / 2) * ((m : ℝ) - ((homN M m : ℤ) : ℝ))) := rpow_three_nonneg _
    have hC0 : (0 : ℝ) ≤ (homS M / 2)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ)) := by
      have : (0 : ℝ) ≤ (homS M / 2)⁻¹ := by rw [hinv2]; linarith only [hLpos]
      linarith only [this, Real.sqrt_nonneg ((m : ℝ) - ((homN M m : ℤ) : ℝ))]
    have hfac : CA * Real.rpow (3 : ℝ) (1 / 2 * (homS M / 2) *
          ((m : ℝ) - ((homN M m : ℤ) : ℝ))) *
        ((homS M / 2)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ))) ≤
        homConst CA * |Real.log M.gamma| := by
      have h1 : CA * Real.rpow (3 : ℝ) (1 / 2 * (homS M / 2) *
          ((m : ℝ) - ((homN M m : ℤ) : ℝ))) ≤ CA * 27 :=
        mul_le_mul_of_nonneg_left hA hCA0
      have h2 : CA * Real.rpow (3 : ℝ) (1 / 2 * (homS M / 2) *
            ((m : ℝ) - ((homN M m : ℤ) : ℝ))) *
          ((homS M / 2)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ))) ≤
          CA * 27 * (4 * |Real.log M.gamma|) :=
        mul_le_mul h1 hbr2 hC0 (by linarith only [hCA0])
      have h3 : CA * 27 * (4 * |Real.log M.gamma|) ≤ homConst CA * |Real.log M.gamma| := by
        rw [homConst]
        have hstep : 108 * CA ≤ 200 * max CA 1 := by linarith only [hCAK, hCApos]
        have := mul_le_mul_of_nonneg_right hstep hLpos.le
        linarith only [this]
      linarith only [h2, h3]
    calc CA * Real.rpow (3 : ℝ) (1 / 2 * (homS M / 2) *
            ((m : ℝ) - ((homN M m : ℤ) : ℝ))) * Real.sqrt q *
          ((homS M / 2)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ))) * Real.sqrt M.gamma
        = (CA * Real.rpow (3 : ℝ) (1 / 2 * (homS M / 2) *
              ((m : ℝ) - ((homN M m : ℤ) : ℝ))) *
            ((homS M / 2)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ)))) *
            (Real.sqrt q * Real.sqrt M.gamma) := by ring
      _ ≤ (homConst CA * |Real.log M.gamma|) * (Real.sqrt q * Real.sqrt M.gamma) :=
          mul_le_mul_of_nonneg_right hfac (mul_nonneg hsqq hsqg)
      _ = homConst CA * |Real.log M.gamma| * Real.sqrt q * Real.sqrt M.gamma := by ring
  · /- slot (ii): `s' = 1/4` (the CLOSED endpoint), gap `0` -/
    have happ := hanchor M hcs hanchor_gate m m (le_refl m) (by
        have : (0 : ℝ) < M.gamma⁻¹ := hginv
        linarith only [this]) (1 / 4)
      ⟨hlowQ, le_refl _⟩ (by norm_num) q ⟨hqloQ, hupQ⟩
    refine le_trans happ (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hqnn)
    have hzero : (m : ℝ) - (m : ℝ) = 0 := sub_self _
    rw [hzero, Real.sqrt_zero]
    have hexp0 : (1 : ℝ) / 2 * (1 / 4) * 0 = 0 := by ring
    rw [hexp0, rpow_three_zero]
    have hfac : CA * 1 * (((1 : ℝ) / 4)⁻¹ + 0) ≤ homConst CA := by
      have he : CA * 1 * (((1 : ℝ) / 4)⁻¹ + 0) = 4 * CA := by norm_num; ring
      rw [he, homConst]
      linarith only [hCAK, hCApos]
    calc CA * 1 * Real.sqrt q * (((1 : ℝ) / 4)⁻¹ + 0) * Real.sqrt M.gamma
        = (CA * 1 * (((1 : ℝ) / 4)⁻¹ + 0)) * (Real.sqrt q * Real.sqrt M.gamma) := by ring
      _ ≤ homConst CA * (Real.sqrt q * Real.sqrt M.gamma) :=
          mul_le_mul_of_nonneg_right hfac (mul_nonneg hsqq hsqg)
      _ = homConst CA * Real.sqrt q * Real.sqrt M.gamma := by ring
  · /- slot (iii): `s' = s/4`, gap `k` -/
    have happ := hanchor M hcs hanchor_gate m (homN M m) hnm hmn (homS M / 4)
      ⟨hlow4, by linarith only [hs4, hs]⟩ (by linarith only [hs]) q ⟨hqlo4, hup4⟩
    refine le_trans happ (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hqnn)
    have hA : Real.rpow (3 : ℝ) (1 / 2 * (homS M / 4) *
        ((m : ℝ) - ((homN M m : ℤ) : ℝ))) ≤ 27 := rpow_three_le_twentySeven hexp4
    have hA0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ)
        (1 / 2 * (homS M / 4) * ((m : ℝ) - ((homN M m : ℤ) : ℝ))) := rpow_three_nonneg _
    have hC0 : (0 : ℝ) ≤ (homS M / 4)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ)) := by
      have : (0 : ℝ) ≤ (homS M / 4)⁻¹ := by rw [hinv4]; linarith only [hLpos]
      linarith only [this, Real.sqrt_nonneg ((m : ℝ) - ((homN M m : ℤ) : ℝ))]
    have hfac : CA * Real.rpow (3 : ℝ) (1 / 2 * (homS M / 4) *
          ((m : ℝ) - ((homN M m : ℤ) : ℝ))) *
        ((homS M / 4)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ))) ≤
        homConst CA * |Real.log M.gamma| := by
      have h1 : CA * Real.rpow (3 : ℝ) (1 / 2 * (homS M / 4) *
          ((m : ℝ) - ((homN M m : ℤ) : ℝ))) ≤ CA * 27 :=
        mul_le_mul_of_nonneg_left hA hCA0
      have h2 : CA * Real.rpow (3 : ℝ) (1 / 2 * (homS M / 4) *
            ((m : ℝ) - ((homN M m : ℤ) : ℝ))) *
          ((homS M / 4)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ))) ≤
          CA * 27 * (6 * |Real.log M.gamma|) :=
        mul_le_mul h1 hbr4 hC0 (by linarith only [hCA0])
      have h3 : CA * 27 * (6 * |Real.log M.gamma|) ≤ homConst CA * |Real.log M.gamma| := by
        rw [homConst]
        have hstep : 162 * CA ≤ 200 * max CA 1 := by linarith only [hCAK, hCApos]
        have := mul_le_mul_of_nonneg_right hstep hLpos.le
        linarith only [this]
      linarith only [h2, h3]
    calc CA * Real.rpow (3 : ℝ) (1 / 2 * (homS M / 4) *
            ((m : ℝ) - ((homN M m : ℤ) : ℝ))) * Real.sqrt q *
          ((homS M / 4)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ))) * Real.sqrt M.gamma
        = (CA * Real.rpow (3 : ℝ) (1 / 2 * (homS M / 4) *
              ((m : ℝ) - ((homN M m : ℤ) : ℝ))) *
            ((homS M / 4)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ)))) *
            (Real.sqrt q * Real.sqrt M.gamma) := by ring
      _ ≤ (homConst CA * |Real.log M.gamma|) * (Real.sqrt q * Real.sqrt M.gamma) :=
          mul_le_mul_of_nonneg_right hfac (mul_nonneg hsqq hsqg)
      _ = homConst CA * |Real.log M.gamma| * Real.sqrt q * Real.sqrt M.gamma := by ring

end

end Algsuperdiff.Section4.Provider.Homogenization
