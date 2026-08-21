/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomStepOneMoment

/-!
# Theorem B, §4.5, Step 1: the printed display the `𝓔` estimate

## The target

The Step-1 conclusion, in the ADOPTED form of (fix 2):

```
𝔼[ EthmB(m)^p ]^{1/p}  ≤  C ( √p + √|log γ| ) √γ (log γ)²
```

for `p ∈ [1, C⁻¹ γ⁻¹ |log γ|⁻¹]`, in the `lintegral` normal form `∫⁻ EthmB^p ≤
(ofReal R)^p`.

The `√|log γ|` summand is NOT cosmetic: it is exactly the anchor's own
lower moment endpoint `q ≥ 2 d s'⁻¹`, which at the §4.5 exponents reads
`q ≥ 8 d |log γ|`.  The assembly below evaluates the anchor at
`q = max(4p, 8d|log γ|)` and `√q ≤ 2√p + √(8d)√|log γ|` is where the second
summand comes from.  The printed `√p` alone is unreachable below
`p ≈ d|log γ|`; this module states the reachable bound.

## The `Cgap`-explicit constant

The produced constant is `C₀ (1 + C_gap)`, LINEAR in the Step-3 gap constant
`C_gap` of `EthmB`'s second summand, with `C₀ = C₀(d, c⋆)` independent of it.
Keeping `C_gap` a free parameter rather than fixing it here is the honest
reading: the source's `C` in `C γ⁵` is pinned by Step 3, not by Step 1, and
(the Step-3 rescaling of the witness) then costs exactly one more factor,
absorbed by `lintegral_rpow_const_mul_le`.

## The conditional set (exactly one edge)

`hY` — the Markov/`Γ₁` moment `𝔼[(3^{(1-α)X_m(α)})^{2p}] ≤ 2^{2p}` of the
Theorem-C minimal-scale factor, transcribed as a named hypothesis at the single
exponent it is consumed at.  Theorem C is a declared dependency of the Step 1
(the moment bound).  NOTHING else is assumed.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. Elementary square-root facts -/

theorem sqrt_max_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (max a b) ≤ Real.sqrt a + Real.sqrt b := by
  have e : (Real.sqrt a + Real.sqrt b) ^ (2 : ℕ) =
      Real.sqrt a ^ (2 : ℕ) + 2 * (Real.sqrt a * Real.sqrt b) + Real.sqrt b ^ (2 : ℕ) := by
    ring
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb] at e
  have hcross : (0 : ℝ) ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
  have hmax : max a b ≤ a + b := max_le (by linarith only [hb]) (by linarith only [ha])
  have hsum : max a b ≤ (Real.sqrt a + Real.sqrt b) ^ (2 : ℕ) := by
    linarith only [e, hcross, hmax]
  calc Real.sqrt (max a b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]

theorem sqrt_le_one_of_le_one {x : ℝ} (h : x ≤ 1) : Real.sqrt x ≤ 1 := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_one] at this

/-! ## 2. The purely algebraic collapse -/

/-- **The Step-1 numeric collapse**, over abstract reals.

`W` is `√q`, `S` is `√p + √|log γ|`, `G` is `√γ`, `L` is `|log γ|`, `A` the
anchor's factor constant and `D = 2 + √(8d)` the `√max` loss.  Nothing
`γ`-dependent is hidden: every hypothesis is displayed. -/
theorem display_collapse {A D L S G W gam Cgap C0 : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hL : 4 ≤ L) (hS : 3 ≤ S) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hCgap : 0 ≤ Cgap)
    (hWDS : W ≤ D * S) (hSG : S * G ≤ 2) (hgam5 : gam ^ (5 : ℕ) ≤ G)
    (h1 : 2 * A * D * (1 + 2 * A * D) ≤ C0)
    (h2 : 1 + 4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) ≤ C0) :
    L * (2 * (A * L * W * G * (1 + A * W * G))) +
        Cgap * gam ^ (5 : ℕ) * (1 + (A * L * W * G) ^ (2 : ℕ)) ≤
      C0 * (1 + Cgap) * S * G * L ^ (2 : ℕ) := by
  have hL0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have hS0 : (0 : ℝ) ≤ S := by linarith only [hS]
  have hL2 : (16 : ℝ) ≤ L ^ (2 : ℕ) := by
    calc (16 : ℝ) = 4 ^ (2 : ℕ) := by norm_num
      _ ≤ L ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) hL 2
  have hT0 : (0 : ℝ) ≤ L ^ (2 : ℕ) * S * G := by positivity
  /- `W G ≤ D (S G) ≤ 2 D` -/
  have hWG : W * G ≤ D * (S * G) := by
    have hstep : W * G ≤ (D * S) * G := mul_le_mul_of_nonneg_right hWDS hG
    calc W * G ≤ (D * S) * G := hstep
      _ = D * (S * G) := by ring
  have hWG2D : W * G ≤ 2 * D := by
    have hstep : D * (S * G) ≤ D * 2 := mul_le_mul_of_nonneg_left hSG hD
    calc W * G ≤ D * (S * G) := hWG
      _ ≤ D * 2 := hstep
      _ = 2 * D := by ring
  have hWG0 : (0 : ℝ) ≤ W * G := mul_nonneg hW hG
  /- ### the first summa -/
  have hbr : 1 + A * (W * G) ≤ 1 + 2 * A * D := by
    have h := mul_le_mul_of_nonneg_left hWG2D hA
    linarith only [h]
  have hbr0 : (0 : ℝ) ≤ 1 + A * (W * G) := by positivity
  have hfac0 : (0 : ℝ) ≤ 2 * A * L ^ (2 : ℕ) := by positivity
  have hlhs1 : 2 * A * L ^ (2 : ℕ) * (W * G) ≤ 2 * A * L ^ (2 : ℕ) * (D * (S * G)) :=
    mul_le_mul_of_nonneg_left hWG hfac0
  have hrhs0 : (0 : ℝ) ≤ 2 * A * L ^ (2 : ℕ) * (D * (S * G)) := by positivity
  have hterm1 : L * (2 * (A * L * W * G * (1 + A * W * G))) ≤ C0 * (L ^ (2 : ℕ) * S * G) := by
    have hstep : 2 * A * L ^ (2 : ℕ) * (W * G) * (1 + A * (W * G)) ≤
        2 * A * L ^ (2 : ℕ) * (D * (S * G)) * (1 + 2 * A * D) :=
      mul_le_mul hlhs1 hbr hbr0 hrhs0
    have he1 : L * (2 * (A * L * W * G * (1 + A * W * G))) =
        2 * A * L ^ (2 : ℕ) * (W * G) * (1 + A * (W * G)) := by ring
    have he2 : 2 * A * L ^ (2 : ℕ) * (D * (S * G)) * (1 + 2 * A * D) =
        (2 * A * D * (1 + 2 * A * D)) * (L ^ (2 : ℕ) * S * G) := by ring
    have hconst : (2 * A * D * (1 + 2 * A * D)) * (L ^ (2 : ℕ) * S * G) ≤
        C0 * (L ^ (2 : ℕ) * S * G) := mul_le_mul_of_nonneg_right h1 hT0
    rw [he1]
    calc 2 * A * L ^ (2 : ℕ) * (W * G) * (1 + A * (W * G))
        ≤ 2 * A * L ^ (2 : ℕ) * (D * (S * G)) * (1 + 2 * A * D) := hstep
      _ = (2 * A * D * (1 + 2 * A * D)) * (L ^ (2 : ℕ) * S * G) := he2
      _ ≤ C0 * (L ^ (2 : ℕ) * S * G) := hconst
  /- ### the second summa -/
  have hLS1 : (1 : ℝ) ≤ L ^ (2 : ℕ) * S := by
    have hmul : (1 : ℝ) * 1 ≤ L ^ (2 : ℕ) * S :=
      mul_le_mul (by linarith only [hL2]) (by linarith only [hS]) (by norm_num)
        (by linarith only [hL2])
    linarith only [hmul]
  have hGLS : G ≤ L ^ (2 : ℕ) * S * G := by
    have h := mul_le_mul_of_nonneg_right hLS1 hG
    linarith only [h]
  have hpieceA : Cgap * gam ^ (5 : ℕ) ≤ Cgap * (L ^ (2 : ℕ) * S * G) := by
    have hstep : Cgap * gam ^ (5 : ℕ) ≤ Cgap * G := mul_le_mul_of_nonneg_left hgam5 hCgap
    have hstep2 : Cgap * G ≤ Cgap * (L ^ (2 : ℕ) * S * G) :=
      mul_le_mul_of_nonneg_left hGLS hCgap
    linarith only [hstep, hstep2]
  have hWGsq : (W * G) ^ (2 : ℕ) ≤ (2 * D) ^ (2 : ℕ) := pow_le_pow_left₀ hWG0 hWG2D 2
  have hgamsq : gam ^ (5 : ℕ) * (W * G) ^ (2 : ℕ) ≤ G * (2 * D) ^ (2 : ℕ) :=
    mul_le_mul hgam5 hWGsq (by positivity) hG
  have hpieceB : Cgap * gam ^ (5 : ℕ) * (A * L * W * G) ^ (2 : ℕ) ≤
      (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * S * G) := by
    have he : Cgap * gam ^ (5 : ℕ) * (A * L * W * G) ^ (2 : ℕ) =
        (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) * (gam ^ (5 : ℕ) * (W * G) ^ (2 : ℕ)) := by
      ring
    have hnn : (0 : ℝ) ≤ Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ)) := by positivity
    have hstep : (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) *
        (gam ^ (5 : ℕ) * (W * G) ^ (2 : ℕ)) ≤
        (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) * (G * (2 * D) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hgamsq hnn
    have he2 : (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) * (G * (2 * D) ^ (2 : ℕ)) =
        (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * G) := by ring
    have hSstep : (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * G) ≤
        (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * S * G) := by
      have hfac : (0 : ℝ) ≤ 4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap := by positivity
      have hinner : L ^ (2 : ℕ) * G ≤ L ^ (2 : ℕ) * S * G := by
        have h1S : (1 : ℝ) ≤ S := by linarith only [hS]
        have hb : L ^ (2 : ℕ) * G * 1 ≤ L ^ (2 : ℕ) * G * S :=
          mul_le_mul_of_nonneg_left h1S (by positivity)
        calc L ^ (2 : ℕ) * G = L ^ (2 : ℕ) * G * 1 := by ring
          _ ≤ L ^ (2 : ℕ) * G * S := hb
          _ = L ^ (2 : ℕ) * S * G := by ring
      exact mul_le_mul_of_nonneg_left hinner hfac
    rw [he]
    calc (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) * (gam ^ (5 : ℕ) * (W * G) ^ (2 : ℕ))
        ≤ (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) * (G * (2 * D) ^ (2 : ℕ)) := hstep
      _ = (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * G) := he2
      _ ≤ (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * S * G) := hSstep
  have hterm2 : Cgap * gam ^ (5 : ℕ) * (1 + (A * L * W * G) ^ (2 : ℕ)) ≤
      (C0 * Cgap) * (L ^ (2 : ℕ) * S * G) := by
    have he : Cgap * gam ^ (5 : ℕ) * (1 + (A * L * W * G) ^ (2 : ℕ)) =
        Cgap * gam ^ (5 : ℕ) + Cgap * gam ^ (5 : ℕ) * (A * L * W * G) ^ (2 : ℕ) := by ring
    have hsum : Cgap * (L ^ (2 : ℕ) * S * G) +
        (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * S * G) ≤
        (C0 * Cgap) * (L ^ (2 : ℕ) * S * G) := by
      have hc : Cgap + 4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap ≤ C0 * Cgap := by
        have hstep := mul_le_mul_of_nonneg_right h2 hCgap
        linarith only [hstep]
      have hstep2 := mul_le_mul_of_nonneg_right hc hT0
      linarith only [hstep2]
    rw [he]
    linarith only [hpieceA, hpieceB, hsum]
  have hfinal : C0 * (L ^ (2 : ℕ) * S * G) + (C0 * Cgap) * (L ^ (2 : ℕ) * S * G) =
      C0 * (1 + Cgap) * S * G * L ^ (2 : ℕ) := by ring
  linarith only [hterm1, hterm2, hfinal]


/-! ## 3. The Step-1 display -/

variable {d : ℕ}

/-- The `√max` loss `D = 2 + √(8d)` of the boosted anchor exponent
`q = max(4p, 8d|log γ|)`. -/
def homSqrtLoss (d : ℕ) : ℝ := 2 + Real.sqrt (8 * (d : ℝ))

theorem homSqrtLoss_nonneg (d : ℕ) : 0 ≤ homSqrtLoss d := by
  have h : (0 : ℝ) ≤ Real.sqrt (8 * (d : ℝ)) := Real.sqrt_nonneg _
  rw [homSqrtLoss]; linarith only [h]

/-- The produced Step-1 constant, as a function of the anchor's factor
constant `A` and the dimension.  The `4A` summand is the `q = 4p` boost of the
`p`-range; the other two are the two collapse budgets of `display_collapse`. -/
def homDisplayConst (A : ℝ) (d : ℕ) : ℝ :=
  4 * A + 2 * A * homSqrtLoss d * (1 + 2 * A * homSqrtLoss d) +
    (1 + 4 * A ^ (2 : ℕ) * homSqrtLoss d ^ (2 : ℕ))

theorem homDisplayConst_parts {A : ℝ} (hA : 0 ≤ A) (d : ℕ) :
    0 ≤ 4 * A ∧ 0 ≤ 2 * A * homSqrtLoss d * (1 + 2 * A * homSqrtLoss d) ∧
      0 ≤ 4 * A ^ (2 : ℕ) * homSqrtLoss d ^ (2 : ℕ) := by
  have hD : (0 : ℝ) ≤ homSqrtLoss d := homSqrtLoss_nonneg d
  exact ⟨by positivity, by positivity, by positivity⟩

theorem four_mul_le_homDisplayConst {A : ℝ} (hA : 0 ≤ A) (d : ℕ) :
    4 * A ≤ homDisplayConst A d := by
  obtain ⟨_, h2, h3⟩ := homDisplayConst_parts hA d
  rw [homDisplayConst]
  linarith only [h2, h3]

theorem collapse_budget_one {A : ℝ} (hA : 0 ≤ A) (d : ℕ) :
    2 * A * homSqrtLoss d * (1 + 2 * A * homSqrtLoss d) ≤ homDisplayConst A d := by
  obtain ⟨h1, _, h3⟩ := homDisplayConst_parts hA d
  rw [homDisplayConst]
  linarith only [h1, h3]

theorem collapse_budget_two {A : ℝ} (hA : 0 ≤ A) (d : ℕ) :
    1 + 4 * A ^ (2 : ℕ) * homSqrtLoss d ^ (2 : ℕ) ≤ homDisplayConst A d := by
  obtain ⟨h1, h2, _⟩ := homDisplayConst_parts hA d
  rw [homDisplayConst]
  linarith only [h1, h2]

theorem homDisplayConst_pos {A : ℝ} (hA : 0 < A) (d : ℕ) : 0 < homDisplayConst A d := by
  obtain ⟨h1, h2, h3⟩ := homDisplayConst_parts hA.le d
  rw [homDisplayConst]
  linarith only [h1, h2, h3, hA]

theorem one_le_homDisplayConst {A : ℝ} (hA : 0 ≤ A) (d : ℕ) : 1 ≤ homDisplayConst A d := by
  obtain ⟨h1, h2, h3⟩ := homDisplayConst_parts hA d
  rw [homDisplayConst]
  linarith only [h1, h2, h3]

/-- **STEP 1's DISPLAY the `𝓔` estimate, in the ADOPTED form.**

The `bounds_mathcal_E_aL` lemma is consumed (in
`exists_ethmB_factor_moments`) at the boosted exponent
`q = max(4p, 8d|log γ|)`, brought down to `4p`/`2p` by exponent monotonicity,
and combined with the Theorem-C minimal-scale moment `hY` by the Hölder
assembly `ethmB_moment_of_factor_moments`.  The `√|log γ|` summand is the
anchor's own lower moment endpoint, made visible rather than absorbed. -/
theorem exists_ethmB_moment_bound (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C0 : ℝ, 0 < gamma0 ∧ 1 ≤ C0 ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ hs : 0 < homS M, ∀ m : ℤ,
          ∀ Y : Cutoff.CutoffSample d → ℝ≥0∞,
            AEMeasurable Y (Cutoff.cutoffSampleLaw M).toMeasure →
            ∀ Cgap : ℝ, 0 ≤ Cgap →
              ∀ p : ℝ, 1 ≤ p → p ≤ C0⁻¹ * M.gamma⁻¹ * homS M →
                (∫⁻ omega, Y omega ^ (2 * p)
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                  ENNReal.ofReal 2 ^ (2 * p) →
                  (∫⁻ omega,
                      ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ^ p
                        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                    ENNReal.ofReal
                        (C0 * (1 + Cgap) *
                          (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                          Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) ^ p := by
  obtain ⟨g0, A, hg0pos, hA1, hfac⟩ := exists_ethmB_factor_moments d cstar hcstar
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hxpos : (0 : ℝ) < 1 + 128 * (d : ℝ) * A := by positivity
  refine ⟨min g0 (min ((1 + 128 * (d : ℝ) * A)⁻¹) (1 / 16) ^ (4 : ℕ)),
    homDisplayConst A d, lt_min hg0pos (by positivity), one_le_homDisplayConst hApos.le d, ?_⟩
  intro M hcs hgamma hs m Y hYm Cgap hCgap p hp hprange hY
  /- ### the two gate branch -/
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_g0 : M.gamma ≤ g0 := le_trans hgamma (min_le_left _ _)
  have hbmin : (0 : ℝ) < min ((1 + 128 * (d : ℝ) * A)⁻¹) (1 / 16) :=
    lt_min (inv_pos.mpr hxpos) (by norm_num)
  have hg_b : M.gamma ≤ min ((1 + 128 * (d : ℝ) * A)⁻¹) (1 / 16) ^ (4 : ℕ) :=
    le_trans hgamma (min_le_right _ _)
  have ht : Real.sqrt (Real.sqrt M.gamma) ≤ min ((1 + 128 * (d : ℝ) * A)⁻¹) (1 / 16) :=
    quarticRoot_le hgpos.le hbmin.le hg_b
  have htpos : 0 < Real.sqrt (Real.sqrt M.gamma) := quarticRoot_pos hgpos
  have ht4 : Real.sqrt (Real.sqrt M.gamma) ^ (4 : ℕ) = M.gamma :=
    quarticRoot_pow_four hgpos.le
  have ht16 : Real.sqrt (Real.sqrt M.gamma) ≤ 1 / 16 := le_trans ht (min_le_right _ _)
  have htA : Real.sqrt (Real.sqrt M.gamma) ≤ (1 + 128 * (d : ℝ) * A)⁻¹ :=
    le_trans ht (min_le_left _ _)
  /- ### the elementary `γ`-consequenc -/
  have hgsmall : M.gamma ≤ 1 / 65536 := by
    rw [← ht4]
    calc Real.sqrt (Real.sqrt M.gamma) ^ (4 : ℕ) ≤ (1 / 16 : ℝ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ htpos.le ht16 4
      _ = 1 / 65536 := by norm_num
  have hg1 : M.gamma < 1 := by linarith only [hgsmall]
  have hL4 : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos (by linarith only [hgsmall])
  have hLpos : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hL4]
  have hs4 : homS M ≤ 1 / 4 := homS_le_quarter hL4
  have hLu : |Real.log M.gamma| ≤ 4 * (Real.sqrt (Real.sqrt M.gamma))⁻¹ :=
    absLog_le_four_div_quarticRoot hgpos hg1
  /- ### the boosted anchor expone -/
  set q : ℝ := max (4 * p) (8 * (d : ℝ) * |Real.log M.gamma|) with hqdef
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hq4p : 4 * p ≤ q := le_max_left _ _
  have hqlo : 8 * (d : ℝ) * |Real.log M.gamma| ≤ q := le_max_right _ _
  /- ### the anchor's upper `q`-endpoi -/
  have hAL : (0 : ℝ) < A * |Real.log M.gamma| := mul_pos hApos hLpos
  have hgamne : M.gamma ≠ 0 := ne_of_gt hgpos
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hLne : |Real.log M.gamma| ≠ 0 := ne_of_gt hLpos
  have hup1 : 4 * p ≤ A⁻¹ * M.gamma⁻¹ * homS M := by
    have hfour : 4 * (homDisplayConst A d)⁻¹ ≤ A⁻¹ := by
      have hCpos : (0 : ℝ) < homDisplayConst A d := homDisplayConst_pos hApos d
      have h4A : 4 * A ≤ homDisplayConst A d := four_mul_le_homDisplayConst hApos.le d
      have hCne : homDisplayConst A d ≠ 0 := ne_of_gt hCpos
      have hl : (4 * (homDisplayConst A d)⁻¹) * (A * homDisplayConst A d) = 4 * A := by
        calc (4 * (homDisplayConst A d)⁻¹) * (A * homDisplayConst A d)
            = 4 * A * ((homDisplayConst A d)⁻¹ * homDisplayConst A d) := by ring
          _ = 4 * A * 1 := by rw [inv_mul_cancel₀ hCne]
          _ = 4 * A := by ring
      have hr : A⁻¹ * (A * homDisplayConst A d) = homDisplayConst A d := by
        calc A⁻¹ * (A * homDisplayConst A d) = (A⁻¹ * A) * homDisplayConst A d := by ring
          _ = 1 * homDisplayConst A d := by rw [inv_mul_cancel₀ hAne]
          _ = homDisplayConst A d := by ring
      refine le_of_mul_le_mul_right ?_ (mul_pos hApos hCpos)
      rw [hl, hr]
      exact h4A
    have hpos : (0 : ℝ) < M.gamma⁻¹ * homS M := mul_pos (inv_pos.mpr hgpos) hs
    have hstep : 4 * p ≤ 4 * ((homDisplayConst A d)⁻¹ * (M.gamma⁻¹ * homS M)) := by
      have hpr := hprange
      have he : (homDisplayConst A d)⁻¹ * M.gamma⁻¹ * homS M =
          (homDisplayConst A d)⁻¹ * (M.gamma⁻¹ * homS M) := by ring
      rw [he] at hpr
      linarith only [hpr]
    have hfin : 4 * ((homDisplayConst A d)⁻¹ * (M.gamma⁻¹ * homS M)) ≤
        A⁻¹ * (M.gamma⁻¹ * homS M) := by
      have h := mul_le_mul_of_nonneg_right hfour hpos.le
      calc 4 * ((homDisplayConst A d)⁻¹ * (M.gamma⁻¹ * homS M))
          = (4 * (homDisplayConst A d)⁻¹) * (M.gamma⁻¹ * homS M) := by ring
        _ ≤ A⁻¹ * (M.gamma⁻¹ * homS M) := h
    have he2 : A⁻¹ * (M.gamma⁻¹ * homS M) = A⁻¹ * M.gamma⁻¹ * homS M := by ring
    rw [← he2]
    linarith only [hstep, hfin]
  have heqdiv : A⁻¹ * M.gamma⁻¹ * homS M = M.gamma⁻¹ / (A * |Real.log M.gamma|) := by
    rw [homS]; field_simp
  have hup2 : 8 * (d : ℝ) * |Real.log M.gamma| ≤ A⁻¹ * M.gamma⁻¹ * homS M := by
    rw [heqdiv, le_div_iff₀ hAL]
    set u : ℝ := (Real.sqrt (Real.sqrt M.gamma))⁻¹ with hudef
    have hupos : (0 : ℝ) < u := inv_pos.mpr htpos
    have hu1 : 1 + 128 * (d : ℝ) * A ≤ u := by
      have hmul : (1 + 128 * (d : ℝ) * A) * Real.sqrt (Real.sqrt M.gamma) ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left htA hxpos.le
        rwa [mul_inv_cancel₀ (ne_of_gt hxpos)] at h
      have hdiv : (1 + 128 * (d : ℝ) * A) ≤ 1 / Real.sqrt (Real.sqrt M.gamma) :=
        (le_div_iff₀ htpos).mpr hmul
      rwa [one_div] at hdiv
    have hu4 : M.gamma⁻¹ = u ^ (4 : ℕ) := by
      rw [hudef, inv_pow, ht4]
    have hstep1 : 8 * (d : ℝ) * |Real.log M.gamma| * (A * |Real.log M.gamma|) ≤
        128 * (d : ℝ) * A * (u * u) := by
      have hLL : |Real.log M.gamma| * |Real.log M.gamma| ≤ (4 * u) * (4 * u) :=
        mul_le_mul hLu hLu hLpos.le (by positivity)
      have hfacnn : (0 : ℝ) ≤ 8 * (d : ℝ) * A := by positivity
      have hmul := mul_le_mul_of_nonneg_left hLL hfacnn
      calc 8 * (d : ℝ) * |Real.log M.gamma| * (A * |Real.log M.gamma|)
          = 8 * (d : ℝ) * A * (|Real.log M.gamma| * |Real.log M.gamma|) := by ring
        _ ≤ 8 * (d : ℝ) * A * ((4 * u) * (4 * u)) := hmul
        _ = 128 * (d : ℝ) * A * (u * u) := by ring
    have hu1' : (1 : ℝ) ≤ u := by
      have hnn : (0 : ℝ) ≤ 128 * (d : ℝ) * A := by positivity
      linarith only [hu1, hnn]
    have hsq : 128 * (d : ℝ) * A ≤ u * u := by
      have h1 : u ≤ u * u := le_mul_of_one_le_left hupos.le hu1'
      linarith only [hu1, h1]
    have hstep2 : 128 * (d : ℝ) * A * (u * u) ≤ u ^ (4 : ℕ) := by
      have hnn : (0 : ℝ) ≤ u * u := by positivity
      have h := mul_le_mul_of_nonneg_right hsq hnn
      calc 128 * (d : ℝ) * A * (u * u) ≤ (u * u) * (u * u) := h
        _ = u ^ (4 : ℕ) := by ring
    rw [hu4]
    linarith only [hstep1, hstep2]
  have hupq : q ≤ A⁻¹ * M.gamma⁻¹ * homS M := max_le hup1 hup2
  /- ### the three factor moments at `q`, then down to `4p` and `2p` -/
  obtain ⟨hf1, hf2, hf3⟩ := hfac M hcs hg_g0 hs m q hqlo hupq
  have hnm : homN M m ≤ m := homN_le M m
  have hm1 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) (homHalf ⟨homS M, hs⟩))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M hnm _).aemeasurable
  have hm2 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) homQuarter).aemeasurable
  have hm3 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) (homQuarterOf ⟨homS M, hs⟩))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M hnm _).aemeasurable
  have h4p0 : (0 : ℝ) < 4 * p := by linarith only [hp0]
  have h2p0 : (0 : ℝ) < 2 * p := by linarith only [hp0]
  have h2pq : 2 * p ≤ q := by linarith only [hq4p, hp0]
  have hd1 := lintegral_rpow_le_of_exponent_le hm1 h4p0 hq4p hf1
  have hd2 := lintegral_rpow_le_of_exponent_le hm2 h4p0 hq4p hf2
  have hd3 := lintegral_rpow_le_of_exponent_le hm3 h2p0 h2pq hf3
  /- ### the Hölder assemb -/
  have hR1 : (0 : ℝ) ≤ A * |Real.log M.gamma| * Real.sqrt q * Real.sqrt M.gamma := by
    have hA0 : (0 : ℝ) ≤ A := hApos.le
    positivity
  have hR2 : (0 : ℝ) ≤ A * Real.sqrt q * Real.sqrt M.gamma := by
    have hA0 : (0 : ℝ) ≤ A := hApos.le
    positivity
  have hassembly := ethmB_moment_of_factor_moments M hnm ⟨homS M, hs⟩ Y hYm hCgap hp
    (by norm_num : (0:ℝ) ≤ 2) hR1 hR2 hR1 hY hd1 hd2 hd3
  refine le_trans hassembly (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0.le)
  /- ### the numeric collap -/
  have hsinv : ((⟨homS M, hs⟩ : {s : ℝ // 0 < s}) : ℝ)⁻¹ = |Real.log M.gamma| := by
    show (homS M)⁻¹ = |Real.log M.gamma|
    rw [homS, inv_inv]
  rw [hsinv]
  have hsqp : (1 : ℝ) ≤ Real.sqrt p := by
    have h := Real.sqrt_le_sqrt hp
    rwa [Real.sqrt_one] at h
  have hsqL : (2 : ℝ) ≤ Real.sqrt |Real.log M.gamma| := by
    have h := Real.sqrt_le_sqrt hL4
    rwa [sqrt_four] at h
  have hS3 : (3 : ℝ) ≤ Real.sqrt p + Real.sqrt |Real.log M.gamma| := by
    linarith only [hsqp, hsqL]
  have hWDS : Real.sqrt q ≤ homSqrtLoss d *
      (Real.sqrt p + Real.sqrt |Real.log M.gamma|) := by
    have hmax := sqrt_max_le (a := 4 * p) (b := 8 * (d : ℝ) * |Real.log M.gamma|)
      (by linarith only [hp0]) (by positivity)
    have he1 : Real.sqrt (4 * p) = 2 * Real.sqrt p := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) p, sqrt_four]
    have he2 : Real.sqrt (8 * (d : ℝ) * |Real.log M.gamma|) =
        Real.sqrt (8 * (d : ℝ)) * Real.sqrt |Real.log M.gamma| :=
      Real.sqrt_mul (by positivity) _
    have hexp : homSqrtLoss d * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) =
        2 * Real.sqrt p + Real.sqrt (8 * (d : ℝ)) * Real.sqrt |Real.log M.gamma| +
          (2 * Real.sqrt |Real.log M.gamma| +
            Real.sqrt (8 * (d : ℝ)) * Real.sqrt p) := by
      rw [homSqrtLoss]; ring
    have hslack : (0 : ℝ) ≤ 2 * Real.sqrt |Real.log M.gamma| +
        Real.sqrt (8 * (d : ℝ)) * Real.sqrt p := by positivity
    rw [he1, he2] at hmax
    rw [hexp]
    linarith only [hmax, hslack]
  have hpg : p * M.gamma ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hprange hgpos.le
    have he : (homDisplayConst A d)⁻¹ * M.gamma⁻¹ * homS M * M.gamma =
        (homDisplayConst A d)⁻¹ * homS M := by field_simp
    rw [he] at h
    have hC1 : (1 : ℝ) ≤ homDisplayConst A d := one_le_homDisplayConst hApos.le d
    have hCinv : (homDisplayConst A d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
    have hbd : (homDisplayConst A d)⁻¹ * homS M ≤ 1 * (1 / 4) :=
      mul_le_mul hCinv hs4 hs.le zero_le_one
    linarith only [h, hbd]
  have hLg : |Real.log M.gamma| * M.gamma ≤ 1 := by
    have hstep : |Real.log M.gamma| * M.gamma ≤
        (4 * (Real.sqrt (Real.sqrt M.gamma))⁻¹) * M.gamma :=
      mul_le_mul_of_nonneg_right hLu hgpos.le
    have hne : Real.sqrt (Real.sqrt M.gamma) ≠ 0 := ne_of_gt htpos
    have he : (4 * (Real.sqrt (Real.sqrt M.gamma))⁻¹) * M.gamma =
        4 * Real.sqrt (Real.sqrt M.gamma) ^ (3 : ℕ) := by
      calc (4 * (Real.sqrt (Real.sqrt M.gamma))⁻¹) * M.gamma
          = (4 * (Real.sqrt (Real.sqrt M.gamma))⁻¹) *
              Real.sqrt (Real.sqrt M.gamma) ^ (4 : ℕ) := by rw [ht4]
        _ = 4 * ((Real.sqrt (Real.sqrt M.gamma))⁻¹ * Real.sqrt (Real.sqrt M.gamma)) *
              Real.sqrt (Real.sqrt M.gamma) ^ (3 : ℕ) := by ring
        _ = 4 * 1 * Real.sqrt (Real.sqrt M.gamma) ^ (3 : ℕ) := by
              rw [inv_mul_cancel₀ hne]
        _ = 4 * Real.sqrt (Real.sqrt M.gamma) ^ (3 : ℕ) := by ring
    have ht3 : Real.sqrt (Real.sqrt M.gamma) ^ (3 : ℕ) ≤ (1 / 16 : ℝ) ^ (3 : ℕ) :=
      pow_le_pow_left₀ htpos.le ht16 3
    have hnum : (1 / 16 : ℝ) ^ (3 : ℕ) = 1 / 4096 := by norm_num
    rw [hnum] at ht3
    rw [he] at hstep
    linarith only [hstep, ht3]
  have hSG : (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma ≤ 2 := by
    have e1 : Real.sqrt p * Real.sqrt M.gamma = Real.sqrt (p * M.gamma) :=
      (Real.sqrt_mul hp0.le M.gamma).symm
    have e2 : Real.sqrt |Real.log M.gamma| * Real.sqrt M.gamma =
        Real.sqrt (|Real.log M.gamma| * M.gamma) :=
      (Real.sqrt_mul (abs_nonneg _) M.gamma).symm
    have b1 : Real.sqrt (p * M.gamma) ≤ 1 := sqrt_le_one_of_le_one hpg
    have b2 : Real.sqrt (|Real.log M.gamma| * M.gamma) ≤ 1 := sqrt_le_one_of_le_one hLg
    have he : (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma =
        Real.sqrt p * Real.sqrt M.gamma +
          Real.sqrt |Real.log M.gamma| * Real.sqrt M.gamma := by ring
    rw [he, e1, e2]
    linarith only [b1, b2]
  have hgam5 : M.gamma ^ (5 : ℕ) ≤ Real.sqrt M.gamma := by
    have h5 : M.gamma ^ (5 : ℕ) ≤ M.gamma :=
      pow_le_of_le_one hgpos.le hg1.le (by norm_num)
    have hsq1 : Real.sqrt M.gamma ≤ 1 := sqrt_le_one_of_le_one hg1.le
    have hself : Real.sqrt M.gamma * Real.sqrt M.gamma = M.gamma :=
      Real.mul_self_sqrt hgpos.le
    have hle : M.gamma ≤ Real.sqrt M.gamma := by
      have hmul : Real.sqrt M.gamma * Real.sqrt M.gamma ≤ Real.sqrt M.gamma * 1 :=
        mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg _)
      rw [hself] at hmul
      linarith only [hmul]
    linarith only [h5, hle]
  have hcollapse := display_collapse (A := A) (D := homSqrtLoss d)
    (L := |Real.log M.gamma|) (S := Real.sqrt p + Real.sqrt |Real.log M.gamma|)
    (G := Real.sqrt M.gamma) (W := Real.sqrt q) (gam := M.gamma) (Cgap := Cgap)
    (C0 := homDisplayConst A d) hApos.le (homSqrtLoss_nonneg d) hL4 hS3
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hCgap hWDS hSG hgam5
    (collapse_budget_one hApos.le d) (collapse_budget_two hApos.le d)
  have habs : |Real.log M.gamma| ^ (2 : ℕ) = Real.log M.gamma ^ (2 : ℕ) := sq_abs _
  rw [← habs]
  exact hcollapse

end

end Algsuperdiff.Section4.Provider.Homogenization
