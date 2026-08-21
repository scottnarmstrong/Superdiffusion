/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomStepTwoEnergy
import Algsuperdiff.Section4.Provider.Homogenization.HomStepOneArith

/-!
# Theorem B, §4.5, Step 2b: the mesoscale energy bound

## The target (Theorem B, Step 2: the local energy extension)

```
  sup_{j ≤ n} sup_{z ∈ 3^j ℤ^d ∩ □_m} 3^{-(s-s₁)(n-j)} ν^{1/2} ‖∇u‖_{L̲²(z+□_j)}
    ≤ C 3^{(1-α) X_m(α)} ( 1 + 𝓔_{1/4} ) ( σ̄_m^{-1/2} 3^{m/2} + σ̄_m^{1/2} 3^{m/2} )
```

The node's `PROOF_SOURCE` is: Theorem C at the §4.5 `α`, then the identity `s -
s₁ = 1 - α`, then the mesoscale envelope `3^{(1-α)(m-n)} ≤ 3^5 ≤ C`.

## What is proved here

Everything in the passage EXCEPT the appeal to Theorem C itself:

1. **The mesoscale envelope, correction-honest** (`homMesoGap_le`,
   `homMesoGap_ge`, `three_rpow_homMesoGap_le`).  With the §4.5 web
   `1 - α = s/2`, `n = m - k`, `k = ⌈10|log γ|⌉`, `s = |log γ|⁻¹`,

   ```
     5  ≤  (1-α)(m-n) = (s/2) k  ≤  5 + s/2,
   ```

   so the printed chain `3^{(1-α)(m-n)} ≤ 3^5` has a FALSE middle
   inequality — — while the outer conclusion `≤ C` is fine.  The
   sharp envelope `3^{5 + s/2}` is proved, and under the gate `s ≤ 1/4` it
   collapses to the numeral `3^{41/8}` (`homMesoConst`).  The false inequality
   is NOWHERE claimed.
2. **The weight identity** `s - s₁ = 1 - α` is the
   `homS_sub_homHalf`; it is consumed, not restated.
3. **The display transfer** (`stepTwoLocal_of_regularityDisplay`,
   `stepTwoLocal_sectionFive`): from the manuscript's post-"Hence" display to the mesoscale energy bound, exactly.  The transfer is
   an identity of `3`-powers and needs NO sign hypothesis on `1 - α`.
4. **The localization of the gap** (`hence_holds_on_deep_range`): The
   manuscript's word "Hence" silently extends the Theorem-C display from `j ≤ m
   - X_m(α)` to ALL `j ≤ m`.  On the DEEP range `j ≤ m - X_m(α)` the extension
   is a triviality and is proved here; the gap is therefore EXACTLY the shallow
   range `m - X_m(α) < j ≤ m`, and nothing else.  Neither of the correction's
   two routes (scale-descendant averaging; invoking Theorem C at `n₀ = min{j, m
   - X_m(α)}`) is written in the manuscript and neither is written here.

## The single conditional edge

Theorem C is a declared dependency of this step, so its conclusion enters as a
NAMED TRANSCRIBED HYPOTHESIS `hC`, at exactly the shape the manuscript deploys
(the post-"Hence" display), and never by importing Theorem C itself.  The gap
lives inside that hypothesis and is disclosed, not discharged; item 4 above
measures precisely how much of it is free.

There is NO other conditional in this module.

## THE RESIDUE (exact statements)

Step 2a (`HomStepTwoEnergy.exists_sqrt_nu_mul_gradL2_le`) prices the global
energy by `CoarseGraining`'s Besov data quantities `B_g`, `B_h`.  Converting
those to the printed `3^{m/2}` needs the bridge
`Provider.ExcessDecay.scaleNormalizedPositiveBesovVectorSeminormTwo_le_gagliardo`
composed with the embedding
`HomBridgeDataEmbedding.three_rpow_mul_normalizedGagliardo_originCube_le_pinned`.
The bridge's two side conditions do not exist anywhere and are the exact
missing atoms:

* **(M1)** for `d ≥ 1`, `Q = □_m`, `g: Vec d → Vec d` with
  `Support.HolderSeminormBoundOn (openCubeSet Q) (1/2) K g`:
  `MeasureTheory.MemLp g 2 (normalizedCubeMeasure Q)`.
  (`normalizedCubeMeasure Q` is a probability measure; a Hölder field on a
  bounded set is bounded there once one value is finite, and Hölder ⟹
  `ContinuousOn` gives `AEStronglyMeasurable`.)
* **(M2)** under the same data with `0 < t < 1/2`:
  `Homogenization.Gagliardo.MemWsp Q t 2 g`.
  Its `eSeminorm < ⊤` half is IMMEDIATE from the
  `normalizedGagliardo_cubeSet_le_of_holderHalf` plus
  `Provider.ExcessDecay.normalizedGagliardoESeminormOn_openCubeSet` (the bound
  is an `ENNReal.ofReal`, hence `≠ ⊤`); only
  `AEStronglyMeasurable (Gagliardo.gagliardoKernel t 2 g) (Gagliardo.gagliardoCubeMeasure Q)`
  is genuinely new.

Both atoms are ALSO exactly what discharges `ForceBesovRegularity`, the
hypothesis of the coarse-graining right-hand side itself, so they are one item,
not two.

* **(M3) A CARRIER FINDING, new here.**  `CoarseGraining`'s boundary leg is stated at
  `scaleNormalizedPositiveBesovVectorNormTwo Q t (∇h)`, which is
  `√|⨍_Q ∇h|² + [∇h]_{B̄^t_{2,2}}` — it carries a MEAN term.  That term is NOT
  controlled by a Hölder SEMINORM bound on `∇h`.  The source is consistent
  here: normalizes `g` by the SEMINORM `[g]_{W̲^{1/2,∞}}` and
  `∇h` by the NORM `‖∇h‖_{W̲^{1/2,∞}}` — the bracket/bar distinction is in the
  printed line and is load-bearing.  This repository's Hölder carrier
  `Support.HolderSeminormBoundOn`, which the frozen §4.3/§4.5 anchors use for
  `h.grad`, records only the seminorm, so pricing the `∇h` leg additionally
  needs a sup datum `‖∇h‖_{L^∞(□_m)} ≤ K_h`.  This is a statement-level item,
  not a proof-level one; it is reported for the authors rather than addressed
  here.

With (M1), (M2) and (M3), nothing else stands between the Step 2 and the
printed energy-from-data display.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The mesoscale envelope `3^{(1-α)(m-n)}` -/

/-- `(1-α)(m-n) = (s/2) k`: the §4.5 web's own value of the Step-2b exponent. -/
theorem homMesoGap_eq (M : ABKModel d) (m : ℤ) :
    (1 - homAlpha M) * ((m : ℝ) - ((homN M m : ℤ) : ℝ)) = homS M / 2 * (homK M : ℝ) := by
  rw [one_sub_homAlpha, homN_gap]

/-- **The lower half of the envelope** — this is what refutes the printed chain.
`(1-α)(m-n) ≥ 5` always, with equality only if the ceiling is exact, so
`3^{(1-α)(m-n)} ≤ 3^5` is FALSE as printed. -/
theorem homMesoGap_ge {M : ABKModel d} (hlog : 0 < |Real.log M.gamma|) (m : ℤ) :
    5 ≤ (1 - homAlpha M) * ((m : ℝ) - ((homN M m : ℤ) : ℝ)) := by
  have hs : homS M = |Real.log M.gamma|⁻¹ := rfl
  have hspos : 0 < homS M := homS_pos hlog
  have hk : 10 * |Real.log M.gamma| ≤ (homK M : ℝ) := homK_ge M
  have hmul : homS M / 2 * (10 * |Real.log M.gamma|) ≤ homS M / 2 * (homK M : ℝ) :=
    mul_le_mul_of_nonneg_left hk (by linarith only [hspos])
  have hprod : homS M * |Real.log M.gamma| = 1 := by
    rw [hs]
    exact inv_mul_cancel₀ (ne_of_gt hlog)
  have hval : homS M / 2 * (10 * |Real.log M.gamma|) = 5 := by
    have : homS M / 2 * (10 * |Real.log M.gamma|) = 5 * (homS M * |Real.log M.gamma|) := by
      ring
    rw [this, hprod]
    ring
  rw [homMesoGap_eq]
  linarith only [hmul, hval]

/-- **The sharp envelope**: `(1-α)(m-n) ≤ 5 + s/2`.  The `+ s/2`
is exactly the ceiling's slack `k ≤ 10|log γ| + 1`. -/
theorem homMesoGap_le {M : ABKModel d} (hlog : 0 < |Real.log M.gamma|) (m : ℤ) :
    (1 - homAlpha M) * ((m : ℝ) - ((homN M m : ℤ) : ℝ)) ≤ 5 + homS M / 2 := by
  have hs : homS M = |Real.log M.gamma|⁻¹ := rfl
  have hspos : 0 < homS M := homS_pos hlog
  have hk : (homK M : ℝ) ≤ 10 * |Real.log M.gamma| + 1 := homK_le M
  have hmul : homS M / 2 * (homK M : ℝ) ≤ homS M / 2 * (10 * |Real.log M.gamma| + 1) :=
    mul_le_mul_of_nonneg_left hk (by linarith only [hspos])
  have hprod : homS M * |Real.log M.gamma| = 1 := by
    rw [hs]
    exact inv_mul_cancel₀ (ne_of_gt hlog)
  have hval : homS M / 2 * (10 * |Real.log M.gamma| + 1) = 5 + homS M / 2 := by
    have hexp : homS M / 2 * (10 * |Real.log M.gamma| + 1) =
        5 * (homS M * |Real.log M.gamma|) + homS M / 2 := by ring
    rw [hexp, hprod]
    ring
  rw [homMesoGap_eq]
  linarith only [hmul, hval]

/-- `C_meso = 3^{41/8}`, the numeral the §4.5 envelope collapses to under the
 gate `s ≤ 1/4`.  It replaces the printed (false) `3^5`. -/
def homMesoConst : ℝ := Real.rpow 3 (41 / 8 : ℝ)

theorem homMesoConst_pos : 0 < homMesoConst :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- **The Step-2b constant, correction-honest.**  Under the `s ≤ 1/4`,

```
  3^{(1-α)(m-n)} ≤ 3^{5 + s/2} ≤ 3^{41/8} = C_meso.
```
-/
theorem three_rpow_homMesoGap_le {M : ABKModel d} (hlog : 4 ≤ |Real.log M.gamma|) (m : ℤ) :
    Real.rpow 3 ((1 - homAlpha M) * ((m : ℝ) - ((homN M m : ℤ) : ℝ))) ≤ homMesoConst := by
  have hlog0 : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hlog]
  have hquarter : homS M ≤ 1 / 4 := homS_le_quarter hlog
  have hgap := homMesoGap_le (M := M) hlog0 m
  have hle : (1 - homAlpha M) * ((m : ℝ) - ((homN M m : ℤ) : ℝ)) ≤ 41 / 8 := by
    linarith only [hgap, hquarter]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hle

/-! ## 2. The display transfer -/

/-- **Step 2b, the transfer.**

From the manuscript's post-"Hence" display

```
  F j z ≤ K · 3^{(1-α)(m-j)}     for all j ≤ m and all admissible z,
```

the weighted local display follows at every `j ≤ n`:

```
  3^{-(1-α)(n-j)} F j z ≤ 3^{(1-α)(m-n)} · K.
```

`F j z` is the manuscript's `ν^{1/2}‖∇u‖_{L̲²(z+□_j)}`; the weight
`3^{-(s-s₁)(n-j)}` is this one by `homS_sub_homHalf`.  The proof is an exact
identity of `3`-powers and needs no sign condition on `1 - α`. -/
theorem stepTwoLocal_of_regularityDisplay {m n : ℤ} {alpha K : ℝ} {F : ℤ → Vec d → ℝ}
    (hC : ∀ j : ℤ, j ≤ m → ∀ z : Vec d,
      F j z ≤ K * Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (j : ℝ))))
    {j : ℤ} (hjn : j ≤ n) (hnm : n ≤ m) (z : Vec d) :
    Real.rpow 3 (-((1 - alpha) * ((n : ℝ) - (j : ℝ)))) * F j z ≤
      Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (n : ℝ))) * K := by
  have hjm : j ≤ m := le_trans hjn hnm
  have hw : (0 : ℝ) ≤ Real.rpow 3 (-((1 - alpha) * ((n : ℝ) - (j : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep := hC j hjm z
  have hsum : Real.rpow 3 (-((1 - alpha) * ((n : ℝ) - (j : ℝ)))) *
      Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (j : ℝ))) =
      Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (n : ℝ))) := by
    rw [show Real.rpow 3 (-((1 - alpha) * ((n : ℝ) - (j : ℝ)))) *
        Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (j : ℝ))) =
        Real.rpow 3 (-((1 - alpha) * ((n : ℝ) - (j : ℝ))) +
          (1 - alpha) * ((m : ℝ) - (j : ℝ))) from
      (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm]
    congr 1
    ring
  calc Real.rpow 3 (-((1 - alpha) * ((n : ℝ) - (j : ℝ)))) * F j z
      ≤ Real.rpow 3 (-((1 - alpha) * ((n : ℝ) - (j : ℝ)))) *
          (K * Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (j : ℝ)))) :=
        mul_le_mul_of_nonneg_left hstep hw
    _ = (Real.rpow 3 (-((1 - alpha) * ((n : ℝ) - (j : ℝ)))) *
          Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (j : ℝ)))) * K := by ring
    _ = Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (n : ℝ))) * K := by rw [hsum]

/-- **Step 2b at the §4.5 parameter web — the mesoscale energy bound.**

The printed weight is `3^{-(s-s₁)(n-j)}`; by `homS_sub_homHalf` it is
`3^{-(1-α)(n-j)}`, and the mesoscale envelope collapses to the numeral `C_meso
= 3^{41/8}` under the gate.  The result is exactly the node's
`SOURCE_CONCLUSION` with `K = C 3^{(1-α)X_m(α)} (1 + 𝓔_{1/4}) (σ̄^{-1/2}3^{m/2}
+ σ̄^{1/2}3^{m/2})`, the majorant Step 2a supplies. -/
theorem stepTwoLocal_sectionFive {M : ABKModel d} (hlog : 4 ≤ |Real.log M.gamma|) {m : ℤ}
    {K : ℝ} (hK : 0 ≤ K) {F : ℤ → Vec d → ℝ}
    (hC : ∀ j : ℤ, j ≤ m → ∀ z : Vec d,
      F j z ≤ K * Real.rpow 3 ((1 - homAlpha M) * ((m : ℝ) - (j : ℝ))))
    {j : ℤ} (hjn : j ≤ homN M m) (z : Vec d) :
    Real.rpow 3 (-((homS M - homS M / 2) * (((homN M m : ℤ) : ℝ) - (j : ℝ)))) * F j z ≤
      homMesoConst * K := by
  have hnm : homN M m ≤ m := homN_le M m
  have hweight : homS M - homS M / 2 = 1 - homAlpha M := homS_sub_homHalf M
  rw [hweight]
  refine (stepTwoLocal_of_regularityDisplay hC hjn hnm z).trans ?_
  exact mul_le_mul_of_nonneg_right (three_rpow_homMesoGap_le hlog m) hK

/-! ## 3. Localizing the gap -/

/-- **The manuscript's "Hence" is free on the deep range.**

Theorem C supplies the display only for `j ≤ m - X_m(α)` extends it to all `j ≤
m` with the single word "Hence", which is recorded as a gap in the source.  On the
DEEP range the extension is a triviality — the extra factor `3^{(1-α)X}` is `≥
1` — and that is proved here.  Consequently the gap is EXACTLY the shallow
range `m - X_m(α) < j ≤ m`, where the only available justification (a volume
comparison) costs `3^{(d/2)(m-j)}`, much larger than `3^{(1-α)X}`.  Nothing
here closes it. -/
theorem hence_holds_on_deep_range {m : ℤ} {alpha X K : ℝ} {F : ℤ → Vec d → ℝ}
    (halpha : alpha ≤ 1) (hX : 0 ≤ X) (hK : 0 ≤ K)
    (hC : ∀ j : ℤ, (j : ℝ) ≤ (m : ℝ) - X → ∀ z : Vec d,
      F j z ≤ K * Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (j : ℝ))))
    {j : ℤ} (hj : (j : ℝ) ≤ (m : ℝ) - X) (z : Vec d) :
    F j z ≤ K * Real.rpow 3 ((1 - alpha) * X) *
      Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (j : ℝ))) := by
  have hone : (1 : ℝ) ≤ Real.rpow 3 ((1 - alpha) * X) := by
    refine Real.one_le_rpow (by norm_num) ?_
    exact mul_nonneg (by linarith only [halpha]) hX
  have hbase : (0 : ℝ) ≤ Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep := hC j hj z
  have hgrow : K * Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (j : ℝ))) ≤
      K * Real.rpow 3 ((1 - alpha) * X) *
        Real.rpow 3 ((1 - alpha) * ((m : ℝ) - (j : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hbase
    calc K = K * 1 := (mul_one K).symm
      _ ≤ K * Real.rpow 3 ((1 - alpha) * X) := mul_le_mul_of_nonneg_left hone hK
  exact hstep.trans hgrow

end

end Algsuperdiff.Section4.Provider.Homogenization
