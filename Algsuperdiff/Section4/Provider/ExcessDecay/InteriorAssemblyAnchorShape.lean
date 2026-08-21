/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.InteriorAssemblyXFrame
import Algsuperdiff.Section4.Provider.ExcessDecay.SigmaBarIndex

/-!
# The anchor-shape weakening of the correction leg

The composed correction leg of `InteriorGlue` is *stronger* than the frozen
statement's second interior summand: it carries the honest `s^{-1/2}` where the
anchor prints `s^{-7}`, and the honest `σ̄_{n+2}` where the anchor prints `σ̄_n`.
This module records the weakening, so that the composed estimate can be read
**in the anchor's own printed shape**:

```text
   σ̄_{n+2}^{-1} · 3^{n} · (correction leg)
       ≤ C(d) · s^{-7} · σ̄_n^{-1} · 3^{(1+s)n} · [g]_{H̲^s(x+□_n)} ,
```

which is exactly the frozen statement's

```text
   C s^{-7} σ̄_n^{-1} 3^{(1+s)n} [g]_{H̲^s(W)}
```

with `C = 4 · interiorCorrectionConst d`.  Two steps, both priced and both
one-directional:

* the `σ̄` index move `σ̄_{n+2}^{-1} ≤ 4 σ̄_n^{-1}` — `SigmaBarIndex`, discharged
  inside the anchor's own regime, no landmark binder.

The prefactor `σ̄_{n+2}^{-1} · 3^{n}` is exactly what dividing the harmonic
display of `InteriorAssemblyXFrame` by its own left-hand weight
`σ · cubeBesovScaleWeight 1 (□_n) = σ · 3^{-n}` produces, at the comparator
choice `σ := σ̄_{n+2}` (the index of the parent's flux correction and of the
anchor's error slot).

**No `γ`-move is made anywhere**; the regime is the anchor's own
`γ ≤ C^{-1} c⋆^{10}`.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the interior clause's second
  summand).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Homogenization.Book MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The two one-directional moves -/

/-- The `s`-power move, on the anchor's own range. -/
theorem rpow_neg_half_le_rpow_neg_seven {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow s (-(1 / 2 : ℝ)) ≤ Real.rpow s (-(7 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)

/-- The scale weights combine to the printed `3^{(1+s)n}`. -/
theorem rpow_three_mul_eq_one_add (s : ℝ) (n : ℤ) :
    Real.rpow (3 : ℝ) ((n : ℝ)) * Real.rpow (3 : ℝ) (s * (n : ℝ)) =
      Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) := by
  show (3 : ℝ) ^ ((n : ℝ)) * (3 : ℝ) ^ (s * (n : ℝ)) = (3 : ℝ) ^ ((1 + s) * (n : ℝ))
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- The anchor's geometry binder, in the `translateSet` spelling the child-frame
composition is entered at. -/
theorem translateSet_openCubeSet_subset_of_anchorGeometry {n m : ℤ} {x z : Vec d}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    translateSet x (openCubeSet (originCube d n)) ⊆ openCubeSet (originCube d m) := by
  rw [← image_add_eq_translateSet x (openCubeSet (originCube d n))]
  exact fun p hp => (hgeom hp).2

/-! ## 2. The correction leg in the frozen statement's printed shape -/

/-- **The correction leg, weakened to the anchor's printed summand.**

Binder-free beyond the anchor's own regime: the `σ̄` index conversion's
induction-state binder is discharged internally.  The constant is explicit and
`d`-only. -/
theorem exists_correctionLeg_le_anchorShape (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ (n : ℤ) (x : Vec d) (g : Vec d → Vec d),
          MemLp g 2 (Support.normalizedVolumeMeasureOn
            ((fun y => x + y) '' openCubeSet (originCube d n))) →
          MemLp (Gagliardo.gagliardoKernel s 2 g) 2
            (Support.normalizedGagliardoMeasureOn
              ((fun y => x + y) '' openCubeSet (originCube d n))) →
          ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ * Real.rpow (3 : ℝ) ((n : ℝ)) *
              (2 * negNormBaseConst d * negativeToL2Factor s *
                (Real.sqrt (Fintype.card (Fin d) : ℝ) *
                  Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
                    (originCube d n) s (fun y => -g (y + x)))) ≤
            C * Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
              (Support.normalizedGagliardoESeminormOn
                ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal := by
  obtain ⟨C0, hC0, hC⟩ := exists_inv_sigmaBar_add_two_le d
  refine ⟨max C0 (4 * interiorCorrectionConst d), ?_, ?_⟩
  · exact lt_of_lt_of_le hC0 (le_max_left _ _)
  intro M hreg s hs hs1 n x g hgL2 hgW
  have hregC0 : M.gamma ≤ C0⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hreg.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hC0
      (le_max_left C0 (4 * interiorCorrectionConst d))
    rw [one_div, one_div] at h1
    exact h1
  have hsig := hC M hregC0 n
  have hA : (0 : ℝ) < (Annealed.sigmaBar M (n + 2) : ℝ) :=
    (Annealed.sigmaBar M (n + 2)).2
  have hB : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hpow : (0 : ℝ) < Real.rpow (3 : ℝ) ((n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hgag : (0 : ℝ) ≤ (Support.normalizedGagliardoESeminormOn
      ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal :=
    ENNReal.toReal_nonneg
  have hcorr := correctionLeg_le_anchorGagliardo n hs hs1 hgL2 hgW
  have hpre : (0 : ℝ) ≤ ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ *
      Real.rpow (3 : ℝ) ((n : ℝ)) :=
    mul_nonneg (inv_pos.2 hA).le hpow.le
  -- the correction leg, at the honest `s`-power
  have hstep1 := mul_le_mul_of_nonneg_left hcorr hpre
  refine hstep1.trans ?_
  -- the `s`-power move and the `σ̄` index move
  have hsE : (0 : ℝ) < Real.rpow s (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hs _
  have hsE7 : Real.rpow s (-(1 / 2 : ℝ)) ≤ Real.rpow s (-(7 : ℝ)) :=
    rpow_neg_half_le_rpow_neg_seven hs hs1
  have hCcorr : (0 : ℝ) < interiorCorrectionConst d := interiorCorrectionConst_pos d
  have hsn : (0 : ℝ) < Real.rpow (3 : ℝ) (s * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hkey : ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ * Real.rpow (3 : ℝ) ((n : ℝ)) *
      (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
        Real.rpow (3 : ℝ) (s * (n : ℝ)) *
        (Support.normalizedGagliardoESeminormOn
          ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal) ≤
      (4 * interiorCorrectionConst d) * Real.rpow s (-(7 : ℝ)) *
        ((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
        (Support.normalizedGagliardoESeminormOn
          ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal := by
    have hfac : (0 : ℝ) ≤ interiorCorrectionConst d *
        Real.rpow (3 : ℝ) ((n : ℝ)) * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
        (Support.normalizedGagliardoESeminormOn
          ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal := by
      have h1 : (0 : ℝ) ≤ interiorCorrectionConst d * Real.rpow (3 : ℝ) ((n : ℝ)) *
          Real.rpow (3 : ℝ) (s * (n : ℝ)) :=
        mul_nonneg (mul_nonneg (interiorCorrectionConst_pos d).le
          (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg (by norm_num) _)
      exact mul_nonneg h1 hgag
    have hsigstep : ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ *
        (Real.rpow s (-(1 / 2 : ℝ)) * (interiorCorrectionConst d *
          Real.rpow (3 : ℝ) ((n : ℝ)) * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          (Support.normalizedGagliardoESeminormOn
            ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal)) ≤
        (4 * ((Annealed.sigmaBar M n : ℝ))⁻¹) *
          (Real.rpow s (-(7 : ℝ)) * (interiorCorrectionConst d *
            Real.rpow (3 : ℝ) ((n : ℝ)) * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn
              ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal)) := by
      refine mul_le_mul hsig (mul_le_mul_of_nonneg_right hsE7 hfac)
        (mul_nonneg hsE.le hfac)
        (mul_nonneg (by norm_num) (inv_pos.2 hB).le)
    calc ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ * Real.rpow (3 : ℝ) ((n : ℝ)) *
          (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
            Real.rpow (3 : ℝ) (s * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn
              ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal)
        = ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ *
            (Real.rpow s (-(1 / 2 : ℝ)) * (interiorCorrectionConst d *
              Real.rpow (3 : ℝ) ((n : ℝ)) * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              (Support.normalizedGagliardoESeminormOn
                ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal)) := by
          ring
      _ ≤ (4 * ((Annealed.sigmaBar M n : ℝ))⁻¹) *
            (Real.rpow s (-(7 : ℝ)) * (interiorCorrectionConst d *
              Real.rpow (3 : ℝ) ((n : ℝ)) * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              (Support.normalizedGagliardoESeminormOn
                ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal)) :=
          hsigstep
      _ = (4 * interiorCorrectionConst d) * Real.rpow s (-(7 : ℝ)) *
            ((Annealed.sigmaBar M n : ℝ))⁻¹ *
            (Real.rpow (3 : ℝ) ((n : ℝ)) * Real.rpow (3 : ℝ) (s * (n : ℝ))) *
            (Support.normalizedGagliardoESeminormOn
              ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal := by
          ring
      _ = (4 * interiorCorrectionConst d) * Real.rpow s (-(7 : ℝ)) *
            ((Annealed.sigmaBar M n : ℝ))⁻¹ *
            Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn
              ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal := by
          rw [rpow_three_mul_eq_one_add s n]
  refine hkey.trans ?_
  have hrest : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
      Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
      (Support.normalizedGagliardoESeminormOn
        ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal := by
    have h1 : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
        Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (inv_pos.2 hB).le)
        (Real.rpow_nonneg (by norm_num) _)
    exact mul_nonneg h1 hgag
  have hCle : 4 * interiorCorrectionConst d ≤ max C0 (4 * interiorCorrectionConst d) :=
    le_max_right _ _
  calc (4 * interiorCorrectionConst d) * Real.rpow s (-(7 : ℝ)) *
        ((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
        (Support.normalizedGagliardoESeminormOn
          ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal
      = (4 * interiorCorrectionConst d) *
          (Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
            Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn
              ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal) := by
        ring
    _ ≤ max C0 (4 * interiorCorrectionConst d) *
          (Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
            Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn
              ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal) :=
        mul_le_mul_of_nonneg_right hCle hrest
    _ = max C0 (4 * interiorCorrectionConst d) * Real.rpow s (-(7 : ℝ)) *
          ((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
          (Support.normalizedGagliardoESeminormOn
            ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal := by
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
