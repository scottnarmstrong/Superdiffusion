/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Annular.ClauseOneFinal

/-!
# The relaxed `σ̄` display, discharged, and the four-slot endpoint

ABK26, Section 4.1, `p.mathcalE.annular.decomp` Step 2.

The ugly chain reads the running-diffusivity lower bound at the *shifted* index
`n − 2` but writes it at the exponent `3^{γn}`:

```
½ κ 3^{γn} ≤ σ̄_{n−2} ,        κ = √c⋆ γ^{−1/2} .
```

That is not what the `Frozen.Section3.inductionState` delivers.  The state
gives `σ̄_k² ≥ ¼ max(c⋆ γ^{−1} 3^{2γk}, ν²)`, hence at `k = n − 2`

```
σ̄_{n−2} ≥ ½ κ 3^{γ(n−2)} = 3^{−2γ} · (½ κ 3^{γn}) ,
```

short of the printed display by exactly the factor `3^{2γ}` — which is at most
`3^{1/16} ≈ 1.072` on the printed window `8γ ≤ s ≤ 1/4`, and at most `2` under
the standing `γ ≤ 1/4` alone.

The chain's `hsignlow` binder has been relaxed to `¼` throughout
(`Ugly` → `UglyChain` → `GradNormalization` → `UglyLatticeChain` →
`FinalStitch` → `ClauseOneFinal`), at the cost of doubling two output-constant
coefficients and nothing else.  This module closes the loop:

* `sigmaBar_sub_two_lower_quarter_of_inductionState` proves the relaxed display
  outright from the induction state and the standing `γ ≤ 1/4`;
* `exists_clauseOne_final_four` is `ClauseOneFinal.exists_clauseOne_final` with
  the `hsignlow` binder **gone**: its remaining mathematical inputs are exactly
  `hpref`, `hpret`, `huglyt` and `hlam`.

## Why the endpoint is re-run rather than composed

`exists_clauseOne_final` quantifies `C_shom` existentially, and the induction
state that discharges `hsignlow` is produced *inside* its proof from a different
constant (`C₀`) of the same `∃`-package.  From the outside the two constants
cannot be related, so the `hsignlow` slot cannot be filled after the fact.  The
proof below is therefore the same composition re-run with the slot discharged in
place; this is a forced re-derivation of
`ClauseOneFinal.exists_clauseOne_final`'s proof body, not new mathematics.  The
two private `3^x` helpers are re-derived here for the same reason (they are
`private` upstream).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open Homogenization Homogenization.Book Homogenization.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the index-shift cost `3^{2γ} ≤ 2` -/

private theorem three_rpow_mono₃ {x y : ℝ} (h : x ≤ y) : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- `3^{1/2} ≤ 2`, the only numeric fact the `3^{2γ}` index shift costs. -/
private theorem three_rpow_half_le_two' : (3 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num) ?_
  have hsq : ((3 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hsq]
  norm_num

/-! ## Part B -- the relaxed display, discharged -/

/-- **The relaxed `hsignlow` display, proved.**

On the Section 3 induction state, at the honest clause-(i) amplitude `κ = √c⋆
γ^{−1/2}` and at any index with `n − 2 ≤ m₀`,

```
¼ κ 3^{γn} ≤ σ̄_{n−2} .
```

The printed constant is `½`; the gap is the index shift `3^{2γ} ≤ 2`, which the
standing `γ ≤ 1/4` (`ABKModel.shellPrefix.gamma_le_quarter`) supplies with no
regime input.  This is the *exact* binder the relaxed ugly chain carries. -/
theorem sigmaBar_sub_two_lower_quarter_of_inductionState (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {n : ℤ} (hn : n - 2 ≤ m0) :
    1 / 4 * ((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)
        * (3 : ℝ) ^ (M.gamma * (n : ℝ)))
      ≤ (Annealed.sigmaBar M (n - 2) : ℝ) := by
  have hkap0 := annularEventAmplitude_pos M
  have hg14 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hlow := sigmaBar_lower_of_inductionState M hS hn
  have hP0 : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (((n - 2 : ℤ)) : ℝ)) := by positivity
  have hsplit : (3 : ℝ) ^ (M.gamma * (n : ℝ))
      = (3 : ℝ) ^ (2 * M.gamma) * (3 : ℝ) ^ (M.gamma * (((n - 2 : ℤ)) : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have h2g : (3 : ℝ) ^ (2 * M.gamma) ≤ 2 :=
    le_trans (three_rpow_mono₃ (by linarith only [hg14])) three_rpow_half_le_two'
  rw [hsplit]
  have hmul : (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) *
      ((3 : ℝ) ^ (2 * M.gamma) * (3 : ℝ) ^ (M.gamma * (((n - 2 : ℤ)) : ℝ)))
      ≤ (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) *
        (2 * (3 : ℝ) ^ (M.gamma * (((n - 2 : ℤ)) : ℝ))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2g hP0.le) hkap0.le
  linarith only [hmul, hlow]

/-! ## Part C -- the four-slot clause-(i) endpoint -/

/-- **The clause-(i) endpoint at four remaining slots.**

`ClauseOneFinal.exists_clauseOne_final` with `hsignlow` discharged by
`sigmaBar_sub_two_lower_quarter_of_inductionState`, so that the remaining inputs
are exactly

* the printed ranges `s ≤ 1/4`, `8γ ≤ s`, `c⋆⁴ ≤ 6`, `1 ≤ |log γ|` and the
  standing regime `γ ≤ C_shom^{−10} c⋆^{10}`;
* the typing nondegeneracies `0 < C₁`, `0 < C`, `0 ≤ C_l`, `0 ≤ Jannt` and the
  constant inequality fixing `C`; **and**
* the four mathematical obligations `hlam`, `hpref`, `hpret` and `huglyt`,
  left as binders here.

Nothing else is assumed.  The `s ≤ 1/4` restriction of the Section 2.4 anchor
is carried, not narrowed silently. -/
theorem exists_clauseOne_final_four (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Cs Cshom : ℝ, 0 < Cs ∧ 6 ≤ Cshom ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (Cshom ^ (10 : ℕ))⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ (Ccg : ℝ) (m : ℤ) (s : {s : ℝ // 0 < s}),
          (s : ℝ) ≤ 1 / 4 → 8 * M.gamma ≤ (s : ℝ) → Disorder.cstar M ^ 4 ≤ 6 →
          1 ≤ |Real.log M.gamma| →
        ∀ (Jannt : Cutoff.CutoffSample d → ℤ → ℤ → ℤ → ℝ) (C₁ Cl C : ℝ),
          0 < C₁ → 0 < C → 0 ≤ Cl →
          Cs * (1 + 196 * Cl) ^ 2 * 4 * (1 + Cl)
              + 16 * Cs * (1 + 196 * Cl) ^ 2 * Cl * (1 + centeringConst d ^ 2)
              + 4 * Cs * (1 + 4 * Cl ^ 2) ≤ C →
          (∀ omega L j n, 0 ≤ Jannt omega L j n) →
          (∀ omega ∈ Support.eventG0 M Ccg m ∩
              Support.eventG1 M m (s : ℝ)
                (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
            ∀ (n : ℤ) (v : Fin d → ℤ), n ≤ m - 1 →
              v ∈ Support.latticeAnnulusSet d n m n →
              (Annealed.sigmaBar M (n - 2) : ℝ) *
                  (unitCubeLambda (2 * M.gamma) (.finite 2)
                    (unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2)
                      omega))⁻¹ ≤
                Cl * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ)))) →
          (∀ omega ∈ Support.eventG0 M Ccg m ∩
              Support.eventG1 M m (s : ℝ)
                (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
            ∀ L : ℤ, m ≤ L →
              IsAnnularDecompPre (s : ℝ) m (jLegField M L m omega)
                (annularResponseMax M L m omega) C₁) →
          (∀ omega ∈ Support.eventG0 M Ccg m ∩
              Support.eventG1 M m (s : ℝ)
                (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
            ∀ L : ℤ, m ≤ L →
              IsAnnularDecompPre (s : ℝ) m (jLegTranspose M L m omega)
                (Jannt omega L) C₁) →
          (∀ omega ∈ Support.eventG0 M Ccg m ∩
              Support.eventG1 M m (s : ℝ)
                (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
            ∀ L : ℤ, m ≤ L → ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
              IsUglyJEstimate (Jannt omega L j n)
                (annularErrorLatticeMax M s omega j n)
                (((Annealed.sigmaBar M m : ℝ) *
                  ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
                (annularL2Block M m omega j n)
                (2 * annularGradBlock M m omega j n + 2 * gradTailSq M m omega)
                (gradTailSq M m omega) (Disorder.cstar M) M.gamma
                ((3 : ℝ) ^ ((s : ℝ) * ((m - n : ℤ) : ℝ)))
                ((3 : ℝ) ^ (((s : ℝ) + M.gamma) * ((m - n : ℤ) : ℝ))) C) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          Set.indicator (Support.eventG0 M Ccg m ∩
              Support.eventG1 M m (s : ℝ)
                (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
              (Support.fluxCorrectedErrorObservableSqSup M m s) omega
            ≤ ENNReal.ofReal (clauseOneOutConstant C₁ C 2 Cshom * (s : ℝ))
                * clauseOneTermOne M m s omega
              + ENNReal.ofReal (clauseOneOutConstant C₁ C 2 Cshom
                  * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
                  * M.gamma ^ 2 * |Real.log M.gamma| ^ 4)
              + ENNReal.ofReal (clauseOneOutConstant C₁ C 2 Cshom
                  * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
                * clauseOneTermThree M m omega
              + ENNReal.ofReal (clauseOneOutConstant C₁ C 2 Cshom
                  * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
                * clauseOneTermFour M m s omega := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, hCs, hugly⟩ := exists_uglyJEstimate_annulus_of_eventG1 d dimension
  obtain ⟨C₀, hC₀6, -, hstate⟩ :=
    Algsuperdiff.Section4.Provider.GoodEvents.exists_allScalesInductionState_ge d 0
  obtain ⟨Cshom, hC6, hC₀le, hshomGen⟩ := exists_shomSlot_ge d C₀
  refine ⟨Cs, Cshom, hCs, hC6, ?_⟩
  intro M hreg Ccg m s hs14 hsg hcstar4 hlog Jannt C₁ Cl C hC₁ hC0 hCl hCconst
    hJt0 hlam hpref hpret huglyt
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hs1 : (s : ℝ) ≤ 1 := by linarith only [hs14]
  have hregA : M.gamma ≤ (Cshom⁻¹) ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ) := by
    rwa [inv_pow]
  have hshom := hshomGen M hregA m
  have hC₀0 : (0 : ℝ) < C₀ := lt_of_lt_of_le (by norm_num) hC₀6
  have hregC : M.gamma ≤ (C₀⁻¹) ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregA.trans ?_
    have hinv : Cshom⁻¹ ≤ C₀⁻¹ := inv_anti₀ hC₀0 hC₀le
    have h10 : (Cshom⁻¹) ^ (10 : ℕ) ≤ (C₀⁻¹) ^ (10 : ℕ) :=
      pow_le_pow_left₀ (inv_nonneg.mpr (le_trans hC₀0.le hC₀le)) hinv 10
    exact mul_le_mul_of_nonneg_right h10 (pow_nonneg hcs0.le 10)
  obtain ⟨E, -, -, hSall⟩ := hstate M hregC
  -- the relaxed display of ABK26, from the state
  have hsignlow : ∀ n : ℤ, n ≤ m - 1 →
      1 / 4 * ((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)
          * (3 : ℝ) ^ (M.gamma * (n : ℝ)))
        ≤ (Annealed.sigmaBar M (n - 2) : ℝ) := fun n hn =>
    sigmaBar_sub_two_lower_quarter_of_inductionState M (hSall m) (by omega)
  have hbound : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ Support.eventG0 M Ccg m ∩
          Support.eventG1 M m (s : ℝ)
            (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) →
        clauseOneTermOne M m s omega ≠ ⊤ → ∀ L : ℤ, m ≤ L →
        IsClauseOneBound (Support.fluxCorrectedError M L m (s : ℝ) omega ^ 2)
          (annDouble m (fun j n =>
            (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
              * annularErrorLatticeMax M s omega j n))
          (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) (gradTailSq M m omega)
          (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ))
            * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2)
          (s : ℝ) (Disorder.cstar M) M.gamma
          (clauseOneOutConstant C₁ C 2 Cshom) := by
    filter_upwards [annularErrorAtomMax_ae_le_annularErrorLatticeMax M s] with
      omega hae hmem hfin L hL
    refine clauseOne_bound_final M L m s omega hs1 hsg hcstar4 hlog hmem.2
      (summable_annFam_error_of_clauseOneTermOne_ne_top M m s omega hfin)
      hC6 hshom hC₁.le hC0.le (fun j n => hJt0 omega L j n)
      (hpref omega hmem L hL) (hpret omega hmem L hL) ?_ (huglyt omega hmem L hL)
    intro j n hjm hnj
    refine isUglyJEstimate_mono_E2 hC0.le (Real.rpow_nonneg (by norm_num) _)
      (hae j n hnj) ?_
    exact hugly M m L m E omega (s : ℝ) Cl C (hSall m) le_rfl hL s.2 hs14 hsg
      hmem.2 hCl (hlam omega hmem) hsignlow hCconst j n hjm hnj
  have hdisplay := clauseOne_representative_display_dichotomy M m s
    (Support.eventG0 M Ccg m ∩
      Support.eventG1 M m (s : ℝ)
        (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
    (C := clauseOneOutConstant C₁ C 2 Cshom)
    (clauseOneOutConstant_pos hC₁ hC0 (by norm_num) hC6) hbound
  filter_upwards [hdisplay] with omega hom
  rwa [clauseOneDisplayRhs_eq] at hom

/-! ## Part D -- clause (ii) off the four-slot endpoint -/

/-- **Clause (ii) off the four-slot display.**  Unchanged from
`ClauseOneFinal.clauseTwo_of_final_display`; stated here so that the four-slot
endpoint carries its own clause-(ii) consumer. -/
theorem clauseTwo_of_final_four_display [NeZero d] (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) {ep C : ℝ} (hC0 : 0 ≤ C)
    (hep : ep ∈ Set.Ioc (0 : ℝ) (1 / 2)) (hsep : (s : ℝ) * ep ≤ 1)
    (hsmall : M.gamma * |Real.log M.gamma| ^ 2
      ≤ (s : ℝ) ^ (3 / 2 : ℝ) * Disorder.cstar M ^ 2 * ep)
    (hdisp : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Set.indicator (Support.eventG0 M Ccg m ∩
          Support.eventG1 M m (s : ℝ)
            (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
          (Support.fluxCorrectedErrorObservableSqSup M m s) omega
        ≤ clauseOneDisplayRhs M m s C omega) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Set.indicator (Support.goodEventBase M Ccg m s ep)
          (Support.fluxCorrectedErrorObservableSup M m s) omega
        ≤ ENNReal.ofReal (2 * Real.sqrt C * ep) :=
  clauseTwo_of_final_display M Ccg m s hC0 hep hsep hsmall hdisp

end

end Algsuperdiff.Section4.Provider.Annular
