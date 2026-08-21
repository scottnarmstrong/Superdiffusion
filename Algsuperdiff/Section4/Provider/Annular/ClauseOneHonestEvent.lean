/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Annular.DichotomyDisplay

/-!
# The clause-(i) endpoint at the honest Section 4.1 event

The A6a endpoint `ClauseOneConditional.exists_clauseOne_conditional_display` is
stated at `Support.goodEventBase M Ccg m s ε = 𝒢₀ ∩ 𝒢₁(m; s, s ε √c⋆ γ^{−1/2})
∩ 𝒢₂(m; s, ε)`.  The Section 4.1 clause-(i) display is stated at the **larger**
event

```
𝒢₀(m) ∩ 𝒢₁(m; s, √c⋆ γ^{−1/2}),
```

with no `𝒢₂` factor and with the `𝒢₁` amplitude *not* damped by `s ε`.  A6a's
finding (d) recorded the divergence and finding (e) mapped the route out; this
module walks it.

## What changes, and what does not

* `𝒢₂` is gone.  Its **only** consumer was the `hsumE` binder of
  `ClauseOne.clauseOne_bound`, and `DichotomyDisplay` supplies that binder from
  finiteness of the display's own first term, with no event at all.
* The `𝒢₁` amplitude rises from `T = s ε √c⋆ γ^{−1/2}` to `T' = √c⋆ γ^{−1/2}`,
  i.e. the event gets **larger** and the reading gets **weaker**.  Nothing in the
  clause-(i) composite is harmed, because every `𝒢₁` consumer on this lane is a
  *summability* statement:
  `EventReading.summable_annFam_annularL2Block_of_eventG1`,
  `…_annularGradBlock_of_eventG1` and
  `…_summable_shellBlockLatticeReal_of_eventG1` each need only `0 ≤ T` and the
  membership.  The threshold enters those proofs solely through the auxiliary
  constant `K_sh = 3^{s/4} T²` of `AssemblyFeed.summable_annFam_grad` /
  `…_l2`, which is quantified inside a `Summable` claim and never reaches the
  display.  **No output constant changes**: the endpoint's constant is the same
  `clauseOneOutConstant C₁ C₂ K_tail C_shom` as in A6a.
* `ε` disappears from the statement entirely, together with `0 ≤ ε` and the
  containment side condition `s ε ≤ 1` of
  `ClauseOneConditional.goodEventBase_subset_annularEvent`.
* `0 ≤ C₁`, `0 ≤ C₂` are strengthened to `0 < C₁`, `0 < C₂`, so that the output
  constant is positive.  This is what the `⊤` branch of the dichotomy consumes,
  and it is the positivity the frozen `∃ C, 0 < C` already carries.

The quadratic `𝒢₁` readings `EventReading.gradTailSq_le_of_eventG1` and
`…_tsum_shellQuarter_le_of_eventG1` — the ones that would degrade from `T²` to
`T'² = c⋆ γ^{−1}` — are **not** used by clause (i) at all.  They are consumed by
the clause-(ii) budget `ClauseTwo.clauseOneDisplayRhs_le_of_goodEventBase`, which
legitimately runs on the smaller `goodEventBase` (the manuscript's own
`e.lambda.good.events`) and is untouched here.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open Homogenization Homogenization.Book Homogenization.Book.Ch02
open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the honest amplitude and the positive output constant -/

/-- The `𝒢₁` amplitude of the printed clause-(i) event, `T' = √c⋆ γ^{−1/2}`, is
nonnegative.  Unlike `ClauseOneConditional.goodEventAmplitude_nonneg` this needs
no hypothesis: no `ε` occurs. -/
theorem annularEventAmplitude_nonneg (M : ABKModel d) :
    (0 : ℝ) ≤ Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ :=
  mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _))

/-- The square of the honest amplitude: `T'² = c⋆ γ^{−1}`. -/
theorem annularEventAmplitude_sq (M : ABKModel d) :
    (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ 2
      = Disorder.cstar M * (M.gamma)⁻¹ := by
  have hc : Real.sqrt (Disorder.cstar M) ^ 2 = Disorder.cstar M :=
    Real.sq_sqrt (Disorder.cstar_characterization M).1.le
  have hg : Real.sqrt M.gamma ^ 2 = M.gamma :=
    Real.sq_sqrt M.shellPrefix.gamma_pos.le
  have hexp : (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ 2
      = Real.sqrt (Disorder.cstar M) ^ 2 * ((Real.sqrt M.gamma) ^ 2)⁻¹ := by
    rw [← inv_pow]
    ring
  rw [hexp, hc, hg]

/-- The output constant of the clause-(i) composite is **positive** as soon as
the two slot constants are.  This is the input of the dichotomy's `⊤` branch. -/
theorem clauseOneOutConstant_pos {C₁ C₂ Ktail Cshom : ℝ} (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (hKtail : 0 ≤ Ktail) (hCshom : 6 ≤ Cshom) :
    0 < clauseOneOutConstant C₁ C₂ Ktail Cshom := by
  have h1 : (0 : ℝ) < 1 + Ktail := by linarith only [hKtail]
  have hleg : (0 : ℝ) < clauseOneLegConstant C₁ C₂ Ktail := by
    unfold clauseOneLegConstant
    exact mul_pos (mul_pos (by norm_num) hC₁) (mul_pos h1 hC₂)
  have hCs2 : (36 : ℝ) ≤ Cshom ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) hCshom 2
    calc (36 : ℝ) = (6 : ℝ) ^ 2 := by norm_num
      _ ≤ Cshom ^ 2 := h
  have hbig : (0 : ℝ) < 7000 * Cshom ^ 2 := by linarith only [hCs2]
  unfold clauseOneOutConstant
  exact mul_pos (by linarith only [hleg]) hbig

/-! ## Part B -- the pointwise composite at an arbitrary `𝒢₁` threshold -/

/-- **The clause-(i) composite with `𝒢₂` removed and the `𝒢₁` threshold free.**

Every binder of `ClauseOne.clauseOne_bound` is discharged here except the four
author-consult slots `hpref`, `hpret`, `huglyf`, `huglyt`, the `hsumE` binder
(now an explicit argument, supplied eventlessly by
`DichotomyDisplay.summable_annFam_error_of_clauseOneTermOne_ne_top`), and the
`𝒢₁` membership at an **arbitrary** nonnegative threshold `T`.

This is the A6a `clauseOne_bound_conditional` with the good-event membership
split into its two genuine uses: `𝒢₁` at whatever amplitude the caller has, and
`𝒢₂` replaced by the dichotomy.  `𝒢₀` never entered the composite.

The remaining inequalities are conditional A obligations, not source premises. -/
theorem clauseOne_bound_of_eventG1 [NeZero d] (M : ABKModel d) (L m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d)
    (hs1 : (s : ℝ) ≤ 1) (hsg : 8 * M.gamma ≤ (s : ℝ))
    (hcstar4 : Disorder.cstar M ^ 4 ≤ 6) (hlog : 1 ≤ |Real.log M.gamma|)
    {T : ℝ} (hT : 0 ≤ T) (hG1 : omega ∈ Support.eventG1 M m (s : ℝ) T)
    (hsumE : Summable (annFam m (fun j n => (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
      * annularErrorLatticeMax M s omega j n)))
    {Cshom : ℝ} (hCshom : 6 ≤ Cshom)
    (hshom : ∀ n : ℤ, n ≤ m - 1 →
      ((Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2
        ≤ (Cshom * M.gamma * ((m - n : ℤ) : ℝ)
            + Cshom * (2 * M.gamma
              + (Disorder.cstar M ^ 2)⁻¹ * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2
          * (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ)))
    {Jannf Jannt : ℤ → ℤ → ℝ} {C₁ C₂ Ktail : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hKtail : 0 ≤ Ktail)
    (hJannf0 : ∀ j n, 0 ≤ Jannf j n) (hJannt0 : ∀ j n, 0 ≤ Jannt j n)
    (hpref : IsAnnularDecompPre (s : ℝ) m (jLegField M L m omega) Jannf C₁)
    (hpret : IsAnnularDecompPre (s : ℝ) m (jLegTranspose M L m omega) Jannt C₁)
    (huglyf : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      IsUglyJEstimate (Jannf j n) (annularErrorLatticeMax M s omega j n)
        (((Annealed.sigmaBar M m : ℝ) *
          ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
        (annularL2Block M m omega j n)
        (annularGradBlock M m omega j n + Ktail * gradTailSq M m omega)
        (gradTailSq M m omega) (Disorder.cstar M) M.gamma
        ((3 : ℝ) ^ ((s : ℝ) * ((m - n : ℤ) : ℝ)))
        ((3 : ℝ) ^ (((s : ℝ) + M.gamma) * ((m - n : ℤ) : ℝ))) C₂)
    (huglyt : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      IsUglyJEstimate (Jannt j n) (annularErrorLatticeMax M s omega j n)
        (((Annealed.sigmaBar M m : ℝ) *
          ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
        (annularL2Block M m omega j n)
        (annularGradBlock M m omega j n + Ktail * gradTailSq M m omega)
        (gradTailSq M m omega) (Disorder.cstar M) M.gamma
        ((3 : ℝ) ^ ((s : ℝ) * ((m - n : ℤ) : ℝ)))
        ((3 : ℝ) ^ (((s : ℝ) + M.gamma) * ((m - n : ℤ) : ℝ))) C₂) :
    IsClauseOneBound (Support.fluxCorrectedError M L m (s : ℝ) omega ^ 2)
      (annDouble m (fun j n => (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
        * annularErrorLatticeMax M s omega j n))
      (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) (gradTailSq M m omega)
      (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ))
        * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2)
      (s : ℝ) (Disorder.cstar M) M.gamma
      (clauseOneOutConstant C₁ C₂ Ktail Cshom) := by
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  -- the `hsumS` inputs
  have hCshom0 : (0 : ℝ) ≤ Cshom := by linarith only [hCshom]
  have ha0 : (0 : ℝ) ≤ Cshom * M.gamma := mul_nonneg hCshom0 hgam0.le
  have hB0 : (0 : ℝ) ≤ Cshom * (2 * M.gamma
      + (Disorder.cstar M ^ 2)⁻¹ * (M.gamma * |Real.log M.gamma| ^ 2)) := by
    have h1 : (0 : ℝ) ≤ 2 * M.gamma := by linarith only [hgam0]
    have h2 : (0 : ℝ) ≤ (Disorder.cstar M ^ 2)⁻¹
        * (M.gamma * |Real.log M.gamma| ^ 2) :=
      mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (mul_nonneg hgam0.le (sq_nonneg _))
    exact mul_nonneg hCshom0 (by linarith only [h1, h2])
  -- the constant bookkeeping at the pinned family `Cbf = 1`, `Kl2 = 1`, `Kgn = 81`
  have hCleg0 : (0 : ℝ) ≤ clauseOneLegConstant C₁ C₂ Ktail :=
    clauseOneLegConstant_nonneg hC₁ hC₂ hKtail
  have hCleg2 : (0 : ℝ) ≤ 2 * clauseOneLegConstant C₁ C₂ Ktail := by
    linarith only [hCleg0]
  have hCs2 : (36 : ℝ) ≤ Cshom ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) hCshom 2
    calc (36 : ℝ) = (6 : ℝ) ^ 2 := by norm_num
      _ ≤ Cshom ^ 2 := h
  have hbig : (252000 : ℝ) ≤ 7000 * Cshom ^ 2 := by linarith only [hCs2]
  have hCleg : 24 * 1 * C₁ * ((1 + Ktail) * C₂) ≤ clauseOneLegConstant C₁ C₂ Ktail := by
    have hval : 24 * 1 * C₁ * ((1 + Ktail) * C₂) = clauseOneLegConstant C₁ C₂ Ktail := by
      unfold clauseOneLegConstant
      ring
    exact le_of_eq hval
  have hCout1 : 2 * clauseOneLegConstant C₁ C₂ Ktail
      ≤ clauseOneOutConstant C₁ C₂ Ktail Cshom := by
    unfold clauseOneOutConstant
    calc 2 * clauseOneLegConstant C₁ C₂ Ktail
        = 2 * clauseOneLegConstant C₁ C₂ Ktail * 1 := (mul_one _).symm
      _ ≤ 2 * clauseOneLegConstant C₁ C₂ Ktail * (7000 * Cshom ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith only [hbig]) hCleg2
  have hCout2 : 2 * clauseOneLegConstant C₁ C₂ Ktail * (7000 * Cshom ^ 2)
      ≤ clauseOneOutConstant C₁ C₂ Ktail Cshom := le_of_eq rfl
  have hCout3 : 2 * clauseOneLegConstant C₁ C₂ Ktail * (4608 * 1 + 576 * 81)
      ≤ clauseOneOutConstant C₁ C₂ Ktail Cshom := by
    unfold clauseOneOutConstant
    have h51 : (4608 * 1 + 576 * 81 : ℝ) ≤ 7000 * Cshom ^ 2 := by
      have hval : (4608 * 1 + 576 * 81 : ℝ) = 51264 := by norm_num
      rw [hval]
      linarith only [hbig]
    exact mul_le_mul_of_nonneg_left h51 hCleg2
  exact clauseOne_bound M L m s.2 hs1 hsg omega
    (Jlegf := jLegField M L m omega) (Jlegt := jLegTranspose M L m omega)
    (Jannf := Jannf) (Jannt := Jannt)
    (E2 := fun j n => annularErrorLatticeMax M s omega j n)
    (sig := fun n => ((Annealed.sigmaBar M m : ℝ) *
      ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
    (L2f := annularL2Block M m omega) (gradNf := annularGradBlock M m omega)
    (A := shellBlockLatticeReal M m omega)
    (Cbf := 1) (Kl2 := 1) (Kgn := 81) (Cshom := Cshom)
    (by norm_num) hC₁ hC₂ (by norm_num) (by norm_num) hKtail
    (jLegField_nonneg M L m omega) (jLegTranspose_nonneg M L m omega)
    hJannf0 hJannt0
    (fun j n => annularErrorLatticeMax_nonneg M s omega j n)
    (fun _n => sq_nonneg _)
    (annularL2Block_nonneg M m omega) (annularGradBlock_nonneg M m omega)
    (hbfJ_latticeMax M L m omega le_rfl)
    (summable_jLegField M L m omega s.2) (summable_jLegTranspose M L m omega s.2)
    hpref hpret huglyf huglyt hsumE
    (summable_annFam_sig (a := Cshom * M.gamma)
      (B := Cshom * (2 * M.gamma
        + (Disorder.cstar M ^ 2)⁻¹ * (M.gamma * |Real.log M.gamma| ^ 2)))
      s.2 hs1 hgam0.le hsg ha0 hB0 (fun _n => sq_nonneg _) hshom)
    (summable_annFam_annularL2Block_of_eventG1 M m s.2 hs1 hsg hT hG1)
    (summable_annFam_annularGradBlock_of_eventG1 M m s.2 hs1 hT hG1)
    hcstar4 hlog hshom
    (summable_shellBlockLatticeReal_of_eventG1 M m s.2.le hG1)
    (fun j n hj hn => annularL2Block_le M m omega j n hj hn)
    (fun j n hj hn => annularGradBlock_le M m omega j n hj hn)
    hCleg hCout1 hCout2 hCout3

/-! ## Part C -- the endpoint at the frozen clause-(i) event -/

/-- **The clause-(i) endpoint at the honest Section 4.1 event.**

`ClauseOneConditional.exists_clauseOne_conditional_display` restated with the
indicator and the slot quantifiers at the event the printed clause-(i) display
actually carries,

```
𝒢₀(m) ∩ 𝒢₁(m; s, √c⋆ γ^{−1/2}),
```

instead of `Support.goodEventBase`.  No `𝒢₂` occurs anywhere in the statement or
in the proof, and no `ε` occurs at all.

The `σ̄`-continuity slot is supplied inside by A5a's `exists_shomSlot_ge`, which
is why the statement is an existential over `C_shom`; the regime hypothesis is
the printed `γ ≤ C^{−1} c⋆^{10}` at `C = C_shom^{10}`.

The remaining hypotheses are, in order: the printed ranges (`s ≤ 1`, `8γ ≤ s`,
`c⋆⁴ ≤ 6`, `1 ≤ |log γ|`); the positivity and nonnegativity of the slot
constants; and the four author-consult slots `hpref`, `hpret`, `huglyf`,
`huglyt`.  The good-event membership enters through the indicator on the left and
through the slots' own quantifier.  No source node is claimed, realized or
closed. -/
theorem exists_clauseOne_honest_display (d : ℕ) [NeZero d] :
    ∃ Cshom : ℝ, 6 ≤ Cshom ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (Cshom ^ (10 : ℕ))⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ (Ccg : ℝ) (m : ℤ) (s : {s : ℝ // 0 < s}),
          (s : ℝ) ≤ 1 → 8 * M.gamma ≤ (s : ℝ) → Disorder.cstar M ^ 4 ≤ 6 →
          1 ≤ |Real.log M.gamma| →
        ∀ (Jannf Jannt : Cutoff.CutoffSample d → ℤ → ℤ → ℤ → ℝ) (C₁ C₂ Ktail : ℝ),
          0 < C₁ → 0 < C₂ → 0 ≤ Ktail →
          (∀ omega L j n, 0 ≤ Jannf omega L j n) →
          (∀ omega L j n, 0 ≤ Jannt omega L j n) →
          (∀ omega ∈ Support.eventG0 M Ccg m ∩
              Support.eventG1 M m (s : ℝ)
                (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
            ∀ L : ℤ, m ≤ L →
              IsAnnularDecompPre (s : ℝ) m (jLegField M L m omega) (Jannf omega L) C₁) →
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
              IsUglyJEstimate (Jannf omega L j n)
                (annularErrorLatticeMax M s omega j n)
                (((Annealed.sigmaBar M m : ℝ) *
                  ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
                (annularL2Block M m omega j n)
                (annularGradBlock M m omega j n + Ktail * gradTailSq M m omega)
                (gradTailSq M m omega) (Disorder.cstar M) M.gamma
                ((3 : ℝ) ^ ((s : ℝ) * ((m - n : ℤ) : ℝ)))
                ((3 : ℝ) ^ (((s : ℝ) + M.gamma) * ((m - n : ℤ) : ℝ))) C₂) →
          (∀ omega ∈ Support.eventG0 M Ccg m ∩
              Support.eventG1 M m (s : ℝ)
                (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
            ∀ L : ℤ, m ≤ L → ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
              IsUglyJEstimate (Jannt omega L j n)
                (annularErrorLatticeMax M s omega j n)
                (((Annealed.sigmaBar M m : ℝ) *
                  ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
                (annularL2Block M m omega j n)
                (annularGradBlock M m omega j n + Ktail * gradTailSq M m omega)
                (gradTailSq M m omega) (Disorder.cstar M) M.gamma
                ((3 : ℝ) ^ ((s : ℝ) * ((m - n : ℤ) : ℝ)))
                ((3 : ℝ) ^ (((s : ℝ) + M.gamma) * ((m - n : ℤ) : ℝ))) C₂) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          Set.indicator (Support.eventG0 M Ccg m ∩
              Support.eventG1 M m (s : ℝ)
                (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
              (Support.fluxCorrectedErrorObservableSqSup M m s) omega
            ≤ ENNReal.ofReal (clauseOneOutConstant C₁ C₂ Ktail Cshom * (s : ℝ))
                * clauseOneTermOne M m s omega
              + ENNReal.ofReal (clauseOneOutConstant C₁ C₂ Ktail Cshom
                  * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
                  * M.gamma ^ 2 * |Real.log M.gamma| ^ 4)
              + ENNReal.ofReal (clauseOneOutConstant C₁ C₂ Ktail Cshom
                  * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
                * clauseOneTermThree M m omega
              + ENNReal.ofReal (clauseOneOutConstant C₁ C₂ Ktail Cshom
                  * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
                * clauseOneTermFour M m s omega := by
  obtain ⟨Cshom, hC6, -, hshomGen⟩ := exists_shomSlot_ge d 0
  refine ⟨Cshom, hC6, ?_⟩
  intro M hreg Ccg m s hs1 hsg hcstar4 hlog Jannf Jannt C₁ C₂ Ktail
    hC₁ hC₂ hKtail hJf0 hJt0 hpref hpret huglyf huglyt
  have hregA : M.gamma ≤ (Cshom⁻¹) ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ) := by
    rwa [inv_pow]
  have hshom := hshomGen M hregA m
  have hdisplay := clauseOne_representative_display_dichotomy M m s
    (Support.eventG0 M Ccg m ∩
      Support.eventG1 M m (s : ℝ)
        (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
    (C := clauseOneOutConstant C₁ C₂ Ktail Cshom)
    (clauseOneOutConstant_pos hC₁ hC₂ hKtail hC6) (Filter.Eventually.of_forall ?_)
  · filter_upwards [hdisplay] with omega hom
    rwa [clauseOneDisplayRhs_eq] at hom
  · intro omega hmem hfin L hL
    exact clauseOne_bound_of_eventG1 M L m s omega hs1 hsg hcstar4 hlog
      (annularEventAmplitude_nonneg M) hmem.2
      (summable_annFam_error_of_clauseOneTermOne_ne_top M m s omega hfin)
      hC6 hshom hC₁.le hC₂.le hKtail (fun j n => hJf0 omega L j n)
      (fun j n => hJt0 omega L j n) (hpref omega hmem L hL) (hpret omega hmem L hL)
      (huglyf omega hmem L hL) (huglyt omega hmem L hL)

end

end Algsuperdiff.Section4.Provider.Annular
