/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Annular.EventReading
import Algsuperdiff.Section4.Provider.Annular.ShomContinuityUngated

/-!
# The conditional clause-(i) endpoint of the annular decomposition

This module composes the proved clause-(i) chain into a single **conditional**
endpoint: the almost-sure, `[0,∞]`-valued, representative-side display of
`DisplaySlots.clauseOne_representative_display_latticeMax`, carrying *exactly*
the four author-consult slots as named hypotheses and nothing else.

## What is discharged here

Starting from `ClauseOne.clauseOne_bound` (18 binders + two event memberships
after the A5c feed), this module closes:

* the **good-event plumbing** — the two event memberships `hG1` / `hG2` and the
  threshold nonnegativity `0 ≤ T`, from a single membership `ω ∈
  Support.goodEventBase M Ccg m s ε` through the proved projections
  `Support.goodEventBase_subset_eventG1` / `…_subset_eventG2`, at the
  `e.lambda.good.events` amplitude `T = s ε √c⋆ γ^{−1/2}`;
* the **σ̄-continuity slot** `hshom` (with its companion `hsig0`), from A5a's
  `exists_shomSlot_ge` at the floor `6`, so the endpoint's regime hypothesis is
  the printed `γ ≤ C^{−1} c⋆^{10}` with `C = C_shom^{10}`;
* the **constant bookkeeping** at the pinned family `C_bf = 1`, `K_L2 = 1`,
  `K_gn = 81`, with the two output constants given by the explicit formulas
  `clauseOneLegConstant` and `clauseOneOutConstant`;
* the **`∀ L` / `Eventually` wrapper**: the pointwise chain holds for *every*
  `L ≥ m`, with no `m ≤ L` side condition beyond the one the display carries.

## What remains, and why

* `hpref` / `hpret` — the Step-1 annular cover at the concrete grids
  `AssemblyFeed.jLegField` / `AssemblyFeed.jLegTranspose`; author-consult item
  A1 STOP- (`hcov` / `hcen` subadditivity);
* `huglyf` — the per-cube ugly estimate at the pinned carriers
  `DisplaySlots.annularErrorLatticeMax`, `EventBudgets.annularL2Block`,
  `EventBudgets.annularGradBlock`; the unit-cube-to-lattice-cube transport
  development (A2b frontier (a1)–(a4));
* `huglyt` — its transpose leg; author-consult item on (CoarseGraining has no
  transpose-invariance theorem for the error functionals).

Together with the printed ranges (`s ≤ 1`, `8γ ≤ s`, `c⋆^4 ≤ 6`,
`1 ≤ |log γ|`, `0 ≤ ε`) and the good-event membership, these are the *only*
inputs of the endpoint.

## Wrinkle  of the graph's clause-(ii) route, recorded

`goodEventBase_subset_annularEvent` is the containment the manuscript leaves
unstated: `𝒢(m; s, ε) ⊆ 𝒢₀(m) ∩ 𝒢₁(m; s, √c⋆ γ^{−1/2})`, i.e. the event of the
printed clause-(i) display, valid because `s ε ≤ 1`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open Homogenization Homogenization.Book Homogenization.Book.Ch02
open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the `𝒢₁` amplitude of `e.lambda.good.events` -/

/-- The `𝒢₁` amplitude carried by `Support.goodEventBase`, `T = s ε √c⋆ γ^{-1/2}`,
is nonnegative. -/
theorem goodEventAmplitude_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) {ep : ℝ}
    (hep : 0 ≤ ep) :
    (0 : ℝ) ≤ (s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ :=
  mul_nonneg (mul_nonneg (mul_nonneg s.2.le hep) (Real.sqrt_nonneg _))
    (inv_nonneg.2 (Real.sqrt_nonneg _))

/-- The square of the `𝒢₁` amplitude, in the form the third and fourth
right-hand terms of clause (i) consume: `T² = s² ε² c⋆ γ^{-1}`. -/
theorem goodEventAmplitude_sq (M : ABKModel d) (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ 2
      = (s : ℝ) ^ 2 * ep ^ 2 * Disorder.cstar M * (M.gamma)⁻¹ := by
  have hc : Real.sqrt (Disorder.cstar M) ^ 2 = Disorder.cstar M :=
    Real.sq_sqrt (Disorder.cstar_characterization M).1.le
  have hg : Real.sqrt M.gamma ^ 2 = M.gamma :=
    Real.sq_sqrt M.shellPrefix.gamma_pos.le
  have hexp : ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ 2
      = (s : ℝ) ^ 2 * ep ^ 2 * (Real.sqrt (Disorder.cstar M) ^ 2)
        * ((Real.sqrt M.gamma) ^ 2)⁻¹ := by
    rw [← inv_pow]
    ring
  rw [hexp, hc, hg]

/-- **Wrinkle  of the clause-(ii) route, made explicit.**  The good event `𝒢(m; s,
ε)` of `e.lambda.good.events` sits inside the event of the printed clause-(i)
display, whose `𝒢₁` amplitude is the larger `√c⋆ γ^{-1/2}`.  The manuscript
uses this containment without stating it. -/
theorem goodEventBase_subset_annularEvent (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) {ep : ℝ} (hep0 : 0 ≤ ep) (hsep : (s : ℝ) * ep ≤ 1) :
    Support.goodEventBase M Ccg m s ep ⊆
      Support.eventG0 M Ccg m ∩
        Support.eventG1 M m (s : ℝ)
          (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) := by
  intro omega homega
  refine ⟨Support.goodEventBase_subset_eventG0 M Ccg m s ep homega, ?_⟩
  refine Support.eventG1_subset_of_le M m (s : ℝ)
    (goodEventAmplitude_nonneg M s hep0) ?_
    (Support.goodEventBase_subset_eventG1 M Ccg m s ep homega)
  have hnn : (0 : ℝ) ≤ Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ :=
    mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _))
  calc (s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹
      = ((s : ℝ) * ep) * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) := by
        ring
    _ ≤ 1 * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) :=
        mul_le_mul_of_nonneg_right hsep hnn
    _ = Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ := one_mul _

/-! ## Part B -- the two output constants at the pinned family -/

/-- The per-leg constant of `ClauseOne.clauseOne_bound`'s `hCleg` binder at the
pinned `C_bf = 1`: `C_leg = 24 C₁ (1 + K_tail) C₂`. -/
def clauseOneLegConstant (C₁ C₂ Ktail : ℝ) : ℝ := 24 * C₁ * ((1 + Ktail) * C₂)

/-- The output constant of the clause-(i) composite at the pinned family
`C_bf = 1`, `K_L2 = 1`, `K_gn = 81`:
`C_out = 2 C_leg · 7000 C_shom²`.

Because A5a delivers `C_shom ≥ 6`, this single value dominates all three
`hCout` binders: `7000 C_shom² ≥ 252000 ≥ 51264 = 4608 K_L2 + 576 K_gn ≥ 1`. -/
def clauseOneOutConstant (C₁ C₂ Ktail Cshom : ℝ) : ℝ :=
  2 * clauseOneLegConstant C₁ C₂ Ktail * (7000 * Cshom ^ 2)

theorem clauseOneLegConstant_nonneg {C₁ C₂ Ktail : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hKtail : 0 ≤ Ktail) : 0 ≤ clauseOneLegConstant C₁ C₂ Ktail := by
  have h1 : (0 : ℝ) ≤ 1 + Ktail := by linarith only [hKtail]
  exact mul_nonneg (mul_nonneg (by norm_num) hC₁) (mul_nonneg h1 hC₂)

theorem clauseOneOutConstant_nonneg {C₁ C₂ Ktail Cshom : ℝ} (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hKtail : 0 ≤ Ktail) :
    0 ≤ clauseOneOutConstant C₁ C₂ Ktail Cshom := by
  have hleg : (0 : ℝ) ≤ 2 * clauseOneLegConstant C₁ C₂ Ktail := by
    have := clauseOneLegConstant_nonneg hC₁ hC₂ hKtail
    linarith only [this]
  exact mul_nonneg hleg (by positivity)

/-! ## Part C -- the pointwise conditional bound -/

/-- **The clause-(i) composite, conditional on the four consult slots only.**

Every binder of `ClauseOne.clauseOne_bound` is discharged here except the four
author-consult slots `hpref`, `hpret`, `huglyf`, `huglyt`; the two event
memberships come from the single good-event membership `hmem`, and the constant
bookkeeping is closed at `clauseOneOutConstant`.

The remaining inequalities are conditional A obligations, not source premises. -/
theorem clauseOne_bound_conditional [NeZero d] (M : ABKModel d) (Ccg : ℝ) (L m : ℤ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) (omega : Cutoff.CutoffSample d)
    (hs1 : (s : ℝ) ≤ 1) (hsg : 8 * M.gamma ≤ (s : ℝ))
    (hcstar4 : Disorder.cstar M ^ 4 ≤ 6) (hlog : 1 ≤ |Real.log M.gamma|)
    (hep0 : 0 ≤ ep)
    (hmem : omega ∈ Support.goodEventBase M Ccg m s ep)
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
  -- the two good-event projections at the `e.lambda.good.events` amplitude
  have hG1 := Support.goodEventBase_subset_eventG1 M Ccg m s ep hmem
  have hG2 := Support.goodEventBase_subset_eventG2 M Ccg m s ep hmem
  have hT : (0 : ℝ) ≤ (s : ℝ) * ep * Real.sqrt (Disorder.cstar M)
      * (Real.sqrt M.gamma)⁻¹ := goodEventAmplitude_nonneg M s hep0
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
  -- the constant bookkeeping at the pinned family
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
    have : 24 * 1 * C₁ * ((1 + Ktail) * C₂) = clauseOneLegConstant C₁ C₂ Ktail := by
      unfold clauseOneLegConstant
      ring
    exact le_of_eq this
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
    hpref hpret huglyf huglyt
    (summable_annFam_error_of_eventG2 M m s hG2)
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

/-! ## Part D -- the almost-sure representative display -/

/-- **The conditional clause-(i) endpoint.**

The A5b representative display
`DisplaySlots.clauseOne_representative_display_latticeMax`, with every input
discharged except the four author-consult slots.  The `σ̄`-continuity slot is
supplied inside by A5a's `exists_shomSlot_ge`, which is why the statement is an
existential over `C_shom`; the regime hypothesis is the printed
`γ ≤ C^{−1} c⋆^{10}` at `C = C_shom^{10}`.

The remaining hypotheses are, in order: the printed ranges (`s ≤ 1`, `8γ ≤ s`,
`c⋆^4 ≤ 6`, `1 ≤ |log γ|`, `0 ≤ ε`); the nonnegativity and the four slot
inequalities `hpref`, `hpret`, `huglyf`, `huglyt`.  The good-event membership
enters through the indicator on the left and through the slots' own
quantifier.  No source node is claimed, realized or closed. -/
theorem exists_clauseOne_conditional_display (d : ℕ) [NeZero d] :
    ∃ Cshom : ℝ, 6 ≤ Cshom ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (Cshom ^ (10 : ℕ))⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ (Ccg : ℝ) (m : ℤ) (s : {s : ℝ // 0 < s}) (ep : ℝ),
          (s : ℝ) ≤ 1 → 8 * M.gamma ≤ (s : ℝ) → Disorder.cstar M ^ 4 ≤ 6 →
          1 ≤ |Real.log M.gamma| → 0 ≤ ep →
        ∀ (Jannf Jannt : Cutoff.CutoffSample d → ℤ → ℤ → ℤ → ℝ) (C₁ C₂ Ktail : ℝ),
          0 ≤ C₁ → 0 ≤ C₂ → 0 ≤ Ktail →
          (∀ omega L j n, 0 ≤ Jannf omega L j n) →
          (∀ omega L j n, 0 ≤ Jannt omega L j n) →
          (∀ omega ∈ Support.goodEventBase M Ccg m s ep, ∀ L : ℤ, m ≤ L →
            IsAnnularDecompPre (s : ℝ) m (jLegField M L m omega) (Jannf omega L) C₁) →
          (∀ omega ∈ Support.goodEventBase M Ccg m s ep, ∀ L : ℤ, m ≤ L →
            IsAnnularDecompPre (s : ℝ) m (jLegTranspose M L m omega)
              (Jannt omega L) C₁) →
          (∀ omega ∈ Support.goodEventBase M Ccg m s ep, ∀ L : ℤ, m ≤ L →
            ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
              IsUglyJEstimate (Jannf omega L j n)
                (annularErrorLatticeMax M s omega j n)
                (((Annealed.sigmaBar M m : ℝ) *
                  ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
                (annularL2Block M m omega j n)
                (annularGradBlock M m omega j n + Ktail * gradTailSq M m omega)
                (gradTailSq M m omega) (Disorder.cstar M) M.gamma
                ((3 : ℝ) ^ ((s : ℝ) * ((m - n : ℤ) : ℝ)))
                ((3 : ℝ) ^ (((s : ℝ) + M.gamma) * ((m - n : ℤ) : ℝ))) C₂) →
          (∀ omega ∈ Support.goodEventBase M Ccg m s ep, ∀ L : ℤ, m ≤ L →
            ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
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
          Set.indicator (Support.goodEventBase M Ccg m s ep)
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
  intro M hreg Ccg m s ep hs1 hsg hcstar4 hlog hep0 Jannf Jannt C₁ C₂ Ktail
    hC₁ hC₂ hKtail hJf0 hJt0 hpref hpret huglyf huglyt
  have hregA : M.gamma ≤ (Cshom⁻¹) ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ) := by
    rwa [inv_pow]
  have hshom := hshomGen M hregA m
  refine clauseOne_representative_display_latticeMax M m s
    (Support.goodEventBase M Ccg m s ep)
    (clauseOneOutConstant_nonneg hC₁ hC₂ hKtail) ?_
  refine Filter.Eventually.of_forall ?_
  intro omega hmem L hL
  exact clauseOne_bound_conditional M Ccg L m s ep omega hs1 hsg hcstar4 hlog hep0
    hmem hC6 hshom hC₁ hC₂ hKtail (fun j n => hJf0 omega L j n)
    (fun j n => hJt0 omega L j n) (hpref omega hmem L hL) (hpret omega hmem L hL)
    (huglyf omega hmem L hL) (huglyt omega hmem L hL)

end

end Algsuperdiff.Section4.Provider.Annular
