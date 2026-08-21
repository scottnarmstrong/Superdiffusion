/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Annular.ClauseTwo
import Algsuperdiff.Section4.Provider.Annular.FinalStitch

/-!
# The clause-(i) endpoint with `huglyf` stitched in

`ClauseOneHonestEvent.exists_clauseOne_honest_display` reduced clause (i) to the
four slots `hpref`, `hpret`, `huglyf`, `huglyt` at the honest event
`𝒢₀(m) ∩ 𝒢₁(m; s, √c⋆ γ^{−1/2})`.  `FinalStitch` produces the `huglyf` slot from
the lattice chain, at the annulus family `annularResponseMax`.  This module
runs the composition, so that the endpoint's remaining inputs are

* `hpref`, `hpret`, `huglyt` — three hypotheses left as binders, unchanged;
  **and**
* `hlam`, `hsignlow` — the two obligations `FinalStitch` does not discharge (at
  the relaxed constant `¼`; see `FinalStitch` and `SigmaBarBudget`).
  `SignLowDischarge` removes `hsignlow` from this list.

Three differences from `exists_clauseOne_honest_display`, all forced by the
producer:

1. `K_tail = 2` and `gradNf = 2 · annularGradBlock` (so `K_gn = 162`).  The
   lattice chain's fourth slot is the gauge of the *whole* increment `k_L −
   k_{n−2}`, and splitting it at `m` costs `(X+Y)² ≤ 2X² + 2Y²`; no choice of
   `K_tail` makes the coefficient of `annularGradBlock` equal to `1`.  The
   output constant is unaffected: `clauseOneOutConstant C₁ C_shom` still
   dominates `2 C_leg (4608 K_l2 + 576 K_gn)` because `C_shom ≥ 6`.
2. `Jannf` is *pinned* to `annularResponseMax`, so `hpref` becomes a comparison
   of `jLegField` with a family of the same shape (a lattice maximum of
   `scalarResponseMax`).
3. The `(2,2)` slot is bridged from the literal atom to the measurable
   observable by `annularErrorAtomMax_ae_le_annularErrorLatticeMax`, one a.e.
   step at the display level — which is where the display already lives.
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

/-! ## Part A -- the atom-to-observable bridge for the `(2,2)` slot -/

/-- **The reconciliation.**  The annulus maximum of the *literal* `(2,2)` error
atom is almost surely below the annulus maximum of the measurable observable —
indeed the two agree a.s.  The null set is the representative-choice set of
the `𝒢₂` lane, taken over the countable family of scales and lattice indices. -/
theorem annularErrorAtomMax_ae_le_annularErrorLatticeMax [NeZero d] (M : ABKModel d)
    (s : {s : ℝ // 0 < s}) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ j n : ℤ, n ≤ j - 1 →
        annularErrorAtomMax M (s : ℝ) omega j n
          ≤ annularErrorLatticeMax M s omega j n := by
  classical
  have hpt : ∀ p : ℤ × (Fin d → ℤ),
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        Support.annularErrorAtom M p.1 (s : ℝ)
            (Cutoff.translateCutoffSample
              (Support.triadicLatticePoint p.1 p.2) omega)
          = Support.annularErrorObservable M p.1 s
            (Cutoff.translateCutoffSample
              (Support.triadicLatticePoint p.1 p.2) omega) := by
    intro p
    exact (GoodEvents.measurePreserving_translateCutoffSample M
        (Support.triadicLatticePoint p.1 p.2)).quasiMeasurePreserving.ae_eq_comp
      (Support.annularErrorAtom_ae_eq_annularErrorObservable M p.1 s)
  rw [← MeasureTheory.ae_all_iff] at hpt
  filter_upwards [hpt] with omega hom
  intro j n hnj
  rw [annularErrorAtomMax]
  refine Proportion.fmax_le (annularErrorLatticeMax_nonneg M s omega j n) ?_
  intro v hv
  have hvset : v ∈ Support.latticeAnnulusSet d n j (j - 1) :=
    (Proportion.mem_latticeAnnulusFinset_iff (by omega)).mp hv
  rw [hom (n, v)]
  exact le_annularErrorLatticeMax M s omega (by omega : n ≤ j) hvset

/-! ## Part B -- the summability of the doubled gradient family -/

/-- The `hsumG` binder at the doubled head-block gradient family. -/
theorem summable_annFam_two_annularGradBlock_of_eventG1 (M : ABKModel d) (m : ℤ)
    {s T : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hT : 0 ≤ T)
    {omega : Cutoff.CutoffSample d} (homega : omega ∈ Support.eventG1 M m s T) :
    Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
      * (2 * annularGradBlock M m omega j n))) := by
  classical
  have hbase := (summable_annFam_annularGradBlock_of_eventG1 M m hs0 hs1 hT
    homega).mul_left 2
  refine hbase.congr fun p => ?_
  show (2 : ℝ) * annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
      * annularGradBlock M m omega j n) p
    = annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
      * (2 * annularGradBlock M m omega j n)) p
  unfold annFam
  split_ifs with h
  · ring
  · ring

/-! ## Part C -- the clause-(i) composite at the lattice-chain pinning -/

/-- **The clause-(i) composite with `Jannf` pinned and `K_tail = 2`.**  This is
`ClauseOneHonestEvent.clauseOne_bound_of_eventG1` re-run at the pinning the
lattice chain produces: `gradNf = 2 · annularGradBlock`, `K_gn = 162`,
`K_tail = 2`, `Jannf = annularResponseMax`.  The output constant is the same
`clauseOneOutConstant`. -/
theorem clauseOne_bound_final [NeZero d] (M : ABKModel d) (L m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d)
    (hs1 : (s : ℝ) ≤ 1) (hsg : 8 * M.gamma ≤ (s : ℝ))
    (hcstar4 : Disorder.cstar M ^ 4 ≤ 6) (hlog : 1 ≤ |Real.log M.gamma|)
    (hG1 : omega ∈ Support.eventG1 M m (s : ℝ)
      (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
    (hsumE : Summable (annFam m (fun j n => (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
      * annularErrorLatticeMax M s omega j n)))
    {Cshom : ℝ} (hCshom : 6 ≤ Cshom)
    (hshom : ∀ n : ℤ, n ≤ m - 1 →
      ((Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2
        ≤ (Cshom * M.gamma * ((m - n : ℤ) : ℝ)
            + Cshom * (2 * M.gamma
              + (Disorder.cstar M ^ 2)⁻¹ * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2
          * (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ)))
    {Jannt : ℤ → ℤ → ℝ} {C₁ C : ℝ} (hC₁ : 0 ≤ C₁) (hC0 : 0 ≤ C)
    (hJannt0 : ∀ j n, 0 ≤ Jannt j n)
    (hpref : IsAnnularDecompPre (s : ℝ) m (jLegField M L m omega)
      (annularResponseMax M L m omega) C₁)
    (hpret : IsAnnularDecompPre (s : ℝ) m (jLegTranspose M L m omega) Jannt C₁)
    (huglyf : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      IsUglyJEstimate (annularResponseMax M L m omega j n)
        (annularErrorLatticeMax M s omega j n)
        (((Annealed.sigmaBar M m : ℝ) *
          ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
        (annularL2Block M m omega j n)
        (2 * annularGradBlock M m omega j n + 2 * gradTailSq M m omega)
        (gradTailSq M m omega) (Disorder.cstar M) M.gamma
        ((3 : ℝ) ^ ((s : ℝ) * ((m - n : ℤ) : ℝ)))
        ((3 : ℝ) ^ (((s : ℝ) + M.gamma) * ((m - n : ℤ) : ℝ))) C)
    (huglyt : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      IsUglyJEstimate (Jannt j n)
        (annularErrorLatticeMax M s omega j n)
        (((Annealed.sigmaBar M m : ℝ) *
          ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
        (annularL2Block M m omega j n)
        (2 * annularGradBlock M m omega j n + 2 * gradTailSq M m omega)
        (gradTailSq M m omega) (Disorder.cstar M) M.gamma
        ((3 : ℝ) ^ ((s : ℝ) * ((m - n : ℤ) : ℝ)))
        ((3 : ℝ) ^ (((s : ℝ) + M.gamma) * ((m - n : ℤ) : ℝ))) C) :
    IsClauseOneBound (Support.fluxCorrectedError M L m (s : ℝ) omega ^ 2)
      (annDouble m (fun j n => (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
        * annularErrorLatticeMax M s omega j n))
      (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) (gradTailSq M m omega)
      (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ))
        * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2)
      (s : ℝ) (Disorder.cstar M) M.gamma
      (clauseOneOutConstant C₁ C 2 Cshom) := by
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hT0 : (0 : ℝ) ≤ Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ :=
    (annularEventAmplitude_pos M).le
  have hCshom0 : (0 : ℝ) ≤ Cshom := by linarith only [hCshom]
  have ha0 : (0 : ℝ) ≤ Cshom * M.gamma := mul_nonneg hCshom0 hgam0.le
  have hB0 : (0 : ℝ) ≤ Cshom * (2 * M.gamma
      + (Disorder.cstar M ^ 2)⁻¹ * (M.gamma * |Real.log M.gamma| ^ 2)) := by
    have h1 : (0 : ℝ) ≤ 2 * M.gamma := by linarith only [hgam0]
    have h2 : (0 : ℝ) ≤ (Disorder.cstar M ^ 2)⁻¹
        * (M.gamma * |Real.log M.gamma| ^ 2) :=
      mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (mul_nonneg hgam0.le (sq_nonneg _))
    exact mul_nonneg hCshom0 (by linarith only [h1, h2])
  -- the constant bookkeeping at `Cbf = 1`, `Kl2 = 1`, `Kgn = 162`, `Ktail = 2`
  have hCleg0 : (0 : ℝ) ≤ clauseOneLegConstant C₁ C 2 :=
    clauseOneLegConstant_nonneg hC₁ hC0 (by norm_num)
  have hCleg2 : (0 : ℝ) ≤ 2 * clauseOneLegConstant C₁ C 2 := by
    linarith only [hCleg0]
  have hCs2 : (36 : ℝ) ≤ Cshom ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) hCshom 2
    calc (36 : ℝ) = (6 : ℝ) ^ 2 := by norm_num
      _ ≤ Cshom ^ 2 := h
  have hbig : (252000 : ℝ) ≤ 7000 * Cshom ^ 2 := by linarith only [hCs2]
  have hCleg : 24 * 1 * C₁ * ((1 + 2) * C) ≤ clauseOneLegConstant C₁ C 2 := by
    refine le_of_eq ?_
    unfold clauseOneLegConstant
    ring
  have hCout1 : 2 * clauseOneLegConstant C₁ C 2
      ≤ clauseOneOutConstant C₁ C 2 Cshom := by
    unfold clauseOneOutConstant
    calc 2 * clauseOneLegConstant C₁ C 2
        = 2 * clauseOneLegConstant C₁ C 2 * 1 := (mul_one _).symm
      _ ≤ 2 * clauseOneLegConstant C₁ C 2 * (7000 * Cshom ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith only [hbig]) hCleg2
  have hCout2 : 2 * clauseOneLegConstant C₁ C 2 * (7000 * Cshom ^ 2)
      ≤ clauseOneOutConstant C₁ C 2 Cshom := le_of_eq rfl
  have hCout3 : 2 * clauseOneLegConstant C₁ C 2 * (4608 * 1 + 576 * 162)
      ≤ clauseOneOutConstant C₁ C 2 Cshom := by
    unfold clauseOneOutConstant
    have h51 : (4608 * 1 + 576 * 162 : ℝ) ≤ 7000 * Cshom ^ 2 := by
      have hval : (4608 * 1 + 576 * 162 : ℝ) = 97920 := by norm_num
      rw [hval]
      linarith only [hbig]
    exact mul_le_mul_of_nonneg_left h51 hCleg2
  exact clauseOne_bound M L m s.2 hs1 hsg omega
    (Jlegf := jLegField M L m omega) (Jlegt := jLegTranspose M L m omega)
    (Jannf := annularResponseMax M L m omega) (Jannt := Jannt)
    (E2 := fun j n => annularErrorLatticeMax M s omega j n)
    (sig := fun n => ((Annealed.sigmaBar M m : ℝ) *
      ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
    (L2f := annularL2Block M m omega)
    (gradNf := fun j n => 2 * annularGradBlock M m omega j n)
    (A := shellBlockLatticeReal M m omega)
    (Cbf := 1) (Kl2 := 1) (Kgn := 162) (Ktail := 2) (Cshom := Cshom)
    (by norm_num) hC₁ hC0 (by norm_num) (by norm_num) (by norm_num)
    (jLegField_nonneg M L m omega) (jLegTranspose_nonneg M L m omega)
    (annularResponseMax_nonneg M L m omega) hJannt0
    (fun j n => annularErrorLatticeMax_nonneg M s omega j n)
    (fun _n => sq_nonneg _)
    (annularL2Block_nonneg M m omega)
    (fun j n => by
      have h := annularGradBlock_nonneg M m omega j n
      linarith only [h])
    (hbfJ_latticeMax M L m omega le_rfl)
    (summable_jLegField M L m omega s.2) (summable_jLegTranspose M L m omega s.2)
    hpref hpret huglyf huglyt hsumE
    (summable_annFam_sig (a := Cshom * M.gamma)
      (B := Cshom * (2 * M.gamma
        + (Disorder.cstar M ^ 2)⁻¹ * (M.gamma * |Real.log M.gamma| ^ 2)))
      s.2 hs1 hgam0.le hsg ha0 hB0 (fun _n => sq_nonneg _) hshom)
    (summable_annFam_annularL2Block_of_eventG1 M m s.2 hs1 hsg hT0 hG1)
    (summable_annFam_two_annularGradBlock_of_eventG1 M m s.2 hs1 hT0 hG1)
    hcstar4 hlog hshom
    (summable_shellBlockLatticeReal_of_eventG1 M m s.2.le hG1)
    (fun j n hj hn => annularL2Block_le M m omega j n hj hn)
    (fun j n hj hn => by
      have hb := annularGradBlock_le M m omega j n hj hn
      have hid : (162 : ℝ) * (((m - n : ℤ) : ℝ) + 2)
            * ∑ v ∈ Finset.range ((m - n).toNat + 2),
              shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2
          = 2 * (81 * (((m - n : ℤ) : ℝ) + 2)
            * ∑ v ∈ Finset.range ((m - n).toNat + 2),
              shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2) := by ring
      rw [hid]
      linarith only [hb])
    hCleg hCout1 hCout2 hCout3

/-! ## Part D -- the endpoint -/

/-- **The clause-(i) endpoint with `huglyf` discharged.**

`ClauseOneHonestEvent.exists_clauseOne_honest_display` with its `huglyf` slot
supplied by the lattice chain (through `FinalStitch`), so that the remaining
inputs are exactly

* the printed ranges `s ≤ 1/4`, `8γ ≤ s`, `c⋆⁴ ≤ 6`, `1 ≤ |log γ|` and the
  standing regime `γ ≤ C_shom^{−10} c⋆^{10}`;
* the typing nondegeneracies `0 < C₁`, `0 < C`, `0 ≤ C_l`, `0 ≤ Jannt` and the
  constant inequality fixing `C`;
* the three hypotheses `hpref`, `hpret`, `huglyt`, left as binders here; **and**
* the two obligations `FinalStitch` does not close, `hsignlow` (at the relaxed
  constant `¼`, closed downstream in `SignLowDischarge`) and `hlam`.

The `s ≤ 1` of the honest-event endpoint is tightened to `s ≤ 1/4`: that is the
Section 2.4 window the ugly chain needs, carried honestly and never narrowed
silently. -/
theorem exists_clauseOne_final (d : ℕ) (dimension : 2 ≤ d) :
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
          (∀ n : ℤ, n ≤ m - 1 →
            1 / 4 * ((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)
                * (3 : ℝ) ^ (M.gamma * (n : ℝ)))
              ≤ (Annealed.sigmaBar M (n - 2) : ℝ)) →
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
    hJt0 hsignlow hlam hpref hpret huglyt
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

/-! ## Part E -- the clause-(ii) corollary -/

/-- **Clause (ii) off the honest-event clause-(i) display.**  The display is
restricted from `𝒢₀ ∩ 𝒢₁(m; s, √c⋆ γ^{−1/2})` to the manuscript's own
`e.lambda.good.events` by `goodEventBase_subset_annularEvent`, and then
`ClauseTwo.clauseTwo_of_clauseOne_display` fires unchanged. -/
theorem clauseTwo_of_final_display [NeZero d] (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
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
        ≤ ENNReal.ofReal (2 * Real.sqrt C * ep) := by
  refine clauseTwo_of_clauseOne_display M Ccg m s hC0 hep hsmall ?_
  filter_upwards [hdisp] with omega hom
  refine le_trans ?_ hom
  exact Set.indicator_le_indicator_of_subset
    (goodEventBase_subset_annularEvent M Ccg m s hep.1.le hsep)
    (fun _a => zero_le _) omega

end

end Algsuperdiff.Section4.Provider.Annular
