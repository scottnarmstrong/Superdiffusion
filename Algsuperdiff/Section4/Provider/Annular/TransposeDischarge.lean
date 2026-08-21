/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Annular.NegationSymmetry
import Algsuperdiff.Section4.Provider.Annular.SignLowDischarge

/-!
# The transposed ugly estimate, discharged by the `(J3)` symmetry

ABK26, Section 4.1, `p.mathcalE.annular.decomp`: the manuscript runs
`e.ugly.estimate.for.J` a second time for the transposed field and asserts the
same right-hand side.

This module formalizes exactly that argument.  Write `N ω = −ω` for the proved
negation of the whole shell sequence on the genuine lower-tail carrier
(`Cutoff.negateCutoffSample`).  Then:

1. `a_L(Nω) = a_L(ω)ᵀ` — the proved `(J3)` carrier identity
   `Cutoff.coefficientCutoff_negateCutoffSample_eq_adjoint`, itself a
   consequence of the proved skewness of the genuine lower-infinite cutoff;
2. the flux-correction constant `(k_L − k_m)_{□_m}` is linear in the shell
   fields, so it changes sign under `N` (`fluxIncrementAverage_negateCutoffSample`),
   and therefore `ã_{L,m}(Nω) = ã_{L,m}(ω)ᵀ` pointwise
   (`fluxCorrectedField_negateCutoffSample`);
3. every shell-norm-built slot is literally `N`-invariant, and the two
   variational slots (`λ_{γ,2}` and `𝓔_{s,2,2}`) are `N`-invariant because the
   skew part drops out of the coarse quadratic form
   (`NegationSymmetry.lean`, `TransposeError.lean`);
4. consequently the transposed `J`-leg at `ω` **is** the field `J`-leg at `Nω`
   (`jLegField_negateCutoffSample`), and the ugly estimate for the transposed
   field at `ω` **is** the proved field-side ugly estimate
   (`exists_uglyJEstimate_annulus_of_eventG1`) evaluated at `Nω`.

The ugly estimate itself is never re-proved: it is *transported*.  And the
transport is **deterministic** — the ruled "same law" is not consumed.  Every
step above is a pointwise identity on the carrier, so the transposed estimate
holds at each individual sample, not merely in law; the proved
`Cutoff.map_negateCutoffSample_cutoffSampleLaw` is not used.  The only
almost-sure input is the atom-versus-representative reconciliation
`annularErrorAtomMax_ae_le_annularErrorLatticeMax`, which the field-side leg of
`exists_clauseOne_final_four` already consumes at the same place.

## The payoff

`exists_clauseOne_final_two` is `SignLowDischarge.exists_clauseOne_final_four`
with **both** the `huglyt` slot and the `hpret` slot gone, and with the
transposed response family `Jannt` no longer a free variable: it is the
concrete `fun ω L ↦ annularResponseMax M L m (N ω)`, which
`annularResponseMax_negateCutoffSample` identifies with the manuscript's own
transposed annulus maximum `annularResponseMaxTranspose M L m ω` — so this is a
transcription, not a substitution.  The endpoint's remaining mathematical
inputs are exactly **two**: `hlam` and `hpref` (the Step-1 leg).

## Why the endpoint is re-run rather than composed

`exists_clauseOne_final_four` binds `huglyt` *pointwise* on the good event,
whereas the atom-versus-representative reconciliation
`annularErrorAtomMax_ae_le_annularErrorLatticeMax` is only almost sure.  The
transposed estimate therefore has to be produced **inside** the
`filter_upwards` of the display, exactly where the field-side estimate already
is.

## References

* ABK26, (`ã_{L,m}`), (the transposed ugly estimate).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open Homogenization Homogenization.Book Homogenization.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Localization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the flux-corrected field transposes under `N` -/

/-- **The cube-averaged flux increment changes sign under `N`.**  It is linear in
the shell fields; equivalently, it is the transpose of itself at `ω`, and it is
antisymmetric. -/
theorem fluxIncrementAverage_negateCutoffSample (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    Support.fluxIncrementAverage M L m Q (Cutoff.negateCutoffSample omega) =
      -Support.fluxIncrementAverage M L m Q omega := by
  funext i j
  have hentry : ∀ (k : ℤ) (x : Vec d),
      Cutoff.coefficientCutoff M.nu k (Cutoff.negateCutoffSample omega) x i j =
        Cutoff.coefficientCutoff M.nu k omega x j i := by
    intro k x
    have hx := congrArg (fun a : RegCoeffField d => a x)
      (Cutoff.coefficientCutoff_negateCutoffSample_eq_adjoint (d := d) M.nu k omega)
    change Cutoff.coefficientCutoff M.nu k (Cutoff.negateCutoffSample omega) x =
      adjointReg (Cutoff.coefficientCutoff M.nu k omega) x at hx
    rw [hx, adjointReg_apply]
    rfl
  have hfun : (fun x : Vec d =>
        Cutoff.coefficientCutoff M.nu L (Cutoff.negateCutoffSample omega) x i j -
          Cutoff.coefficientCutoff M.nu m (Cutoff.negateCutoffSample omega) x i j)
      = fun x : Vec d =>
        Cutoff.coefficientCutoff M.nu L omega x j i -
          Cutoff.coefficientCutoff M.nu m omega x j i := by
    funext x
    rw [hentry L x, hentry m x]
  have hstep : Support.fluxIncrementAverage M L m Q
      (Cutoff.negateCutoffSample omega) i j =
      Support.fluxIncrementAverage M L m Q omega j i := by
    rw [Support.fluxIncrementAverage_apply, Support.fluxIncrementAverage_apply, hfun]
  rw [hstep, Support.fluxIncrementAverage_skew]
  rfl

/-- **The flux-corrected coefficient transposes under `N`**, pointwise:
`ã_{L,m}(Nω)(x) = ã_{L,m}(ω)(x)ᵀ`.  The `a_L` leg transposes by the `(J3)`
carrier identity and the subtracted antisymmetric constant changes sign, which
is exactly what the transpose of the difference demands. -/
theorem fluxCorrectedField_negateCutoffSample (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    Support.fluxCorrectedField M L m Q (Cutoff.negateCutoffSample omega) x =
      matTranspose (Support.fluxCorrectedField M L m Q omega x) := by
  have hx := congrArg (fun a : RegCoeffField d => a x)
    (Cutoff.coefficientCutoff_negateCutoffSample_eq_adjoint (d := d) M.nu L omega)
  have hx' : Cutoff.coefficientCutoff M.nu L (Cutoff.negateCutoffSample omega) x =
      matTranspose (Cutoff.coefficientCutoff M.nu L omega x) := by
    change Cutoff.coefficientCutoff M.nu L (Cutoff.negateCutoffSample omega) x =
      adjointReg (Cutoff.coefficientCutoff M.nu L omega) x at hx
    rw [hx, adjointReg_apply]
    rfl
  have hC := matTranspose_fluxIncrementAverage M L m Q omega
  have hT : ∀ A B : Mat d, matTranspose (A - B) = matTranspose A - matTranspose B := by
    intro A B
    funext i j
    simp [matTranspose, Matrix.sub_apply]
  rw [Support.fluxCorrectedField_apply, Support.fluxCorrectedField_apply,
    fluxIncrementAverage_negateCutoffSample, hx', hT, hC]

/-- The flux-corrected triadic family at `Nω` is the adjoint family at `ω`. -/
theorem fluxCorrectedCoeffFamily_negateCutoffSample_aeEq (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    Ch02.TriadicCoeffFamily.AEEq
      (Support.fluxCorrectedCoeffFamily M L m Q (Cutoff.negateCutoffSample omega))
      (adjointFamily (Support.fluxCorrectedCoeffFamily M L m Q omega)) := by
  intro R
  refine Filter.Eventually.of_forall fun x => ?_
  show Support.fluxCorrectedRegField M L m Q (Cutoff.negateCutoffSample omega) x =
    matTranspose (Support.fluxCorrectedRegField M L m Q omega x)
  rw [Support.fluxCorrectedRegField_apply, Support.fluxCorrectedRegField_apply]
  exact fluxCorrectedField_negateCutoffSample M L m Q omega x

/-! ## Part B -- the two `J`-legs are exchanged by `N` -/

/-- The scalar response maximum depends on the coefficient object only through
its almost-everywhere class. -/
theorem scalarResponseMax_congr_aeeq {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (sigma : Observable.PositiveScalar) :
    scalarResponseMax a sigma = scalarResponseMax b sigma := by
  unfold scalarResponseMax scalarResponseSet
  refine congrArg sSup (Set.ext fun x => ?_)
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, responseJ_eq_ofAEEq h _ _⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, responseJ_eq_ofAEEq h.symm _ _⟩

theorem jLegField_negateCutoffSample [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (n : ℤ) :
    jLegField M L m (Cutoff.negateCutoffSample omega) n =
      jLegTranspose M L m omega n := by
  unfold jLegField jLegTranspose
  refine congrArg _ (funext fun v => ?_)
  exact scalarResponseMax_congr_aeeq
    (fluxCorrectedCoeffFamily_negateCutoffSample_aeEq M L m (originCube d m) omega
      (latticeCube n v))
    (Annealed.sigmaBar M m)

/-- Function form of `jLegField_negateCutoffSample`, as the `hpret` slot reads
it. -/
theorem jLegField_negateCutoffSample_funext [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    jLegField M L m (Cutoff.negateCutoffSample omega) = jLegTranspose M L m omega :=
  funext (jLegField_negateCutoffSample M L m omega)

/-! ## Part B' -- the transposed annulus response family -/

/-- **The manuscript's transposed annulus `J`-maximum**: the same annulus maximum
as `annularResponseMax`, read at the *transposed* coefficient object
`ã_{L,m}ᵀ`. -/
def annularResponseMaxTranspose (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) : ℝ :=
  Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1)) fun v =>
    scalarResponseMax
      ((subConstCutoffTriadicCoeffFamily M L
        (Support.fluxIncrementAverage M L m (originCube d m) omega)
        (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
        omega).coeffOn (⟨n, v⟩ : TriadicCube d)).transpose
      (Annealed.sigmaBar M m)

/-- `ã_{L,m}` at `Nω` is `ã_{L,m}ᵀ` at `ω`, as a field identity. -/
theorem subConstCutoffField_negateCutoffSample (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    subConstCutoffField M L
        (Support.fluxIncrementAverage M L m Q (Cutoff.negateCutoffSample omega))
        (Cutoff.negateCutoffSample omega) x =
      matTranspose (subConstCutoffField M L
        (Support.fluxIncrementAverage M L m Q omega) omega x) := by
  have hx := congrArg (fun a : RegCoeffField d => a x)
    (Cutoff.coefficientCutoff_negateCutoffSample_eq_adjoint (d := d) M.nu L omega)
  have hx' : Cutoff.coefficientCutoff M.nu L (Cutoff.negateCutoffSample omega) x =
      matTranspose (Cutoff.coefficientCutoff M.nu L omega x) := by
    change Cutoff.coefficientCutoff M.nu L (Cutoff.negateCutoffSample omega) x =
      adjointReg (Cutoff.coefficientCutoff M.nu L omega) x at hx
    rw [hx, adjointReg_apply]
    rfl
  have hC := matTranspose_fluxIncrementAverage M L m Q omega
  have hT : ∀ A B : Mat d, matTranspose (A - B) = matTranspose A - matTranspose B := by
    intro A B
    funext i j
    simp [matTranspose, Matrix.sub_apply]
  rw [subConstCutoffField_apply, subConstCutoffField_apply,
    fluxIncrementAverage_negateCutoffSample, hx', hT, hC]

/-- **`Jannt` is the manuscript's transposed object.**  The annulus response
maximum at the negated sample is exactly the transposed annulus response
maximum at the sample; this is what makes the discharge below a transcription
rather than a substitution. -/
theorem annularResponseMax_negateCutoffSample [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) :
    annularResponseMax M L m (Cutoff.negateCutoffSample omega) j n =
      annularResponseMaxTranspose M L m omega j n := by
  unfold annularResponseMax annularResponseMaxTranspose
  refine congrArg _ (funext fun v => ?_)
  refine scalarResponseMax_congr_aeeq ?_ (Annealed.sigmaBar M m)
  refine Filter.Eventually.of_forall fun x => ?_
  exact subConstCutoffField_negateCutoffSample M L m (originCube d m) omega x

/-! ## Part C -- the two-slot clause-(i) endpoint -/

/-- **The clause-(i) endpoint at two remaining slots.**

The remaining inputs are exactly

* the printed ranges `s ≤ 1/4`, `8γ ≤ s`, `c⋆⁴ ≤ 6`, `1 ≤ |log γ|` and the
  standing regime `γ ≤ C_shom^{−10} c⋆^{10}`;
* the typing nondegeneracies `0 < C₁`, `0 < C`, `0 ≤ C_l` and the constant
  inequality fixing `C`; **and**
* the two mathematical obligations `hlam` and `hpref` (the Step-1 leg).

Nothing else is assumed. -/
theorem exists_clauseOne_final_two (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Cs Cshom : ℝ, 0 < Cs ∧ 6 ≤ Cshom ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (Cshom ^ (10 : ℕ))⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ (Ccg : ℝ) (m : ℤ) (s : {s : ℝ // 0 < s}),
          (s : ℝ) ≤ 1 / 4 → 8 * M.gamma ≤ (s : ℝ) → Disorder.cstar M ^ 4 ≤ 6 →
          1 ≤ |Real.log M.gamma| →
        ∀ C₁ Cl C : ℝ,
          0 < C₁ → 0 < C → 0 ≤ Cl →
          Cs * (1 + 196 * Cl) ^ 2 * 4 * (1 + Cl)
              + 16 * Cs * (1 + 196 * Cl) ^ 2 * Cl * (1 + centeringConst d ^ 2)
              + 4 * Cs * (1 + 4 * Cl ^ 2) ≤ C →
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
  intro M hreg Ccg m s hs14 hsg hcstar4 hlog C₁ Cl C hC₁ hC0 hCl hCconst hlam hpref
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
  have hsignlow : ∀ n : ℤ, n ≤ m - 1 →
      1 / 4 * ((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)
          * (3 : ℝ) ^ (M.gamma * (n : ℝ)))
        ≤ (Annealed.sigmaBar M (n - 2) : ℝ) := fun n hn =>
    sigmaBar_sub_two_lower_quarter_of_inductionState M (hSall m) (by omega)
  -- the `(J3)` symmetry: the good event is invariant under whole-sequence negation
  have hmemN : ∀ omega ∈ Support.eventG0 M Ccg m ∩
      Support.eventG1 M m (s : ℝ)
        (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
      Cutoff.negateCutoffSample omega ∈ Support.eventG0 M Ccg m ∩
        Support.eventG1 M m (s : ℝ)
          (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) := by
    intro omega hmem
    exact ⟨(mem_eventG0_negateCutoffSample_iff M Ccg m omega).2 hmem.1,
      (mem_eventG1_negateCutoffSample_iff M m (s : ℝ) _ omega).2 hmem.2⟩
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
    have hpretN := hpref (Cutoff.negateCutoffSample omega) (hmemN omega hmem) L hL
    rw [jLegField_negateCutoffSample_funext M L m omega] at hpretN
    refine clauseOne_bound_final M L m s omega hs1 hsg hcstar4 hlog hmem.2
      (summable_annFam_error_of_clauseOneTermOne_ne_top M m s omega hfin)
      hC6 hshom hC₁.le hC0.le
      (fun j n => annularResponseMax_nonneg M L m (Cutoff.negateCutoffSample omega) j n)
      (hpref omega hmem L hL) hpretN ?_ ?_
    · -- the field leg
      intro j n hjm hnj
      refine isUglyJEstimate_mono_E2 hC0.le (Real.rpow_nonneg (by norm_num) _)
        (hae j n hnj) ?_
      exact hugly M m L m E omega (s : ℝ) Cl C (hSall m) le_rfl hL s.2 hs14 hsg
        hmem.2 hCl (hlam omega hmem) hsignlow hCconst j n hjm hnj
    · -- the transposed leg: the field leg at the negated sample
      intro j n hjm hnj
      have hraw := hugly M m L m E (Cutoff.negateCutoffSample omega) (s : ℝ) Cl C
        (hSall m) le_rfl hL s.2 hs14 hsg (hmemN omega hmem).2 hCl
        (hlam (Cutoff.negateCutoffSample omega) (hmemN omega hmem)) hsignlow hCconst
        j n hjm hnj
      rw [annularErrorAtomMax_negateCutoffSample,
        annularL2Block_negateCutoffSample, annularGradBlock_negateCutoffSample,
        gradTailSq_negateCutoffSample] at hraw
      exact isUglyJEstimate_mono_E2 hC0.le (Real.rpow_nonneg (by norm_num) _)
        (hae j n hnj) hraw
  have hdisplay := clauseOne_representative_display_dichotomy M m s
    (Support.eventG0 M Ccg m ∩
      Support.eventG1 M m (s : ℝ)
        (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
    (C := clauseOneOutConstant C₁ C 2 Cshom)
    (clauseOneOutConstant_pos hC₁ hC0 (by norm_num) hC6) hbound
  filter_upwards [hdisplay] with omega hom
  rwa [clauseOneDisplayRhs_eq] at hom

/-- **Clause (ii) off the two-slot display.**  Unchanged from
`SignLowDischarge.clauseTwo_of_final_four_display`; stated here so that the
two-slot endpoint carries its own clause-(ii) consumer. -/
theorem clauseTwo_of_final_two_display [NeZero d] (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
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
  clauseTwo_of_final_four_display M Ccg m s hC0 hep hsep hsmall hdisp

end

end Algsuperdiff.Section4.Provider.Annular
