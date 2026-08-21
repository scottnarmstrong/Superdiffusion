/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateChain
import Algsuperdiff.Section4.Provider.Regularity.StepSixBoundaryIterationC1

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The outer collapse with the `H` leg kept -/

/-- **The clause-(B) bracket collapse on the boundary branch.**

`RootClauseBArith.rootClauseB_collapse` with `H ≠ 0`: the chain's data bracket
splits as `√σ̄_m^{-1}(W·G) + √σ̄_m(W·H)`, and the two dominations `W·G ≤
C_WG·L_g`, `W·H ≤ C_WH·L_h` carry it onto the printed three-leg bracket.

Pure arithmetic: every domination is a hypothesis, `Real.rpow` and `Real.sqrt`
are opaque throughout, and no estimate is derived. -/
theorem rootClauseB_collapse_boundary
    {E Kmain Kdata Ccol CdG CWG CWH CdM shomM gradLoc gradM dataG dataM
      W G H Lg Lh : ℝ}
    (hKmain : 0 ≤ Kmain) (hKdata : 0 ≤ Kdata) (hCcol : 0 ≤ Ccol)
    (hCWG : 0 ≤ CWG) (hCWH : 0 ≤ CWH) (hCdM : 0 ≤ CdM) (hE : 0 ≤ E)
    (hgradM : 0 ≤ gradM) (hLg : 0 ≤ Lg) (hLh : 0 ≤ Lh)
    (hWG0 : 0 ≤ W * G) (hWH0 : 0 ≤ W * H) (hdataM0 : 0 ≤ dataM)
    (hdataG : dataG ≤ CdG * Lg)
    (hWG : W * G ≤ CWG * Lg)
    (hWH : W * H ≤ CWH * Lh)
    (hdataM : dataM ≤ CdM * (Real.sqrt shomM⁻¹ * Lg))
    (h : gradLoc ≤
      Kmain * Real.rpow (3 : ℝ) E * (gradM + Real.sqrt shomM⁻¹ * dataG) +
        Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) *
          (Ccol *
            (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM)) :
    gradLoc ≤
      (Kmain * max 1 CdG + Kdata * (Ccol * CWG + Ccol * CWH + CdM)) *
        Real.rpow (3 : ℝ) E *
        (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
  have hSI : (0 : ℝ) ≤ Real.sqrt shomM⁻¹ := Real.sqrt_nonneg _
  have hS : (0 : ℝ) ≤ Real.sqrt shomM := Real.sqrt_nonneg _
  have hinv : (Real.sqrt shomM)⁻¹ = Real.sqrt shomM⁻¹ := (Real.sqrt_inv shomM).symm
  have hR : (0 : ℝ) ≤ Real.rpow (3 : ℝ) E := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hLegG : (0 : ℝ) ≤ Real.sqrt shomM⁻¹ * Lg := mul_nonneg hSI hLg
  have hLegH : (0 : ℝ) ≤ Real.sqrt shomM * Lh := mul_nonneg hS hLh
  have hT : (0 : ℝ) ≤ gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh := by
    linarith only [hgradM, hLegG, hLegH]
  -- the bracket, split
  have hbr : W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H) =
      Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H) := by
    rw [hinv]; ring
  rw [hbr] at h
  -- the two data legs against the printed bracket
  have hoscG : Real.sqrt shomM⁻¹ * (W * G) ≤
      CWG * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hstep : Real.sqrt shomM⁻¹ * (W * G) ≤ Real.sqrt shomM⁻¹ * (CWG * Lg) :=
      mul_le_mul_of_nonneg_left hWG hSI
    have hid : Real.sqrt shomM⁻¹ * (CWG * Lg) = CWG * (Real.sqrt shomM⁻¹ * Lg) := by
      ring
    have hgrow : CWG * (Real.sqrt shomM⁻¹ * Lg) ≤
        CWG * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) :=
      mul_le_mul_of_nonneg_left (by linarith only [hgradM, hLegH]) hCWG
    linarith only [hstep, hid, hgrow]
  have hoscH : Real.sqrt shomM * (W * H) ≤
      CWH * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hstep : Real.sqrt shomM * (W * H) ≤ Real.sqrt shomM * (CWH * Lh) :=
      mul_le_mul_of_nonneg_left hWH hS
    have hid : Real.sqrt shomM * (CWH * Lh) = CWH * (Real.sqrt shomM * Lh) := by ring
    have hgrow : CWH * (Real.sqrt shomM * Lh) ≤
        CWH * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) :=
      mul_le_mul_of_nonneg_left (by linarith only [hgradM, hLegG]) hCWH
    linarith only [hstep, hid, hgrow]
  have hdM : dataM ≤
      CdM * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hstep : CdM * (Real.sqrt shomM⁻¹ * Lg) ≤
        CdM * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) :=
      mul_le_mul_of_nonneg_left (by linarith only [hgradM, hLegH]) hCdM
    linarith only [hdataM, hstep]
  -- the gradient half
  have hgrad1 : Real.sqrt shomM⁻¹ * dataG ≤ CdG * (Real.sqrt shomM⁻¹ * Lg) := by
    have hstep : Real.sqrt shomM⁻¹ * dataG ≤ Real.sqrt shomM⁻¹ * (CdG * Lg) :=
      mul_le_mul_of_nonneg_left hdataG hSI
    have hid : Real.sqrt shomM⁻¹ * (CdG * Lg) = CdG * (Real.sqrt shomM⁻¹ * Lg) := by
      ring
    linarith only [hstep, hid]
  have hhalf1 : gradM + Real.sqrt shomM⁻¹ * dataG ≤
      max 1 CdG * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hpull := bracket_pull_weight (A := gradM) (L := Real.sqrt shomM⁻¹ * Lg)
      (W := CdG) hgradM hLegG
    have hmax : (1 : ℝ) ≤ max 1 CdG := le_max_left _ _
    have hgrow : max 1 CdG * (gradM + Real.sqrt shomM⁻¹ * Lg) ≤
        max 1 CdG * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) :=
      mul_le_mul_of_nonneg_left (by linarith only [hLegH]) (by linarith only [hmax])
    linarith only [hgrad1, hpull, hgrow]
  -- the data half
  have hhalf2 : Ccol * (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) +
        dataM ≤
      (Ccol * CWG + Ccol * CWH + CdM) *
        (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hstep := mul_le_mul_of_nonneg_left
      (show Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H) ≤
          CWG * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) +
            CWH * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) by
        linarith only [hoscG, hoscH]) hCcol
    have hexp : Ccol * (CWG * (gradM + Real.sqrt shomM⁻¹ * Lg +
            Real.sqrt shomM * Lh) +
          CWH * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh)) +
        CdM * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh)
        = (Ccol * CWG + Ccol * CWH + CdM) *
          (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by ring
    linarith only [hstep, hdM, hexp]
  -- the two halves, multiplied out
  have hbrNN : (0 : ℝ) ≤
      Ccol * (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) + dataM := by
    have hb : (0 : ℝ) ≤ Ccol *
        (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) :=
      mul_nonneg hCcol (by
        have h1 : (0 : ℝ) ≤ Real.sqrt shomM⁻¹ * (W * G) := mul_nonneg hSI hWG0
        have h2 : (0 : ℝ) ≤ Real.sqrt shomM * (W * H) := mul_nonneg hS hWH0
        linarith only [h1, h2])
    linarith only [hb, hdataM0]
  have hterm1 : Kmain * Real.rpow (3 : ℝ) E * (gradM + Real.sqrt shomM⁻¹ * dataG) ≤
      Kmain * max 1 CdG * Real.rpow (3 : ℝ) E *
        (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hstep := mul_le_mul_of_nonneg_left hhalf1 (mul_nonneg hKmain hR)
    calc Kmain * Real.rpow (3 : ℝ) E * (gradM + Real.sqrt shomM⁻¹ * dataG)
        ≤ Kmain * Real.rpow (3 : ℝ) E *
            (max 1 CdG *
              (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh)) := hstep
      _ = Kmain * max 1 CdG * Real.rpow (3 : ℝ) E *
            (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by ring
  have hterm2 : Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) *
        (Ccol * (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) +
          dataM) ≤
      Kdata * (Ccol * CWG + Ccol * CWH + CdM) * Real.rpow (3 : ℝ) E *
        (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hexp : Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) ≤
        Kdata * Real.rpow (3 : ℝ) E :=
      mul_le_mul_of_nonneg_left (rpow_three_threeQuarter_le hE) hKdata
    have hstep1 := mul_le_mul_of_nonneg_right hexp hbrNN
    have hstep2 := mul_le_mul_of_nonneg_left hhalf2 (mul_nonneg hKdata hR)
    calc Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) *
          (Ccol * (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) + dataM)
        ≤ Kdata * Real.rpow (3 : ℝ) E *
            (Ccol * (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) +
              dataM) := hstep1
      _ ≤ Kdata * Real.rpow (3 : ℝ) E *
            ((Ccol * CWG + Ccol * CWH + CdM) *
              (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh)) := hstep2
      _ = Kdata * (Ccol * CWG + Ccol * CWH + CdM) * Real.rpow (3 : ℝ) E *
            (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by ring
  have hsum : (Kmain * max 1 CdG + Kdata * (Ccol * CWG + Ccol * CWH + CdM)) *
        Real.rpow (3 : ℝ) E *
        (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) =
      Kmain * max 1 CdG * Real.rpow (3 : ℝ) E *
          (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) +
        Kdata * (Ccol * CWG + Ccol * CWH + CdM) * Real.rpow (3 : ℝ) E *
          (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by ring
  linarith only [h, hterm1, hterm2, hsum, hT]

/-! ## 2. The `(W, G, H)` presentation that carries the boundary datum -/

/-- **The boundary presentation of the `dataOsc` slot.**

`RootClauseBArith.edFinalDataG_eq_dataOsc_scaled` puts the interior data leg in
the chain's slot at `H = 0` and `W = 4C_δC_gag/(1-r₁)`.  The boundary leg cannot
join that presentation without dividing by `W`, so the slot is entered at `W = 1`
instead, with the whole interior leg moved into `G`:

```text
   edFinalDataG + dataH_∂  =  1 · ( σ̄_m^{-1}·(σ̄_m·edFinalDataG)  +  dataH_∂ ) .
```

A ring identity modulo `σ̄_m·σ̄_m^{-1} = 1`. -/
theorem edFinalDataG_add_boundary_eq_dataOsc {M : ABKModel d} (Cdel Kg Cgag : ℝ)
    (m : ℤ) (H : ℝ) :
    edFinalDataG M Cdel (Kg * Cgag) m + H =
      1 * (((Annealed.sigmaBar M m : ℝ))⁻¹ *
        ((Annealed.sigmaBar M m : ℝ) * edFinalDataG M Cdel (Kg * Cgag) m) + H) := by
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  rw [one_mul, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]

/-- **The `W·G` domination at the boundary presentation is an identity.**

`σ̄_m · edFinalDataG M C_δ (K_g C_gag) m = (4C_δC_gag/(1-r₁)) · 3^{m/2}K_g`:
the `σ̄_m^{-1}` of the Step-5 budget cancels against the `σ̄_m` introduced by
the presentation, leaving the printed datum `3^{m/2}K_g` at the budget's own
weight.  No estimate, no unit conversion. -/
theorem sigmaBar_mul_edFinalDataG_eq {M : ABKModel d} (Cdel Kg Cgag : ℝ) (m : ℤ) :
    (Annealed.sigmaBar M m : ℝ) * edFinalDataG M Cdel (Kg * Cgag) m =
      (edFinalDataOscW M Cdel * Cgag) * edFinalDataOscG Kg m := by
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hpow : Real.rpow (3 : ℝ) ((m : ℝ) / 2) = (3 : ℝ) ^ ((m : ℝ) / 2) := rfl
  rw [edFinalDataG, edFinalKgTop, edFinalDataOscW, edFinalDataOscG, hpow]
  field_simp

/-- The seam constant `C_WH = C_ah(1+C_gag)/(1-3^{-1/2}) + (4/log 3)·2C_bd`. -/
def boundaryCWH (d : ℕ) [NeZero d] (Cb C : ℝ) (k : ℕ) : ℝ :=
  edBoundaryCah d Cb C k * (1 + stepFourGagliardoConst d stepOneS) /
      (1 - stepFiveRatioH) +
    4 / Real.log 3 * (2 * edBoundaryCbd d Cb C k)

/-- **The unit-2 → unit-3 seam.**

```text
   dataH^print_∂ = ( C_ah(1+C_gag)/(1-3^{-1/2}) + (4/log 3)·2C_bd ) · 3^{m/2}K_h .
```

So the `hWH` slot of `rootClauseB_display_gate_boundaryC1` is met at that explicit
`C_WH`, with no estimate and no `σ̄`. -/
theorem edBoundaryDataHPrinted_eq_boundaryCWH_mul (d : ℕ) [NeZero d] (Cb C : ℝ)
    (k : ℕ) (Kh : ℝ) (m : ℤ) :
    edBoundaryDataHPrinted d Cb C k Kh m = boundaryCWH d Cb C k * edFinalDataOscG Kh m := by
  have hr : (0 : ℝ) < 1 - stepFiveRatioH := by linarith only [stepFiveRatioH_lt_one]
  have hpow : Real.rpow (3 : ℝ) ((m : ℝ) / 2) = (3 : ℝ) ^ ((m : ℝ) / 2) := rfl
  rw [edBoundaryDataHPrinted, boundaryCWH, edFinalDataOscG, hpow]
  field_simp

/-- The seam constant is nonnegative. -/
theorem boundaryCWH_nonneg (d : ℕ) [NeZero d] (Cb : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) : (0 : ℝ) ≤ boundaryCWH d Cb C k := by
  rw [boundaryCWH]
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hr : (0 : ℝ) < 1 - stepFiveRatioH := by linarith only [stepFiveRatioH_lt_one]
  have hgag : (0 : ℝ) ≤ stepFourGagliardoConst d stepOneS :=
    stepFourGagliardoConst_nonneg d stepOneS
  have h1 : (0 : ℝ) ≤ edBoundaryCah d Cb C k * (1 + stepFourGagliardoConst d stepOneS) /
      (1 - stepFiveRatioH) :=
    div_nonneg (mul_nonneg (edBoundaryCah_nonneg d Cb hC k) (by linarith only [hgag]))
      hr.le
  have h2 : (0 : ℝ) ≤ 4 / Real.log 3 * (2 * edBoundaryCbd d Cb C k) :=
    mul_nonneg (le_of_lt (div_pos (by norm_num) hlog))
      (by linarith only [edBoundaryCbd_nonneg d Cb hC k])
  linarith only [h1, h2]

/-! ## 3. The boundary prefactor -/

/-- **The clause-(A) boundary prefactor**: `rootClauseBPrefactor` with the extra
`√C_cmp·C_WH` charge of the `√σ̄_m` leg. -/
def rootClauseBBoundaryPrefactor (d : ℕ) [NeZero d]
    (Cch Ccacc Cosc CBc CB Ctr CWG CWH CdM : ℝ) : ℝ :=
  rootClauseBCg d Ccacc Cosc CBc * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) +
    rootClauseBCg d Ccacc Cosc CBc *
      (Real.sqrt 4 * CWG + Real.sqrt 4 * CWH + CdM)

/-! ## 4. The three-leg display at the gate -/

/-- **Clause (A) of the a.e. lattice display, at a free coarse scale, off the
printed interior gate, and WITH the printed `√σ̄_m·3^{m/2}K_h` leg.**

`rootClauseB_display_gate_freeCoarse` with the Step-7 chain's `H` slot
carrying the boundary Step-6 datum leg instead of `0`.  Every geometric binder,
every ellipticity record and every scale condition is the parent's, verbatim; the two
new inputs are the datum leg's nonnegativity and its printed domination
`dataH_∂ ≤ C_WH·3^{m/2}K_h`. -/
theorem rootClauseB_display_gate_boundaryC1 (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        ∀ (L : ℤ) {alpha : ℝ} {n m kc n' : ℤ} {z : Vec d}
          (omega : Cutoff.CutoffSample d)
          (uglob hdat : H1Function (openCubeSet (originCube d m)))
          {gsrc : Vec d → Vec d}
          {Khol Kh Kd CB CBc Cdel Cosc CdM CWH C1 delta Cest dataH : ℝ} {B : ℕ},
          (fun y => z + y) '' openCubeSet (originCube d kc) ⊆
            openCubeSet (originCube d m) → m ≤ m0 →
          n' ≤ m - 1 → n + 1 ≤ n' - 2 → n ≤ m →
          n' ≤ kc → kc ≤ m - 1 → m - (kc + 1) ≤ (B : ℤ) + 1 →
          Support.IsDirichletSolutionOn
              (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
              (originCube d m) uglob hdat gsrc →
          MemLp gsrc 2
              (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
          MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
              (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
          0 ≤ Khol → 0 ≤ Kh → 0 ≤ Kd → 0 ≤ CB → 0 ≤ CBc → 0 ≤ Cdel → 0 ≤ Cosc →
          0 ≤ CdM → 0 ≤ CWH → 0 ≤ dataH →
          2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 →
          delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
          (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
          StepSevenLambdaCaps (originCube d (kc + 1))
              (Support.fluxCorrectedCoeffFamily M L (kc + 1) (originCube d (kc + 1))
                (Cutoff.translateCutoffSample z omega))
              ((Annealed.sigmaBar M (kc + 1) : ℝ)) CB →
          StepSevenLambdaCaps (originCube d (n' + 1))
              (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
                (Cutoff.translateCutoffSample z omega))
              ((Annealed.sigmaBar M (n' + 1) : ℝ)) CBc →
          scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d kc)
              stepSevenCgS (fun x => -gsrc (x + z)) ≤
            Kd * edFinalDataOscG Khol m →
          stepSevenCaccDataM (originCube d n')
              (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
                (Cutoff.translateCutoffSample z omega))
              (fun x => -gsrc (x + z)) ≤
            CdM * (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
              edFinalDataOscG Khol m) →
          dataH ≤ CWH * edFinalDataOscG Kh m →
          ((3 : ℝ) ^ (-n') *
              normalizedL2On (truncatedWindow z m n')
                (fun x => uglob.toFun x -
                  volumeAverage (truncatedWindow z m n') uglob.toFun) ≤
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                ((3 : ℝ) ^ (-kc) *
                  normalizedL2On (truncatedWindow z m kc)
                    (fun x => uglob.toFun x -
                      volumeAverage (truncatedWindow z m kc) uglob.toFun)) +
              Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                (edFinalDataG M Cdel
                  (Khol * stepFourGagliardoConst d stepOneS) m + dataH)) →
          rootClauseBBoundaryPrefactor d Cch
              (stepSevenCaccConst Cc (originCube d n')
                (Support.fluxCorrectedCoeffFamily M L (n' + 1)
                  (originCube d (n' + 1)) (Cutoff.translateCutoffSample z omega)))
              Cosc CBc CB (rootClauseBTopCtr d Kd)
              (edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS) CWH CdM ≤
            Cest →
          Real.sqrt M.nu *
              normalizedL2On (truncatedWindow z m (n + 1))
                (fun y => Real.sqrt (vecNormSq (uglob.grad y)))
            ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
              (Real.sqrt M.nu *
                  normalizedL2On (openCubeSet (originCube d m))
                    (fun y => Real.sqrt (vecNormSq (uglob.grad y))) +
                Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol +
                Real.sqrt ((Annealed.sigmaBar M m : ℝ)) *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
  obtain ⟨Cch, Cc, hCch, hCc, hchain⟩ := exists_stepSevenEnd_chain_gate_of_dirichlet d
  refine ⟨Cch, Cc, hCch, hCc, ?_⟩
  intro M m0 Ecap hS hgamma L alpha n m kc n' z omega uglob hdat gsrc Khol Kh Kd CB CBc
    Cdel Cosc CdM CWH C1 delta Cest dataH B hgate hmm0 hn' hcore hnm hn'kc hkc hgapTop
    hsol hgL2 hgW hKhol hKh hKd hCB hCBc hCdel hCosc hCdM hCWH hdataH0 hC1 halpha0
    halpha1 hdelta hgap hbudget hcaps hcapsc hdataB hdataM hWH hosc hCest
  -- geometry at the re-cut coarse scale, from the gate alone
  have hgateN : (fun y => z + y) '' openCubeSet (originCube d n') ⊆
      openCubeSet (originCube d m) :=
    image_add_subset_openCubeSet_of_gate_le hn'kc hgate
  have hzm : z ∈ openCubeSet (originCube d m) := mem_openCubeSet_of_gate hgate
  have hWeq : truncatedWindow z m kc =
      (fun y => z + y) '' openCubeSet (originCube d kc) := by
    rw [truncatedWindow_eq_translateSet_of_gate hgate, image_add_eq_translateSet]
  have hTsub : (fun y => z + y) '' openCubeSet (originCube d kc) ⊆
      openCubeSet (originCube d m) := hgate
  have hTtop : volume ((fun y => z + y) '' openCubeSet (originCube d kc)) ≠ ⊤ :=
    volume_image_add_openCubeSet_ne_top z kc
  have hStop : volume (truncatedWindow z m kc) ≠ ⊤ :=
    (volume_truncatedWindow_lt_top z m kc).ne
  -- the solution object at the lattice centre, at the free flux pair
  obtain ⟨v, hval, hgradid, heqv⟩ :=
    exists_stepSevenCaccGateSolution (n' := kc) (mf := kc + 1) M L
      (originCube d (kc + 1)) omega hgate hsol
  have hgradE : forcedSolutionEnergyNorm (originCube d kc)
        (Support.fluxCorrectedCoeffFamily M L (kc + 1) (originCube d (kc + 1))
          (Cutoff.translateCutoffSample z omega))
        (⟨v, heqv⟩ : ForcedCubeSolution (originCube d kc)
          (Support.fluxCorrectedCoeffFamily M L (kc + 1) (originCube d (kc + 1))
            (Cutoff.translateCutoffSample z omega)) (fun x => -gsrc (x + z))) ≤
      rootClauseBTopKg d m kc *
        stepSevenNuGradNorm (M.nu : ℝ) (openCubeSet (originCube d m)) uglob.grad := by
    rw [forcedSolutionEnergyNorm_fluxCorrected_eq_nuGradNorm_gate M L (kc + 1) m kc
      (originCube d (kc + 1)) omega _ uglob.grad hgradid hgate]
    exact stepSevenNuGradNorm_window_le_cube_gate d (le_of_lt M.nu_pos) hgate uglob
  -- the two `σ̄` slots
  have hsigmaPos : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hsigmaCoarse : (0 : ℝ) < (Annealed.sigmaBar M (kc + 1) : ℝ) :=
    (Annealed.sigmaBar M (kc + 1)).2
  have htrShom : ((Annealed.sigmaBar M (kc + 1) : ℝ))⁻¹ ≤
      rootClauseBTopKs M.gamma m (kc + 1) * ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    rootClauseBTop_htrShom hS (by omega) hmm0
  have hcomp : (Annealed.sigmaBar M (n' + 1) : ℝ) ≤ 4 * (Annealed.sigmaBar M m : ℝ) :=
    sigmaBar_le_four_mul_sigmaBar M hS (by omega) hmm0
  -- the two `K_tr` dominations at the re-cut
  have hE : (0 : ℝ) ≤ stepSixExponent alpha n m := by
    have hc : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    rw [stepSixExponent]
    exact mul_nonneg (by linarith only [halpha1]) (by linarith only [hc])
  have hKgb := rootClauseBTop_hKgb (d := d) (Kd := Kd) (n := n) (m := m) (k := kc)
    (Bb := B) hgamma hC1 halpha0 halpha1 hnm hdelta hbudget (by omega) hgapTop
  have hKdb := rootClauseBTop_hKdb (d := d) (Kd := Kd) (n := n) (m := m) (k := kc)
    (Bb := B) hgamma hKd hC1 halpha0 halpha1 hnm hdelta hbudget (by omega) hgapTop
  have hCtr0 : (0 : ℝ) ≤ rootClauseBTopCtr d Kd := rootClauseBTopCtr_nonneg d Kd
  -- the `dataOsc` slot, at the boundary presentation `W = 1`
  have hW0 : (0 : ℝ) ≤ edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS :=
    mul_nonneg (edFinalDataOscW_nonneg hgamma hCdel) (stepFourGagliardoConst_nonneg d _)
  have hG0 : (0 : ℝ) ≤ edFinalDataOscG Khol m := edFinalDataOscG_nonneg hKhol m
  have hGpres : (0 : ℝ) ≤
      (Annealed.sigmaBar M m : ℝ) *
        edFinalDataG M Cdel (Khol * stepFourGagliardoConst d stepOneS) m := by
    rw [sigmaBar_mul_edFinalDataG_eq]
    exact mul_nonneg hW0 hG0
  have hoscChain := hosc
  rw [edFinalDataG_add_boundary_eq_dataOsc (M := M) Cdel Khol
      (stepFourGagliardoConst d stepOneS) m dataH,
    ← cubeScaleFactor_originCube_inv d kc] at hoscChain
  -- the chain
  have hmain := hchain M L (originCube d (n' + 1)) uglob hdat omega ⟨v, heqv⟩
    (Ccmp := 4) (Kg := rootClauseBTopKg d m kc) (Kd := Kd)
    (Ks := rootClauseBTopKs M.gamma m (kc + 1))
    (Ctr := rootClauseBTopCtr d Kd) (CB := CB) (CBc := CBc)
    (sigma := (Annealed.sigmaBar M (kc + 1) : ℝ))
    (sigmac := (Annealed.sigmaBar M (n' + 1) : ℝ))
    (shomM := (Annealed.sigmaBar M m : ℝ))
    (gradM := stepSevenNuGradNorm (M.nu : ℝ) (openCubeSet (originCube d m)) uglob.grad)
    (dataG := edFinalDataOscG Khol m) (W := 1)
    (G := (Annealed.sigmaBar M m : ℝ) *
      edFinalDataG M Cdel (Khol * stepFourGagliardoConst d stepOneS) m)
    (H := dataH) (C1 := C1) (delta := delta) (Cosc := Cosc)
    (B := B) hval hzm (by omega) (hWeq ▸ Set.Subset.refl _)
    (integrableOn_toFun_subset uglob (truncatedWindow_subset_domain z m kc) hStop)
    (integrableOn_sq_toFun_subset uglob (truncatedWindow_subset_domain z m kc) hStop)
    (integrableOn_toFun_subset uglob hTsub hTtop)
    (integrableOn_sq_toFun_subset uglob hTsub hTtop)
    (integrableOn_sub_sq_toFun_subset uglob hTsub hTtop _)
    hCB (rootClauseBTopKs_nonneg _ _ _) (by norm_num) hsigmaCoarse hsigmaPos
    (stepSevenNuGradNorm_nonneg _ _ _) hG0 zero_le_one hGpres hdataH0
    (forceBesovRegularity_stepSevenCacc_gate (n' := kc) hgate hgL2 hgW)
    hcaps hgradE hdataB htrShom hKgb hKdb hcomp hgateN hcore hsol hgL2 hgW hC1
    halpha0 halpha1 hnm hdelta hgap hbudget hCosc hCBc hcapsc hoscChain
  -- the outer collapse, with the `H` leg kept
  have hCgnn : (0 : ℝ) ≤ rootClauseBCg d
      (stepSevenCaccConst Cc (originCube d n')
        (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
          (Cutoff.translateCutoffSample z omega))) Cosc CBc := by
    have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have h3 : (0 : ℝ) ≤ Cosc * Real.sqrt (256 / 63 * CBc) + 1 := by
      have h4 := mul_nonneg hCosc (Real.sqrt_nonneg (256 / 63 * CBc))
      linarith only [h4]
    rw [rootClauseBCg]
    exact mul_nonneg (mul_nonneg h1 (stepSevenCaccConst_nonneg _ _ _)) h3
  have hXnn : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
      stepSevenBridgeConst stepSevenCgS *
      (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) *
      rootClauseBTopCtr d Kd := by
    have hb : (0 : ℝ) ≤ Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB) := by
      have h1 : (0 : ℝ) ≤ Cch * 64 := by linarith only [hCch]
      have h2 : (0 : ℝ) ≤ Real.sqrt (32 / 7 * CB) + 32 / 7 * CB := by
        have := Real.sqrt_nonneg (32 / 7 * CB)
        linarith only [this, hCB]
      exact mul_nonneg h1 h2
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)) hb) hCtr0
  have hKmain : (0 : ℝ) ≤ rootClauseBCg d
        (stepSevenCaccConst Cc (originCube d n')
          (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
            (Cutoff.translateCutoffSample z omega))) Cosc CBc * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) *
        rootClauseBTopCtr d Kd) :=
    mul_nonneg (mul_nonneg hCgnn (Real.sqrt_nonneg 4)) hXnn
  have hWGid : (1 : ℝ) * ((Annealed.sigmaBar M m : ℝ) *
        edFinalDataG M Cdel (Khol * stepFourGagliardoConst d stepOneS) m) ≤
      (edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS) *
        edFinalDataOscG Khol m := by
    rw [one_mul, sigmaBar_mul_edFinalDataG_eq]
  have hcoll := rootClauseB_collapse_boundary (CdG := 1)
    (Lg := edFinalDataOscG Khol m) (Lh := edFinalDataOscG Kh m)
    hKmain hCgnn (Real.sqrt_nonneg 4) hW0 hCWH hCdM hE
    (stepSevenNuGradNorm_nonneg _ _ _) hG0 (edFinalDataOscG_nonneg hKh m)
    (by rw [one_mul]; exact hGpres) (by rw [one_mul]; exact hdataH0)
    (stepSevenCaccDataM_nonneg _ _
      (forceBesovRegularity_stepSevenCacc_gate (n' := n') hgateN hgL2 hgW))
    (by rw [one_mul]) hWGid (by rw [one_mul]; exact hWH) hdataM hmain
  rw [max_self, mul_one] at hcoll
  -- into the root's own carrier and constant
  rw [stepSevenNuGradNorm_eq_sqrt_mul_normalizedL2On (le_of_lt M.nu_pos),
    stepSevenNuGradNorm_eq_sqrt_mul_normalizedL2On (le_of_lt M.nu_pos),
    stepSixExponent, edFinalDataOscG, edFinalDataOscG,
    ← mul_assoc (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹)
      (Real.rpow (3 : ℝ) ((m : ℝ) / 2)) Khol,
    ← mul_assoc (Real.sqrt ((Annealed.sigmaBar M m : ℝ)))
      (Real.rpow (3 : ℝ) ((m : ℝ) / 2)) Kh] at hcoll
  rw [rootClauseBBoundaryPrefactor] at hCest
  refine clauseB_const_mono (Real.rpow_pos_of_pos (by norm_num) _).le ?_ hCest hcoll
  have h1 : (0 : ℝ) ≤ Real.sqrt M.nu *
      normalizedL2On (openCubeSet (originCube d m))
        (fun y => Real.sqrt (vecNormSq (uglob.grad y))) :=
    mul_nonneg (Real.sqrt_nonneg _) (normalizedL2On_nonneg _ _)
  have h2 : (0 : ℝ) ≤ Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_pos_of_pos (by norm_num) _).le) hKhol
  have h3 : (0 : ℝ) ≤ Real.sqrt ((Annealed.sigmaBar M m : ℝ)) *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_pos_of_pos (by norm_num) _).le) hKh
  linarith only [h1, h2, h3]

/-! ## 5. The composition with the boundary Step 6 -/

/-- **The three-leg display at the gate, off the boundary Step 6.**

`rootClauseB_display_gate_boundaryC1` with its `hosc` slot instantiated at the
shape `StepSixBoundaryIterationC1.edFinal_oscillationHolderBound_boundaryC1`
produces — `dataG` at the boundary `δ`-constant `C_bd`, `dataH` at the printed
`dataH^print_∂` — and the `hWH` domination discharged by the seam identity. -/
theorem rootClauseB_display_gate_boundaryC1_ofStepSix (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        ∀ (L : ℤ) (Cb C : ℝ) (k : ℕ) {alpha : ℝ} {n m kc n' : ℤ} {z : Vec d}
          (omega : Cutoff.CutoffSample d)
          (uglob hdat : H1Function (openCubeSet (originCube d m)))
          {gsrc : Vec d → Vec d}
          {Khol Kh Kd CB CBc Cosc CdM C1 delta Cest : ℝ} {B : ℕ},
          (fun y => z + y) '' openCubeSet (originCube d kc) ⊆
            openCubeSet (originCube d m) → m ≤ m0 →
          n' ≤ m - 1 → n + 1 ≤ n' - 2 → n ≤ m →
          n' ≤ kc → kc ≤ m - 1 → m - (kc + 1) ≤ (B : ℤ) + 1 →
          Support.IsDirichletSolutionOn
              (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
              (originCube d m) uglob hdat gsrc →
          MemLp gsrc 2
              (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
          MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
              (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
          0 ≤ Khol → 0 ≤ Kh → 0 ≤ Kd → 0 ≤ CB → 0 ≤ CBc → 0 ≤ C → 0 ≤ Cosc →
          0 ≤ CdM →
          2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 →
          delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
          (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
          StepSevenLambdaCaps (originCube d (kc + 1))
              (Support.fluxCorrectedCoeffFamily M L (kc + 1) (originCube d (kc + 1))
                (Cutoff.translateCutoffSample z omega))
              ((Annealed.sigmaBar M (kc + 1) : ℝ)) CB →
          StepSevenLambdaCaps (originCube d (n' + 1))
              (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
                (Cutoff.translateCutoffSample z omega))
              ((Annealed.sigmaBar M (n' + 1) : ℝ)) CBc →
          scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d kc)
              stepSevenCgS (fun x => -gsrc (x + z)) ≤
            Kd * edFinalDataOscG Khol m →
          stepSevenCaccDataM (originCube d n')
              (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
                (Cutoff.translateCutoffSample z omega))
              (fun x => -gsrc (x + z)) ≤
            CdM * (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
              edFinalDataOscG Khol m) →
          ((3 : ℝ) ^ (-n') *
              normalizedL2On (truncatedWindow z m n')
                (fun x => uglob.toFun x -
                  volumeAverage (truncatedWindow z m n') uglob.toFun) ≤
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                ((3 : ℝ) ^ (-kc) *
                  normalizedL2On (truncatedWindow z m kc)
                    (fun x => uglob.toFun x -
                      volumeAverage (truncatedWindow z m kc) uglob.toFun)) +
              Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                (edFinalDataG M (edBoundaryCbd d Cb C k)
                    (Khol * stepFourGagliardoConst d stepOneS) m +
                  edBoundaryDataHPrinted d Cb C k Kh m)) →
          rootClauseBBoundaryPrefactor d Cch
              (stepSevenCaccConst Cc (originCube d n')
                (Support.fluxCorrectedCoeffFamily M L (n' + 1)
                  (originCube d (n' + 1)) (Cutoff.translateCutoffSample z omega)))
              Cosc CBc CB (rootClauseBTopCtr d Kd)
              (edFinalDataOscW M (edBoundaryCbd d Cb C k) *
                stepFourGagliardoConst d stepOneS) (boundaryCWH d Cb C k) CdM ≤
            Cest →
          Real.sqrt M.nu *
              normalizedL2On (truncatedWindow z m (n + 1))
                (fun y => Real.sqrt (vecNormSq (uglob.grad y)))
            ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
              (Real.sqrt M.nu *
                  normalizedL2On (openCubeSet (originCube d m))
                    (fun y => Real.sqrt (vecNormSq (uglob.grad y))) +
                Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol +
                Real.sqrt ((Annealed.sigmaBar M m : ℝ)) *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
  obtain ⟨Cch, Cc, hCch, hCc, hdisp⟩ := rootClauseB_display_gate_boundaryC1 d
  refine ⟨Cch, Cc, hCch, hCc, ?_⟩
  intro M m0 Ecap hS hgamma L Cb C k alpha n m kc n' z omega uglob hdat gsrc Khol Kh Kd
    CB CBc Cosc CdM C1 delta Cest B hgate hmm0 hn' hcore hnm hn'kc hkc hgapTop hsol
    hgL2 hgW hKhol hKh hKd hCB hCBc hC hCosc hCdM hC1 halpha0 halpha1 hdelta hgap
    hbudget hcaps hcapsc hdataB hdataM hosc hCest
  exact hdisp M m0 Ecap hS hgamma L omega uglob hdat hgate hmm0 hn' hcore hnm hn'kc hkc
    hgapTop hsol hgL2 hgW hKhol hKh hKd hCB hCBc (edBoundaryCbd_nonneg d Cb hC k) hCosc
    hCdM (boundaryCWH_nonneg d Cb hC k)
    (edBoundaryDataHPrinted_nonneg d Cb hC k hKh m) hC1 halpha0 halpha1 hdelta hgap
    hbudget hcaps hcapsc hdataB hdataM
    (le_of_eq (edBoundaryDataHPrinted_eq_boundaryCWH_mul d Cb C k Kh m)) hosc hCest


end

end Algsuperdiff.Section4.Provider.Regularity
