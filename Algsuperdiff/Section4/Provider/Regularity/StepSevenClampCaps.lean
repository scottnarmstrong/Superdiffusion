/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaSlots
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringSlot

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

private theorem isotropicComparator_eq_scalarMatrix_clamp (sigma : PositiveScalar) :
    isotropicComparatorMatrix (d := d) sigma = scalarMatrix (d := d) (sigma : ℝ) :=
  rfl

/-! ## 1. The two off-grid constants at the §4.4 pin -/

/-- **The off-grid stability constant at the upper ratio index.** `36 d (1/8) /
((1/8 − 1/32)(1 − 1/16)) = 51.2 d ≤ 96 d`. -/
theorem offGridStabilityConst_stepSevenUpper_le (d : ℕ) :
    offGridStabilityConst d (1 / 8) (1 / 32) ≤ 96 * (d : ℝ) := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hden : (0 : ℝ) < ((1 : ℝ) / 8 - 1 / 32) * (1 - 2 * (1 / 32)) := by norm_num
  rw [offGridStabilityConst, div_le_iff₀ hden]
  linarith only [hd]

/-- **The off-grid stability constant at the lower ratio index.** `36 d (1/16) /
((1/16 − 1/32)(1 − 1/16)) = 76.8 d ≤ 96 d`.  This is the index that measures
how much room the §4.4 pin leaves above the good-event slot: it is exactly twice
the slot, and the constant is finite. -/
theorem offGridStabilityConst_stepSevenLower_le (d : ℕ) :
    offGridStabilityConst d (1 / 16) (1 / 32) ≤ 96 * (d : ℝ) := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hden : (0 : ℝ) < ((1 : ℝ) / 16 - 1 / 32) * (1 - 2 * (1 / 32)) := by norm_num
  rw [offGridStabilityConst, div_le_iff₀ hden]
  linarith only [hd]

/-! ## 2. The pin's index identities -/

/-- The Caccioppoli's first exponent, halved, is the upper ratio index `1/8`. -/
theorem stepSevenCaccS_half_eq : stepSevenCaccS / 2 = 1 / 8 := by
  rw [stepSevenCaccS_eq]; norm_num

/-- The Caccioppoli's second exponent, halved, is the lower ratio index `1/16` —
strictly above the good-event slot `1/32`. -/
theorem stepSevenCaccT_half_eq : stepSevenCaccT / 2 = 1 / 16 := by
  rw [stepSevenCaccT_eq]; norm_num

/-- The `hlambda` slot's index is the upper ratio index: `s₀/2 = 1/8`. -/
theorem stepSevenCgS_half_eq : stepSevenCgS / 2 = 1 / 8 := by
  rw [stepSevenCgS_eq]; norm_num

/-- The good-event slot, in numerals. -/
theorem stepOneS_div_eight_eq : stepOneS / 8 = 1 / 32 := by
  rw [stepOneS_eq]; norm_num

/-! ## 3. The comparator algebra -/

/-- `sigma⁻¹ · x ≤ K → x ≤ K · sigma`. -/
private theorem clamp_le_mul_of_inv_mul_le {sigma x K : ℝ} (hsigma : 0 < sigma)
    (h : sigma⁻¹ * x ≤ K) : x ≤ K * sigma := by
  have hmul := mul_le_mul_of_nonneg_right h hsigma.le
  rwa [inv_mul_eq_div, div_mul_cancel₀ _ hsigma.ne'] at hmul

/-- `sigma · x ≤ K → x ≤ K · sigma⁻¹`. -/
private theorem clamp_le_mul_inv_of_mul_le {sigma x K : ℝ} (hsigma : 0 < sigma)
    (h : sigma * x ≤ K) : x ≤ K * sigma⁻¹ := by
  have hmul := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hsigma.le)
  rwa [mul_comm sigma, mul_assoc, mul_inv_cancel₀ hsigma.ne', mul_one] at hmul

/-! ## 4. The caps at the clamped covering cube -/

/-- **The caps at the clamped covering cube, at the §4.4 pin.**

Almost surely, on the §4.4 good event `𝒢(n+3, z; s/8, (s/8)δ^{1/2})` at the
lattice centre `z`, the four coarse-grained ellipticity quantities the Step-7
chain reads at the Step-7a centre `c = wellPlacedCentre x m (n+2)` — the
`hlambda` slot `λ_{1/8,2}^{-1}`, the Caccioppoli's `λ_{1/8,1}` and its inverse,
and the contrast `Θ_{1/4,1/8}` — are all controlled by one `d`-only constant
`K` against `σ̄_{n+3}`, on the covering cube `□_{n+2}` at the `(n+3)`-re-based
family.

Both ratio indices (`1/8` and `1/16`) are strictly above the good-event slot
`1/32`, so the off-grid transport applies with a finite constant; see the
module docstring for the exact weight inequality that blocks the `s* = 1/16`
and for why the boundary branch does not need it. -/
theorem ae_stepSevenClampCaps (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
          8 * M.gamma ≤ stepOneSEighth →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp delta →
            ∀ L m n : ℤ, n + 2 ≤ m → n + 3 ≤ L → ∀ z : Vec d,
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                omega ∈ stepThreeGoodEvent M delta (n + 3) z →
                  ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                    (fun y => x + y) '' openCubeSet (originCube d n) ⊆
                        ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                          openCubeSet (originCube d m) →
                    stepSevenCgLamInv (originCube d (n + 2))
                          (parentRebasedFamily M L (n + 3)
                            (wellPlacedCentre x m (n + 2)) z omega) stepSevenCgS ≤
                        K * ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ ∧
                      Ch02.lambdaS (originCube d (n + 2)) stepSevenCaccT
                            (parentRebasedFamily M L (n + 3)
                              (wellPlacedCentre x m (n + 2)) z omega) ≤
                          K * (Annealed.sigmaBar M (n + 3) : ℝ) ∧
                      (Ch02.lambdaS (originCube d (n + 2)) stepSevenCaccT
                            (parentRebasedFamily M L (n + 3)
                              (wellPlacedCentre x m (n + 2)) z omega))⁻¹ ≤
                          K * ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ ∧
                      Ch02.ThetaRatio (originCube d (n + 2)) stepSevenCaccS
                            stepSevenCaccT
                            (parentRebasedFamily M L (n + 3)
                              (wellPlacedCentre x m (n + 2)) z omega) ≤ K * K := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorRepresentative_le_of_mem_goodEventAt d
  have hd : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set kappa : ℝ := Real.sqrt (96 * (d : ℝ)) * 3 with hkappadef
  refine ⟨C, 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1), hCpos, ?_, ?_⟩
  · have h1 : (0 : ℝ) < (kappa * (C * (1 / 2))) ^ 2 + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (d : ℝ) := by linarith only [hd]
    exact mul_pos h2 h1
  intro M hregime delta hdelta hfloor hsmall L m n hnm hnL z
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) := (Annealed.sigmaBar M (n + 3)).2
  have hslot :
      ((⟨stepOneSEighth, stepOneSEighth_pos⟩ : {t : ℝ // 0 < t}) : ℝ) ∈
        Set.Icc (8 * M.gamma) (1 / 4 : ℝ) := by
    refine ⟨hfloor, ?_⟩
    show stepOneSEighth ≤ (1 : ℝ) / 4
    rw [stepOneSEighth_eq]; norm_num
  have hepHalf : stepOneEp delta ≤ 1 / 2 := (stepOneEp_mem_Ioc hdelta).2
  filter_upwards [hC M hregime ⟨stepOneSEighth, stepOneSEighth_pos⟩ hslot
      (stepOneEp delta) (stepOneEp_mem_Ioc hdelta) hsmall (n + 3) z,
    ae_coveringCubeError_le_representative (s := stepOneS)
      (t := stepSevenCaccS / 2) M L n m z stepOneS_pos
      (by rw [stepOneS_div_eight_eq, stepSevenCaccS_half_eq]; norm_num)
      (by rw [stepSevenCaccS_half_eq]; norm_num),
    ae_coveringCubeError_le_representative (s := stepOneS)
      (t := stepSevenCaccT / 2) M L n m z stepOneS_pos
      (by rw [stepOneS_div_eight_eq, stepSevenCaccT_half_eq]; norm_num)
      (by rw [stepSevenCaccT_half_eq]; norm_num)]
    with omega hcap herrUp herrLo
  intro hmem x hx hgeom
  -- the representative at the good-event slot, capped by the event
  have hErep0 : (0 : ℝ) ≤ fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
      (Cutoff.translateCutoffSample z omega) :=
    fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hErepCap : fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
      (Cutoff.translateCutoffSample z omega) ≤ C * (1 / 2) := by
    have hraw := hcap hmem L hnL
    have hstep : C * stepOneEp delta ≤ C * (1 / 2) :=
      mul_le_mul_of_nonneg_left hepHalf hCpos.le
    exact le_trans hraw hstep
  have h3s8 : ((3 : ℝ) ^ (stepOneS / 8)) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by rw [stepOneS_div_eight_eq]; norm_num : stepOneS / 8 ≤ (1 : ℝ))
    rwa [Real.rpow_one] at h
  have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ (stepOneS / 8) *
      fluxCorrectedErrorRepresentative M L (n + 3)
        ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
        (Cutoff.translateCutoffSample z omega) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hErep0
  have h3 : (3 : ℝ) ^ (stepOneS / 8) *
      fluxCorrectedErrorRepresentative M L (n + 3)
        ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
        (Cutoff.translateCutoffSample z omega) ≤ 3 * (C * (1 / 2)) := by
    have hstepa := mul_le_mul_of_nonneg_right h3s8 hErep0
    have hstepb : (3 : ℝ) * fluxCorrectedErrorRepresentative M L (n + 3)
        ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
        (Cutoff.translateCutoffSample z omega) ≤ 3 * (C * (1 / 2)) := by
      linarith only [hErepCap]
    linarith only [hstepa, hstepb]
  -- the two coarse-graining errors at the pin's ratio indices
  have hEUp : Ch02.HomogenizationErrorOnCube (originCube d (n + 2))
      (stepSevenCaccS / 2) .infinity (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
      kappa * (C * (1 / 2)) := by
    refine (herrUp x hnm hx hgeom).trans ?_
    have h1 : Real.sqrt (offGridStabilityConst d (stepSevenCaccS / 2) (stepOneS / 8)) ≤
        Real.sqrt (96 * (d : ℝ)) := by
      refine Real.sqrt_le_sqrt ?_
      rw [stepSevenCaccS_half_eq, stepOneS_div_eight_eq]
      exact offGridStabilityConst_stepSevenUpper_le d
    calc Real.sqrt (offGridStabilityConst d (stepSevenCaccS / 2) (stepOneS / 8)) *
          ((3 : ℝ) ^ (stepOneS / 8) *
            fluxCorrectedErrorRepresentative M L (n + 3)
              ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
              (Cutoff.translateCutoffSample z omega))
        ≤ Real.sqrt (96 * (d : ℝ)) * (3 * (C * (1 / 2))) :=
          mul_le_mul h1 h3 h3nn (Real.sqrt_nonneg _)
      _ = kappa * (C * (1 / 2)) := by rw [hkappadef]; ring
  have hELo : Ch02.HomogenizationErrorOnCube (originCube d (n + 2))
      (stepSevenCaccT / 2) .infinity (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
      kappa * (C * (1 / 2)) := by
    refine (herrLo x hnm hx hgeom).trans ?_
    have h1 : Real.sqrt (offGridStabilityConst d (stepSevenCaccT / 2) (stepOneS / 8)) ≤
        Real.sqrt (96 * (d : ℝ)) := by
      refine Real.sqrt_le_sqrt ?_
      rw [stepSevenCaccT_half_eq, stepOneS_div_eight_eq]
      exact offGridStabilityConst_stepSevenLower_le d
    calc Real.sqrt (offGridStabilityConst d (stepSevenCaccT / 2) (stepOneS / 8)) *
          ((3 : ℝ) ^ (stepOneS / 8) *
            fluxCorrectedErrorRepresentative M L (n + 3)
              ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
              (Cutoff.translateCutoffSample z omega))
        ≤ Real.sqrt (96 * (d : ℝ)) * (3 * (C * (1 / 2))) :=
          mul_le_mul h1 h3 h3nn (Real.sqrt_nonneg _)
      _ = kappa * (C * (1 / 2)) := by rw [hkappadef]; ring
  -- the `q = 2` ratio pairs at the two indices
  have hUpPos : (0 : ℝ) < stepSevenCaccS / 2 := by
    rw [stepSevenCaccS_half_eq]; norm_num
  have hLoPos : (0 : ℝ) < stepSevenCaccT / 2 := by
    rw [stepSevenCaccT_half_eq]; norm_num
  have hEUpnn : 0 ≤ Ch02.HomogenizationErrorOnCube (originCube d (n + 2))
      (stepSevenCaccS / 2) .infinity (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) :=
    homogenizationErrorOnCube_infinity_two_nonneg (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) hUpPos
  have hELonn : 0 ≤ Ch02.HomogenizationErrorOnCube (originCube d (n + 2))
      (stepSevenCaccT / 2) .infinity (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) :=
    homogenizationErrorOnCube_infinity_two_nonneg (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) hLoPos
  have hratioUp := max_ellipticityRatio_le_homogenizationError (d := d)
    (originCube d (n + 2))
    (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) hUpPos hsig
  have hratioLo := max_ellipticityRatio_le_homogenizationError (d := d)
    (originCube d (n + 2))
    (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) hLoPos hsig
  rw [← isotropicComparator_eq_scalarMatrix_clamp] at hratioUp hratioLo
  have hmaxUp := hratioUp.trans (two_mul_dim_mul_sq_add_one_le_of_le hEUpnn hEUp)
  have hmaxLo := hratioLo.trans (two_mul_dim_mul_sq_add_one_le_of_le hELonn hELo)
  have hUp8 := le_trans (le_max_left _ _) hmaxUp
  have hLo8 := le_trans (le_max_right _ _) hmaxUp
  have hLo16 := le_trans (le_max_right _ _) hmaxLo
  -- row 1: the `hlambda` slot, a `q = 2` quantity at `1/8`
  have hR1 : stepSevenCgLamInv (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      stepSevenCgS ≤
      2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ := by
    rw [stepSevenCgLamInv_eq_inv, stepSevenCgS_half_eq]
    refine clamp_le_mul_inv_of_mul_le hsig ?_
    rw [← stepSevenCaccS_half_eq]
    exact hLo8
  -- row 2: the `q = 1` upper constant at `1/4`, and the lower one at `1/8`
  have hR2Up : Ch02.LambdaS (originCube d (n + 2)) stepSevenCaccS
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) ≤
      2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        (Annealed.sigmaBar M (n + 3) : ℝ) :=
    LambdaS_le_of_ratio_cap (originCube d (n + 2)) _ stepSevenCaccS_pos hsig hUp8
  have hR2 : Ch02.lambdaS (originCube d (n + 2)) stepSevenCaccT
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) ≤
      2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        (Annealed.sigmaBar M (n + 3) : ℝ) :=
    le_trans (lambdaS_le_LambdaS (originCube d (n + 2)) _ stepSevenCaccS_pos
      stepSevenCaccT_pos) hR2Up
  -- row 3: the inverse `q = 1` lower constant at `1/8`, through the `1/16` datum
  have hR3 : (Ch02.lambdaS (originCube d (n + 2)) stepSevenCaccT
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega))⁻¹ ≤
      2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ :=
    lambdaS_inv_le_of_ratio_cap (originCube d (n + 2)) _ stepSevenCaccT_pos hsig hLo16
  refine ⟨hR1, hR2, hR3, ?_⟩
  -- row 4: the contrast, with the comparators cancelling
  refine (thetaRatio_le_of_caps (originCube d (n + 2)) _ stepSevenCaccS_pos
    stepSevenCaccT_pos hR2Up hR3).trans (le_of_eq ?_)
  have hsne : ((Annealed.sigmaBar M (n + 3) : ℝ)) ≠ 0 := ne_of_gt hsig
  calc 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        (Annealed.sigmaBar M (n + 3) : ℝ) *
        (2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
          ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹)
      = 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
          (2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1)) *
          ((Annealed.sigmaBar M (n + 3) : ℝ) *
            ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹) := by ring
    _ = 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
          (2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1)) := by
        rw [mul_inv_cancel₀ hsne, mul_one]

/-- **The three factors of the boundary `hcacc`, at the clamped cube.**

`StepSevenCaccBoundary.exists_stepSevenCaccHcacc_boundaryGate` produces its
estimate with the coarse-grained prefactor `caccioppoliWith C₁ (□_{n+2}; a)
(1/4) (1/8)`, the lower constant `λ_{1/8,1}` and its inverse on the right.  On
the §4.4 good event at the lattice centre `z`, all three are `d`-only (the first)
or `σ̄_{n+3}`-weighted (the last two), at the Step-7a centre.  The prefactor
cap is `StepSevenCaccMatching.stepSevenCaccPrefactor_le` read at the `Θ` cap of
`ae_stepSevenClampCaps`; no `s`-power is spent. -/
theorem ae_stepSevenClampCaccFactors (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
          8 * M.gamma ≤ stepOneSEighth →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp delta →
            ∀ L m n : ℤ, n + 2 ≤ m → n + 3 ≤ L → ∀ z : Vec d,
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                omega ∈ stepThreeGoodEvent M delta (n + 3) z →
                  ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                    (fun y => x + y) '' openCubeSet (originCube d n) ⊆
                        ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                          openCubeSet (originCube d m) →
                    ∀ C₁ : ℝ, 0 < C₁ →
                      caccioppoliWithRHSPrefactor C₁ (originCube d (n + 2))
                            (parentRebasedFamily M L (n + 3)
                              (wellPlacedCentre x m (n + 2)) z omega)
                            stepSevenCaccS stepSevenCaccT ≤
                          (2 * max 1 C₁) ^ (4 : ℕ) * 4 * (K * K) ^ (2 : ℕ) ∧
                        Ch02.lambdaS (originCube d (n + 2)) stepSevenCaccT
                              (parentRebasedFamily M L (n + 3)
                                (wellPlacedCentre x m (n + 2)) z omega) ≤
                            K * (Annealed.sigmaBar M (n + 3) : ℝ) ∧
                        (Ch02.lambdaS (originCube d (n + 2)) stepSevenCaccT
                              (parentRebasedFamily M L (n + 3)
                                (wellPlacedCentre x m (n + 2)) z omega))⁻¹ ≤
                            K * ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ := by
  obtain ⟨C, K, hCpos, hKpos, hcaps⟩ := ae_stepSevenClampCaps d
  refine ⟨C, K, hCpos, hKpos, ?_⟩
  intro M hregime delta hdelta hfloor hsmall L m n hnm hnL z
  filter_upwards [hcaps M hregime delta hdelta hfloor hsmall L m n hnm hnL z]
    with omega hall
  intro hmem x hx hgeom C₁ hC₁
  obtain ⟨_, hlam, hlaminv, hTheta⟩ := hall hmem x hx hgeom
  exact ⟨stepSevenCaccPrefactor_le hC₁ hTheta, hlam, hlaminv⟩

end

end Algsuperdiff.Section4.Provider.Regularity
