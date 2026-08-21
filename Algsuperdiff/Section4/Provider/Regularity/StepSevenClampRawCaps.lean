/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepSevenClampCaps

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

private theorem isotropicComparator_eq_scalarMatrix_raw (sigma : PositiveScalar) :
    isotropicComparatorMatrix (d := d) sigma = scalarMatrix (d := d) (sigma : ℝ) :=
  rfl

/-! ## 1. The two datum-leg indices -/

/-- The Poincaré U index of the datum leg is the Caccioppoli upper half-index: `s/2
= 1/8`. -/
theorem stepSevenCaccS_half_eq_stepOneS_div_two : stepSevenCaccS / 2 = stepOneS / 2 := by
  rw [stepSevenCaccS_half_eq, stepOneS]
  norm_num

/-- The Poincaré lower index of the datum leg is the Caccioppoli lower half-index:
`s/4 = 1/16`. -/
theorem stepSevenCaccT_half_eq_stepOneS_div_four : stepSevenCaccT / 2 = stepOneS / 4 := by
  rw [stepSevenCaccT_half_eq, stepOneS]
  norm_num

/-! ## 2. The raw caps -/

/-- Almost surely, on the §4.4 good event `𝒢(n+3, z; s/8, (s/8)δ^{1/2})` at the
lattice centre `z`, the two coarse-grained `q = 2` ratios that the boundary datum
leg reads at the clamped Step-7a centre `c = wellPlacedCentre x m (n+2)` — the
upper ratio at the index `s/2 = 1/8` and the inverse lower ratio at `s/4 =
1/16` — are controlled by one `d`-only constant `K` against `σ̄_{n+3}`, on the
covering cube `□_{n+2}` at the `(n+3)`-re-based family.

This is `ae_stepSevenClampCaps`'s own internal pair, exported. -/
theorem ae_stepSevenClampRatioCaps (d : ℕ) [NeZero d] :
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
                    ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                          Ch02.LambdaSq (originCube d (n + 2)) (stepOneS / 2)
                            (Ch02.MultiscaleExponent.finite 2)
                            (parentRebasedFamily M L (n + 3)
                              (wellPlacedCentre x m (n + 2)) z omega) ≤ K ∧
                      ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                          (Ch02.lambdaSq (originCube d (n + 2)) (stepOneS / 4)
                            (Ch02.MultiscaleExponent.finite 2)
                            (parentRebasedFamily M L (n + 3)
                              (wellPlacedCentre x m (n + 2)) z omega))⁻¹ ≤ K := by
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
  rw [← isotropicComparator_eq_scalarMatrix_raw] at hratioUp hratioLo
  have hmaxUp := hratioUp.trans (two_mul_dim_mul_sq_add_one_le_of_le hEUpnn hEUp)
  have hmaxLo := hratioLo.trans (two_mul_dim_mul_sq_add_one_le_of_le hELonn hELo)
  have hUp8 := le_trans (le_max_left _ _) hmaxUp
  have hLo16 := le_trans (le_max_right _ _) hmaxLo
  rw [stepSevenCaccS_half_eq_stepOneS_div_two] at hUp8
  rw [stepSevenCaccT_half_eq_stepOneS_div_four] at hLo16
  exact ⟨hUp8, hLo16⟩

end

end Algsuperdiff.Section4.Provider.Regularity
