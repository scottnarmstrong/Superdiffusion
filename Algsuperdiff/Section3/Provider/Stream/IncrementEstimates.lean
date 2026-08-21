import Algsuperdiff.Section3.Provider.Stream.IncrementL2LargeCube
import Algsuperdiff.Section3.Provider.Stream.IncrementLinftyNorm
import Algsuperdiff.Section3.Provider.Stream.IncrementLpNormSqAllP
import Algsuperdiff.Section3.Provider.Stream.StreamDerivativeSum

/-!
# Stream-increment estimates

This module assembles the five conclusions of ABK26
`l.km.kn.Lp.estimates` from the separately proved squared `L2`, all-`p`,
small- and large-cube `L∞`, and derivative-sum estimates.  One common positive
constant is selected from the dimension before the model, exponent, and
scales.  This ordinary provider is proof-readiness infrastructure for a
proposed corrected source-facing declaration; it does not create or close a
source node.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open Homogenization
open Algsuperdiff.Section3.Cutoff

noncomputable section

private theorem isDeterministicShiftOneSidedOrlicz_mono_shift_and_scale
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {Psi : ℝ → ℝ} {X : Omega → ℝ}
    {b b' A B : ℝ}
    (h : Probability.IsDeterministicShiftOneSidedOrlicz mu Psi X b A)
    (hbb' : b ≤ b') (hAB : A ≤ B) :
    Probability.IsDeterministicShiftOneSidedOrlicz mu Psi X b' B := by
  have htail := h.2.2.2.mono_scale hAB
  exact ⟨h.1, lt_of_lt_of_le h.2.1 hAB, h.2.2.1,
    htail.of_le (fun omega => by linarith)⟩

private theorem isOneSidedOrlicz_mono_scale
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {Psi : ℝ → ℝ} {X : Omega → ℝ} {A B : ℝ}
    (h : Probability.IsOneSidedOrlicz mu Psi X A) (hAB : A ≤ B) :
    Probability.IsOneSidedOrlicz mu Psi X B := by
  exact ⟨h.1, lt_of_lt_of_le h.2.1 hAB, h.2.2.1, h.2.2.2.mono_scale hAB⟩

/-- An internal combination of five proved estimates under one common
dimension-only constant.  This declaration does not designate a source node. -/
theorem stream_increment_estimates_provider (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (M : ABKModel d) (p : ℝ), 1 ≤ p →
        ∀ l m n : ℤ, n < m → m ≤ l →
          Homogenization.Book.Ch04.IsBigO
            M.P.toMeasure
            (Homogenization.Book.Ch04.gammaSigma 1)
            (fun omega : ShellSeq d =>
              cubeFrobeniusMassFiniteShellIncrement l n m omega -
                (Disorder.cstarPlus M * Real.log 3) *
                  ∑ k ∈ Finset.Ioc n m,
                    (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)))
            (C * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) ∧
          Probability.IsDeterministicShiftOneSidedOrlicz
            M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 1)
            (fun omega => streamIncrementLpNorm p l n m omega ^ 2)
            (C * p *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))))
            (C * p *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
              (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ)))) ∧
          Probability.IsOneSidedOrlicz
            M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 1)
            (fun omega : ShellSeq d => streamIncrementLinftyNorm n n m omega ^ 2)
            (C * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ∧
          Probability.IsOneSidedOrlicz
            M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 1)
            (fun omega : ShellSeq d => streamIncrementLinftyNorm l n m omega ^ 2)
            (C * ((l : ℝ) - (n : ℝ)) *
              min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) ∧
      ∀ (M : ABKModel d) (l m n : ℤ), n ≤ min m l →
        Homogenization.IndependentSums.IsBigOWith
          M.P.toMeasure
          (Homogenization.IndependentSums.gammaSigma 2)
          (fun omega : ShellSeq d =>
            ∑ k ∈ Finset.Ioc n m,
              ((3 : ℝ) ^ k * localCubeDerivNorm l (omega k) +
                (3 : ℝ) ^ (2 * k) * localCubeSecondDerivNorm l (omega k)))
          (C * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
            min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
  obtain ⟨C2, _hC2pos, hL2⟩ :=
    stream_increment_l2_large_cube_bound_provider d
  obtain ⟨Cp, _hCppos, hLp⟩ :=
    stream_increment_lp_norm_sq_large_cube_bound_provider d
  obtain ⟨CW, _hCWpos, hW⟩ :=
    stream_derivative_sum_bound_provider d
  let C : ℝ := max 1
    (max C2 (max Cp (max (streamLinftyConst d ^ 2) (max (largeCubeLinftyConst d) CW))))
  have hCpos : 0 < C := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC2C : C2 ≤ C := by simp [C]
  have hCpC : Cp ≤ C := by simp [C]
  have hsmallC : streamLinftyConst d ^ 2 ≤ C := by simp [C]
  have hlargeC : largeCubeLinftyConst d ≤ C := by simp [C]
  have hCWC : CW ≤ C := by simp [C]
  refine ⟨C, hCpos, ?_, ?_⟩
  · intro M p hp l m n hnm hml
    have hp0 : 0 ≤ p := (zero_le_one.trans hp)
    have hmn : 0 ≤ (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    have hln : 0 ≤ (l : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (l : ℝ) := by
        exact_mod_cast hnm.trans_le hml
      linarith
    have hB : 0 ≤ min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
      exact mul_nonneg
        (le_min (inv_pos.mpr M.shellPrefix.gamma_pos).le hmn)
        (Real.rpow_nonneg (by norm_num) _)
    have hdecay : 0 ≤
        (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hL2scale :
        C2 * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) ≤
          C * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC2C (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (by norm_num) _)
    have hhead : Cp * p *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ≤
        C * p *
          (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCpC hp0) hB
    have htail : Cp * p *
          (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
          (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ))) ≤
        C * p *
          (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
          (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hhead hdecay
    have hsmallScale :
        streamLinftyConst d ^ 2 *
            min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤
          C * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsmallC
          (le_min (inv_pos.mpr M.shellPrefix.gamma_pos).le hmn))
        (Real.rpow_nonneg (by norm_num) _)
    have hlargeScale :
        largeCubeLinftyConst d * ((l : ℝ) - (n : ℝ)) *
            min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤
          C * ((l : ℝ) - (n : ℝ)) *
            min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hlargeC hln)
          (le_min (inv_pos.mpr M.shellPrefix.gamma_pos).le hmn))
        (Real.rpow_nonneg (by norm_num) _)
    exact ⟨
      (hL2 M l m n hnm hml).mono_scale hL2scale,
      isDeterministicShiftOneSidedOrlicz_mono_shift_and_scale
        (hLp M p hp l m n hnm hml) hhead htail,
      isOneSidedOrlicz_mono_scale
        (streamIncrementLinftyNorm_sq_isOneSidedOrlicz_smallCube M hnm)
        hsmallScale,
      isOneSidedOrlicz_mono_scale
        (streamIncrementLinftyNorm_sq_isOneSidedOrlicz_largeCube M hnm hml)
        hlargeScale⟩
  · intro M l m n hrange
    have hnm : n ≤ m := hrange.trans (min_le_left _ _)
    have hmn : 0 ≤ (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith
    have hWscale :
        CW * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
            min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)) ≤
          C * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
            min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCWC (Real.sqrt_nonneg _))
          (le_min (inv_pos.mpr M.shellPrefix.gamma_pos).le hmn))
        (Real.rpow_nonneg (by norm_num) _)
    exact (hW M l m n hrange).mono_scale hWscale

end

end Algsuperdiff.Section3.Provider.Stream
