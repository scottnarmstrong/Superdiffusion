import Algsuperdiff.Section3.Provider.Stream.IncrementLpRecombination
import Algsuperdiff.Section3.Provider.Stream.MomentBoostedLargeAllP

/-!
# The corrected all-`p` squared stream-increment estimate

This module consumes the proved moment-boosted mass estimate and the all-power
recombination A.  The mass tail is clamped at zero internally, raised to the
power `2 / p`, and absorbed using the uniform split bound `c(p) ≤ 2`.  The one
public theorem has the source binders of corrected `e.km.kn.Lp`; none of the
clamping, positivity, or recombination obligations crosses its surface.

The source is ABK26 `l.km.kn.Lp.estimates`, using `e.kl.bounds.large`, and
`e.powerofGammasigma`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open Homogenization Homogenization.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

private theorem isBigOWith_max_zero_for_norm_sq
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {Psi : ℝ → ℝ} {Y : Omega → ℝ} {A : ℝ} (hA : 0 < A)
    (hY : IsBigOWith mu Psi Y A) :
    IsBigOWith mu Psi (fun omega => max 0 (Y omega)) A := by
  intro t ht
  have hAt : 0 < A * t := mul_pos hA (lt_of_lt_of_le zero_lt_one ht)
  have hsets :
      upperTailEvent (fun omega => max 0 (Y omega)) (A * t) =
        upperTailEvent Y (A * t) := by
    ext omega
    simp only [mem_upperTailEvent, lt_max_iff]
    constructor
    · rintro (homega | homega)
      · exact absurd homega (not_lt.2 hAt.le)
      · exact homega
    · exact Or.inr
  rw [hsets]
  exact hY ht

private theorem mass_head_rpow_two_div_exact
    (M : ABKModel d) {C p : ℝ} (hC : 0 < C) (hp : 1 ≤ p)
    {n m : ℤ} (hnm : n < m) :
    (((C * p) ^ (p / 2) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2)) ^ (2 / p)) =
      C * p *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hmn : 0 < (m : ℝ) - (n : ℝ) := by
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hB : 0 < min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
    mul_pos (lt_min (inv_pos.mpr M.shellPrefix.gamma_pos) hmn)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hCp : 0 < C * p := mul_pos hC hp0
  have hexp : (p / 2) * (2 / p) = 1 := by
    field_simp
  rw [Real.mul_rpow (Real.rpow_nonneg hCp.le _) (Real.rpow_nonneg hB.le _),
    ← Real.rpow_mul hCp.le, ← Real.rpow_mul hB.le, hexp, Real.rpow_one,
    Real.rpow_one]

private theorem mass_tail_rpow_two_div_exact
    (M : ABKModel d) {C p : ℝ} (hC : 0 < C) (hp : 1 ≤ p)
    {l n m : ℤ} (hnm : n < m) :
    ((((C * p) ^ (p / 2) *
          (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) ^ (2 / p)) =
      C * p *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ))) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hmn : 0 < (m : ℝ) - (n : ℝ) := by
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hB : 0 < min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
    mul_pos (lt_min (inv_pos.mpr M.shellPrefix.gamma_pos) hmn)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hhead : 0 ≤ (C * p) ^ (p / 2) *
      (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) := by
    exact mul_nonneg (Real.rpow_nonneg (mul_pos hC hp0).le _)
      (Real.rpow_nonneg hB.le _)
  have hgain : 0 ≤ (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hexp :
      (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) * (2 / p) =
        -((d : ℝ) / p) * ((l : ℝ) - (m : ℝ)) := by
    have hp_ne : p ≠ 0 := ne_of_gt hp0
    field_simp
  rw [Real.mul_rpow hhead hgain, mass_head_rpow_two_div_exact M hC hp hnm,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hexp]

private theorem fixed_mass_bound_to_norm_sq
    (M : ABKModel d) {C p : ℝ} (hC : 0 < C) (hp : 1 ≤ p)
    {l n m : ℤ} (hnm : n < m)
    (hmass : Probability.IsDeterministicShiftOneSidedOrlicz
      M.P.toMeasure (gammaSigma (2 / p))
      (streamIncrementLpMass p l n m)
      ((C * p) ^ (p / 2) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2))
      ((C * p) ^ (p / 2) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))))) :
    Probability.IsDeterministicShiftOneSidedOrlicz
      M.P.toMeasure (gammaSigma 1)
      (fun omega => streamIncrementLpNorm p l n m omega ^ 2)
      ((2 * C) * p *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))))
      ((2 * C) * p *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ)))) := by
  let H : ℝ := (C * p) ^ (p / 2) *
    (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2)
  let K : ℝ := H * (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))
  let T : ShellSeq d → ℝ := fun omega =>
    max 0 (streamIncrementLpMass p l n m omega - H)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hmn : 0 < (m : ℝ) - (n : ℝ) := by
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hB : 0 < min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
    mul_pos (lt_min (inv_pos.mpr M.shellPrefix.gamma_pos) hmn)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hH : 0 < H := by
    dsimp [H]
    exact mul_pos (Real.rpow_pos_of_pos (mul_pos hC hp0) _)
      (Real.rpow_pos_of_pos hB _)
  have hK : 0 < K := by
    exact mul_pos hH (Real.rpow_pos_of_pos (by norm_num) _)
  have hT0 : ∀ omega, 0 ≤ T omega := fun omega => by
    exact le_max_left _ _
  have hmass_le : ∀ omega, streamIncrementLpMass p l n m omega ≤ H + T omega := by
    intro omega
    dsimp [T]
    linarith [le_max_right (0 : ℝ) (streamIncrementLpMass p l n m omega - H)]
  have hTtail : IsBigOWith M.P.toMeasure (gammaSigma (2 / p)) T K := by
    exact isBigOWith_max_zero_for_norm_sq hmass.2.1 hmass.2.2.2
  obtain ⟨hTpow0, hnorm, htail⟩ :=
    streamIncrementLpNormSq_head_tail_with_splitConst_of_mass_head_tail
      M hp l n m hH.le hK.le hT0 hmass_le hTtail
  have hHpow : H ^ (2 / p) = C * p *
      (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
    exact mass_head_rpow_two_div_exact M hC hp hnm
  have hKpow : K ^ (2 / p) = C * p *
      (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
      (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ))) := by
    exact mass_tail_rpow_two_div_exact M hC hp hnm
  have hhead_le : streamIncrementLpNormSqSplitConst p * H ^ (2 / p) ≤
      (2 * C) * p *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
    rw [hHpow]
    calc
      streamIncrementLpNormSqSplitConst p *
          (C * p *
            (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) ≤
          2 *
            (C * p *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) :=
        mul_le_mul_of_nonneg_right (streamIncrementLpNormSqSplitConst_le_two hp)
          (mul_nonneg (mul_nonneg hC.le hp0.le) hB.le)
      _ = (2 * C) * p *
          (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by ring
  have htail_le : streamIncrementLpNormSqSplitConst p * K ^ (2 / p) ≤
      (2 * C) * p *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ))) := by
    rw [hKpow]
    calc
      streamIncrementLpNormSqSplitConst p *
          (C * p *
            (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
            (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ)))) ≤
          2 *
            (C * p *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
              (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ)))) :=
        mul_le_mul_of_nonneg_right (streamIncrementLpNormSqSplitConst_le_two hp)
          (mul_nonneg (mul_nonneg (mul_nonneg hC.le hp0.le) hB.le)
            (Real.rpow_nonneg (by norm_num) _))
      _ = (2 * C) * p *
          (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
          (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ))) := by ring
  have hnormsq_meas :
      Measurable (fun omega : ShellSeq d => streamIncrementLpNorm p l n m omega ^ 2) := by
    rw [show (fun omega : ShellSeq d => streamIncrementLpNorm p l n m omega ^ 2) =
        fun omega => streamIncrementLpMass p l n m omega ^ (2 / p) by
      funext omega
      exact streamIncrementLpNorm_sq_eq_mass_rpow p l n m omega]
    exact hmass.2.2.1.pow_const _
  refine ⟨Probability.isAdmissibleTail_gammaSigma (by norm_num),
    lt_of_lt_of_le
      (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hC) hp0) hB)
        (Real.rpow_pos_of_pos (by norm_num) _))
      (le_rfl), hnormsq_meas, ?_⟩
  exact (htail.mono_scale htail_le).of_le fun omega => by
    linarith [hnorm omega, hhead_le, hTpow0 omega]

/-- The corrected all-`p` squared stream-increment estimate.  Its one positive
constant is selected from the dimension before the model, exponent, and
scales. -/
theorem stream_increment_lp_norm_sq_large_cube_bound_provider (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (p : ℝ), 1 ≤ p →
        ∀ l m n : ℤ, n < m → m ≤ l →
          Probability.IsDeterministicShiftOneSidedOrlicz
            M.P.toMeasure
            (gammaSigma 1)
            (fun omega => streamIncrementLpNorm p l n m omega ^ 2)
            (C * p *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))))
            (C * p *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
              (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ)))) := by
  obtain ⟨C, hC, hmass⟩ := stream_increment_lp_large_cube_bound_provider d
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro M p hp l m n hnm hml
  exact fixed_mass_bound_to_norm_sq M hC hp hnm (hmass M p hp l m n hnm hml)

end

end Algsuperdiff.Section3.Provider.Stream
