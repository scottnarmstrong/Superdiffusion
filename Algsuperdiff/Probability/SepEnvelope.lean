import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The deterministic envelope reconciliation of `l.minimal.scale.sep`

ABK26, Lemma `l.minimal.scale.sep`.  The proof of the Lemma produces **three
deterministic levels** plus **one residual**, while the statement of the Lemma
carries only a single envelope

  `E := c⋆⁻¹ · s^{−7/2} · γ^{1/2}`.

This module is the elementary (purely deterministic, purely real-analytic)
arithmetic that collapses all four into `E`. Parameter ranges from the paper:
`c⋆ ∈ (0,1]`, `s ∈ (0,1/2]`, `γ ∈ (0,1/2]`, and the smallness condition
`γ ≤ C^{-10} c⋆^{10}`.

## The four contributions

* Level 1: already `C · c⋆⁻¹ · s^{−7/2} · √γ` — nothing to do.
* Level 2: `C · c⋆^{−1/2} · s^{−1} · √γ` — `detLevel2_le`.
* Level 3: `C · c⋆^{−1/2} · s^{−7/2} · √γ` — `detLevel3_le`.
* Residual: `c⋆^{−2} · s^{−1} · γ · |log γ|²` — `residual_le_of_small`.

The two monotonicity facts driving levels 2 and 3 are the `(0,1]`-rpow
comparisons `c⋆^{−1/2} ≤ c⋆⁻¹` and `s⁻¹ ≤ s^{−7/2}`.

## The residual

Honest two-stage form. Stage 1 (`residual_le_of_small`) reduces the residual to
the clean smallness condition `√γ · (log γ)² ≤ c⋆` by the exact factorization

  `c⋆^{−2} s^{−1} γ (log γ)² = (c⋆⁻¹ s^{−7/2} √γ) · (c⋆⁻¹ · s^{5/2} · √γ (log γ)²)`,

whose bracket is `≤ 1` since `s^{5/2} ≤ 1`. Stage 2
(`sqrt_mul_log_sq_le_of_gamma_small`) derives that smallness condition from the
paper's own hypothesis `γ ≤ C^{-10} c⋆^{10}` (for `C ≥ 64`), via the scale-free
bound `γ^{1/4} (log γ)² ≤ 64` on `(0,1]` (`gamma_quarter_log_sq_le`), which in
turn is the elementary `|t log t| ≤ 1` on `(0,1]` applied to `t = γ^{1/8}`. The
smallness condition is never assumed silently: it is a named hypothesis of stage 1
and a *conclusion* of stage 2.

The one-shot collapse the assembly calls is `sepEnvelope_collapse`; the
fluctuation-side twins are `sepFluc_scale_le` / `sepFluc_scale_le'`.

## Note on binders

`detLevel3_le`, `residual_le_of_small`, `sepFluc_scale_le` and `sepFluc_scale_le'`
each carry one or two range binders (`0 ≤ γ`, `s ≤ 1`, `c⋆ ≤ 1`) that the proof
does not consume; they are retained because they are part of the printed parameter
range and because dropping them would be a statement change. The `have _h := h`
lines mark exactly where that happens.

## Main results

* `Algsuperdiff.Probability.detLevel2_le`, `Algsuperdiff.Probability.detLevel3_le`
* `Algsuperdiff.Probability.residual_le_of_small`
* `Algsuperdiff.Probability.sqrt_mul_log_sq_le_of_gamma_small`
* `Algsuperdiff.Probability.sepEnvelope_collapse`

## References

* ABK26, `l.minimal.scale.sep`.
-/

namespace Algsuperdiff.Probability

variable {cstar s γ C K L Cbig t : ℝ}

/-! ## Abstract-real algebra helpers -/

/-- Four-factor monotonicity, over abstract reals (the rpow factors are
opaque). -/
theorem mul_four_mono {a a' b b' g : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (haa : a ≤ a')
    (hb : 0 ≤ b) (hbb : b ≤ b') (hg : 0 ≤ g) :
    C * a * b * g ≤ C * a' * b' * g := by
  have ha' : 0 ≤ a' := ha.trans haa
  have h1 : C * a ≤ C * a' := mul_le_mul_of_nonneg_left haa hC
  have h2 : C * a * b ≤ C * a' * b := mul_le_mul_of_nonneg_right h1 hb
  have h3 : C * a' * b ≤ C * a' * b' := mul_le_mul_of_nonneg_left hbb (mul_nonneg hC ha')
  exact mul_le_mul_of_nonneg_right (h2.trans h3) hg

/-- The residual factorization, over abstract reals. -/
theorem residual_factor_id (ci a b r Lg : ℝ) :
    ci * ci * (a * b) * (r * r) * Lg = ci * a * r * (ci * b * (r * Lg)) := by ring

/-! ## rpow monotonicity on `(0,1]` -/

/-- `c⋆^{−1/2} ≤ c⋆⁻¹` for `c⋆ ∈ (0,1]`. -/
theorem cstar_rpow_half_le_inv (hc : 0 < cstar) (hc1 : cstar ≤ 1) :
    cstar ^ (-(1 : ℝ) / 2) ≤ cstar⁻¹ := by
  have h : cstar ^ (-(1 : ℝ) / 2) ≤ cstar ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hc hc1 (by norm_num)
  rwa [Real.rpow_neg_one] at h

/-- `s⁻¹ ≤ s^{−7/2}` for `s ∈ (0,1]`. -/
theorem s_inv_le_rpow_seven_halves (hs : 0 < s) (hs1 : s ≤ 1) :
    s⁻¹ ≤ s ^ (-(7 : ℝ) / 2) := by
  have h : s ^ (-1 : ℝ) ≤ s ^ (-(7 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
  rwa [Real.rpow_neg_one] at h

/-- `c⋆^{−2} = c⋆⁻¹ · c⋆⁻¹` — the normal form used by the residual
factorization. -/
theorem cstar_rpow_neg_two_eq (hc : 0 < cstar) :
    cstar ^ (-(2 : ℝ)) = cstar⁻¹ * cstar⁻¹ := by
  rw [Real.rpow_neg hc.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    pow_two, mul_inv]

/-! ## The three-level collapse -/

/-- Level-2 envelope comparison (without the constant): the level-2 envelope is
dominated by the Lemma's envelope. -/
theorem env2_le (hc : 0 < cstar) (hc1 : cstar ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) :
    cstar ^ (-(1 : ℝ) / 2) * s⁻¹ * Real.sqrt γ
      ≤ cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ := by
  have h := mul_four_mono (C := 1) zero_le_one (Real.rpow_nonneg hc.le _)
    (cstar_rpow_half_le_inv hc hc1) (inv_nonneg.mpr hs.le)
    (s_inv_le_rpow_seven_halves hs hs1) (Real.sqrt_nonneg γ)
  simpa using h

/-- Level-3 envelope comparison (without the constant). -/
theorem env3_le (hc : 0 < cstar) (hc1 : cstar ≤ 1) (hs : 0 < s) :
    cstar ^ (-(1 : ℝ) / 2) * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ
      ≤ cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ := by
  have h := mul_four_mono (C := 1) zero_le_one (Real.rpow_nonneg hc.le _)
    (cstar_rpow_half_le_inv hc hc1) (Real.rpow_nonneg hs.le _)
    (le_refl (s ^ (-(7 : ℝ) / 2))) (Real.sqrt_nonneg γ)
  simpa using h

/-- **Level 2 → envelope.** `C c⋆^{−1/2} s^{−1} √γ ≤ C c⋆⁻¹ s^{−7/2} √γ`. -/
theorem detLevel2_le (hc : 0 < cstar) (hc1 : cstar ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hC : 0 ≤ C) :
    C * cstar ^ (-(1 : ℝ) / 2) * s⁻¹ * Real.sqrt γ
      ≤ C * cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ := by
  have _hγ := hγ
  exact mul_four_mono hC (Real.rpow_nonneg hc.le _) (cstar_rpow_half_le_inv hc hc1)
    (inv_nonneg.mpr hs.le) (s_inv_le_rpow_seven_halves hs hs1) (Real.sqrt_nonneg γ)

/-- **Level 3 → envelope.** `C c⋆^{−1/2} s^{−7/2} √γ ≤ C c⋆⁻¹ s^{−7/2} √γ`. -/
theorem detLevel3_le (hc : 0 < cstar) (hc1 : cstar ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hC : 0 ≤ C) :
    C * cstar ^ (-(1 : ℝ) / 2) * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ
      ≤ C * cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ := by
  have _hγ := hγ
  have _hs1 := hs1
  exact mul_four_mono hC (Real.rpow_nonneg hc.le _) (cstar_rpow_half_le_inv hc hc1)
    (Real.rpow_nonneg hs.le _) (le_refl (s ^ (-(7 : ℝ) / 2))) (Real.sqrt_nonneg γ)

/-! ## The residual, stage 1: reduction to the smallness condition -/

/-- **Residual absorption (stage 1).** `c⋆^{−2} s^{−1} γ |log γ|² ≤ c⋆⁻¹ s^{−7/2}
γ^{1/2}` under the clean smallness condition `√γ (log γ)² ≤ c⋆`.

The proof is the exact factorization
`LHS = (c⋆⁻¹ s^{−7/2} √γ) · (c⋆⁻¹ · s^{5/2} · √γ (log γ)²)` with the bracket
`≤ 1`. -/
theorem residual_le_of_small
    (hc : 0 < cstar) (hc1 : cstar ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) (hγ : 0 < γ)
    (hsmall : Real.sqrt γ * (Real.log γ) ^ 2 ≤ cstar) :
    cstar ^ (-(2 : ℝ)) * s⁻¹ * γ * (Real.log γ) ^ 2
      ≤ cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ := by
  have _hc1 := hc1
  have hci : (0 : ℝ) ≤ cstar⁻¹ := inv_nonneg.mpr hc.le
  have hE : 0 ≤ cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ :=
    mul_nonneg (mul_nonneg hci (Real.rpow_nonneg hs.le _)) (Real.sqrt_nonneg γ)
  -- the bracket is `≤ 1`
  have hs52 : s ^ ((5 : ℝ) / 2) ≤ 1 := Real.rpow_le_one hs.le hs1 (by norm_num)
  have hX0 : 0 ≤ Real.sqrt γ * (Real.log γ) ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg γ) (sq_nonneg _)
  have hB : cstar⁻¹ * s ^ ((5 : ℝ) / 2) * (Real.sqrt γ * (Real.log γ) ^ 2) ≤ 1 := by
    have h1 : cstar⁻¹ * s ^ ((5 : ℝ) / 2) ≤ cstar⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hs52 hci
    have h2 : cstar⁻¹ * s ^ ((5 : ℝ) / 2) * (Real.sqrt γ * (Real.log γ) ^ 2)
        ≤ cstar⁻¹ * 1 * cstar := mul_le_mul h1 hsmall hX0 (by simpa using hci)
    have h3 : cstar⁻¹ * 1 * cstar = 1 := by rw [mul_one, inv_mul_cancel₀ hc.ne']
    linarith only [h2, h3]
  -- the exact factorization
  have hcc : cstar ^ (-(2 : ℝ)) = cstar⁻¹ * cstar⁻¹ := cstar_rpow_neg_two_eq hc
  have hss : s ^ (-(7 : ℝ) / 2) * s ^ ((5 : ℝ) / 2) = s⁻¹ := by
    rw [← Real.rpow_add hs, show (-(7 : ℝ) / 2 + (5 : ℝ) / 2) = -1 by norm_num,
      Real.rpow_neg_one]
  have hgg : Real.sqrt γ * Real.sqrt γ = γ := Real.mul_self_sqrt hγ.le
  have key : cstar ^ (-(2 : ℝ)) * s⁻¹ * γ * (Real.log γ) ^ 2
      = cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ
        * (cstar⁻¹ * s ^ ((5 : ℝ) / 2) * (Real.sqrt γ * (Real.log γ) ^ 2)) := by
    calc cstar ^ (-(2 : ℝ)) * s⁻¹ * γ * (Real.log γ) ^ 2
        = cstar⁻¹ * cstar⁻¹ * (s ^ (-(7 : ℝ) / 2) * s ^ ((5 : ℝ) / 2))
            * (Real.sqrt γ * Real.sqrt γ) * (Real.log γ) ^ 2 := by
          rw [hcc, hss, hgg]
      _ = _ := residual_factor_id _ _ _ _ _
  rw [key]
  calc cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ
        * (cstar⁻¹ * s ^ ((5 : ℝ) / 2) * (Real.sqrt γ * (Real.log γ) ^ 2))
      ≤ cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ * 1 :=
        mul_le_mul_of_nonneg_left hB hE
    _ = _ := mul_one _

/-! ## The residual, stage 2: the smallness condition from `γ ≤ C^{-10} c⋆^{10}` -/

/-- `-(t log t) ≤ 1` for every `t > 0` (on `(0,1]` this is the useful half of
`|t log t| ≤ 1`). Proof: `t·(-log t) ≤ t·(t⁻¹ − 1) = 1 − t ≤ 1`. -/
theorem neg_mul_log_le_one (ht : 0 < t) : -(t * Real.log t) ≤ 1 := by
  have h1 : Real.log t⁻¹ ≤ t⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at h1
  have h2 : t * -Real.log t ≤ t * (t⁻¹ - 1) := mul_le_mul_of_nonneg_left h1 ht.le
  have h3 : t * (t⁻¹ - 1) = 1 - t := by rw [mul_sub, mul_inv_cancel₀ ht.ne', mul_one]
  linarith only [h2, h3, ht.le]

/-- The `t = γ^{1/8}` core of `gamma_quarter_log_sq_le`, over abstract reals: for
`t ∈ (0,1]`, `t² · (8 log t)² = 64 (t log t)² ≤ 64`. -/
theorem quarter_log_sq_aux (ht : 0 < t) (ht1 : t ≤ 1) :
    t * t * (8 * Real.log t) ^ 2 ≤ 64 := by
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have h0 : 0 ≤ -(t * Real.log t) := by
    have h := mul_nonneg ht.le (neg_nonneg.mpr hlog)
    linarith only [h]
  have h1 : -(t * Real.log t) ≤ 1 := neg_mul_log_le_one ht
  have h2 : (-(t * Real.log t)) ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have h3 : t * t * (8 * Real.log t) ^ 2 = 64 * (-(t * Real.log t)) ^ 2 := by ring
  linarith only [h2, h3]

/-- **The scale-free log bound.** `γ^{1/4} (log γ)² ≤ 64` for `γ ∈ (0,1]`. -/
theorem gamma_quarter_log_sq_le (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    γ ^ ((1 : ℝ) / 4) * (Real.log γ) ^ 2 ≤ 64 := by
  have ht : (0 : ℝ) < γ ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hγ _
  have ht1 : γ ^ ((1 : ℝ) / 8) ≤ 1 := Real.rpow_le_one hγ.le hγ1 (by norm_num)
  have hlog : Real.log (γ ^ ((1 : ℝ) / 8)) = 1 / 8 * Real.log γ := Real.log_rpow hγ _
  have hqq : γ ^ ((1 : ℝ) / 8) * γ ^ ((1 : ℝ) / 8) = γ ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hγ, show (1 : ℝ) / 8 + (1 : ℝ) / 8 = (1 : ℝ) / 4 by norm_num]
  have h := quarter_log_sq_aux ht ht1
  rw [hqq, hlog, show (8 : ℝ) * (1 / 8 * Real.log γ) = Real.log γ by ring] at h
  exact h

/-- `√γ = γ^{1/4} · γ^{1/4}`. -/
theorem sqrt_eq_quarter_mul_quarter (hγ : 0 < γ) :
    Real.sqrt γ = γ ^ ((1 : ℝ) / 4) * γ ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hγ,
    show (1 : ℝ) / 4 + (1 : ℝ) / 4 = 1 / (2 : ℝ) by norm_num]

/-- `√γ (log γ)² ≤ 64 γ^{1/4}` on `(0,1]`. -/
theorem sqrt_mul_log_sq_le_quarter (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    Real.sqrt γ * (Real.log γ) ^ 2 ≤ 64 * γ ^ ((1 : ℝ) / 4) := by
  have h := gamma_quarter_log_sq_le hγ hγ1
  have hq0 : (0 : ℝ) ≤ γ ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hγ.le _
  calc Real.sqrt γ * (Real.log γ) ^ 2
      = γ ^ ((1 : ℝ) / 4) * (γ ^ ((1 : ℝ) / 4) * (Real.log γ) ^ 2) := by
        rw [sqrt_eq_quarter_mul_quarter hγ]; ring
    _ ≤ γ ^ ((1 : ℝ) / 4) * 64 := mul_le_mul_of_nonneg_left h hq0
    _ = 64 * γ ^ ((1 : ℝ) / 4) := mul_comm _ _

/-- **Residual absorption (stage 2).** The smallness condition
`√γ (log γ)² ≤ c⋆` consumed by `residual_le_of_small` follows from the paper's own
hypothesis `γ ≤ C^{-10} c⋆^{10}` whenever `C ≥ 64`. -/
theorem sqrt_mul_log_sq_le_of_gamma_small
    (hc : 0 < cstar) (hc1 : cstar ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hC : 64 ≤ Cbig)
    (hsm : γ ≤ Cbig ^ (-(10 : ℝ)) * cstar ^ (10 : ℝ)) :
    Real.sqrt γ * (Real.log γ) ^ 2 ≤ cstar := by
  have hCb0 : (0 : ℝ) < Cbig := lt_of_lt_of_le (by norm_num) hC
  have hCb1 : (1 : ℝ) ≤ Cbig := le_trans (by norm_num) hC
  -- push the smallness hypothesis through the monotone `1/4` power
  have h4 : γ ^ ((1 : ℝ) / 4)
      ≤ Cbig ^ (-(5 : ℝ) / 2) * cstar ^ ((5 : ℝ) / 2) := by
    have hmono : γ ^ ((1 : ℝ) / 4)
        ≤ (Cbig ^ (-(10 : ℝ)) * cstar ^ (10 : ℝ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow hγ.le hsm (by norm_num)
    have hsplit : (Cbig ^ (-(10 : ℝ)) * cstar ^ (10 : ℝ)) ^ ((1 : ℝ) / 4)
        = Cbig ^ (-(5 : ℝ) / 2) * cstar ^ ((5 : ℝ) / 2) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hCb0.le _) (Real.rpow_nonneg hc.le _),
        ← Real.rpow_mul hCb0.le, ← Real.rpow_mul hc.le,
        show -(10 : ℝ) * ((1 : ℝ) / 4) = -(5 : ℝ) / 2 by norm_num,
        show (10 : ℝ) * ((1 : ℝ) / 4) = (5 : ℝ) / 2 by norm_num]
    rwa [hsplit] at hmono
  -- `c⋆^{5/2} ≤ c⋆`
  have hc52 : cstar ^ ((5 : ℝ) / 2) ≤ cstar := by
    have h := Real.rpow_le_rpow_of_exponent_ge hc hc1
      (show (1 : ℝ) ≤ (5 : ℝ) / 2 by norm_num)
    rwa [Real.rpow_one] at h
  -- `64 C^{-5/2} ≤ 1`
  have hCpos : (0 : ℝ) < Cbig ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hCb0 _
  have hCpow : (64 : ℝ) ≤ Cbig ^ ((5 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hCb1
      (show (1 : ℝ) ≤ (5 : ℝ) / 2 by norm_num)
    rw [Real.rpow_one] at h
    linarith only [h, hC]
  have hneg : Cbig ^ (-(5 : ℝ) / 2) = (Cbig ^ ((5 : ℝ) / 2))⁻¹ := by
    rw [show -(5 : ℝ) / 2 = -((5 : ℝ) / 2) by ring, Real.rpow_neg hCb0.le]
  have h6 : 64 * Cbig ^ (-(5 : ℝ) / 2) ≤ 1 := by
    rw [hneg]
    have h := mul_le_mul_of_nonneg_right hCpow (le_of_lt (inv_pos.mpr hCpos))
    rwa [mul_inv_cancel₀ hCpos.ne'] at h
  have hc52nonneg : (0 : ℝ) ≤ cstar ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hc.le _
  calc Real.sqrt γ * (Real.log γ) ^ 2
      ≤ 64 * γ ^ ((1 : ℝ) / 4) := sqrt_mul_log_sq_le_quarter hγ hγ1
    _ ≤ 64 * (Cbig ^ (-(5 : ℝ) / 2) * cstar ^ ((5 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = 64 * Cbig ^ (-(5 : ℝ) / 2) * cstar ^ ((5 : ℝ) / 2) := by ring
    _ ≤ 1 * cstar ^ ((5 : ℝ) / 2) := mul_le_mul_of_nonneg_right h6 hc52nonneg
    _ = cstar ^ ((5 : ℝ) / 2) := one_mul _
    _ ≤ cstar := hc52

/-! ## The one-shot collapse -/

/-- **`l.minimal.scale.sep` envelope reconciliation.** The three deterministic
levels and the residual of the Lemma's proof all collapse into the single
envelope `c⋆⁻¹ s^{−7/2} √γ`, at the cost of the constant `3C + 1`. -/
theorem sepEnvelope_collapse
    (hc : 0 < cstar) (hc1 : cstar ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) (hγ : 0 < γ)
    (hC : 0 ≤ C) (hsmall : Real.sqrt γ * (Real.log γ) ^ 2 ≤ cstar) :
    C * cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ
      + C * cstar ^ (-(1 : ℝ) / 2) * s⁻¹ * Real.sqrt γ
      + C * cstar ^ (-(1 : ℝ) / 2) * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ
      + cstar ^ (-(2 : ℝ)) * s⁻¹ * γ * (Real.log γ) ^ 2
      ≤ (3 * C + 1) * (cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ) := by
  have h2 := detLevel2_le hc hc1 hs hs1 hγ.le hC
  have h3 := detLevel3_le hc hc1 hs hs1 hγ.le hC
  have h4 := residual_le_of_small hc hc1 hs hs1 hγ hsmall
  linarith only [h2, h3, h4]

/-! ## Fluctuation-side envelope scaling

The `Γ₂`-fluctuation scales downstream carry an extra factor
`((m − n : ℤ) : ℝ) ^ (-(1:ℝ)/2)`; these two lemmas apply the same collapse with
that trailing factor (and a leading constant) left abstract, so they slot directly
into a `calc`. -/

/-- Level-2 fluctuation envelope scaling:
`K · (c⋆^{−1/2} s^{−1} √γ) · L ≤ K · (c⋆⁻¹ s^{−7/2} √γ) · L`. -/
theorem sepFluc_scale_le (hK : 0 ≤ K) (hc : 0 < cstar) (hc1 : cstar ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hγ : 0 ≤ γ) (hL : 0 ≤ L) :
    K * (cstar ^ (-(1 : ℝ) / 2) * s⁻¹ * Real.sqrt γ) * L
      ≤ K * (cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ) * L := by
  have _hγ := hγ
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (env2_le hc hc1 hs hs1) hK) hL

/-- Level-3 fluctuation envelope scaling:
`K · (c⋆^{−1/2} s^{−7/2} √γ) · L ≤ K · (c⋆⁻¹ s^{−7/2} √γ) · L`. -/
theorem sepFluc_scale_le' (hK : 0 ≤ K) (hc : 0 < cstar) (hc1 : cstar ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hγ : 0 ≤ γ) (hL : 0 ≤ L) :
    K * (cstar ^ (-(1 : ℝ) / 2) * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ) * L
      ≤ K * (cstar⁻¹ * s ^ (-(7 : ℝ) / 2) * Real.sqrt γ) * L := by
  have _hγ := hγ
  have _hs1 := hs1
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (env3_le hc hc1 hs) hK) hL

end Algsuperdiff.Probability
