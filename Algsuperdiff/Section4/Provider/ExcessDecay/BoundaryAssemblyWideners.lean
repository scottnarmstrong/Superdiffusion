/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.EnnrealShell

/-!
# The arity wideners for a general-clause successor

This module proves the widened variants, once, so the successor's re-cut is a
name change and not a proof.  Each widening comes in the two shapes a successor
leg can take:

* **a further summand** — one more top-level leg on the right-hand side;
* **a further bracket slot** — one more companion *inside* the first leg's
  bracket, sharing the flux-error prefactor with the `L̲²` leg (the place the
  frozen statement already puts its `∇h` average companion).

Nothing here is mathematics of the manuscript: every declaration is real or
`ℝ≥0∞` arithmetic on abstract letters, with no cube, no coefficient field, no
measure and no scale anywhere.

## The five pinned helpers, and their wideners

1. the join lane's pinned four-summand bracket nonnegativity — widened
   by `fiveSummandBracket_nonneg` and `fourSummandBracket_nonneg_bracketSlot`;
2. `Join.four_summand_absorb` — widened by
   `five_summand_absorb`;
3. `EnnrealShell.le_ofReal_mul_bracket_add_three` — widened by
   `le_ofReal_mul_bracket_add_four` and `le_ofReal_mul_bracketTwo_add_three`;
4. `ReindexGeneralClause.general_absorb_window` — widened by
   `general_absorb_window_five`;
5. `GeneralClauseInteriorFinal.general_absorb` — widened by
   `general_absorb_five`.

The tracked files are **not** edited: the pinned helpers stay exactly as they
are, and these are independent public siblings.  (They are stated here as
public declarations precisely because the pinned originals are `private` and
therefore invisible to any successor module.)

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the clause whose right-hand
  side arity is at issue).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

/-! ## 1. Nonnegativity of the widened brackets -/

/-- **Nonnegativity of a five-summand successor bracket.**

Widening of the join lane's pinned four-summand bracket nonnegativity
by one further top-level leg `g * V`. -/
theorem fiveSummandBracket_nonneg {a b e f g X c Y Z W V : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 ≤ g) (hX : 0 ≤ X)
    (hc : 0 ≤ c) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hW : 0 ≤ W) (hV : 0 ≤ V) :
    0 ≤ a * (X + c) + b * Y + e * Z + f * W + g * V := by
  have h1 : 0 ≤ a * (X + c) := mul_nonneg ha (add_nonneg hX hc)
  have h2 : 0 ≤ b * Y := mul_nonneg hb hY
  have h3 : 0 ≤ e * Z := mul_nonneg he hZ
  have h4 : 0 ≤ f * W := mul_nonneg hf hW
  have h5 : 0 ≤ g * V := mul_nonneg hg hV
  linarith only [h1, h2, h3, h4, h5]

/-- **Nonnegativity of a four-summand bracket with a second in-bracket
companion.**

Widening of the join lane's pinned four-summand bracket nonnegativity
by one further companion `p` *inside* the first leg's bracket, i.e. sharing that leg's
prefactor `a` rather than carrying one of its own. -/
theorem fourSummandBracket_nonneg_bracketSlot {a b e f X c p Y Z W : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (he : 0 ≤ e) (hf : 0 ≤ f) (hX : 0 ≤ X) (hc : 0 ≤ c)
    (hp : 0 ≤ p) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hW : 0 ≤ W) :
    0 ≤ a * (X + c + p) + b * Y + e * Z + f * W := by
  have h1 : 0 ≤ a * (X + c + p) :=
    mul_nonneg ha (add_nonneg (add_nonneg hX hc) hp)
  have h2 : 0 ≤ b * Y := mul_nonneg hb hY
  have h3 : 0 ≤ e * Z := mul_nonneg he hZ
  have h4 : 0 ≤ f * W := mul_nonneg hf hW
  linarith only [h1, h2, h3, h4]

/-! ## 2. The joint-constant absorption at one more summand -/

/-- **Raising a five-summand right-hand side to the joint constant.**

Widening of `Join`'s pinned `four_summand_absorb` by one further
nonnegative leg `t₅`. -/
theorem five_summand_absorb {C₀ C t₁ t₂ t₃ t₄ t₅ : ℝ} (h : C₀ ≤ C)
    (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (h₃ : 0 ≤ t₃) (h₄ : 0 ≤ t₄) (h₅ : 0 ≤ t₅) :
    C₀ * (t₁ + t₂ + t₃ + t₄ + t₅) ≤
      C * t₁ + C * t₂ + C * t₃ + C * t₄ + C * t₅ := by
  have e₁ := mul_le_mul_of_nonneg_right h h₁
  have e₂ := mul_le_mul_of_nonneg_right h h₂
  have e₃ := mul_le_mul_of_nonneg_right h h₃
  have e₄ := mul_le_mul_of_nonneg_right h h₄
  have e₅ := mul_le_mul_of_nonneg_right h h₅
  have hexp : C₀ * (t₁ + t₂ + t₃ + t₄ + t₅) =
      C₀ * t₁ + C₀ * t₂ + C₀ * t₃ + C₀ * t₄ + C₀ * t₅ := by ring
  rw [hexp]
  linarith only [e₁, e₂, e₃, e₄, e₅]

/-! ## 3. The `ℝ≥0∞` shell at one more leg -/

/-- **The five-summand shell with the in-bracket companion.**

Widening of `EnnrealShell`'s `le_ofReal_mul_bracket_add_three` by one further
top-level leg `ofReal c₅ * V`.  As there, only the left-hand side is required
to be finite: the right-hand carriers may be `⊤`. -/
theorem le_ofReal_mul_bracket_add_four {A X Y Z W V : ℝ≥0∞}
    {c₁ b c₂ c₃ c₄ c₅ : ℝ} (hA : A ≠ ⊤) (hc₁ : 0 ≤ c₁) (hb : 0 ≤ b)
    (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) (hc₅ : 0 ≤ c₅)
    (h : A.toReal ≤
      c₁ * (X.toReal + b) + c₂ * Y.toReal + c₃ * Z.toReal + c₄ * W.toReal +
        c₅ * V.toReal) :
    A ≤ ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
      ENNReal.ofReal c₃ * Z + ENNReal.ofReal c₄ * W +
      ENNReal.ofReal c₅ * V := by
  have hxb : (0 : ℝ) ≤ c₁ * (X.toReal + b) :=
    mul_nonneg hc₁ (add_nonneg ENNReal.toReal_nonneg hb)
  have hy : (0 : ℝ) ≤ c₂ * Y.toReal := mul_nonneg hc₂ ENNReal.toReal_nonneg
  have hz : (0 : ℝ) ≤ c₃ * Z.toReal := mul_nonneg hc₃ ENNReal.toReal_nonneg
  have hw : (0 : ℝ) ≤ c₄ * W.toReal := mul_nonneg hc₄ ENNReal.toReal_nonneg
  have hv : (0 : ℝ) ≤ c₅ * V.toReal := mul_nonneg hc₅ ENNReal.toReal_nonneg
  have hbracket : ENNReal.ofReal (c₁ * (X.toReal + b)) ≤
      ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) := by
    have hsplit : c₁ * (X.toReal + b) = c₁ * X.toReal + c₁ * b := by ring
    calc ENNReal.ofReal (c₁ * (X.toReal + b))
        = ENNReal.ofReal (c₁ * X.toReal) + ENNReal.ofReal (c₁ * b) := by
          rw [hsplit, ENNReal.ofReal_add (mul_nonneg hc₁ ENNReal.toReal_nonneg)
            (mul_nonneg hc₁ hb)]
      _ ≤ ENNReal.ofReal c₁ * X + ENNReal.ofReal c₁ * ENNReal.ofReal b :=
          add_le_add (ofReal_mul_toReal_le hc₁ X)
            (le_of_eq (ENNReal.ofReal_mul hc₁))
      _ = ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) := (mul_add _ _ _).symm
  calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
    _ ≤ ENNReal.ofReal
          (c₁ * (X.toReal + b) + c₂ * Y.toReal + c₃ * Z.toReal +
            c₄ * W.toReal + c₅ * V.toReal) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (c₁ * (X.toReal + b)) + ENNReal.ofReal (c₂ * Y.toReal) +
          ENNReal.ofReal (c₃ * Z.toReal) + ENNReal.ofReal (c₄ * W.toReal) +
          ENNReal.ofReal (c₅ * V.toReal) := by
        rw [ENNReal.ofReal_add (by linarith only [hxb, hy, hz, hw]) hv,
          ENNReal.ofReal_add (by linarith only [hxb, hy, hz]) hw,
          ENNReal.ofReal_add (by linarith only [hxb, hy]) hz,
          ENNReal.ofReal_add hxb hy]
    _ ≤ ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
          ENNReal.ofReal c₃ * Z + ENNReal.ofReal c₄ * W +
          ENNReal.ofReal c₅ * V :=
        add_le_add (add_le_add (add_le_add (add_le_add hbracket
          (ofReal_mul_toReal_le hc₂ Y)) (ofReal_mul_toReal_le hc₃ Z))
          (ofReal_mul_toReal_le hc₄ W)) (ofReal_mul_toReal_le hc₅ V)

/-- **The four-summand shell with two in-bracket companions.**

Widening of `EnnrealShell`'s `le_ofReal_mul_bracket_add_three` by a *second*
companion `b'` inside the first leg's bracket, sharing the prefactor `c₁`. -/
theorem le_ofReal_mul_bracketTwo_add_three {A X Y Z W : ℝ≥0∞}
    {c₁ b b' c₂ c₃ c₄ : ℝ} (hA : A ≠ ⊤) (hc₁ : 0 ≤ c₁) (hb : 0 ≤ b)
    (hb' : 0 ≤ b') (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄)
    (h : A.toReal ≤
      c₁ * (X.toReal + b + b') + c₂ * Y.toReal + c₃ * Z.toReal +
        c₄ * W.toReal) :
    A ≤ ENNReal.ofReal c₁ * (X + ENNReal.ofReal b + ENNReal.ofReal b') +
      ENNReal.ofReal c₂ * Y + ENNReal.ofReal c₃ * Z +
      ENNReal.ofReal c₄ * W := by
  have hxb : (0 : ℝ) ≤ c₁ * (X.toReal + b + b') :=
    mul_nonneg hc₁ (add_nonneg (add_nonneg ENNReal.toReal_nonneg hb) hb')
  have hy : (0 : ℝ) ≤ c₂ * Y.toReal := mul_nonneg hc₂ ENNReal.toReal_nonneg
  have hz : (0 : ℝ) ≤ c₃ * Z.toReal := mul_nonneg hc₃ ENNReal.toReal_nonneg
  have hw : (0 : ℝ) ≤ c₄ * W.toReal := mul_nonneg hc₄ ENNReal.toReal_nonneg
  have hbracket : ENNReal.ofReal (c₁ * (X.toReal + b + b')) ≤
      ENNReal.ofReal c₁ * (X + ENNReal.ofReal b + ENNReal.ofReal b') := by
    have hsplit : c₁ * (X.toReal + b + b') =
        c₁ * X.toReal + c₁ * b + c₁ * b' := by ring
    calc ENNReal.ofReal (c₁ * (X.toReal + b + b'))
        = ENNReal.ofReal (c₁ * X.toReal) + ENNReal.ofReal (c₁ * b) +
            ENNReal.ofReal (c₁ * b') := by
          rw [hsplit,
            ENNReal.ofReal_add
              (by
                have h1 : (0 : ℝ) ≤ c₁ * X.toReal :=
                  mul_nonneg hc₁ ENNReal.toReal_nonneg
                have h2 : (0 : ℝ) ≤ c₁ * b := mul_nonneg hc₁ hb
                linarith only [h1, h2])
              (mul_nonneg hc₁ hb'),
            ENNReal.ofReal_add (mul_nonneg hc₁ ENNReal.toReal_nonneg)
              (mul_nonneg hc₁ hb)]
      _ ≤ ENNReal.ofReal c₁ * X + ENNReal.ofReal c₁ * ENNReal.ofReal b +
            ENNReal.ofReal c₁ * ENNReal.ofReal b' :=
          add_le_add (add_le_add (ofReal_mul_toReal_le hc₁ X)
            (le_of_eq (ENNReal.ofReal_mul hc₁)))
            (le_of_eq (ENNReal.ofReal_mul hc₁))
      _ = ENNReal.ofReal c₁ * (X + ENNReal.ofReal b + ENNReal.ofReal b') := by
          rw [mul_add, mul_add]
  calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
    _ ≤ ENNReal.ofReal
          (c₁ * (X.toReal + b + b') + c₂ * Y.toReal + c₃ * Z.toReal +
            c₄ * W.toReal) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (c₁ * (X.toReal + b + b')) +
          ENNReal.ofReal (c₂ * Y.toReal) + ENNReal.ofReal (c₃ * Z.toReal) +
          ENNReal.ofReal (c₄ * W.toReal) := by
        rw [ENNReal.ofReal_add (by linarith only [hxb, hy, hz]) hw,
          ENNReal.ofReal_add (by linarith only [hxb, hy]) hz,
          ENNReal.ofReal_add hxb hy]
    _ ≤ ENNReal.ofReal c₁ * (X + ENNReal.ofReal b + ENNReal.ofReal b') +
          ENNReal.ofReal c₂ * Y + ENNReal.ofReal c₃ * Z +
          ENNReal.ofReal c₄ * W :=
        add_le_add (add_le_add (add_le_add hbracket
          (ofReal_mul_toReal_le hc₂ Y)) (ofReal_mul_toReal_le hc₃ Z))
          (ofReal_mul_toReal_le hc₄ W)

/-! ## 4. The re-cut absorptions at one more leg -/

/-- **The re-cut absorption with a fifth nonnegative leg.**

Widening of `ReindexGeneralClause`'s pinned `general_absorb_window` by the leg
`T5`: the composed two-summand bound is absorbed into a *five*-summand
successor right-hand side, with the window factor `K` paid on both surviving
legs and the `σ̄` gap-3 factor `4` on the force leg, exactly as before. -/
theorem general_absorb_window_five {Cf C K A A' B B' T3 T4 T5 : ℝ} (hK : 0 ≤ K)
    (hAA' : A ≤ K * A') (hA' : 0 ≤ A') (hBB' : B ≤ 4 * K * B') (hB' : 0 ≤ B')
    (hT3 : 0 ≤ T3) (hT4 : 0 ≤ T4) (hT5 : 0 ≤ T5) (hCf : 0 ≤ Cf)
    (h1 : K * Cf ≤ C) (h4 : 4 * K * Cf ≤ C) :
    Cf * (A + B) ≤ C * (A' + B' + T3 + T4 + T5) := by
  have hKCf : 0 ≤ K * Cf := mul_nonneg hK hCf
  have hC0 : 0 ≤ C := le_trans hKCf h1
  have hstep1 : Cf * A ≤ C * A' := by
    have ha := mul_le_mul_of_nonneg_left hAA' hCf
    have hb := mul_le_mul_of_nonneg_right h1 hA'
    have hc : Cf * (K * A') = K * Cf * A' := by ring
    rw [hc] at ha
    linarith only [ha, hb]
  have hstep2 : Cf * B ≤ C * B' := by
    have ha := mul_le_mul_of_nonneg_left hBB' hCf
    have hb := mul_le_mul_of_nonneg_right h4 hB'
    have hc : Cf * (4 * K * B') = 4 * K * Cf * B' := by ring
    rw [hc] at ha
    linarith only [ha, hb]
  have h3 : 0 ≤ C * T3 := mul_nonneg hC0 hT3
  have h4' : 0 ≤ C * T4 := mul_nonneg hC0 hT4
  have h5' : 0 ≤ C * T5 := mul_nonneg hC0 hT5
  have hexp : C * (A' + B' + T3 + T4 + T5) =
      C * A' + C * B' + C * T3 + C * T4 + C * T5 := by ring
  have hexp2 : Cf * (A + B) = Cf * A + Cf * B := by ring
  linarith only [hstep1, hstep2, h3, h4', h5', hexp, hexp2]

/-- **The interior re-cut absorption with a fifth nonnegative leg.**

Widening of `GeneralClauseInteriorFinal`'s pinned `general_absorb` by the leg
`T5`; it is `general_absorb_window_five` at the window factor `K = 1`, restated
without that factor so the interior call sites read unchanged. -/
theorem general_absorb_five {Cf C A A' B B' T3 T4 T5 : ℝ} (hAA' : A ≤ A')
    (hA' : 0 ≤ A') (hBB' : B ≤ 4 * B') (hB' : 0 ≤ B') (hT3 : 0 ≤ T3)
    (hT4 : 0 ≤ T4) (hT5 : 0 ≤ T5) (hCf : 0 ≤ Cf) (h1 : Cf ≤ C)
    (h4 : 4 * Cf ≤ C) :
    Cf * (A + B) ≤ C * (A' + B' + T3 + T4 + T5) := by
  have hC0 : 0 ≤ C := le_trans hCf h1
  have hstep1 : Cf * A ≤ C * A' := by
    have ha := mul_le_mul_of_nonneg_left hAA' hCf
    have hb := mul_le_mul_of_nonneg_right h1 hA'
    linarith only [ha, hb]
  have hstep2 : Cf * B ≤ C * B' := by
    have ha := mul_le_mul_of_nonneg_left hBB' hCf
    have hb := mul_le_mul_of_nonneg_right h4 hB'
    linarith only [ha, hb]
  have h3 : 0 ≤ C * T3 := mul_nonneg hC0 hT3
  have h4' : 0 ≤ C * T4 := mul_nonneg hC0 hT4
  have h5' : 0 ≤ C * T5 := mul_nonneg hC0 hT5
  have hexp : C * (A' + B' + T3 + T4 + T5) =
      C * A' + C * B' + C * T3 + C * T4 + C * T5 := by ring
  have hexp2 : Cf * (A + B) = Cf * A + Cf * B := by ring
  linarith only [hstep1, hstep2, h3, h4', h5', hexp, hexp2]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
