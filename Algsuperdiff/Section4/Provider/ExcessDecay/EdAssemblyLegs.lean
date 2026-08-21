/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.EnnrealShell

/-!
# The `B.toReal` expansion of the anchor's four-leg display

This module is that expansion, in the direction the one-step consumers need —
`ℝ≥0∞` display **down to** real legs — and it is the exact mirror of
`EnnrealShell`'s `le_ofReal_mul_bracket_add_three`, which goes the other way.

## The two atoms

* `toReal_ofReal_mul_bracket_add_three_le` — the expansion itself.  It is
  **unconditional**: no carrier needs to be finite.
* `ofReal_mul_bracket_add_three_ne_top` — the finiteness of the display, which is
  what the one-step consumers' own `hB` slot asks for.  Here the four carriers
  *do* have to be finite; the anchor's clause (iv) `MemLp` binders and the `H¹`
  data of `u` and `h` are exactly what supplies them at the consumption site.

The shape targeted is the frozen theorem's general clause verbatim,

```text
  ofReal c₁ * (X + ofReal b) + ofReal c₂ * Y + ofReal c₃ * Z + ofReal c₄ * W
```

with the in-bracket `∇h` companion `b` carrying no constant of its own (the
frozen statement's deliberate asymmetry).

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the display whose shell is
  expanded).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## 1. The expansion -/

/-- **The `B.toReal` expansion of the anchor's four-leg display.**

`ENNReal.toReal` is multiplicative unconditionally and subadditive unconditionally, so
no finiteness hypothesis is needed: at a `⊤` carrier the left-hand side
collapses to `0` and the bound is trivial. -/
theorem toReal_ofReal_mul_bracket_add_three_le {c₁ b c₂ c₃ c₄ : ℝ}
    (X Y Z W : ℝ≥0∞) (hc₁ : 0 ≤ c₁) (hb : 0 ≤ b) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hc₄ : 0 ≤ c₄) :
    (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
        ENNReal.ofReal c₃ * Z + ENNReal.ofReal c₄ * W).toReal ≤
      c₁ * (X.toReal + b) + c₂ * Y.toReal + c₃ * Z.toReal + c₄ * W.toReal := by
  have hbracket : (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b)).toReal ≤
      c₁ * (X.toReal + b) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₁]
    refine mul_le_mul_of_nonneg_left ?_ hc₁
    refine le_trans ENNReal.toReal_add_le (le_of_eq ?_)
    rw [ENNReal.toReal_ofReal hb]
  have hY : (ENNReal.ofReal c₂ * Y).toReal = c₂ * Y.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₂]
  have hZ : (ENNReal.ofReal c₃ * Z).toReal = c₃ * Z.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₃]
  have hW : (ENNReal.ofReal c₄ * W).toReal = c₄ * W.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₄]
  have hstep1 : (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
        ENNReal.ofReal c₃ * Z + ENNReal.ofReal c₄ * W).toReal ≤
      (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
        ENNReal.ofReal c₃ * Z).toReal + (ENNReal.ofReal c₄ * W).toReal :=
    ENNReal.toReal_add_le
  have hstep2 : (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
        ENNReal.ofReal c₃ * Z).toReal ≤
      (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y).toReal +
        (ENNReal.ofReal c₃ * Z).toReal :=
    ENNReal.toReal_add_le
  have hstep3 : (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y).toReal ≤
      (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b)).toReal + (ENNReal.ofReal c₂ * Y).toReal :=
    ENNReal.toReal_add_le
  linarith only [hstep1, hstep2, hstep3, hbracket, hY, hZ, hW]

/-! ## 2. The finiteness of the display -/

/-- **The anchor's display is finite as soon as its four carriers are.**

This is the `hB` slot of every one-step consumer.  The four carriers are the
mean-subtracted `L̲²` oscillation, the two Gagliardo seminorms and the `∇h`
`L̲²` norm; the anchor's clause (iv) `MemLp` binders and the `H¹` data of `u`
and `h` supply all four at the consumption site. -/
theorem ofReal_mul_bracket_add_three_ne_top {c₁ b c₂ c₃ c₄ : ℝ} {X Y Z W : ℝ≥0∞}
    (hX : X ≠ ⊤) (hY : Y ≠ ⊤) (hZ : Z ≠ ⊤) (hW : W ≠ ⊤) :
    ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
      ENNReal.ofReal c₃ * Z + ENNReal.ofReal c₄ * W ≠ ⊤ := by
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY⟩,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZ⟩,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW⟩
  exact ENNReal.add_ne_top.mpr ⟨hX, ENNReal.ofReal_ne_top⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay
