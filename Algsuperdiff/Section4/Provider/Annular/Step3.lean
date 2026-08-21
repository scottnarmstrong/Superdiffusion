/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast

/-!
# The Step-3 regrouping of the annular decomposition

Local helpers for ABK26, Section 4.1, proof of Proposition
`p.mathcalE.annular.decomp`, Step 3: the arithmetic that converts the
intermediate five-term estimate `e.mathcalE.annular.decomp.pre.zero` into the
final four-term display, together with the good-event corollary.

Everything here is a proved *conditional* helper over abstract reals.  The
caller-supplied inequalities (the three field-level order-of-summation
interchanges, the `sigma-bar` continuity sum, the `l^1`/`W^{2,infty}` sums) are
conditional A obligations, not source premises; no source node is claimed,
realized or closed by this module.

## Contents

* `poly2_geom_tail_le` -- the polynomial-times-geometric summation core
  `sum_i (i+1)^2 r^i <= 2 (1-r)^(-3)`, the origin of the `C s^(-3)` constants of
  the three Step-3 interchanges (`1 - 3^(-s/2)` is comparable to `s`).
* `annular_sum_interchange` -- the order-of-summation swap over finite blocks.
* `IsAnnularDecomp` -- a local abbreviation for the four-term shape.
* `sub_four_gamma_inv_cube_le` -- the `(s - 4 gamma)^(-3) <= 8 s^(-3)`
  absorption under the standing hypothesis `s >= 8 gamma`, which is what lets
  both `G_1^b` interchanges be quoted with the single constant `C s^(-3)`.
* `annularDecomp_of_preZero` -- the regrouping proper: the `s * s^(-3) = s^(-2)`
  collapses and the constant absorption, with the fifth `pre.zero` term entering
  through the free `hGm` slot and the `sigma-bar` term through the free constant
  `Csig`.
* `mathcalE_annular_decomp_good_event` -- the good-event corollary
  `Ecal <= 2 sqrt C * epsilon`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

noncomputable section

/-! ## The polynomial-times-geometric summation core -/

/-- **Polynomial-times-geometric tail (abstract reals).**  For `r` in `[0,1)`,
`sum_i (i+1)^2 r^i <= 2 (1-r)^(-3)`, via `sum_i C(i+2,2) r^i = (1-r)^(-3)` and
the termwise bound `(i+1)^2 <= 2 C(i+2,2)`.  With `1 - r` comparable to `s`
(base `r = 3^(-s/2)`) this is the origin of the `C s^(-3)` factors of Step 3. -/
theorem poly2_geom_tail_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' i : ℕ, ((i : ℝ) + 1) ^ 2 * r ^ i ≤ 2 / (1 - r) ^ 3 := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hch : ∑' n : ℕ, ((n + 2).choose 2 : ℝ) * r ^ n = 1 / (1 - r) ^ (2 + 1) :=
    tsum_choose_mul_geometric_of_norm_lt_one 2 hnorm
  have hchSummable : Summable (fun n : ℕ => ((n + 2).choose 2 : ℝ) * r ^ n) :=
    summable_choose_mul_geometric_of_norm_lt_one 2 hnorm
  have hterm : ∀ i : ℕ, ((i : ℝ) + 1) ^ 2 * r ^ i
      ≤ 2 * (((i + 2).choose 2 : ℝ) * r ^ i) := by
    intro i
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hle : ((i : ℝ) + 1) ^ 2 ≤ 2 * ((i + 2).choose 2 : ℝ) := by
      rw [Nat.cast_choose_two]
      push_cast
      linarith only [hi]
    have hrpow : 0 ≤ r ^ i := pow_nonneg hr0 i
    calc ((i : ℝ) + 1) ^ 2 * r ^ i ≤ 2 * ((i + 2).choose 2 : ℝ) * r ^ i :=
          mul_le_mul_of_nonneg_right hle hrpow
      _ = 2 * (((i + 2).choose 2 : ℝ) * r ^ i) := by ring
  have hgnn : ∀ i : ℕ, 0 ≤ ((i : ℝ) + 1) ^ 2 * r ^ i :=
    fun i => mul_nonneg (by positivity) (pow_nonneg hr0 i)
  have hgsum : Summable (fun i : ℕ => 2 * (((i + 2).choose 2 : ℝ) * r ^ i)) :=
    hchSummable.mul_left 2
  have hLsummable : Summable (fun i : ℕ => ((i : ℝ) + 1) ^ 2 * r ^ i) :=
    Summable.of_nonneg_of_le hgnn hterm hgsum
  calc ∑' i : ℕ, ((i : ℝ) + 1) ^ 2 * r ^ i
      ≤ ∑' i : ℕ, 2 * (((i + 2).choose 2 : ℝ) * r ^ i) :=
        Summable.tsum_le_tsum hterm hLsummable hgsum
    _ = 2 * ∑' i : ℕ, ((i + 2).choose 2 : ℝ) * r ^ i := tsum_mul_left
    _ = 2 / (1 - r) ^ 3 := by rw [hch]; ring

/-! ## The order-of-summation interchange -/

/-- **Order-of-summation interchange (abstract reals).**  For a doubly indexed
field over finite index blocks the two iterated sums agree.  This is the
"interchange the order of summation" step of the three Step-3 triple sums on
the finite blocks. -/
theorem annular_sum_interchange (F : ℤ → ℤ → ℝ) (S T : Finset ℤ) :
    ∑ n ∈ S, ∑ j ∈ T, F n j = ∑ j ∈ T, ∑ n ∈ S, F n j :=
  Finset.sum_comm

/-! ## The four-term shape -/

/-- A local abbreviation for the four-term right-hand side shape of the final
Step-3 display:

```
Ecal2 <= C G2 + C s^(-2) cstar^(-4) Rem
        + C s^(-2) cstar^(-1) gamma G1a + C s^(-2) cstar^(-1) gamma G1b .
```

This is a naming convenience inside this provider module.  It is **not** a
source-facing declaration, and neither it nor any theorem below closes,
realizes or instantiates a source node; the source-facing rendering of the
Section 4.1 display is separate, later work at the frozen surface. -/
def IsAnnularDecomp (Ecal2 G2 Rem G1a G1b s cstar gamma C : ℝ) : Prop :=
  Ecal2 ≤ C * G2 + C * (s ^ 2)⁻¹ * (cstar ^ 4)⁻¹ * Rem
    + C * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a + C * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b

/-! ## The `(s - 4 gamma)^(-3)` absorption -/

/-- **The `(s - 4 gamma)^(-3) -> s^(-3)` absorption.**  The second Step-3
interchange produces the constant `C (s - 4 gamma)^(-3)`; under the standing
hypothesis `s >= 8 gamma` one has `s - 4 gamma >= s/2`, hence `(s - 4
gamma)^(-3) <= 8 s^(-3)`, so both interchanges may be quoted with the single
constant `C s^(-3)`. -/
theorem sub_four_gamma_inv_cube_le {s gamma : ℝ} (hs : 0 < s)
    (hsg : 8 * gamma ≤ s) : ((s - 4 * gamma) ^ 3)⁻¹ ≤ 8 * (s ^ 3)⁻¹ := by
  have hd : 0 < s - 4 * gamma := by linarith only [hs, hsg]
  have hcube : (s / 2) ^ 3 ≤ (s - 4 * gamma) ^ 3 :=
    pow_le_pow_left₀ (by linarith only [hs]) (by linarith only [hsg]) 3
  have key : s ^ 3 ≤ 8 * (s - 4 * gamma) ^ 3 := by linarith only [hcube]
  rw [← sub_nonneg]
  have hrw : 8 * (s ^ 3)⁻¹ - ((s - 4 * gamma) ^ 3)⁻¹
      = (8 * (s - 4 * gamma) ^ 3 - s ^ 3) / (s ^ 3 * (s - 4 * gamma) ^ 3) := by
    field_simp
  rw [hrw]
  exact div_nonneg (by linarith only [key]) (by positivity)

/-! ## The Step-3 regrouping -/

/-- **The Step-3 regrouping.**  From the five-term `pre.zero` shape and the
three Step-3 interchange bounds, the four-term shape follows with a single
output constant.

The caller supplies:

* `hpre` -- the five-term `pre.zero` estimate;
* `hgrad`, `hL2` -- the two `G_1^b` triple-sum interchanges, the `(s - 4
  gamma)^(-3)` of the second already folded into `s^(-3)` by
  `sub_four_gamma_inv_cube_le`;
* `hsig` -- the `sigma-bar` continuity sum, carried with a **free** constant
  `Csig`.  That freedom is what absorbs the annulus multiplicity the printed
  second `pre.zero` term omits (see the resummation module): the multiplicity
  costs one extra power of `(s - 2 gamma)^(-1)`, i.e. `Csig` of order `s^(-1)`,
  and nothing downstream changes;
* `hGm` -- the free `hGm` slot: the fifth `pre.zero` term is already a `G_1^a`
  term.

Proved here are the `s * s^(-3) = s^(-2)` collapses and the constant
absorption.  Every hypothesis is a conditional A obligation on the caller. -/
theorem annularDecomp_of_preZero
    {Ecal2 G2raw SigSum GradSum L2Sum Gm Rem G1a G1b s cstar gamma C Csig Cgrad
      CL2 Cout : ℝ}
    (hs : 0 < s) (hcstar : 0 < cstar) (hgamma : 0 ≤ gamma) (hC : 0 ≤ C)
    (hG2raw : 0 ≤ G2raw) (hRem : 0 ≤ Rem) (hG1a0 : 0 ≤ G1a) (hG1b0 : 0 ≤ G1b)
    (hpre : Ecal2 ≤ C * s * G2raw + C * s * SigSum
      + C * cstar⁻¹ * gamma * s * GradSum + C * cstar⁻¹ * gamma * s * L2Sum
      + C * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * Gm)
    (hsig : SigSum ≤ Csig * (s ^ 3)⁻¹ * (cstar ^ 4)⁻¹ * Rem)
    (hgrad : GradSum ≤ Cgrad * (s ^ 3)⁻¹ * G1b)
    (hL2 : L2Sum ≤ CL2 * (s ^ 3)⁻¹ * G1b)
    (hGm : Gm ≤ G1a)
    (hCout1 : C ≤ Cout) (hCout2 : C * Csig ≤ Cout)
    (hCout3 : C * (Cgrad + CL2) ≤ Cout) :
    IsAnnularDecomp Ecal2 (s * G2raw) Rem G1a G1b s cstar gamma Cout := by
  unfold IsAnnularDecomp
  have hs' : s ≠ 0 := ne_of_gt hs
  have hcs' : cstar ≠ 0 := ne_of_gt hcstar
  have hcsinv : (0 : ℝ) ≤ cstar⁻¹ := inv_nonneg.2 hcstar.le
  have hpref : (0 : ℝ) ≤ C * cstar⁻¹ * gamma * s :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hcsinv) hgamma) hs.le
  have hnnRem : (0 : ℝ) ≤ (s ^ 2)⁻¹ * (cstar ^ 4)⁻¹ * Rem :=
    mul_nonneg (by positivity) hRem
  have hnnG1a : (0 : ℝ) ≤ (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hcsinv) hgamma) hG1a0
  have hnnG1b : (0 : ℝ) ≤ (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hcsinv) hgamma) hG1b0
  have hT1 : C * s * G2raw ≤ Cout * (s * G2raw) := by
    calc C * s * G2raw = C * (s * G2raw) := by ring
      _ ≤ Cout * (s * G2raw) :=
          mul_le_mul_of_nonneg_right hCout1 (mul_nonneg hs.le hG2raw)
  have hT2 : C * s * SigSum ≤ Cout * (s ^ 2)⁻¹ * (cstar ^ 4)⁻¹ * Rem := by
    calc C * s * SigSum
        ≤ C * s * (Csig * (s ^ 3)⁻¹ * (cstar ^ 4)⁻¹ * Rem) :=
          mul_le_mul_of_nonneg_left hsig (mul_nonneg hC hs.le)
      _ = (C * Csig) * ((s ^ 2)⁻¹ * (cstar ^ 4)⁻¹ * Rem) := by field_simp
      _ ≤ Cout * ((s ^ 2)⁻¹ * (cstar ^ 4)⁻¹ * Rem) :=
          mul_le_mul_of_nonneg_right hCout2 hnnRem
      _ = Cout * (s ^ 2)⁻¹ * (cstar ^ 4)⁻¹ * Rem := by ring
  have hT34 : C * cstar⁻¹ * gamma * s * GradSum + C * cstar⁻¹ * gamma * s * L2Sum
      ≤ Cout * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b := by
    calc C * cstar⁻¹ * gamma * s * GradSum + C * cstar⁻¹ * gamma * s * L2Sum
        ≤ C * cstar⁻¹ * gamma * s * (Cgrad * (s ^ 3)⁻¹ * G1b)
            + C * cstar⁻¹ * gamma * s * (CL2 * (s ^ 3)⁻¹ * G1b) :=
          add_le_add (mul_le_mul_of_nonneg_left hgrad hpref)
            (mul_le_mul_of_nonneg_left hL2 hpref)
      _ = (C * (Cgrad + CL2)) * ((s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b) := by field_simp
      _ ≤ Cout * ((s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b) :=
          mul_le_mul_of_nonneg_right hCout3 hnnG1b
      _ = Cout * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b := by ring
  have hT5 : C * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * Gm
      ≤ Cout * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a := by
    calc C * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * Gm
        ≤ C * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * G1a :=
          mul_le_mul_of_nonneg_left hGm
            (mul_nonneg (mul_nonneg (mul_nonneg hC hcsinv) (by positivity)) hgamma)
      _ = C * ((s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a) := by ring
      _ ≤ Cout * ((s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a) :=
          mul_le_mul_of_nonneg_right hCout1 hnnG1a
      _ = Cout * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a := by ring
  linarith only [hpre, hT1, hT2, hT34, hT5]

/-! ## The good-event corollary -/

/-- **The good-event corollary.**  From the four-term shape and the
event-smallness inputs, `Ecal <= 2 sqrt C * epsilon`.

The three non-`G2` terms each collapse to `C epsilon^2` (`s^(-2) cstar^(-4)
(gamma |log gamma|^2)^2 <= epsilon^2` and `s^(-2) cstar^(-1) gamma * s^2
epsilon^2 cstar gamma^(-1) = epsilon^2`), giving `Ecal^2 <= 4 C epsilon^2`.
All the smallness inputs are conditional A obligations on the caller. -/
theorem mathcalE_annular_decomp_good_event
    {Ecal G2 G1a G1b s cstar gamma ep C : ℝ}
    (hs0 : 0 < s) (hcstar0 : 0 < cstar) (hgamma0 : 0 < gamma) (hep0 : 0 ≤ ep)
    (hC0 : 0 ≤ C) (hEcal0 : 0 ≤ Ecal)
    (hdecomp : IsAnnularDecomp (Ecal ^ 2) G2 (gamma ^ 2 * |Real.log gamma| ^ 4)
      G1a G1b s cstar gamma C)
    (hG2 : G2 ≤ ep ^ 2)
    (hG1a : G1a ≤ s ^ 2 * ep ^ 2 * cstar * gamma⁻¹)
    (hG1b : G1b ≤ s ^ 2 * ep ^ 2 * cstar * gamma⁻¹)
    (hcond : gamma * |Real.log gamma| ^ 2 ≤ s * cstar ^ 2 * ep) :
    Ecal ≤ 2 * Real.sqrt C * ep := by
  unfold IsAnnularDecomp at hdecomp
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hcs4 : (0 : ℝ) < cstar ^ 4 := by positivity
  set Lg : ℝ := |Real.log gamma| with hLg
  have hLg0 : 0 ≤ Lg := by
    rw [hLg]
    exact abs_nonneg _
  have hRem : C * (s ^ 2)⁻¹ * (cstar ^ 4)⁻¹ * (gamma ^ 2 * Lg ^ 4) ≤ C * ep ^ 2 := by
    have hnn : 0 ≤ gamma * Lg ^ 2 := by positivity
    have hsq : (gamma * Lg ^ 2) ^ 2 ≤ (s * cstar ^ 2 * ep) ^ 2 :=
      pow_le_pow_left₀ hnn hcond 2
    have hexpand : (gamma * Lg ^ 2) ^ 2 = gamma ^ 2 * Lg ^ 4 := by ring
    have hrhs : (s * cstar ^ 2 * ep) ^ 2 = s ^ 2 * cstar ^ 4 * ep ^ 2 := by ring
    rw [hexpand, hrhs] at hsq
    have hpre : C * (s ^ 2)⁻¹ * (cstar ^ 4)⁻¹ * (gamma ^ 2 * Lg ^ 4)
        ≤ C * (s ^ 2)⁻¹ * (cstar ^ 4)⁻¹ * (s ^ 2 * cstar ^ 4 * ep ^ 2) := by
      refine mul_le_mul_of_nonneg_left hsq ?_
      positivity
    refine hpre.trans_eq ?_
    field_simp
  have hG1aTerm : C * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a ≤ C * ep ^ 2 := by
    have hpre : C * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a
        ≤ C * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * (s ^ 2 * ep ^ 2 * cstar * gamma⁻¹) := by
      refine mul_le_mul_of_nonneg_left hG1a ?_
      positivity
    refine hpre.trans_eq ?_
    field_simp
  have hG1bTerm : C * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b ≤ C * ep ^ 2 := by
    have hpre : C * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b
        ≤ C * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * (s ^ 2 * ep ^ 2 * cstar * gamma⁻¹) := by
      refine mul_le_mul_of_nonneg_left hG1b ?_
      positivity
    refine hpre.trans_eq ?_
    field_simp
  have hG2Term : C * G2 ≤ C * ep ^ 2 := mul_le_mul_of_nonneg_left hG2 hC0
  have hsqC : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC0
  have hrhs0 : 0 ≤ 2 * Real.sqrt C * ep := by positivity
  have hrhssq : (2 * Real.sqrt C * ep) ^ 2 = 4 * C * ep ^ 2 := by
    rw [mul_pow, mul_pow, hsqC]
    ring
  have hsq : Ecal ^ 2 ≤ (2 * Real.sqrt C * ep) ^ 2 := by
    rw [hrhssq]
    calc Ecal ^ 2 ≤ C * G2 + C * (s ^ 2)⁻¹ * (cstar ^ 4)⁻¹ * (gamma ^ 2 * Lg ^ 4)
            + C * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a
            + C * (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b := hdecomp
      _ ≤ C * ep ^ 2 + C * ep ^ 2 + C * ep ^ 2 + C * ep ^ 2 :=
          add_le_add (add_le_add (add_le_add hG2Term hRem) hG1aTerm) hG1bTerm
      _ = 4 * C * ep ^ 2 := by ring
  calc Ecal = Real.sqrt (Ecal ^ 2) := (Real.sqrt_sq hEcal0).symm
    _ ≤ Real.sqrt ((2 * Real.sqrt C * ep) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 * Real.sqrt C * ep := Real.sqrt_sq hrhs0

end

end Algsuperdiff.Section4.Provider.Annular
