/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepSevenEndAssembly
import Algsuperdiff.Section4.Provider.Annular.SigmaBarBudget

/-!
# `t.regularity` Step 7d: the `σ̄` comparison at a generic constant

## The gap this module closes

The Step-7d chain hard-codes the printed comparison

```text
  e.shom.m.vs.shom.n :   σ̄_{n'}  ≤  2 σ̄_m
```

 at the literal constant `2` in five places (`stepSevenDataLeg_merge`,
`stepSevenEnergyDensityEstimate_merged`, `stepSevenEnergyDensityEstimate`,
`stepSevenEnd_chain`, `exists_stepSevenEnd_chain_of_lambda`), while the only
comparison proved here is
`Annular.SigmaBarBudget.sigmaBar_ratio_le_four`, i.e. the constant `4`.

The route is the `rootBracket_collapse` pattern already used for `Ccol`:
generic-`Ccmp` siblings of the pinned theorems, leaving the pinned statements
untouched.

The printed `√2` becomes `√Ccmp`; at `Ccmp = 4` that is `2`.  The difference is
immaterial inside `C(d, c_*)` — the deviation that `StepSevenEndAssembly`'s
docstring already describes.

## What `sigmaBar_ratio_le_four` actually gives

`Annular.sigmaBar_ratio_le_four M hS (hnm : n - 2 ≤ m) (hm : m ≤ m0)` reads
`σ̄_m^{-1}·σ̄_{n-2} ≤ 4`.  Re-indexed at `n := n' + 2` it is exactly `σ̄_{n'} ≤
4 σ̄_m` under `n' ≤ m ≤ m₀` — no adjacency and no plateau hypothesis.

## References

* ABK26, `e.energy.density.estimate`; the assembly.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The proved comparison, in the chain's own slot shape -/

/-- **`e.shom.m.vs.shom.n` at the proved constant `4`.**

`Annular.sigmaBar_ratio_le_four` in the multiplicative form the Step-7d chain
consumes:

```text
  σ̄_{n'}  ≤  4 σ̄_m          for  n' ≤ m ≤ m₀ .
```

Derived from conjunct 1 of the frozen Section-3 `inductionState` at the two
scales alone — no adjacency. -/
theorem sigmaBar_le_four_mul_sigmaBar (M : ABKModel d) {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    {n' m : ℤ} (hnm : n' ≤ m) (hm : m ≤ m0) :
    (Annealed.sigmaBar M n' : ℝ) ≤ 4 * (Annealed.sigmaBar M m : ℝ) := by
  have hsm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hidx : (n' + 2) - 2 = n' := by ring
  have hratio := Annular.sigmaBar_ratio_le_four M hS (n := n' + 2) (m := m)
    (by linarith only [hnm]) hm
  rw [hidx] at hratio
  have hmul := mul_le_mul_of_nonneg_left hratio hsm.le
  have hcancel : (Annealed.sigmaBar M m : ℝ) *
      (((Annealed.sigmaBar M m : ℝ))⁻¹ * (Annealed.sigmaBar M n' : ℝ)) =
      (Annealed.sigmaBar M n' : ℝ) := by
    field_simp
  rw [hcancel] at hmul
  linarith only [hmul]

/-! ## 2. The data-leg collapse, generic in `Ccmp` -/

/-- **`stepSevenDataLeg_merge` at a generic comparison constant**.

```text
  √σ̄_{n'} · W · (σ̄_m^{-1}G + H)  ≤  √Ccmp · W · ((√σ̄_m)^{-1}G + √σ̄_m·H) .
```

At `Ccmp := 2` this is `stepSevenDataLeg_merge` verbatim (machine-checked); at
`Ccmp := 4` it is the proved envelope's own comparison, at cost `2`. -/
theorem stepSevenDataLeg_merge_gen {shomNp shomM Ccmp W G H : ℝ} (hshomM : 0 < shomM)
    (hCcmp : 0 ≤ Ccmp) (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcomp : shomNp ≤ Ccmp * shomM) :
    Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) ≤
      Real.sqrt Ccmp * (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) := by
  have hstep : Real.sqrt shomNp ≤ Real.sqrt Ccmp * Real.sqrt shomM := by
    calc Real.sqrt shomNp ≤ Real.sqrt (Ccmp * shomM) := Real.sqrt_le_sqrt hcomp
      _ = Real.sqrt Ccmp * Real.sqrt shomM := Real.sqrt_mul hCcmp shomM
  have hinv : Real.sqrt shomM * shomM⁻¹ = (Real.sqrt shomM)⁻¹ := by
    have hsq : Real.sqrt shomM * Real.sqrt shomM = shomM := Real.mul_self_sqrt hshomM.le
    field_simp
    linarith only [hsq]
  have hnn : 0 ≤ W * (shomM⁻¹ * G + H) := by
    have : 0 ≤ shomM⁻¹ * G + H :=
      add_nonneg (mul_nonneg (inv_nonneg.mpr hshomM.le) hG) hH
    exact mul_nonneg hW this
  have h1 : Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) ≤
      (Real.sqrt Ccmp * Real.sqrt shomM) * (W * (shomM⁻¹ * G + H)) :=
    mul_le_mul_of_nonneg_right hstep hnn
  have h2 : (Real.sqrt Ccmp * Real.sqrt shomM) * (W * (shomM⁻¹ * G + H)) =
      Real.sqrt Ccmp * (W * ((Real.sqrt shomM * shomM⁻¹) * G + Real.sqrt shomM * H)) := by
    ring
  rw [hinv] at h2
  linarith only [h1, h2.ge, h2.le]

/-! ## 3. `e.energy.density.estimate` with the printed bracket, generic in `Ccmp` -/

/-- **`stepSevenEnergyDensityEstimate_merged` at a generic comparison constant.**

`stepSevenEnergyDensityEstimate_compose` (already generic in `Ccmp`) followed
by `stepSevenDataLeg_merge_gen` at the SAME comparison, so `e.shom.m.vs.shom.n`
is still consumed exactly once.  At `Ccmp := 2` this is the pinned parent
verbatim. -/
theorem stepSevenEnergyDensityEstimate_merged_gen {Cg Cend Ccmp R34 R14 shomNp shomM
    gradLoc oscTrunc dataM gradM dataG W G H : ℝ}
    (hCg : 0 ≤ Cg) (hCcmp : 0 ≤ Ccmp) (hshomM : 0 < shomM)
    (hR34 : 0 ≤ R34) (hoscTrunc : 0 ≤ oscTrunc)
    (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcomp : shomNp ≤ Ccmp * shomM)
    (hgrad : gradLoc ≤ Cg * Real.sqrt shomNp * R34 * oscTrunc +
      Cg * R34 * (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM))
    (hend : oscTrunc ≤ Cend * R14 *
      (Real.sqrt shomM⁻¹ * (gradM + Real.sqrt shomM⁻¹ * dataG))) :
    gradLoc ≤ Cg * (Real.sqrt Ccmp * (Cend * R14)) * R34 *
        (gradM + Real.sqrt shomM⁻¹ * dataG) +
      Cg * R34 * (Real.sqrt Ccmp *
        (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  have hbase := stepSevenEnergyDensityEstimate_compose (Ccmp := Ccmp)
    (dataOsc := W * (shomM⁻¹ * G + H)) hCg hCcmp hshomM hR34
    hoscTrunc hcomp hgrad hend
  have hmerge := stepSevenDataLeg_merge_gen hshomM hCcmp hW hG hH hcomp
  have hpush : Cg * R34 * (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM) ≤
      Cg * R34 * (Real.sqrt Ccmp *
        (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCg hR34)
    linarith only [hmerge]
  linarith only [hbase, hpush]

/-- **`stepSevenEnergyDensityEstimate` at a generic comparison constant**, i.e.
`e.energy.density.estimate` at the printed exponent `3^{(1-α)(m-n)}` with the
printed data bracket and the `σ̄` comparison left as a parameter.  At `Ccmp:=
2` this is the pinned parent verbatim. -/
theorem stepSevenEnergyDensityEstimate_gen {alpha : ℝ} {n m : ℤ}
    {Cg Cend Ccmp shomNp shomM gradLoc oscTrunc dataM gradM dataG W G H : ℝ}
    (hCg : 0 ≤ Cg) (hCcmp : 0 ≤ Ccmp) (hshomM : 0 < shomM)
    (hoscTrunc : 0 ≤ oscTrunc)
    (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcomp : shomNp ≤ Ccmp * shomM)
    (hgrad : gradLoc ≤
      Cg * Real.sqrt shomNp *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscTrunc +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM))
    (hend : oscTrunc ≤
      Cend * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) *
        (Real.sqrt shomM⁻¹ * (gradM + Real.sqrt shomM⁻¹ * dataG))) :
    gradLoc ≤
      Cg * Real.sqrt Ccmp * Cend * Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
          (gradM + Real.sqrt shomM⁻¹ * dataG) +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt Ccmp *
            (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  have hR34 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have h := stepSevenEnergyDensityEstimate_merged_gen hCg hCcmp hshomM hR34 hoscTrunc
    hW hG hH hcomp hgrad hend
  have hprod : Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) *
      Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) =
      Real.rpow (3 : ℝ) (stepSixExponent alpha n m) := by
    rw [rpow_three_stepSixExponent_mul]
    norm_num
  have hrw : Cg * (Real.sqrt Ccmp *
        (Cend * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m))) *
      Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
      (gradM + Real.sqrt shomM⁻¹ * dataG) =
      Cg * Real.sqrt Ccmp * Cend *
        (Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m)) *
        (gradM + Real.sqrt shomM⁻¹ * dataG) := by ring
  rw [hrw, hprod] at h
  exact h

/-! ## 4. Step 7d end to end, generic in `Ccmp` -/

/-- **`stepSevenEnd_chain` at a generic comparison constant.**

The three proved displays of the node, chained, with `e.shom.m.vs.shom.n` a
parameter rather than the printed `2`.  Each hypothesis is literally the
conclusion of the named theorem, exactly as in the pinned parent, and at
`Ccmp:= 2` the statement IS the pinned parent. -/
theorem stepSevenEnd_chain_gen {alpha : ℝ} {n m : ℤ}
    {Cg Cmean Cemb Cbr Cout Ctr Ccmp shomNp shomM gradLoc oscTrunc oscLoc besovP1 besov
      dataM gradM dataG W G H : ℝ}
    (hCg : 0 ≤ Cg) (hCmean : 0 ≤ Cmean) (hCemb : 0 ≤ Cemb) (hCbr : 0 ≤ Cbr)
    (hCcmp : 0 ≤ Ccmp) (hshomM : 0 < shomM) (hoscTrunc : 0 ≤ oscTrunc)
    (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcomp : shomNp ≤ Ccmp * shomM)
    (hgrad : gradLoc ≤
      Cg * Real.sqrt shomNp *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscTrunc +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM))
    (hmean : oscTrunc ≤ Cmean * oscLoc)
    (hembed : oscLoc ≤ Cemb * besovP1)
    (hbridge : besovP1 ≤ Cbr * besov)
    (hpoincare : besov ≤
      Cout * (Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m)) *
        (Real.sqrt shomM⁻¹ * gradM + shomM⁻¹ * dataG)) :
    gradLoc ≤
      Cg * Real.sqrt Ccmp * (Cmean * Cemb * Cbr * Cout * Ctr) *
          Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
          (gradM + Real.sqrt shomM⁻¹ * dataG) +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt Ccmp *
            (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  have hshomMinv : (0 : ℝ) ≤ shomM⁻¹ := (inv_pos.mpr hshomM).le
  have hend0 := stepSevenOscillationEndpoint hCmean hCemb hCbr hshomMinv hmean hembed
    hbridge hpoincare
  have hassoc : Cmean * Cemb * Cbr *
      (Cout * (Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m))) =
      Cmean * Cemb * Cbr * Cout * Ctr *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by ring
  rw [hassoc] at hend0
  exact stepSevenEnergyDensityEstimate_gen hCg hCcmp hshomM hoscTrunc hW hG hH hcomp
    hgrad hend0

/-! ## 5. The chain at the proved comparison `Ccmp = 4` -/

/-- **Step 7d end to end at the proved `σ̄` comparison.**

`stepSevenEnd_chain_gen` with `shomNp := σ̄_{n'}`, `shomM := σ̄_m` and `Ccmp:=
4`, the comparison discharged from the frozen Section-3 `inductionState` by
`sigmaBar_le_four_mul_sigmaBar`.  The printed `√2` becomes `√4 = 2`; no other
constant moves.  This is the form the outer assembly can actually consume — the
printed `2` is not available in this repository. -/
theorem stepSevenEnd_chain_sigmaBarFour (M : ABKModel d) {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    {alpha : ℝ} {n m n' : ℤ} (hnm : n' ≤ m) (hm : m ≤ m0)
    {Cg Cmean Cemb Cbr Cout Ctr gradLoc oscTrunc oscLoc besovP1 besov
      dataM gradM dataG W G H : ℝ}
    (hCg : 0 ≤ Cg) (hCmean : 0 ≤ Cmean) (hCemb : 0 ≤ Cemb) (hCbr : 0 ≤ Cbr)
    (hoscTrunc : 0 ≤ oscTrunc) (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hgrad : gradLoc ≤
      Cg * Real.sqrt (Annealed.sigmaBar M n' : ℝ) *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscTrunc +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt (Annealed.sigmaBar M n' : ℝ) *
            (W * (((Annealed.sigmaBar M m : ℝ))⁻¹ * G + H)) + dataM))
    (hmean : oscTrunc ≤ Cmean * oscLoc)
    (hembed : oscLoc ≤ Cemb * besovP1)
    (hbridge : besovP1 ≤ Cbr * besov)
    (hpoincare : besov ≤
      Cout * (Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m)) *
        (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ * gradM +
          ((Annealed.sigmaBar M m : ℝ))⁻¹ * dataG)) :
    gradLoc ≤
      Cg * 2 * (Cmean * Cemb * Cbr * Cout * Ctr) *
          Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
          (gradM + Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ * dataG) +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (2 * (W * ((Real.sqrt (Annealed.sigmaBar M m : ℝ))⁻¹ * G +
            Real.sqrt (Annealed.sigmaBar M m : ℝ) * H)) + dataM) := by
  have hshomM : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hcomp := sigmaBar_le_four_mul_sigmaBar M hS hnm hm
  have h := stepSevenEnd_chain_gen (Ccmp := 4) hCg hCmean hCemb hCbr (by norm_num)
    hshomM hoscTrunc hW hG hH hcomp hgrad hmean hembed hbridge hpoincare
  have hfour : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hfour] at h
  exact h

end

end Algsuperdiff.Section4.Provider.Regularity
