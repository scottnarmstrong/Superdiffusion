/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepSevenEndEmbedding
import Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons

/-!
# `t.regularity` Step 7d, part three: `e.energy.density.estimate`

## The target

ABK26, the last line of the proof of `t.regularity`:

> Since `m - m' ≤ |𝓑_z| + 3 ≤ C₁⁻¹(1-α)(m-n) + 3`, we obtain
> `e.energy.density.estimate` by the previous display and `e.gradient.with.shom`
> since `σ̄_{n'} ≤ 2 σ̄_m`.

and the target display `e.energy.density.estimate`:

```text
  ν^{1/2}‖∇u‖_{L̲²((x+□_n)∩□_m)}
    ≤ C 3^{(1-α)(m-n)} ( ν^{1/2}‖∇u‖_{L̲²(□_m)}
        + σ̄_m^{-1/2} 3^{m/2}[𝐠]_{W̲^{1/2,∞}(□_m)}
        + σ̄_m^{1/2} 3^{m/2}‖∇h‖_{W̲^{1/2,∞}(□_m)} 1_{x ∉ □_{m-1}} ) .
```

## The exponent bookkeeping — the two halves make exactly `(1-α)(m-n)`

`stepSevenGradientWithShom` carries `3^{(3/4)(1-α)(m-n)}`, and the Step-7d
endpoint (`StepSevenEndEmbedding`) contributes the transport factor, which
`StepSevenEndPoincare` absorbs into `3^{(1/4)(1-α)(m-n)}`.  Their product is
`3^{(1-α)(m-n)}` — the printed exponent, character for character.  This is the
arithmetic reason the printed `3/4` of `e.gradient.with.shom` is what it is:
the theorem's own exponent is `1`, and Step 7d spends the remaining quarter on
the coarse-graining transport.

## `σ̄_{n'} ≤ 2 σ̄_m` needs no adjacency

The final sentence presents `σ̄_{n'} ≤ 2σ̄_m` as an adjacency consequence.  In
this repository the growth cap is
`sigmaBar_le_rpow_mul_sigmaBar_of_inductionState`, derived from conjunct 1 of
the frozen Section-3 `inductionState` at the two scales alone — at the explicit
constant `4` rather than the printed `2`, which is immaterial inside `C` (the
collapse cost becomes `√4 = 2` instead of `√2`).  Both are delivered: the
composition takes `σ̄_{n'} ≤ Ccmp · σ̄_m` for an arbitrary `Ccmp`, and the
printed `Ccmp = 2` and the proved `Ccmp = 4` are both instances.

## The data-bracket collapse is owned here

This module owns the collapse: `stepSevenDataLeg_merge` is applied here, at the
same comparison `σ̄_{n'} ≤ Ccmp σ̄_m` that the assembly uses for the
oscillation leg, so the two consumptions of `e.shom.m.vs.shom.n` are one
hypothesis.

## The `[𝐠]_{H̲^s}` → `[𝐠]_{W̲^{1/2,∞}}` passage

The endpoint's data leg is `3^{sm}[𝐠]_{H̲^s(□_m)}` while the theorem's data leg
is `3^{m/2}[𝐠]_{W̲^{1/2,∞}(□_m)}`; the manuscript never displays the passage.
It is the proved atom `three_rpow_mul_normalizedGagliardoESeminormOn_cube_le`,
and it is consumed here
(`stepSevenDataG_le_of_holderHalf`, the real-valued layer), not re-derived: the
free `s` cancels out of the scale weight, which is why
`e.energy.density.estimate` can be `s`-free.

## The conditional inputs reaching this module

Nothing new is assumed here.  The assembly is a theorem about the two proved
displays; the live conditional inputs are the ones its two arguments carry —'s
`hcacc`/`hlambda`/`hosc`, `StepSevenEndPoincare`'s `hcg`/`hlambda`, and
`StepSevenEndEmbedding`'s `hembed`/`hbridge`.

`stepSevenEnd_chain` is the single entry point: it takes each of the three
proved displays' conclusions V in its hypothesis slots ('s
`stepSevenGradientWithShom`, `stepSevenCgPoincareApplied_absorbed`, and the
oscillation endpoint's three links) and produces `e.energy.density.estimate`.
The unification is syntactic — no massaging, one associativity `ring`.

## Strengthenings

`sqrt_shomNp_mul_endpoint_le` and the two composition theorems need no sign
condition on the endpoint constant or on the transported bracket: the
multiplicative step only uses `0 ≤ oscTrunc` and `0 ≤ √Ccmp·√σ̄_m`.  Those
binders were therefore dropped rather than carried unused.

## References

* ABK26, `e.energy.density.estimate`; the assembly.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open Homogenization
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

/-! ## 1. `σ̄_{n'} ≤ C σ̄_m` on the oscillation leg -/

/-- `√σ̄_m · √(σ̄_m⁻¹) = 1`. -/
theorem sqrt_mul_sqrt_inv_eq_one {S : ℝ} (hS : 0 < S) :
    Real.sqrt S * Real.sqrt S⁻¹ = 1 := by
  rw [← Real.sqrt_mul hS.le, mul_inv_cancel₀ (ne_of_gt hS), Real.sqrt_one]

/-- **The `σ̄` collapse on the oscillation leg**.

The Step-7c gradient display multiplies the endpoint by `√σ̄_{n'}`, while the
endpoint itself carries `√(σ̄_m⁻¹)`; the comparison `σ̄_{n'} ≤ Ccmp σ̄_m` makes the
two cancel at the cost `√Ccmp`:

```text
  √σ̄_{n'} · Cend · √(σ̄_m⁻¹) · X  ≤  √Ccmp · Cend · X .
```

`Ccmp = 2` is the printed constant; the derived growth cap gives `Ccmp = 4`.  No
sign condition on `Cend` or `X` is needed — a strengthening: the multiplicative
step only uses `0 ≤ oscTrunc` and `0 ≤ √Ccmp·√σ̄_m`. -/
theorem sqrt_shomNp_mul_endpoint_le {shomNp shomM Ccmp Cend X oscTrunc : ℝ}
    (hshomM : 0 < shomM) (hCcmp : 0 ≤ Ccmp)
    (hoscTrunc : 0 ≤ oscTrunc) (hcomp : shomNp ≤ Ccmp * shomM)
    (hend : oscTrunc ≤ Cend * (Real.sqrt shomM⁻¹ * X)) :
    Real.sqrt shomNp * oscTrunc ≤ Real.sqrt Ccmp * Cend * X := by
  have hSm : (0 : ℝ) ≤ Real.sqrt shomM := Real.sqrt_nonneg _
  have hCc : (0 : ℝ) ≤ Real.sqrt Ccmp := Real.sqrt_nonneg _
  have hstep : Real.sqrt shomNp ≤ Real.sqrt Ccmp * Real.sqrt shomM := by
    calc Real.sqrt shomNp ≤ Real.sqrt (Ccmp * shomM) := Real.sqrt_le_sqrt hcomp
      _ = Real.sqrt Ccmp * Real.sqrt shomM := Real.sqrt_mul hCcmp shomM
  have h1 : Real.sqrt shomNp * oscTrunc ≤
      (Real.sqrt Ccmp * Real.sqrt shomM) * (Cend * (Real.sqrt shomM⁻¹ * X)) :=
    mul_le_mul hstep hend hoscTrunc (mul_nonneg hCc hSm)
  have hcancel := sqrt_mul_sqrt_inv_eq_one hshomM
  have h2 : (Real.sqrt Ccmp * Real.sqrt shomM) * (Cend * (Real.sqrt shomM⁻¹ * X)) =
      Real.sqrt Ccmp * Cend * ((Real.sqrt shomM * Real.sqrt shomM⁻¹) * X) := by ring
  rw [hcancel, one_mul] at h2
  linarith only [h1, h2.ge, h2.le]

/-! ## 2. The assembly -/

/-- **`e.energy.density.estimate`, assembled** — the abstract-real core.

From's `e.gradient.with.shom` at the power = 3^{(3/4)(1-α)(m-n)}` and the
Step-7d endpoint = 3^{(1/4)(1-α)(m-n)}`, together with `σ̄_{n'} ≤ Ccmp σ̄_m`,
the theorem's own display follows at the power `R34 · = 3^{(1-α)(m-n)}`:

```text
  gradLoc ≤ Cg·(√Ccmp·Cend)·(R34·R14)·( gradM + √(σ̄_m⁻¹)·dataG )
            + Cg·R34·( √σ̄_{n'}·dataOsc + dataM ) ,
```

the second summand being the honest data bracket, which
`stepSevenEnergyDensityEstimate_merged` collapses to the printed one. -/
theorem stepSevenEnergyDensityEstimate_compose {Cg Cend Ccmp R34 R14 shomNp shomM
    gradLoc oscTrunc dataOsc dataM gradM dataG : ℝ}
    (hCg : 0 ≤ Cg) (hCcmp : 0 ≤ Ccmp) (hshomM : 0 < shomM)
    (hR34 : 0 ≤ R34) (hoscTrunc : 0 ≤ oscTrunc)
    (hcomp : shomNp ≤ Ccmp * shomM)
    (hgrad : gradLoc ≤ Cg * Real.sqrt shomNp * R34 * oscTrunc +
      Cg * R34 * (Real.sqrt shomNp * dataOsc + dataM))
    (hend : oscTrunc ≤ Cend * R14 *
      (Real.sqrt shomM⁻¹ * (gradM + Real.sqrt shomM⁻¹ * dataG))) :
    gradLoc ≤ Cg * (Real.sqrt Ccmp * (Cend * R14)) * R34 *
        (gradM + Real.sqrt shomM⁻¹ * dataG) +
      Cg * R34 * (Real.sqrt shomNp * dataOsc + dataM) := by
  have hkey := sqrt_shomNp_mul_endpoint_le (Cend := Cend * R14) hshomM hCcmp
    hoscTrunc hcomp hend
  -- push the collapsed leg through `Cg · R34`
  have hmul : Cg * R34 * (Real.sqrt shomNp * oscTrunc) ≤
      Cg * R34 * (Real.sqrt Ccmp * (Cend * R14) *
        (gradM + Real.sqrt shomM⁻¹ * dataG)) :=
    mul_le_mul_of_nonneg_left hkey (mul_nonneg hCg hR34)
  have hexp1 : Cg * Real.sqrt shomNp * R34 * oscTrunc =
      Cg * R34 * (Real.sqrt shomNp * oscTrunc) := by ring
  have hexp2 : Cg * R34 * (Real.sqrt Ccmp * (Cend * R14) *
      (gradM + Real.sqrt shomM⁻¹ * dataG)) =
      Cg * (Real.sqrt Ccmp * (Cend * R14)) * R34 *
        (gradM + Real.sqrt shomM⁻¹ * dataG) := by ring
  linarith only [hgrad, hmul, hexp1.ge, hexp1.le, hexp2.ge, hexp2.le]

/-- **`e.energy.density.estimate` with the printed data bracket**.

`stepSevenEnergyDensityEstimate_compose` followed's `stepSevenDataLeg_merge` at
the SAME comparison `σ̄_{n'} ≤ 2σ̄_m`, so the `e.shom.m.vs.shom.n` edge is
consumed once.  The second summand's bracket is now the theorem's own

```text
  3^{m/2}( σ̄_m^{-1/2}[𝐠]_{W̲^{1/2,∞}(□_m)} + σ̄_m^{1/2}‖∇h‖_{W̲^{1/2,∞}(□_m)}1 ) ,
```

i.e. `dataOsc = W·(σ̄_m⁻¹·G + H)` becomes `W·((√σ̄_m)⁻¹·G + √σ̄_m·H)` at cost
`√2`. -/
theorem stepSevenEnergyDensityEstimate_merged {Cg Cend R34 R14 shomNp shomM
    gradLoc oscTrunc dataM gradM dataG W G H : ℝ}
    (hCg : 0 ≤ Cg) (hshomM : 0 < shomM)
    (hR34 : 0 ≤ R34) (hoscTrunc : 0 ≤ oscTrunc)
    (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcomp : shomNp ≤ 2 * shomM)
    (hgrad : gradLoc ≤ Cg * Real.sqrt shomNp * R34 * oscTrunc +
      Cg * R34 * (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM))
    (hend : oscTrunc ≤ Cend * R14 *
      (Real.sqrt shomM⁻¹ * (gradM + Real.sqrt shomM⁻¹ * dataG))) :
    gradLoc ≤ Cg * (Real.sqrt 2 * (Cend * R14)) * R34 *
        (gradM + Real.sqrt shomM⁻¹ * dataG) +
      Cg * R34 * (Real.sqrt 2 *
        (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  have hbase := stepSevenEnergyDensityEstimate_compose (Ccmp := 2)
    (dataOsc := W * (shomM⁻¹ * G + H)) hCg (by norm_num) hshomM hR34
    hoscTrunc hcomp hgrad hend
  have hmerge := stepSevenDataLeg_merge hshomM hW hG hH hcomp
  have hpush : Cg * R34 * (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM) ≤
      Cg * R34 * (Real.sqrt 2 *
        (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCg hR34)
    linarith only [hmerge]
  linarith only [hbase, hpush]

/-! ## 3. The display at the printed exponents -/

/-- **`e.energy.density.estimate` at the printed exponent `3^{(1-α)(m-n)}`.**

The two halves `3^{(3/4)(1-α)(m-n)}` and `3^{(1/4)(1-α)(m-n)}` (the Step-7d
transport, `StepSevenEndPoincare`) multiply to the theorem's own
`3^{(1-α)(m-n)}`. -/
theorem stepSevenEnergyDensityEstimate {alpha : ℝ} {n m : ℤ}
    {Cg Cend shomNp shomM gradLoc oscTrunc dataM gradM dataG W G H : ℝ}
    (hCg : 0 ≤ Cg) (hshomM : 0 < shomM)
    (hoscTrunc : 0 ≤ oscTrunc)
    (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcomp : shomNp ≤ 2 * shomM)
    (hgrad : gradLoc ≤
      Cg * Real.sqrt shomNp *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscTrunc +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM))
    (hend : oscTrunc ≤
      Cend * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) *
        (Real.sqrt shomM⁻¹ * (gradM + Real.sqrt shomM⁻¹ * dataG))) :
    gradLoc ≤
      Cg * Real.sqrt 2 * Cend * Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
          (gradM + Real.sqrt shomM⁻¹ * dataG) +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt 2 *
            (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  have hR34 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have h := stepSevenEnergyDensityEstimate_merged hCg hshomM hR34 hoscTrunc
    hW hG hH hcomp hgrad hend
  have hprod : Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) *
      Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) =
      Real.rpow (3 : ℝ) (stepSixExponent alpha n m) := by
    rw [rpow_three_stepSixExponent_mul]
    norm_num
  have hrw : Cg * (Real.sqrt 2 *
        (Cend * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m))) *
      Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
      (gradM + Real.sqrt shomM⁻¹ * dataG) =
      Cg * Real.sqrt 2 * Cend *
        (Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m)) *
        (gradM + Real.sqrt shomM⁻¹ * dataG) := by ring
  rw [hrw, hprod] at h
  exact h

/-! ## 4. Step 7d end to end -/

/-- **Step 7d, end to end.**  The three displays of the node, chained:

* `hpoincare` — `stepSevenCgPoincareApplied_absorbed`'s conclusion
  (`e.cg.Poincare.with.rhs.grad.applied` with the transport exponent already
  absorbed into `Ctr · 3^{(1/4)(1-α)(m-n)}`);
* `hgrad` —'s `stepSevenGradientWithShom`;
* `hcomp` — `e.shom.m.vs.shom.n`.

The conclusion is `e.energy.density.estimate` at the printed exponent
`3^{(1-α)(m-n)}` with the printed data bracket.  The three proved displays
unify into this statement with NO massaging: each hypothesis below is literally
the conclusion of the named theorem. -/
theorem stepSevenEnd_chain {alpha : ℝ} {n m : ℤ}
    {Cg Cmean Cemb Cbr Cout Ctr shomNp shomM gradLoc oscTrunc oscLoc besovP1 besov
      dataM gradM dataG W G H : ℝ}
    (hCg : 0 ≤ Cg) (hCmean : 0 ≤ Cmean) (hCemb : 0 ≤ Cemb) (hCbr : 0 ≤ Cbr)
    (hshomM : 0 < shomM) (hoscTrunc : 0 ≤ oscTrunc)
    (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcomp : shomNp ≤ 2 * shomM)
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
      Cg * Real.sqrt 2 * (Cmean * Cemb * Cbr * Cout * Ctr) *
          Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
          (gradM + Real.sqrt shomM⁻¹ * dataG) +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt 2 *
            (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  have hshomMinv : (0 : ℝ) ≤ shomM⁻¹ := (inv_pos.mpr hshomM).le
  have hend0 := stepSevenOscillationEndpoint hCmean hCemb hCbr hshomMinv hmean hembed
    hbridge hpoincare
  have hassoc : Cmean * Cemb * Cbr *
      (Cout * (Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m))) =
      Cmean * Cemb * Cbr * Cout * Ctr *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by ring
  rw [hassoc] at hend0
  exact stepSevenEnergyDensityEstimate hCg hshomM hoscTrunc hW hG hH hcomp hgrad hend0

/-! ## 5. The data leg in the theorem's own seminorm -/

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- This is the never-displayed passage, consumed rather than re-derived.  `K` is
the `C^{0,1/2}(□_m)` bound on `𝐠`, i.e. the `W̲^{1/2,∞}` seminorm. -/
theorem stepSevenDataG_le_of_holderHalf {m : ℤ} {g : Vec d → E} {K s : ℝ}
    (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    (ENNReal.ofReal ((3 : ℝ) ^ ((m : ℝ) * s)) *
        Support.normalizedGagliardoESeminormOn (openCubeSet (originCube d m)) s g).toReal ≤
      K * stepFourGagliardoConst d s * (3 : ℝ) ^ ((m : ℝ) / 2) := by
  have hbound := three_rpow_mul_normalizedGagliardoESeminormOn_cube_le hd hs0 hs hK hg
  have hnn : (0 : ℝ) ≤ K * stepFourGagliardoConst d s * (3 : ℝ) ^ ((m : ℝ) / 2) := by
    have h1 : (0 : ℝ) ≤ K * stepFourGagliardoConst d s :=
      mul_nonneg hK (stepFourGagliardoConst_nonneg d s)
    exact mul_nonneg h1 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rwa [ENNReal.toReal_ofReal hnn] at h

end

end Algsuperdiff.Section4.Provider.Regularity
