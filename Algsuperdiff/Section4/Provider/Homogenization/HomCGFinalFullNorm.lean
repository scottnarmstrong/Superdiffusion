/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomCGFinalGagliardo

/-!
# The FULL `W^{s′,q}` norm of a Hölder field, against the test gauge

## What this file supplies

`HomCGFinalGagliardo` bounds the **seminorm** half of `CoarseGraining`'s
`cubeEuclideanWspFullENorm`.  This file adds the `L^{q}` half — a sup bound is
enough, because the underlying measure is the NORMALIZED cube measure, a
probability measure — and assembles both against the Step-4 test gauge
`wsInftyGauge`.

The `L^{q}` half carries the scale weight `cubeEuclideanWspScalePowerWeight`,
i.e. `L^{-s′q}`; its `q`-th root is `L^{-s′}`.  With `L = 3^{m}` the side, this
is where the predicted single factor comes from:

```text
  ‖φ‖_{W^{s′,q} full}  ≤  L^{-s′}·d·K_sup  +  d·C(d,β)^{1/q}·L^{α-s′}·K_Höl
                       ≤  K_test · ( L^{-α} K_sup + K_Höl )
```

with

```text
  K_test  =  d · L^{α-s′} · (1 + C(d,β)^{1/q}),     β = d - (α-s′)q,
```

because `L^{-s′} = L^{α-s′}·L^{-α}`.  The right-hand factor is exactly
`wsInftyGauge Q α K_sup K_Höl`, whose `L^∞` weight `3^{-α·scale}` IS `L^{-α}`.

So the entire order loss `α - s′ > 0` is paid as the single explicit factor
`L^{α-s′} = 3^{m(α-s′)}` in `cgTestConst`, exactly as the measurement
predicted, and nothing else about the two orders enters.
-/

open Homogenization MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The cube side in the `3`-gauge -/

/-- `L^{t} = 3^{scale·t}` for the triadic side `L = cubeScaleFactor Q`. -/
private theorem cgScaleFactor_rpow (Q : TriadicCube d) (t : ℝ) :
    cubeScaleFactor Q ^ t = (3 : ℝ) ^ (((Q.scale : ℤ) : ℝ) * t) := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  rw [cubeScaleFactor, ← Real.rpow_intCast (3 : ℝ) Q.scale, ← Real.rpow_mul h3]

/-- The test gauge's `L^∞` weight is the side to the power `-α`. -/
theorem three_rpow_neg_scale_eq (Q : TriadicCube d) (alpha : ℝ) :
    Real.rpow 3 (-(alpha * ((Q.scale : ℤ) : ℝ))) = cubeScaleFactor Q ^ (-alpha) := by
  show (3 : ℝ) ^ (-(alpha * ((Q.scale : ℤ) : ℝ))) = cubeScaleFactor Q ^ (-alpha)
  rw [cgScaleFactor_rpow]
  congr 1
  ring

/-! ## 2. The `L^{q}` half of the full norm -/

/-- **A sup bound bounds the normalized `L^{q}` norm**, at the dimensional
constant of the Euclidean/supremum comparison and with NO measure factor: the
normalized cube measure is a probability measure. -/
theorem normalizedEuclideanLpENorm_le_of_bound {Q : TriadicCube d} {r : ℝ≥0∞}
    {F : Vec d → Vec d} {B : ℝ} (hF : ∀ x, ‖F x‖ ≤ B) :
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm r F ≤
      ENNReal.ofReal ((d : ℝ) * B) := by
  have hbd : ∀ᵐ x ∂((cubeBoundedMeasurableDomain Q).normalizedVolume),
      ‖euclideanNorm (F x)‖ ≤ (d : ℝ) * B := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _)]
    exact (euclideanNorm_le_dimension_mul_norm (F x)).trans
      (mul_le_mul_of_nonneg_left (hF x) (Nat.cast_nonneg d))
  have h := eLpNorm_le_of_ae_bound (p := r) hbd
  rw [BoundedMeasurableDomain.normalizedVolume_apply_univ, ENNReal.one_rpow, one_mul] at h
  exact h

/-! ## 3. The full norm of a Hölder field -/

/-- The inverse exponent is at most one. -/
private theorem inv_toReal_le_one (q : FiniteLpExponent) : (q.exponent.toReal)⁻¹ ≤ 1 := by
  have ht1 : 1 < q.exponent.toReal := one_lt_finiteLpExponent_toReal q
  have htpos : 0 < q.exponent.toReal := finiteLpExponent_toReal_pos q
  by_contra hcon
  push_neg at hcon
  have hstep := mul_lt_mul_of_pos_right hcon htpos
  rw [one_mul, inv_mul_cancel₀ (ne_of_gt htpos)] at hstep
  linarith only [hstep, ht1]

/-- **`C^{0,α}(□) ⊂ W^{s′,q}(□)` at the FULL norm.** -/
theorem cubeEuclideanWspFullENorm_le_of_holder {Q : TriadicCube d}
    {s' : FractionalOrder} {q : FiniteLpExponent} {phi : Vec d → Vec d}
    {alpha Ksup KHol : ℝ} (hKHol : 0 ≤ KHol)
    (hlo : 0 < (alpha - s'.1) * q.exponent.toReal)
    (hhi : (alpha - s'.1) * q.exponent.toReal < (d : ℝ))
    (hsup : ∀ x, ‖phi x‖ ≤ Ksup)
    (hg : HolderSeminormBoundOn (openCubeSet Q) alpha KHol phi) :
    cubeEuclideanWspFullENorm Q s' q phi ≤
      ENNReal.ofReal (cubeScaleFactor Q ^ (-s'.1) * ((d : ℝ) * Ksup)) +
        ENNReal.ofReal ((d : ℝ) * KHol *
          Regularity.radialKernelConst d
              (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) ^
            (q.exponent.toReal)⁻¹ *
          cubeScaleFactor Q ^ (alpha - s'.1)) := by
  have htpos : 0 < q.exponent.toReal := finiteLpExponent_toReal_pos q
  have htinv : (0 : ℝ) ≤ (q.exponent.toReal)⁻¹ := le_of_lt (inv_pos.mpr htpos)
  have htinv1 : (q.exponent.toReal)⁻¹ ≤ 1 := inv_toReal_le_one q
  have hR : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos Q
  have hA := normalizedEuclideanLpENorm_le_of_bound (Q := Q) (r := q.exponent) hsup
  have hS := cubeEuclideanWspESeminorm_le_of_holder (Q := Q) (s' := s') (q := q)
    (phi := phi) hKHol hlo hhi hg
  set a : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) * Ksup) with ha
  set b : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) * KHol *
    Regularity.radialKernelConst d
        (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) ^ (q.exponent.toReal)⁻¹ *
    cubeScaleFactor Q ^ (alpha - s'.1)) with hb
  set W : ℝ≥0∞ := cubeEuclideanWspScalePowerWeight Q s' q with hW
  have hmono : W * ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
        q.exponent phi) ^ q.exponent.toReal +
      (cubeEuclideanWspESeminorm Q s' q phi) ^ q.exponent.toReal ≤
      W * a ^ q.exponent.toReal + b ^ q.exponent.toReal :=
    add_le_add (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hA htpos.le))
      (ENNReal.rpow_le_rpow hS htpos.le)
  have hbpow : (b ^ q.exponent.toReal) ^ (q.exponent.toReal)⁻¹ = b := by
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (ne_of_gt htpos), ENNReal.rpow_one]
  have hWapow : (W * a ^ q.exponent.toReal) ^ (q.exponent.toReal)⁻¹ =
      W ^ (q.exponent.toReal)⁻¹ * a := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ htinv, ← ENNReal.rpow_mul,
      mul_inv_cancel₀ (ne_of_gt htpos), ENNReal.rpow_one]
  have hWroot : W ^ (q.exponent.toReal)⁻¹ =
      ENNReal.ofReal (cubeScaleFactor Q ^ (-s'.1)) := by
    rw [hW, cubeEuclideanWspScalePowerWeight, ← ENNReal.rpow_mul]
    have hexp : -s'.1 * q.exponent.toReal * (q.exponent.toReal)⁻¹ = -s'.1 := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt htpos), mul_one]
    rw [hexp, ENNReal.ofReal_rpow_of_pos hR]
  calc cubeEuclideanWspFullENorm Q s' q phi
      = (W * ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
            q.exponent phi) ^ q.exponent.toReal +
          (cubeEuclideanWspESeminorm Q s' q phi) ^ q.exponent.toReal) ^
            (q.exponent.toReal)⁻¹ := rfl
    _ ≤ (W * a ^ q.exponent.toReal + b ^ q.exponent.toReal) ^ (q.exponent.toReal)⁻¹ :=
        ENNReal.rpow_le_rpow hmono htinv
    _ ≤ (W * a ^ q.exponent.toReal) ^ (q.exponent.toReal)⁻¹ +
          (b ^ q.exponent.toReal) ^ (q.exponent.toReal)⁻¹ :=
        ENNReal.rpow_add_le_add_rpow _ _ htinv htinv1
    _ = ENNReal.ofReal (cubeScaleFactor Q ^ (-s'.1)) * a + b := by
        rw [hWapow, hbpow, hWroot]
    _ = ENNReal.ofReal (cubeScaleFactor Q ^ (-s'.1) * ((d : ℝ) * Ksup)) + b := by
        rw [ha, ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]

/-! ## 4. The test constant, and the gauge comparison -/

/-- **The test-class constant of the order-loss route.**
`K_test(Q, α, s′, q) = d · L^{α-s′} · (1 + C(d, β)^{1/q})`, `β = d - (α-s′)q`. -/
def cgTestConst (d : ℕ) (Q : TriadicCube d) (alpha s' t : ℝ) : ℝ :=
  (d : ℝ) * cubeScaleFactor Q ^ (alpha - s') *
    (1 + Regularity.radialKernelConst d (cgGagliardoBeta d alpha s' t) ^ t⁻¹)

theorem cgTestConst_def (d : ℕ) (Q : TriadicCube d) (alpha s' t : ℝ) :
    cgTestConst d Q alpha s' t =
      (d : ℝ) * cubeScaleFactor Q ^ (alpha - s') *
        (1 + Regularity.radialKernelConst d (cgGagliardoBeta d alpha s' t) ^ t⁻¹) := rfl

theorem cgTestConst_nonneg (d : ℕ) (Q : TriadicCube d) {alpha s' t : ℝ}
    (hlo : 0 < (alpha - s') * t) :
    0 ≤ cgTestConst d Q alpha s' t := by
  have hR : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos Q
  have hP : (0 : ℝ) < cubeScaleFactor Q ^ (alpha - s') := Real.rpow_pos_of_pos hR _
  have hblt : cgGagliardoBeta d alpha s' t < (d : ℝ) := cgGagliardoBeta_lt hlo
  have hCc : (0 : ℝ) ≤
      Regularity.radialKernelConst d (cgGagliardoBeta d alpha s' t) ^ t⁻¹ :=
    Real.rpow_nonneg (Regularity.radialKernelConst_pos hblt).le _
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have h1 : (0 : ℝ) ≤ (d : ℝ) * cubeScaleFactor Q ^ (alpha - s') :=
    mul_nonneg hd hP.le
  rw [cgTestConst_def]
  exact mul_nonneg h1 (by linarith only [hCc])

/-- **The full norm of a Hölder test field, against the Step-4 test gauge.**

This is the honest, order-losing form of the `SmoothDualDominatesHolderTests`
comparison: the `W^{s′,q}` unit-ball gauge of a `C^{0,α}` field is at most
`K_test` times its `W^{α,∞}` gauge, with `K_test` carrying the single factor
`3^{m(α-s′)}`. -/
theorem cubeEuclideanWspFullENorm_le_gauge {Q : TriadicCube d}
    {s' : FractionalOrder} {q : FiniteLpExponent} {phi : Vec d → Vec d}
    {alpha Ksup KHol : ℝ} (hKsup : 0 ≤ Ksup) (hKHol : 0 ≤ KHol)
    (hlo : 0 < (alpha - s'.1) * q.exponent.toReal)
    (hhi : (alpha - s'.1) * q.exponent.toReal < (d : ℝ))
    (hsup : ∀ x, ‖phi x‖ ≤ Ksup)
    (hg : HolderSeminormBoundOn (openCubeSet Q) alpha KHol phi) :
    cubeEuclideanWspFullENorm Q s' q phi ≤
      ENNReal.ofReal (cgTestConst d Q alpha s'.1 q.exponent.toReal *
        wsInftyGauge Q alpha Ksup KHol) := by
  have hR : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos Q
  have hblt : cgGagliardoBeta d alpha s'.1 q.exponent.toReal < (d : ℝ) :=
    cgGagliardoBeta_lt hlo
  set Cc : ℝ := Regularity.radialKernelConst d
    (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) ^ (q.exponent.toReal)⁻¹ with hCcdef
  have hCc : (0 : ℝ) ≤ Cc :=
    Real.rpow_nonneg (Regularity.radialKernelConst_pos hblt).le _
  set P : ℝ := cubeScaleFactor Q ^ (alpha - s'.1) with hPdef
  have hP : (0 : ℝ) < P := Real.rpow_pos_of_pos hR _
  set U : ℝ := cubeScaleFactor Q ^ (-alpha) * Ksup with hUdef
  have hU : (0 : ℝ) ≤ U :=
    mul_nonneg (Real.rpow_nonneg hR.le _) hKsup
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hsplit : cubeScaleFactor Q ^ (-s'.1) = P * cubeScaleFactor Q ^ (-alpha) := by
    rw [hPdef, ← Real.rpow_add hR]
    congr 1
    ring
  have hgauge : wsInftyGauge Q alpha Ksup KHol = U + KHol := by
    rw [wsInftyGauge_def, hUdef, three_rpow_neg_scale_eq]
  have hX : cubeScaleFactor Q ^ (-s'.1) * ((d : ℝ) * Ksup) = (d : ℝ) * P * U := by
    rw [hsplit, hUdef]
    ring
  have hkey : cubeScaleFactor Q ^ (-s'.1) * ((d : ℝ) * Ksup) +
      (d : ℝ) * KHol * Cc * P ≤
      cgTestConst d Q alpha s'.1 q.exponent.toReal * wsInftyGauge Q alpha Ksup KHol := by
    rw [hX, cgTestConst_def, hgauge, ← hCcdef, ← hPdef]
    have hid : (d : ℝ) * P * (1 + Cc) * (U + KHol) -
        ((d : ℝ) * P * U + (d : ℝ) * KHol * Cc * P) =
        (d : ℝ) * P * KHol + (d : ℝ) * P * Cc * U := by ring
    have h1 : (0 : ℝ) ≤ (d : ℝ) * P * KHol :=
      mul_nonneg (mul_nonneg hd hP.le) hKHol
    have h2 : (0 : ℝ) ≤ (d : ℝ) * P * Cc * U :=
      mul_nonneg (mul_nonneg (mul_nonneg hd hP.le) hCc) hU
    linarith only [hid, h1, h2]
  have hbase := cubeEuclideanWspFullENorm_le_of_holder (Q := Q) (s' := s') (q := q)
    (phi := phi) (alpha := alpha) (Ksup := Ksup) hKHol hlo hhi hsup hg
  refine hbase.trans ?_
  have hXnn : (0 : ℝ) ≤ cubeScaleFactor Q ^ (-s'.1) * ((d : ℝ) * Ksup) :=
    mul_nonneg (Real.rpow_nonneg hR.le _) (mul_nonneg hd hKsup)
  rw [← ENNReal.ofReal_add hXnn
    (mul_nonneg (mul_nonneg (mul_nonneg hd hKHol) hCc) hP.le)]
  exact ENNReal.ofReal_le_ofReal hkey

end

end Algsuperdiff.Section4.Provider.Homogenization
