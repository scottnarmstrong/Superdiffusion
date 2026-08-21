/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Support.AffineExcess

/-!
# The consumer-side budget of the general clause's right-hand side

The general clause consumed here carries `‖u − h‖_{L̲²(W')}` in its first
bracket leg and `s^{-6}` on legs 4 and 5, in place of the plain mean-subtracted
norm `‖u − (u)_{W'}‖_{L̲²(W')}` and the exponent `s^{-9/2}`.

At the excess-decay application (`OneStepConditional.
excessDecay_oneStep_of_harmonicApprox`, instance `n := n-2`,
`x := wellPlacedCentre x m (n-2)`) the clause's right-hand side is received as
the abstract `B`, and the excess-decay display multiplies `B.toReal` by
`triangleRemainderConst d Csch k * (3^{-n} * √((3^2)^d))`.  So every leg must
survive multiplication by `3^{-n}` into the excess-decay conclusion shape.  This
module proves what **does** survive; what does not is treated in
`OneStepConsumerRefutation`.

## What is proved here

* §1 **The `s^{-9/2} → s^{-6}` exponent move is a weakening, and it is
  invisible to the proved chain.**  `rpow_neg_nine_halves_le_rpow_neg_six`: for
  `0 < s ≤ 1`, `s^{-9/2} ≤ s^{-6}`, so the `s^{-6}` right-hand side dominates
  the `s^{-9/2}` one leg for leg.  At the sole eventual pin `s = 1/4`
  (`Regularity.MinimalScaleShift.stepOneS`) both exponents are numerals,
  `4^{9/2} = 512` and `4^6 = 4096` — a factor `8`, absorbed into `C(d,c⋆)`.
* §2 **The good-event collapse.**
  `rpow_neg_four_mul_goodEventCap_le_rpow_neg_six`: the clause's flux prefactor
  `s^{-4}` against the proved cap `𝓔·1_𝒢 ≤ C s δ^{1/2}` (`OneStepGoodScales.
  ae_errorRepresentative_le_goodEventDeltaSlot`) collapses to `s^{-3}δ^{1/2}`,
  which is below the clause's own `s^{-6}` for every `0 < s ≤ 1`, `δ ≤ 1`.
* §3 **The conditional absorption lemma** — the exact shape the `B`-expansion
  needs for the new first leg, on the **boundary branch**:
  `dataSubtracted_leg_absorbed_of_flatGradientBound`.  **The `hGu` slot — a
  bound on the flat window gradient `∑ᵢ ‖∂ᵢu‖_{L̲²(W')}` — has no producer**
  and is carried as an open hypothesis.
* §4 **The `∇h` half is free.**  `gradH_half_eq_leg5_contribution`: the datum
  half of §3's bound is *equal* to `9·C_cap·C_poin` times the clause's own
  fifth leg after the excess-decay `3^{-n}`, at the exponent `s^{-6}`.  So the
  datum half of the new leg costs nothing beyond a `d`-constant.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- The `rpow` dictionary: the anchor prints `Real.rpow s a`, the `Mathlib`
lemma library is stated at the `^` notation, and the two are definitionally the
same term. -/
private theorem rpow_eq_pow (s y : ℝ) : Real.rpow s y = s ^ y := rfl

/-! ## 1. The `s^{-9/2} → s^{-6}` exponent move -/

/-- **The exponent move weakens the clause.**  For `0 < s ≤ 1` the exponent
`s^{-6}` dominates `s^{-9/2}`, so on legs 4 and 5 the right-hand side carrying
`s^{-6}` is at least the one carrying `s^{-9/2}` — the consumer receives a
weaker bound, and absorbing it is absorbing the larger of the two. -/
theorem rpow_neg_nine_halves_le_rpow_neg_six {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow s (-(9 / 2 : ℝ)) ≤ Real.rpow s (-(6 : ℝ)) := by
  rw [rpow_eq_pow, rpow_eq_pow]
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)

/-- The `s^{-9/2}` value of legs 4/5 at the sole eventual pin `s = 1/4`. -/
theorem rpow_stepOneS_neg_nine_halves : Real.rpow (1 / 4 : ℝ) (-(9 / 2 : ℝ)) = 512 := by
  have hhalf : (1 / 4 : ℝ) ^ (1 / 2 : ℝ) = 1 / 2 := by
    rw [← Real.sqrt_eq_rpow, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [rpow_eq_pow, Real.rpow_neg (by norm_num),
    show (9 / 2 : ℝ) = (1 / 2) * ((9 : ℕ) : ℝ) by norm_num,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4), hhalf, Real.rpow_natCast]
  norm_num

/-- The `s^{-6}` value of legs 4/5 at the sole eventual pin `s = 1/4`: a
numeral, absorbed into `C(d,c⋆)`. -/
theorem rpow_stepOneS_neg_six : Real.rpow (1 / 4 : ℝ) (-(6 : ℝ)) = 4096 := by
  rw [rpow_eq_pow, Real.rpow_neg (by norm_num),
    show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- The cost of the exponent move at the pin, in one line: the `s^{-6}` legs
4/5 are the `s^{-9/2}` ones times `8`. -/
theorem rpow_stepOneS_exponent_move_ratio :
    Real.rpow (1 / 4 : ℝ) (-(6 : ℝ)) = 8 * Real.rpow (1 / 4 : ℝ) (-(9 / 2 : ℝ)) := by
  rw [rpow_stepOneS_neg_six, rpow_stepOneS_neg_nine_halves]
  norm_num

/-! ## 2. The good-event collapse of the flux prefactor -/

/-- **The flux prefactor against the proved cap.**

`s^{-4} · (C s δ^{1/2}) = C s^{-3} δ^{1/2} ≤ C s^{-6}` for `0 < s ≤ 1`,
`δ ≤ 1`: on the good event the clause's own first-bracket prefactor collapses
below the successor's leg-4/5 exponent.  This is the arithmetic that lets §3
land the new leg on the `s^{-6}` shape. -/
theorem rpow_neg_four_mul_goodEventCap_le_rpow_neg_six {s delta : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) (hdelta1 : delta ≤ 1) :
    Real.rpow s (-(4 : ℝ)) * (s * Real.sqrt delta) ≤ Real.rpow s (-(6 : ℝ)) := by
  rw [rpow_eq_pow, rpow_eq_pow]
  have hsqrt1 : Real.sqrt delta ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hdelta1
  have h4pos : (0 : ℝ) < s ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hs _
  have hprod : s ^ (-(4 : ℝ)) * s = s ^ (-(3 : ℝ)) := by
    nth_rewrite 2 [show s = s ^ (1 : ℝ) from (Real.rpow_one s).symm]
    rw [← Real.rpow_add hs]
    norm_num
  have hstep : s ^ (-(4 : ℝ)) * (s * Real.sqrt delta) ≤ s ^ (-(4 : ℝ)) * (s * 1) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt1 hs.le) h4pos.le
  have hmono : s ^ (-(3 : ℝ)) ≤ s ^ (-(6 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
  rw [mul_one, hprod] at hstep
  linarith only [hstep, hmono]

/-! ## 3. The conditional absorption lemma (boundary branch) -/

/-- **The absorption lemma for the data-subtracted first leg, on the boundary
branch.**

```text
  3^{-n} · ( C · s^{-4} · 𝓔 · ‖u − h‖_{L̲²(W')} ) ,
```

`W'` the clause's own `(n+3)`-slot window.  Feed it

* `hcap`  — the proved good-event cap `𝓔 ≤ C_cap s δ^{1/2}`;
* `hpoin` — the proved boundary Poincaré on the `H¹₀(□_m)` datum `u − h`, read
  on the normalized carrier and followed by Minkowski: `‖u − h‖_{L̲²(W')} ≤
  C_poin 3^n (G_u + G_h)` with `G_u = ∑ᵢ‖∂ᵢu‖_{L̲²(W')}`, `G_h =
  ∑ᵢ‖∂ᵢh‖_{L̲²(W')}`;

and the leg proves **exactly on the clause's own leg-4/5 exponent**, the
`3`-powers cancelling with nothing to spare and nothing left over:

```text
  ≤ C · C_cap · C_poin · s^{-6} · (G_u + G_h) .
```

The datum half `G_h` is free (§4).  The solution half `G_u` is the missing
input: **no hypothesis of `l.excess.decay.good.scales` and no leg of its
printed conclusion bounds it**, and `OneStepConsumerRefutation` shows that no
bound in terms of the excess-decay legs exists.  On the *interior* branch the
hypothesis `hpoin` is itself unavailable (there is no zero-trace portion), and
the refutation applies directly to the leg.

Three exits for `G_u`, all closed:

* the **interior** Caccioppoli needs a cut-off vanishing on `∂W'`, which on the
  boundary branch discards the very region the leg lives on;
* the **boundary** Caccioppoli, whose admissible test function is `ζ²(u−h)`,
  returns `‖∇u‖_{L̲²(W')} ≲ 3^{-n}‖u−h‖_{L̲²(W'')} + ‖∇h‖ + ‖g‖` — the same
  quantity one scale up, so it closes a **loop** with `hpoin` (Poincaré and
  Caccioppoli are mutually inverse here) with growth factor `≥ 1`;
* the **global energy identity** on `□_m` bounds the `a`-energy of `u−h` by the
  data on `□_m`, and localizing to `W'` costs the volume ratio
  `3^{(m-n)d/2}`, unbounded in `m − n`; converting the `a`-energy to the flat
  gradient costs `ν^{-1}`, the bare-ellipticity division the units doctrine
  forbids.

What remains is a boundary regularity input (a De Giorgi–Nash–Moser statement
up to a flat face with zero data, or its coarse-grained substitute), whose
constant is not a `d`-constant.  The constant of `l.excess.decay.good.scales`
is `C = C(d)`, uniform in `ω`. -/
theorem dataSubtracted_leg_absorbed_of_flatGradientBound {n : ℤ} {W : Set (Vec d)}
    {u h : Vec d → ℝ} {s delta fluxErr Cclause Ccap Cpoin Gu Gh : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) (hdelta1 : delta ≤ 1) (hCclause : 0 ≤ Cclause) (hCcap : 0 ≤ Ccap)
    (hCpoin : 0 ≤ Cpoin) (hflux0 : 0 ≤ fluxErr)
    (hcap : fluxErr ≤ Ccap * s * Real.sqrt delta) (hGu : 0 ≤ Gu) (hGh : 0 ≤ Gh)
    (hpoin : normalizedL2On W (fun y => u y - h y) ≤ Cpoin * (3 : ℝ) ^ n * (Gu + Gh)) :
    (3 : ℝ) ^ (-n) *
        (Cclause * Real.rpow s (-(4 : ℝ)) * fluxErr * normalizedL2On W (fun y => u y - h y))
      ≤ Cclause * Ccap * Cpoin * Real.rpow s (-(6 : ℝ)) * (Gu + Gh) := by
  set N := normalizedL2On W (fun y => u y - h y) with hN
  set P := Real.rpow s (-(4 : ℝ)) with hP
  set Q := Real.rpow s (-(6 : ℝ)) with hQ
  have hNnn : 0 ≤ N := normalizedL2On_nonneg _ _
  have hPpos : (0 : ℝ) < P := by
    rw [hP, rpow_eq_pow]
    exact Real.rpow_pos_of_pos hs _
  have hcapnn : 0 ≤ Ccap * s * Real.sqrt delta := le_trans hflux0 hcap
  have hsum : 0 ≤ Gu + Gh := by linarith only [hGu, hGh]
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have hAB : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ n = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  have hpoinnn : 0 ≤ Cpoin * (3 : ℝ) ^ n * (Gu + Gh) := le_trans hNnn hpoin
  have hstep1 : fluxErr * N ≤ (Ccap * s * Real.sqrt delta) * (Cpoin * (3 : ℝ) ^ n * (Gu + Gh)) :=
    mul_le_mul hcap hpoin hNnn hcapnn
  have hcoef : (0 : ℝ) ≤ (3 : ℝ) ^ (-n) * (Cclause * P) :=
    mul_nonneg h3pos.le (mul_nonneg hCclause hPpos.le)
  have hstep2 : (3 : ℝ) ^ (-n) * (Cclause * P * fluxErr * N)
      ≤ ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ n) *
        (Cclause * Ccap * Cpoin * (P * (s * Real.sqrt delta)) * (Gu + Gh)) := by
    have h := mul_le_mul_of_nonneg_left hstep1 hcoef
    calc (3 : ℝ) ^ (-n) * (Cclause * P * fluxErr * N)
        = ((3 : ℝ) ^ (-n) * (Cclause * P)) * (fluxErr * N) := by ring
      _ ≤ ((3 : ℝ) ^ (-n) * (Cclause * P)) *
            ((Ccap * s * Real.sqrt delta) * (Cpoin * (3 : ℝ) ^ n * (Gu + Gh))) := h
      _ = ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ n) *
            (Cclause * Ccap * Cpoin * (P * (s * Real.sqrt delta)) * (Gu + Gh)) := by ring
  have hcollapse : P * (s * Real.sqrt delta) ≤ Q :=
    rpow_neg_four_mul_goodEventCap_le_rpow_neg_six hs hs1 hdelta1
  have hCpoinnn : 0 ≤ Cclause * Ccap * Cpoin * (Gu + Gh) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCclause hCcap) hCpoin) hsum
  have hstep3 : Cclause * Ccap * Cpoin * (P * (s * Real.sqrt delta)) * (Gu + Gh)
      ≤ Cclause * Ccap * Cpoin * Q * (Gu + Gh) := by
    have h := mul_le_mul_of_nonneg_left hcollapse hCpoinnn
    calc Cclause * Ccap * Cpoin * (P * (s * Real.sqrt delta)) * (Gu + Gh)
        = (Cclause * Ccap * Cpoin * (Gu + Gh)) * (P * (s * Real.sqrt delta)) := by ring
      _ ≤ (Cclause * Ccap * Cpoin * (Gu + Gh)) * Q := h
      _ = Cclause * Ccap * Cpoin * Q * (Gu + Gh) := by ring
  rw [hAB, one_mul] at hstep2
  linarith only [hstep2, hstep3]

/-! ## 4. The datum half is free -/

/-- **The `∇h` half of the new leg is the clause's own fifth leg.**

After the excess-decay `3^{-n}` the clause's fifth leg contributes
`3^{-n} · (C s^{-6} · 3^{n-2} · G_h)`, and §3's datum half is exactly
`9·C_cap·C_poin` times it — an identity, not an estimate.  So that datum half
costs a `d`-constant and nothing else. -/
theorem gradH_half_eq_leg5_contribution {n : ℤ} (Cclause Ccap Cpoin Gh sPow : ℝ) :
    Cclause * Ccap * Cpoin * sPow * Gh
      = (9 * Ccap * Cpoin) * ((3 : ℝ) ^ (-n) * (Cclause * sPow * (3 : ℝ) ^ (n - 2) * Gh)) := by
  have h : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n - 2) = 1 / 9 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), show -n + (n - 2) = (-2 : ℤ) by ring]
    norm_num
  calc Cclause * Ccap * Cpoin * sPow * Gh
      = 9 * Ccap * Cpoin * Cclause * sPow * Gh * (1 / 9) := by ring
    _ = 9 * Ccap * Cpoin * Cclause * sPow * Gh * ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n - 2)) := by rw [h]
    _ = (9 * Ccap * Cpoin) * ((3 : ℝ) ^ (-n) * (Cclause * sPow * (3 : ℝ) ^ (n - 2) * Gh)) := by
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
