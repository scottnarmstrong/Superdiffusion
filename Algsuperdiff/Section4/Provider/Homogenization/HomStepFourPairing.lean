/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Support.Dirichlet
import Homogenization.CoarseGraining.Definitions

/-!
# Theorem B, §4.5, Step 4: the pairing carrier

## The object

Step 4 uses the negative norm `‖·‖_{Ŵ̲^{-s,∞}(□_m)}` in exactly one way, the
two duality pairings of the manuscript:

```text
  |⨍_{□_m} ∇v · F|  ≤  ‖∇v‖_{W̲^{s,∞}(□_m)} ‖F‖_{Ŵ̲^{-s,∞}(□_m)}.
```

The manuscript **never defines** `Ŵ^{-s,p}` (the manuscript defines only the
order `-1` duals, and it defines *those* by duality: a supremum of `∫_U f g`
over a normalized test class).  Following that pattern — and the corrected
rendering of the same symbol — the carrier here is the
**duality form**: `WeakNegDualBoundOn Q s W F` *is* the family of pairing
inequalities.  The Step-4 pairing is then a theorem
(`WeakNegDualBoundOn.pairing`) rather than an assumption.

## The test gauge

`wsInftyGauge Q s Ksup KHol = 3^{-s·Q.scale} · Ksup + KHol` is the printed display's
volume-normalized Hölder norm `‖φ‖_{C̲^{0,s}(□_m)} = |□_m|^{-s/d}‖φ‖_{L^∞} +
[φ]_{C^{0,s}}`, which the manuscript declares interchangeable with
`‖·‖_{W̲^{s,∞}(□_m)}` up to dimensional constants.  Both halves are carried:
The manuscript's Step-4 test function is `∇v`, whose mean does **not** vanish,
so the `L^∞` half is load-bearing (see the disclosure below).

## Two inequivalent renderings of one printed symbol

The §4.5 negative-norm symbol is consumed at two sites that demand
**inequivalent** objects:

* Step 3c (the `L^∞` upgrade) needs the *multiscale* reading — a bound on the
  cube averages of `F` at every scale (this file's `negBesovInftyNorm`,
  this file's `UniformBoxGaugeBound`).  A single-scale duality bound does not
  give it: it loses `r^{-d}` (machine-checked).
* Step 4 (here) needs the *duality* reading.  The multiscale reading does not
  give it either: pairing `B^{s}_{∞,∞}` against `B^{-s}_{∞,∞}` diverges
  logarithmically in the number of scales (the increments contribute a
  constant per scale).

Neither implies the other.  Both are legitimate readings of an undefined
printed symbol; each Step consumes the one it needs, and each is disclosed at
its own consumption site.

## The hat

The printed display's `Ŵ^{-1,p'}` restricts the test class to **mean-zero**
`g`.  Under the hatted reading the pairing above is valid only for mean-zero
`φ`; the general `φ` splits as `φ = (φ)_{□_m} + (φ - (φ)_{□_m})` and the
constant part pairs against `⨍_{□_m} F`.  `weakNegDual_of_hat_of_mean_zero`
records the case in which the two coincide — `⨍_{□_m} F = 0`, which is exactly
the gradient leg `F = ∇u - ∇v` with `u - v ∈ H¹₀(□_m)`.  For the **flux** leg
`F = a_L∇u - σ̄_m∇v` the mean does not vanish and is not controlled by the
hatted norm; that is the second half of the correction draft.
-/

open Homogenization MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The pairing functional -/

/-- **`⨍_{□} F · φ`**, the volume-normalized pairing of two vector fields on the
open realization of a triadic cube. -/
def cubePairing (Q : TriadicCube d) (F phi : Vec d → Vec d) : ℝ :=
  volumeAverage (openCubeSet Q) fun x => vecDot (F x) (phi x)

theorem cubePairing_def (Q : TriadicCube d) (F phi : Vec d → Vec d) :
    cubePairing Q F phi =
      volumeAverage (openCubeSet Q) (fun x => vecDot (F x) (phi x)) := rfl

theorem cubePairing_zero_right (Q : TriadicCube d) (F : Vec d → Vec d) :
    cubePairing Q F (fun _ => 0) = 0 := by
  have hzero : (fun x => vecDot (F x) ((fun _ : Vec d => (0 : Vec d)) x)) =
      fun _ : Vec d => (0 : ℝ) := by
    funext x
    simp only [vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  rw [cubePairing_def, hzero, volumeAverage]
  simp

/-! ## 2. The test gauge `‖φ‖_{W̲^{s,∞}(□_m)}` -/

/-- **the printed display's volume-normalized Hölder norm on `□_m`**,
`3^{-s·m}‖φ‖_{L^∞(□_m)} + [φ]_{C^{0,s}(□_m)}`, presented at the two explicit
data `Ksup` and `KHol` rather than as a constructed norm. -/
def wsInftyGauge (Q : TriadicCube d) (s Ksup KHol : ℝ) : ℝ :=
  Real.rpow 3 (-(s * ((Q.scale : ℤ) : ℝ))) * Ksup + KHol

theorem wsInftyGauge_def (Q : TriadicCube d) (s Ksup KHol : ℝ) :
    wsInftyGauge Q s Ksup KHol =
      Real.rpow 3 (-(s * ((Q.scale : ℤ) : ℝ))) * Ksup + KHol := rfl

theorem wsInftyGauge_nonneg {Q : TriadicCube d} {s Ksup KHol : ℝ} (hs : 0 ≤ Ksup)
    (hk : 0 ≤ KHol) : 0 ≤ wsInftyGauge Q s Ksup KHol := by
  have h3 : (0 : ℝ) ≤ Real.rpow 3 (-(s * ((Q.scale : ℤ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hmul := mul_nonneg h3 hs
  rw [wsInftyGauge_def]
  linarith only [hmul, hk]

theorem wsInftyGauge_zero_sup (Q : TriadicCube d) (s KHol : ℝ) :
    wsInftyGauge Q s 0 KHol = KHol := by
  rw [wsInftyGauge_def, mul_zero, zero_add]

/-! ## 3. The duality-form negative gauge -/

/-- **`‖F‖_{Ŵ̲^{-s,∞}(□_m)} ≤ W`, in duality form** (a correction to the printed statement).

The predicate *is* the family of pairing inequalities the manuscript uses:
for every test field `φ` with volume-normalized Hölder norm at most
`wsInftyGauge Q s Ksup KHol`,

```text
  |⨍_{□} F · φ| ≤ W · (3^{-s·m} Ksup + KHol).
```

This is the printed display's own definitional pattern for the negative-order
duals, transported from order `-1` to order `-s`.  `CoarseGraining`'s
`cubeEuclideanNegativeWspSmoothDualENorm`
(`Homogenization/Sobolev/Fractional/EuclideanWspSmoothDual.lean`) is the same
construction at a bundled `L²` carrier and smooth tests; the lightweight
predicate here is the one the §4.5 consumers need. -/
def WeakNegDualBoundOn (Q : TriadicCube d) (s W : ℝ) (F : Vec d → Vec d) : Prop :=
  ∀ (phi : Vec d → Vec d) (Ksup KHol : ℝ), 0 ≤ Ksup → 0 ≤ KHol →
    (∀ x ∈ openCubeSet Q, ‖phi x‖ ≤ Ksup) →
    HolderSeminormBoundOn (openCubeSet Q) s KHol phi →
    |cubePairing Q F phi| ≤ W * wsInftyGauge Q s Ksup KHol

theorem weakNegDualBoundOn_def {Q : TriadicCube d} {s W : ℝ} {F : Vec d → Vec d} :
    WeakNegDualBoundOn Q s W F ↔
      ∀ (phi : Vec d → Vec d) (Ksup KHol : ℝ), 0 ≤ Ksup → 0 ≤ KHol →
        (∀ x ∈ openCubeSet Q, ‖phi x‖ ≤ Ksup) →
        HolderSeminormBoundOn (openCubeSet Q) s KHol phi →
        |cubePairing Q F phi| ≤ W * wsInftyGauge Q s Ksup KHol :=
  Iff.rfl

/-- **The Step-4 pairing** — a theorem, not an assumption,
because the carrier is the duality form. -/
theorem WeakNegDualBoundOn.pairing {Q : TriadicCube d} {s W Ksup KHol : ℝ}
    {F phi : Vec d → Vec d} (h : WeakNegDualBoundOn Q s W F) (hsup : 0 ≤ Ksup)
    (hhol : 0 ≤ KHol) (hb : ∀ x ∈ openCubeSet Q, ‖phi x‖ ≤ Ksup)
    (hH : HolderSeminormBoundOn (openCubeSet Q) s KHol phi) :
    |cubePairing Q F phi| ≤ W * wsInftyGauge Q s Ksup KHol :=
  h phi Ksup KHol hsup hhol hb hH

/-- A duality level is nonnegative: test against `φ = 0` at gauge `1`. -/
theorem WeakNegDualBoundOn.nonneg {Q : TriadicCube d} {s W : ℝ} {F : Vec d → Vec d}
    (h : WeakNegDualBoundOn Q s W F) : 0 ≤ W := by
  have hb : ∀ x ∈ openCubeSet Q, ‖(fun _ : Vec d => (0 : Vec d)) x‖ ≤ (0 : ℝ) := by
    intro x _
    simp
  have hH : HolderSeminormBoundOn (openCubeSet Q) s 1 (fun _ : Vec d => (0 : Vec d)) := by
    intro x _ y _
    have h0 : ‖(0 : Vec d) - (0 : Vec d)‖ = 0 := by simp
    rw [h0, one_mul]
    exact Real.rpow_nonneg (norm_nonneg _) s
  have hmain := h (fun _ : Vec d => (0 : Vec d)) 0 1 le_rfl zero_le_one hb hH
  rw [cubePairing_zero_right, abs_zero, wsInftyGauge_zero_sup, mul_one] at hmain
  exact hmain

/-- The duality bound is monotone in its level. -/
theorem WeakNegDualBoundOn.mono {Q : TriadicCube d} {s W W' : ℝ} {F : Vec d → Vec d}
    (h : WeakNegDualBoundOn Q s W F) (hWW : W ≤ W') : WeakNegDualBoundOn Q s W' F := by
  intro phi Ksup KHol hsup hhol hb hH
  refine (h phi Ksup KHol hsup hhol hb hH).trans ?_
  exact mul_le_mul_of_nonneg_right hWW (wsInftyGauge_nonneg hsup hhol)

/-! ## 4. The hatted/un-hatted coincidence on a mean-zero field -/

/-- **When the hatted and un-hatted readings agree.**

The printed display's hat restricts the test class to mean-zero fields.  If the
pairing inequality is known only for the mean-subtracted test field `φ - c` —
the hatted hypothesis, at the *same* gauge data, which is what the mean-zero
test class delivers — and if in addition `⨍_{□} F = 0`, then the inequality
holds for `φ` itself: the discarded term is `⟨c, ⨍_{□} F⟩ = 0`.

`⨍_{□_m}(∇u - ∇v) = 0` whenever `u - v ∈ H¹₀(□_m)`, so this is exactly the
gradient leg of Step 4 ("benign on the Step-3 object").  The flux leg has no
such vanishing mean. -/
theorem abs_cubePairing_le_of_mean_zero {Q : TriadicCube d} {F phi : Vec d → Vec d}
    {c : Vec d} {B : ℝ}
    (hmean : cubePairing Q F (fun _ => c) = 0)
    (hsub : |cubePairing Q F (fun x => phi x - c)| ≤ B)
    (hlin : cubePairing Q F phi =
      cubePairing Q F (fun x => phi x - c) + cubePairing Q F (fun _ => c)) :
    |cubePairing Q F phi| ≤ B := by
  rw [hlin, hmean, add_zero]
  exact hsub

end

end Algsuperdiff.Section4.Provider.Homogenization
