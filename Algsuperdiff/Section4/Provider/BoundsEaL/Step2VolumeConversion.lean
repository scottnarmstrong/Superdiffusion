/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.BoundsEaL.Step1ScaleSum

/-!
# Step 2's volume conversion: `3^{d(m-n)} ↦ 3^{(1/2) p s (m-n)}`

Nothing here imports that file, and nothing here claims the anchor.

## What this module is, and what it is not

Step 2 of the proof of `l.bounds.mathcal.E.aL` does two things to the Step-1
endpoint:

1. it replaces the volume factor `3^{d(m-n)}` by the *gauge* factor `3^{(1/2) p
   s (m-n)}` of the printed conclusion, "using.  `d/2 ≤ (1/4) p s`";
2. it takes expectations and collapses the lattice average `⨍_{z ∈ 3^j ℤ^d ∩ □_m}`
   to a single `z` by negation symmetry (`a.j.iso#negation`) and stationarity
   (`a.j.frd#stationary`).

**Only (1) is supplied here**, and it is supplied *pointwise in the sample*, so
no probabilistic input whatsoever enters.

The latter is what is proved and used below; it is exactly the source's floor
`p ≥ 2ds^{-1}` (multiply by `s > 0` and halve), so the printed bookkeeping is
consistent, as the graph records.

## Main results

* `rpow_three_volume_le_gauge` — `3^{d(m-n)} ≤ 3^{(1/2) p s (m-n)}` for `n ≤ m`
  under the source's floor.
* `step2_volume_pointwise_originCube` — the Step-1 endpoint with Step 2's gauge
  factor: pointwise in the sample, at the development carrier `□_m`.
* `step2_volume_pointwise_originCube_rpow` — the same with the gauge factor in
  the anchor's own spelling `(3^{(1/2) s (m-n)})^p`, which is the shape the
  moment splitter of `MomentSplitter.lean` consumes.

## References

* ABK26, `l.bounds.mathcal.E.aL`, (Step 2).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Homogenization Homogenization.Book
open Algsuperdiff.Section3.Provider

noncomputable section

variable {d : ℕ}

/-- **Step 2's volume conversion.**  Under the source's floor `p ≥ 2ds^{-1}` and
`n ≤ m`, the Step-1 volume factor is dominated by the printed gauge factor:

```
3^{d(m-n)} ≤ 3^{(1/2) p s (m-n)} .
```

The exponent inequality is `d ≤ (1/2) p s`, i.e. the floor itself. -/
theorem rpow_three_volume_le_gauge {m n : ℤ} (hnm : n ≤ m) {s p : ℝ} (hs : 0 < s)
    (hp : 2 * (d : ℝ) * s⁻¹ ≤ p) :
    Real.rpow (3 : ℝ) ((d : ℝ) * ((m : ℝ) - (n : ℝ))) ≤
      Real.rpow (3 : ℝ) (1 / 2 * p * s * ((m : ℝ) - (n : ℝ))) := by
  have hmn : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have h : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith only [h]
  have hps : 2 * (d : ℝ) ≤ p * s := by
    have h := mul_le_mul_of_nonneg_right hp hs.le
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hs), mul_one] at h
    exact h
  have hd : (d : ℝ) ≤ 1 / 2 * p * s := by linarith only [hps]
  have hexp : (d : ℝ) * ((m : ℝ) - (n : ℝ)) ≤
      1 / 2 * p * s * ((m : ℝ) - (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hd hmn
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp

/-- **The Step-1 endpoint carrying Step 2's gauge factor**, pointwise in the
sample:

```
𝓔_{s,∞,2}(□_m, n; a, a₀)^p
  ≤ 2^p 3^{(1/2) p s (m-n)} 𝔠_s ∑_{l ≥ 0} 3^{-s l}
      ⨍_{R ∈ descendants(□_m, n - l)} max_{|e|=1} J(R, A₀^{-1/2} e, A₀^{1/2} e; a)^{p/2} .
```

No expectation is taken and no symmetry or stationarity input is used: this is
the Step-1 endpoint of `Step1ScaleSum.lean` composed with the volume
conversion. -/
theorem step2_volume_pointwise_originCube [NeZero d] {m n : ℤ} (hnm : n ≤ m)
    (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hp : 2 * (d : ℝ) * s⁻¹ ≤ p) :
    Real.rpow
        (Ch02.HomogenizationError (originCube d m) n s .infinity (.finite 2) F a0) p ≤
      Real.rpow (2 : ℝ) p * Real.rpow (3 : ℝ) (1 / 2 * p * s * ((m : ℝ) - (n : ℝ))) *
        Ch02.geometricDiscount s 1 *
          ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
            Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
              (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) := by
  have hcs0 : (0 : ℝ) ≤ Ch02.geometricDiscount s 1 :=
    (Homogenization.geometricDiscount_pos (s := s) (q := (1 : ℝ))
      (by linarith only [hs])).le
  have hZ0 : 0 ≤ ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
      Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) :=
    tsum_nonneg fun l => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (ErrorComparison.finsetAverage_normalizedBlockResponseMax_rpow_nonneg
        (originCube d m) (n - (l : ℤ)) F a0 p)
  have hnn : (0 : ℝ) ≤ Real.rpow (2 : ℝ) p * Ch02.geometricDiscount s 1 *
      ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
        Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
          (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hcs0) hZ0
  have hpow := rpow_three_volume_le_gauge (d := d) hnm hs hp
  calc
    Real.rpow
        (Ch02.HomogenizationError (originCube d m) n s .infinity (.finite 2) F a0) p ≤
        Real.rpow (2 : ℝ) p * Real.rpow (3 : ℝ) ((d : ℝ) * ((m : ℝ) - (n : ℝ))) *
          Ch02.geometricDiscount s 1 *
            ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
              Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
                (fun R =>
                  Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) :=
      step1_scaleSum_endpoint_originCube hnm F a0 hs hs1 hp
    _ = Real.rpow (3 : ℝ) ((d : ℝ) * ((m : ℝ) - (n : ℝ))) *
          (Real.rpow (2 : ℝ) p * Ch02.geometricDiscount s 1 *
            ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
              Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
                (fun R =>
                  Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2))) := by
      ring
    _ ≤ Real.rpow (3 : ℝ) (1 / 2 * p * s * ((m : ℝ) - (n : ℝ))) *
          (Real.rpow (2 : ℝ) p * Ch02.geometricDiscount s 1 *
            ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
              Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
                (fun R =>
                  Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2))) :=
      mul_le_mul_of_nonneg_right hpow hnn
    _ = Real.rpow (2 : ℝ) p *
          Real.rpow (3 : ℝ) (1 / 2 * p * s * ((m : ℝ) - (n : ℝ))) *
          Ch02.geometricDiscount s 1 *
            ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
              Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
                (fun R =>
                  Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) := by
      ring

/-- The same display with the gauge factor written as a `p`-th power,
`3^{(1/2) p s (m-n)} = (3^{(1/2) s (m-n)})^p`: this is the anchor's own spelling
of the scalar (`Real.rpow (3 : ℝ) (1/2 * s * ((m : ℝ) - (n : ℝ)))` inside the
outer `p`-th power), and hence the shape the `(Γ₂, Γ_{1/2})` moment splitter
consumes. -/
theorem step2_volume_pointwise_originCube_rpow [NeZero d] {m n : ℤ} (hnm : n ≤ m)
    (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hp : 2 * (d : ℝ) * s⁻¹ ≤ p) :
    Real.rpow
        (Ch02.HomogenizationError (originCube d m) n s .infinity (.finite 2) F a0) p ≤
      Real.rpow (2 : ℝ) p *
        Real.rpow (Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ)))) p *
        Ch02.geometricDiscount s 1 *
          ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
            Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
              (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) := by
  have hgauge : Real.rpow (Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ)))) p =
      Real.rpow (3 : ℝ) (1 / 2 * p * s * ((m : ℝ) - (n : ℝ))) := by
    rw [ErrorComparison.rpow_rpow (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [hgauge]
  exact step2_volume_pointwise_originCube hnm F a0 hs hs1 hp

end

end Algsuperdiff.Section4.Provider.BoundsEaL
