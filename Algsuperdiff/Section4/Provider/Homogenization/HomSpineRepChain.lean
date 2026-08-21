/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineRepLimit
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineFrameData

/-!
# Theorem B, §4.5, Step 3c: the chain endpoint with NO representative binder

## What this module is

`HomSpineRepLimit` produces a continuous representative from the negative-order
gauge alone.  This module wires that producer into the two places the
chain assumed one:

* `HasContinuousRepresentative` — the residue predicate — is now a THEOREM
  under the gauge (`hasContinuousRepresentative_of_uniformBoxGauge`,
  `hasContinuousRepresentative_of_negBesovLp`);
* `HomFinitePConversion.ae_linfty_of_negBesovLp` — whose three binders `hgc`,
  `hgw`, `hzero` carried the representative and its face vanishing — is
  restated with those three binders GONE and the conclusion at the a.e.-defined
  `w` itself (`ae_linfty_of_negBesovLp_of_frame`).

The face vanishing `hzero` is not lost: it is the derived
`faceZero_of_continuousRepresentative`, applied to the representative this
module produces.  The only new hypothesis is `hWzero` (`w` vanishes off the
open cube), which the `H¹₀` zero extension supplies and which the frame already
carries.

## The shape of the endpoint

```text
  3^{-m}|w x| ≤ 96 d² · liftGeomFactor (s + d/p) · A     for a.e. x ∈ □_m
```

— the same display as the conversion theorem, with `g` replaced by `w`.
The two agree a.e., so the restricted a.e. statement transfers verbatim; the
consumer (clause (C3)) reads `|u - v|` on the open cube, where `w` IS `u - v`.

## References

* ABK26, Theorem B Step 3.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch03

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The residue, discharged -/

/-- **the residue, as a theorem.**

`HasContinuousRepresentative w` — the ONE irreducible frame item of the §4.5
spine — holds under the translate-uniform negative gauge on `∇w` together with
the integrability and compact support the `H¹₀` zero extension already
supplies.  This is `HomSpineRepLimit.exists_continuous_ae_eq_of_uniformBoxGauge`
read in the vocabulary of `HomSpineFrameData`. -/
theorem hasContinuousRepresentative_of_uniformBoxGauge {m : ℤ} {s A : ℝ}
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hgauge : UniformBoxGaugeBound m s A G) (hs0 : 0 < s) (hs2 : s ≤ 1 / 2) :
    HasContinuousRepresentative w :=
  exists_continuous_ae_eq_of_uniformBoxGauge hw hwI hwc hGI hgauge hs0 hs2

variable [NeZero d]

/-- **the residue, from the PRINTED finite-`p` gauge.**

The same statement with the gauge in the shape `hCG'` supplies it: the printed
`(p,p)` negative Besov gauge of order `-s` on `∇w` at level `A`, plus the
vanishing of `∇w` off `□_m` (the `H¹₀` zero extension).  Nothing else. -/
theorem hasContinuousRepresentative_of_negBesovLp (m : ℤ) {s p A : ℝ}
    (hp : 0 < p) (hs0 : 0 < s) (hguard : s + (d : ℝ) / p ≤ 1 / 2)
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hGzero : ∀ y, y ∉ cubeSet (originCube d m) → G y = 0)
    (hgauge : ∀ N : ℕ, negBesovLpPartialNorm (originCube d m) s p N G ≤ A) :
    HasContinuousRepresentative w := by
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := div_nonneg (Nat.cast_nonneg d) hp.le
  have hs' : 0 < s + (d : ℝ) / p := by linarith only [hs0, hdp]
  exact hasContinuousRepresentative_of_uniformBoxGauge hw hwI hwc hGI
    (uniformBoxGaugeBound_of_negBesovLp m hp hs0 hguard hGI hGzero hgauge) hs' hguard

/-! ## 2. The chain endpoint, at the a.e.-defined function -/

/-- **THE CONVERSION THEOREM, WITH NO REPRESENTATIVE BINDER.**

`HomFinitePConversion.ae_linfty_of_negBesovLp` with `hgc`, `hgw` and `hzero`
REMOVED.  From the printed finite-`p` gauge on `∇w`, the global weak-gradient
frame, and the vanishing of `w` and `∇w` off `□_m`,

```text
  3^{-m}|w x| ≤ 96 d² · liftGeomFactor (s + d/p) · A     for a.e. x ∈ □_m.
```

The continuous representative is produced from the gauge
(`hasContinuousRepresentative_of_negBesovLp`), its face vanishing is the
derived `faceZero_of_continuousRepresentative`, and the display transfers back
to `w` because the two agree a.e. -/
theorem ae_linfty_of_negBesovLp_of_frame (m : ℤ) {s p A : ℝ}
    (hp : 0 < p) (hs0 : 0 < s) (hguard : s + (d : ℝ) / p ≤ 1 / 2)
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hGzero : ∀ y, y ∉ cubeSet (originCube d m) → G y = 0)
    (hWzero : ∀ x, x ∉ openCubeSet (originCube d m) → w x = 0)
    (hgauge : ∀ N : ℕ, negBesovLpPartialNorm (originCube d m) s p N G ≤ A) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      (3 : ℝ) ^ (-(m : ℝ)) * |w x| ≤
        96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * A := by
  obtain ⟨gc, hgc, hgw⟩ :=
    hasContinuousRepresentative_of_negBesovLp m hp hs0 hguard hw hwI hwc hGI hGzero hgauge
  have hzero : ∀ y ∈ cubeFaceSet (originCube d m), gc y = 0 :=
    faceZero_of_continuousRepresentative hWzero hgc hgw
  have hres := ae_linfty_of_negBesovLp (d := d) m hp hs0 hguard hw hwI hwc hGI hGzero
    hgauge hgc hgw hzero
  have hgwR : w =ᵐ[volume.restrict (openCubeSet (originCube d m))] gc :=
    hgw.filter_mono (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
  refine (hres.and hgwR).mono fun x hx => ?_
  rw [hx.2]
  exact hx.1

end

end Algsuperdiff.Section4.Provider.Homogenization
