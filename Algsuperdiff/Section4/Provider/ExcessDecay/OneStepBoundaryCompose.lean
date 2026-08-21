/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepCornerSeam
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryComposeGlue

/-!
# The boundary one-step excess-decay contraction at every met configuration

The composed endpoint of the boundary branch: the one-step contraction of
`l.excess.decay.good.scales`, conditional only on the harmonic-approximation
anchor, at **every** met configuration — one met face upper or lower, and every
edge/corner orientation.

```text
  E(u, U_k) ≤ C_t · C · κ · (3^{-k})^{1/2} · E(u, U_0)
              + C_r(d, C, k) · 3^{-n} · √((3²)^d) · ‖RHS‖
```

the same display as `OneStepConditional.excessDecay_oneStep_of_harmonicApprox`
with `K_h = 0`, i.e. with the Schauder slot discharged and **no**
boundary-datum leg.

## What is discharged here, relative to the proved one-face endpoint

* the odd-class defect is folded at every orientation
  (`OneStepCornerSeam.exists_gradientHolder_boundary_metSet`, which composes the
  transported `(★)`/`(★★)` of `OneStepCornerTransport*`);
* the oddness binder is the **window-pointwise** one, which is what the chain's
  Weyl representative satisfies — `faceOdd_eqOn_reflectedWindow_of_ae` below is
  the bridge from the a.e. oddness of 's reflection chain;
* the affine-minimizer datum `hmin` is **discharged**, not assumed
  (`OneStepBoundaryComposeGlue.exists_isAffineMinimizer_shifted_truncatedWindow`
  from the proved sandwich attainment), so the statement carries no affine
  parameters at all.

## What is left between this and `l.excess.decay.good.scales`

1. the **interior branch** (no met face), which is
   `OneStepSchauderComposeInterior`/`OneStepConditional`'s own gate;

No analytic input beyond the chain's own binders remains on the boundary
branch's Schauder side.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec vecDot openCubeSet originCube coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The bridge from the reflection chain's a.e. oddness.**  A classically
harmonic representative almost everywhere equal on the doubled window to a
globally met-face-odd datum — which is exactly what 's chain produces — is
pointwise odd about every met face at every point of the doubled window, the
binder shape `exists_gradientHolder_boundary_metSet` consumes. -/
theorem faceOdd_eqOn_reflectedWindow_of_ae {x : Vec d} {m k : ℤ} (hkm : k < m)
    {V O : Vec d → ℝ}
    (hharm : HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m k))
    (hae : V =ᵐ[volume.restrict (reflectedWindow x m k)] O)
    (hupO : ∀ i : Fin d, MeetsUpperFace x m k i → ∀ z : Vec d,
      O (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z)
    (hlowO : ∀ i : Fin d, MeetsLowerFace x m k i → ∀ z : Vec d,
      O (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z) :
    (∀ i : Fin d, MeetsUpperFace x m k i → ∀ y ∈ reflectedWindow x m k,
        V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) = -V y) ∧
      (∀ i : Fin d, MeetsLowerFace x m k i → ∀ y ∈ reflectedWindow x m k,
        V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) = -V y) := by
  have hcont : ContinuousOn V (reflectedWindow x m k) :=
    continuousOn_of_harmonicOnNhd hharm
  exact ⟨fun i hi => eqOn_faceOdd_upper_of_ae_eq hkm hi hcont hae (hupO i hi),
    fun i hi => eqOn_faceOdd_lower_of_ae_eq hkm hi hcont hae (hlowO i hi)⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The one-step excess-decay contraction on the boundary branch, at every met
configuration, with the Schauder slot discharged, no boundary-datum
leg and no affine-minimizer hypothesis.**

The competitor is odd about every met face at every point of the doubled window
and classically harmonic there; the window meets at least one face of `∂□_m`,
in either orientation, with an arbitrary met set otherwise.  The binders
`_hmem`/`_hB`/`_hharm` and the model, scale and window parameters are
transcribed verbatim from
`OneStepConditional.excessDecay_oneStep_of_harmonicApprox`. -/
theorem excessDecay_oneStep_boundary_metSet_of_harmonicApprox (d : ℕ) [NeZero d]
    (hd : d ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m n : ℤ} {k : ℕ} (_hk : 3 ≤ k) {M : ABKModel d} {s : ℝ}
      (hs : 0 < s) (_hs1 : s ≤ 1) {delta : ℝ} (_hdelta1 : delta ≤ 1) {x z : Vec d}
      {i : Fin d} (_hx : x ∈ openCubeSet (originCube d m)) (_hnm : n - 1 ≤ m)
      (_hmn : n - 2 < m)
      (_hmet : MeetsUpperFace x m (n - 2) i ∨ MeetsLowerFace x m (n - 2) i)
      {u v : Vec d → ℝ}
      (_hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
      (_hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
      (_hvR : MemLp v 2 (volume.restrict (reflectedWindow x m (n - 2))))
      (_huv : MemLp (fun y => u y - v y) 2
        (volume.restrict (movedReplacementCube x m n)))
      (_hupv : ∀ l : Fin d, MeetsUpperFace x m (n - 2) l →
        ∀ y ∈ reflectedWindow x m (n - 2),
          v (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v y)
      (_hlowv : ∀ l : Fin d, MeetsLowerFace x m (n - 2) l →
        ∀ y ∈ reflectedWindow x m (n - 2),
          v (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v y)
      (_hharmclass : HarmonicOnNhd
        (v ∘ (Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
          reflectedWindow x m (n - 2)))
      {omega : Cutoff.CutoffSample d}
      (_hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
        (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
        (s / 8 * Real.sqrt delta))
      {B : ℝ≥0∞} (_hB : B ≠ ⊤)
      (_hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
        (fun _omega' =>
          MeasureTheory.eLpNorm (fun y => u y - v y) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                openCubeSet (originCube d (n - 2)))))
        omega ≤ B),
      affineExcess (truncatedWindow x m (n - (k : ℤ))) u
        ≤ taylorContractionConst d * C * windowRatioConst d 2
              * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m n) u
          + triangleRemainderConst d C k
              * ((3 : ℝ) ^ (-n)
                * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal)) := by
  obtain ⟨C, hC0, hC⟩ := Schauder.exists_gradientHolder_boundary_metSet d hd
  refine ⟨C, hC0, ?_⟩
  intro m n k hk M s hs hs1 delta hdelta1 x z i hx hnm hmn hmet u v hu hv hvR huv
    hupv hlowv hharmclass omega hmem B hB hharm
  have hvU : MemLp v 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    hvR.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_reflectedWindow x m (n - 2)) le_rfl)
  obtain ⟨c, A, hmin⟩ :=
    Schauder.exists_isAffineMinimizer_shifted_truncatedWindow hx (by omega) hvU
  obtain ⟨K, hK, hint, hgrad, hhol, hschauder⟩ :=
    hC m n x i v c A hx hmn hmet hupv hlowv hharmclass hvR hmin
  have hmain := excessDecay_oneStep_of_harmonicApprox hd hk hs hs1 hdelta1 hx hnm hu hv
    huv hmem hB hharm hK hC0 hint hgrad hhol (Kh := 0) (by linarith only [hschauder])
  simpa using hmain

end

end Algsuperdiff.Section4.Provider.ExcessDecay
