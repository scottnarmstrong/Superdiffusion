/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryFull
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerProducer
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryCompose
import Algsuperdiff.Section4.Provider.ExcessDecay.RebaseEpsilon

/-!
# The composed boundary endpoints, re-gated at the clause event

**Strict additions.**  Nothing proved is edited: each theorem here is a new
`_regated` sibling of a proved one-step consumer, stating the SAME conclusion from
the SAME hypotheses except that the anchor display `hharm` is read on the
frozen good event `𝒢(n-2+3, z; s/8, Cv⁻¹ s⁴)` instead of the literal
`𝒢(n-2+3, z; s/8, 1/2)`.

## Why the re-gating is free

Every one of these consumers already carries `hmem`: the sample `ω` is *in* the
printed good-scale event `𝒢(n-2+3, z; s/8, (s/8)√δ)`.  As soon as that supply
threshold sits below the display's threshold — the hypothesis `hrep`, priced by
`RebaseEpsilon.excessDecayDelta_repriced` at `δ ≤ 64 Cv⁻² s⁶` — both
indicators collapse to the same value at `ω`, so a `Cv⁻¹ s⁴`-gated display and a
`(1/2)`-gated one are interchangeable *at that `ω`*
(`indicator_goodEventAt_transfer`).  No analysis, no measurability, no constant
moves.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The re-gated sibling of**
`OneStepBoundaryFull.excessDecay_oneStep_boundary_faceOdd_of_harmonicApprox`.

Statement transcribed byte-for-byte from the proved theorem, with the `hharm`
display re-gated at the frozen threshold `Cv⁻¹ s⁴` and the reachability
hypothesis `hrep` inserted.  The printed supply event `𝒢(n-2+3, z; s/8,
(s/8)√δ)` sits below both thresholds, so the two indicators agree at the
witnessed `ω` and the re-gating is free.
-/
theorem excessDecay_oneStep_boundary_faceOdd_of_harmonicApprox_regated (d : ℕ) [NeZero d]
    (hd : d ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m n : ℤ} {k : ℕ} (_hk : 3 ≤ k) {M : ABKModel d} {s : ℝ}
      (hs : 0 < s) (_hs1 : s ≤ 1) {delta : ℝ} (_hdelta1 : delta ≤ 1) {x z : Vec d}
      {i : Fin d} (_hx : x ∈ openCubeSet (originCube d m)) (_hnm : n - 1 ≤ m)
      (_hmn : n - 2 < m) (_hup : MeetsUpperFace x m (n - 2) i)
      (_hother : ∀ j, j ≠ i →
        ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j)
      {u v : Vec d → ℝ} {c : ℝ} {A : Vec d}
      (_hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
      (_hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
      (_hvR : MemLp v 2 (volume.restrict (reflectedWindow x m (n - 2))))
      (_huv : MemLp (fun y => u y - v y) 2
        (volume.restrict (movedReplacementCube x m n)))
      (_hvodd : ∀ y, v (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) = -v y)
      (_hharmclass : HarmonicOnNhd
        (v ∘ (Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
          reflectedWindow x m (n - 2)))
      (_hmin : IsAffineMinimizer (truncatedWindow x m (n - 2)) v (c - vecDot A x) A)
      {omega : Cutoff.CutoffSample d}
      (_hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
        (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
        (s / 8 * Real.sqrt delta))
      {B : ℝ≥0∞} (_hB : B ≠ ⊤)
      {Cv : ℝ}
      (_hrep : s / 8 * Real.sqrt delta ≤ Cv⁻¹ * s ^ (4 : ℕ))
      (_hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (Cv⁻¹ * s ^ (4 : ℕ)))
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
              * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal)) := by
  obtain ⟨C, hC0, hC⟩ := excessDecay_oneStep_boundary_faceOdd_of_harmonicApprox d hd
  refine ⟨C, hC0, ?_⟩
  intro m n k hk M s hs hs1 delta hdelta1 x z i hx hnm hmn hup hother u v c A hu hv hvR huv hvodd
    hharmclass hmin omega hmem B hB Cv hrep hharm
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrtle : Real.sqrt delta ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hdelta1
  have hep0 : (0 : ℝ) ≤ s / 8 * Real.sqrt delta :=
    mul_nonneg (by linarith only [hs]) hsqrtnn
  have hhalf : s / 8 * Real.sqrt delta ≤ 1 / 2 := by
    have h1 : s / 8 ≤ 1 / 8 := by linarith only [hs1]
    calc s / 8 * Real.sqrt delta ≤ (1 / 8 : ℝ) * 1 :=
          mul_le_mul h1 hsqrtle hsqrtnn (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  exact hC hk hs hs1 hdelta1 hx hnm hmn hup hother hu hv hvR huv hvodd hharmclass hmin hmem hB
    (indicator_goodEventAt_transfer hep0 hrep hhalf hmem hharm)

/-- **The re-gated sibling of**
`OneStepOddClassCornerProducer.excessDecay_oneStep_boundary_corner_of_harmonicApprox`.

Statement transcribed byte-for-byte from the proved theorem, with the `hharm`
display re-gated at the frozen threshold `Cv⁻¹ s⁴` and the reachability
hypothesis `hrep` inserted.  The printed supply event `𝒢(n-2+3, z; s/8,
(s/8)√δ)` sits below both thresholds, so the two indicators agree at the
witnessed `ω` and the re-gating is free.
-/
theorem excessDecay_oneStep_boundary_corner_of_harmonicApprox_regated (d : ℕ) [NeZero d]
    (hd : d ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m n : ℤ} {k : ℕ} (_hk : 3 ≤ k) {M : ABKModel d} {s : ℝ}
      (hs : 0 < s) (_hs1 : s ≤ 1) {delta : ℝ} (_hdelta1 : delta ≤ 1) {x z : Vec d}
      {i j : Fin d} (_hx : x ∈ openCubeSet (originCube d m)) (_hnm : n - 1 ≤ m)
      (_hmn : n - 2 < m) (_hij : i ≠ j) (_hupi : MeetsUpperFace x m (n - 2) i)
      (_hupj : MeetsUpperFace x m (n - 2) j)
      {u v : Vec d → ℝ} {c : ℝ} {A : Vec d}
      (_hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
      (_hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
      (_hvR : MemLp v 2 (volume.restrict (reflectedWindow x m (n - 2))))
      (_huv : MemLp (fun y => u y - v y) 2
        (volume.restrict (movedReplacementCube x m n)))
      (_hupv : ∀ l : Fin d, MeetsUpperFace x m (n - 2) l → ∀ y : Vec d,
        v (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v y)
      (_hlowv : ∀ l : Fin d, MeetsLowerFace x m (n - 2) l → ∀ y : Vec d,
        v (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v y)
      (_hharmclass : HarmonicOnNhd
        (v ∘ (Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
          reflectedWindow x m (n - 2)))
      (_hmin : IsAffineMinimizer (truncatedWindow x m (n - 2)) v (c - vecDot A x) A)
      {omega : Cutoff.CutoffSample d}
      (_hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
        (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
        (s / 8 * Real.sqrt delta))
      {B : ℝ≥0∞} (_hB : B ≠ ⊤)
      {Cv : ℝ}
      (_hrep : s / 8 * Real.sqrt delta ≤ Cv⁻¹ * s ^ (4 : ℕ))
      (_hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (Cv⁻¹ * s ^ (4 : ℕ)))
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
              * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal)) := by
  obtain ⟨C, hC0, hC⟩ := excessDecay_oneStep_boundary_corner_of_harmonicApprox d hd
  refine ⟨C, hC0, ?_⟩
  intro m n k hk M s hs hs1 delta hdelta1 x z i j hx hnm hmn hij hupi hupj u v c A hu hv hvR huv
    hupv hlowv hharmclass hmin omega hmem B hB Cv hrep hharm
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrtle : Real.sqrt delta ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hdelta1
  have hep0 : (0 : ℝ) ≤ s / 8 * Real.sqrt delta :=
    mul_nonneg (by linarith only [hs]) hsqrtnn
  have hhalf : s / 8 * Real.sqrt delta ≤ 1 / 2 := by
    have h1 : s / 8 ≤ 1 / 8 := by linarith only [hs1]
    calc s / 8 * Real.sqrt delta ≤ (1 / 8 : ℝ) * 1 :=
          mul_le_mul h1 hsqrtle hsqrtnn (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  exact hC hk hs hs1 hdelta1 hx hnm hmn hij hupi hupj hu hv hvR huv hupv hlowv hharmclass hmin hmem
    hB (indicator_goodEventAt_transfer hep0 hrep hhalf hmem hharm)

/-- **The re-gated sibling of**
`OneStepBoundaryCompose.excessDecay_oneStep_boundary_metSet_of_harmonicApprox`.

Statement transcribed byte-for-byte from the proved theorem, with the `hharm`
display re-gated at the frozen threshold `Cv⁻¹ s⁴` and the reachability
hypothesis `hrep` inserted.  The printed supply event `𝒢(n-2+3, z; s/8,
(s/8)√δ)` sits below both thresholds, so the two indicators agree at the
witnessed `ω` and the re-gating is free.
-/
theorem excessDecay_oneStep_boundary_metSet_of_harmonicApprox_regated (d : ℕ) [NeZero d]
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
      {Cv : ℝ}
      (_hrep : s / 8 * Real.sqrt delta ≤ Cv⁻¹ * s ^ (4 : ℕ))
      (_hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (Cv⁻¹ * s ^ (4 : ℕ)))
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
  obtain ⟨C, hC0, hC⟩ := excessDecay_oneStep_boundary_metSet_of_harmonicApprox d hd
  refine ⟨C, hC0, ?_⟩
  intro m n k hk M s hs hs1 delta hdelta1 x z i hx hnm hmn hmet u v hu hv hvR huv hupv hlowv
    hharmclass omega hmem B hB Cv hrep hharm
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrtle : Real.sqrt delta ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hdelta1
  have hep0 : (0 : ℝ) ≤ s / 8 * Real.sqrt delta :=
    mul_nonneg (by linarith only [hs]) hsqrtnn
  have hhalf : s / 8 * Real.sqrt delta ≤ 1 / 2 := by
    have h1 : s / 8 ≤ 1 / 8 := by linarith only [hs1]
    calc s / 8 * Real.sqrt delta ≤ (1 / 8 : ℝ) * 1 :=
          mul_le_mul h1 hsqrtle hsqrtnn (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  exact hC hk hs hs1 hdelta1 hx hnm hmn hmet hu hv hvR huv hupv hlowv hharmclass hmem hB
    (indicator_goodEventAt_transfer hep0 hrep hhalf hmem hharm)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
