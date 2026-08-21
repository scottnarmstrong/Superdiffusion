/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomCGCarrierRHS
import Algsuperdiff.Section4.Provider.Homogenization.HomCGFinalDatum
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineEndpoint
import Algsuperdiff.Section4.Provider.Homogenization.HomStepFourSchauder

/-!
# The two Step-4 duality legs, PRODUCED at the endpoint's own levels

## What this file supplies

`HomSpineFinalStepFour.weakNegDualBounds_originCube` produces the two
`WeakNegDualBoundOn` slots of `HomSpineEndpoint.stepFourEnergyEndpoint` from
the transcribed hypothesis `hCG'` (its two DUALITY clauses) plus the arithmetic
side condition `hlevel`.  This file produces the SAME two slots from the
display instead — i.e. with the duality clauses no longer assumed:

```text
  weakNegDualBounds_endpointLevels_of_display:
      (the printed display at the smooth dual, read at s′)
        + (ONE arithmetic side condition)
      ⟹  hWf ∧ hWg   at   3^{sm}·σ̄_m·Level   and   3^{sm}·Level.
```

The side condition `hlevelDual` is the exact analogue of `hlevel`: it says the
printed right-hand side, transported to the data order by the test-class
constant, is below the target level.  Nothing else is assumed; in particular no
clause of `GeneralCoarseGrainingFiniteP` appears.

`exists_weakNegDualBounds_of_cutoffPair` then closes the loop: the display's
own hypotheses are the root's two `IsDirichletSolutionOn` binders
(`HomCGDischargeInstantiation`), its data hypothesis is the root's `C^{0,1/2}`
binder on `𝐠` (`HomCGFinalDatum.memCubeEuclideanFullWsp_of_holderHalf`), and
its right-hand side is transferred to this repository's real-valued spelling by
`HomCGCarrierRHS` on top of the `S`-slot comparison of `HomCGCarrierEnergy`.
-/

open Homogenization Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The two legs at the endpoint's levels -/

/-- **The two Step-4 duality slots, from the display and ONE side condition.**

`hlevelDual` is the analogue of `HomFinitePSource`'s `hlevel`: the printed
right-hand side `R`, carried to the data order `s` by the test-class constant
`K_test`, is below `3^{sm}·σ̄_m·Level`.  Under it the display produces exactly
the two slots `stepFourEnergyEndpoint` consumes. -/
theorem weakNegDualBounds_endpointLevels_of_display {m : ℤ}
    (M : Section3.ABKModel d) (L : ℤ) (omega : Section3.Cutoff.CutoffSample d)
    {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    {u v : H1Function (openCubeSet (originCube d m))}
    (s' s : FractionalOrder) (p : FiniteLpExponent)
    (hlo : 0 < (s.1 - s'.1) * p.conjugate.exponent.toReal)
    (hhi : (s.1 - s'.1) * p.conjugate.exponent.toReal < (d : ℝ))
    {R : ℝ≥0∞} (hRtop : R ≠ ⊤)
    (hdisp : ENNReal.ofReal (Real.rpow 3 (-s'.1 * (m : ℝ))) *
        centeredCubeFluxComparisonSmoothDualLHS m
          (Section3.Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m))
          sigma0 u v s' p ≤ R)
    {Level : ℝ}
    (hlevelDual : cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
        (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal) ≤
      Real.rpow 3 (s.1 * (m : ℝ)) * (sigma0 * Level)) :
    WeakNegDualBoundOn (originCube d m) s.1
        (Real.rpow 3 (s.1 * (m : ℝ)) * sigma0 * Level)
        (fun x => matVecMul
          ((Section3.Cutoff.coefficientCutoff M.nu L omega).toCoeffField x) (u.grad x) -
          sigma0 • v.grad x) ∧
      WeakNegDualBoundOn (originCube d m) s.1 (Real.rpow 3 (s.1 * (m : ℝ)) * Level)
        (fun x => u.grad x - v.grad x) := by
  obtain ⟨hgrad, hflux⟩ :=
    weakNegDualBounds_of_smoothDualDisplay (a :=
      Section3.Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m))
      hsigma0 s' s p hlo hhi hRtop hdisp
  refine ⟨hflux.mono ?_, hgrad.mono ?_⟩
  · /- the flux l -/
    calc cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
          (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal)
        ≤ Real.rpow 3 (s.1 * (m : ℝ)) * (sigma0 * Level) := hlevelDual
      _ = Real.rpow 3 (s.1 * (m : ℝ)) * sigma0 * Level := by ring
  · /- the gradient leg: strip the printed `σ̄_m` weig -/
    have hinv : (0 : ℝ) ≤ sigma0⁻¹ := le_of_lt (inv_pos.mpr hsigma0)
    have hstep := mul_le_mul_of_nonneg_left hlevelDual hinv
    have hleft : sigma0⁻¹ * (cgTestConst d (originCube d m) s.1 s'.1
          p.conjugate.exponent.toReal * (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal)) =
        cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
          (sigma0⁻¹ * (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal)) := by ring
    have hright : sigma0⁻¹ * (Real.rpow 3 (s.1 * (m : ℝ)) * (sigma0 * Level)) =
        Real.rpow 3 (s.1 * (m : ℝ)) * Level := by
      field_simp
    rw [hleft, hright] at hstep
    exact hstep

/-! ## 2. The legs from the root's own binders -/

/-- **The two Step-4 duality slots, from the root's own binders.**

Nothing of `GeneralCoarseGrainingFiniteP` is used.  The inputs are:

* the root's two `IsDirichletSolutionOn` binders (the printed elliptic pair);
* the root's `C^{0,1/2}` binder on `𝐠` (the printed `𝐠 ∈ W^{s₂,p}`);
* the four slot dominations of `HomCGCarrierRHS`, and the `S`-slot comparison
  of `HomCGCarrierEnergy` (whose hypothesis is the bundle's own `hS`);
* the arithmetic side condition `hlevelDual`.

The constant `C(p,d)` is produced ONCE, before the model, the scale and the
data. -/
theorem exists_weakNegDualBounds_of_cutoffPair (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : Section3.ABKModel d) (L : ℤ) (omega : Section3.Cutoff.CutoffSample d)
        (m n : ℤ) (hnm : n < m) (jn : ℕ) (s1' s' s2 s : FractionalOrder),
        s1'.1 < s'.1 → s'.1 < s2.1 →
        0 < (s.1 - s'.1) * p.conjugate.exponent.toReal →
        (s.1 - s'.1) * p.conjugate.exponent.toReal < (d : ℝ) →
        (jn : ℤ) = m - n →
      ∀ (sigma0 : ℝ) (hsigma0 : 0 < sigma0) (g : Vec d → Vec d)
        (u v h : H1Function (openCubeSet (originCube d m))),
        IsDirichletSolutionOn
          (Section3.Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) u h g →
        IsDirichletSolutionOn (fun _ => sigma0 • (1 : Mat d)) (originCube d m) v h g →
      ∀ Kg : ℝ, 0 ≤ Kg →
        s2.1 < 1 / 2 → 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1 →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      ∀ (Ccg E1 E2 Dg S Level : ℝ), 0 ≤ Ccg → 0 ≤ E1 → 0 ≤ E2 → 0 ≤ Dg → 0 ≤ S →
        C ≤ ENNReal.ofReal Ccg →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m) n
            (by simpa [originCube] using hnm.le)
            (Section3.Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m))
            sigma0 hsigma0 s1' ≤ ENNReal.ofReal E1 →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m) n
            (by simpa [originCube] using hnm.le)
            (Section3.Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m))
            sigma0 hsigma0 (fractionalOrderHalf s1') ≤ ENNReal.ofReal E2 →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g ≤
          ENNReal.ofReal Dg →
      ∀ (wgap : ℝ) (Gen : TriadicCube d → ℝ), wgap ≤ s'.1 - s1'.1 →
        (∀ R : TriadicCube d, 0 ≤ Gen R) →
        (∀ R : TriadicCube d,
          printedLocalEnergy (Section3.Cutoff.coefficientCutoffCoeffOn M L omega
            (originCube d m)) u R ≤ Gen R) →
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal wgap jn N Gen ≤ S) →
        cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
            (Real.rpow 3 (s'.1 * (m : ℝ)) *
              coarseGrainingFinitePRHS Ccg s'.1 s2.1 sigma0 E1 E2 Dg S n) ≤
          Real.rpow 3 (s.1 * (m : ℝ)) * (sigma0 * Level) →
        WeakNegDualBoundOn (originCube d m) s.1
            (Real.rpow 3 (s.1 * (m : ℝ)) * sigma0 * Level)
            (fun x => matVecMul
              ((Section3.Cutoff.coefficientCutoff M.nu L omega).toCoeffField x) (u.grad x) -
              sigma0 • v.grad x) ∧
          WeakNegDualBoundOn (originCube d m) s.1 (Real.rpow 3 (s.1 * (m : ℝ)) * Level)
            (fun x => u.grad x - v.grad x) := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCtop, hC⟩ := exists_printedCoarseGraining_of_cutoffPair d hd p hp
  refine ⟨C, hCtop, ?_⟩
  intro M L omega m n hnm jn s1' s' s2 s hs1s hss2 hlo hhi hjn sigma0 hsigma0 g u v h
    hsol hcomp Kg hKg0 hs2lt hs2gt hKg Ccg E1 E2 Dg S Level hCcg0 hE10 hE20 hDg0 hS0
    hCdom hE1 hE2 hDg wgap Gen hw hGen0 hGen hS hlevelDual
  have hn : n ≤ (originCube d m).scale := by simpa [originCube] using hnm.le
  have hjn' : (jn : ℤ) = (originCube d m).scale - n := by
    simpa [originCube] using hjn
  set a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)) :=
    Section3.Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m) with hadef
  /- the printed data hypothesis, from the root's own Hölder bind -/
  have hgmem : MemCubeEuclideanFullWsp (originCube d m) s2 p g :=
    memCubeEuclideanFullWsp_of_holderHalf hKg0 hs2lt hs2gt hKg
  /- the displ -/
  have hdisp := hC M L omega m n hnm s1' s' s2 hs1s hss2 sigma0 hsigma0 g hgmem u v h
    hsol hcomp
  /- the `S`-slot comparis -/
  have hSlot : weightedLocalSymmetricEnergyLp (originCube d m) n hn a u s1' s' p ≤
      ENNReal.ofReal S :=
    weightedLocalSymmetricEnergyLp_le_ofReal hn a u s1' s' p hw hjn' hGen0 hGen hS0 hS
  /- the right-hand side, transferr -/
  have hRle := localCoarseGrainingLpRHS_toReal_le hn a hsigma0 g u s1' s' s2 p hss2
    hCcg0 hE10 hE20 hDg0 hS0 hCdom hE1 hE2 hDg hSlot
  have hRtop := localCoarseGrainingLpRHS_ne_top hn a hsigma0 g u s1' s' s2 p hss2
    hCcg0 hE10 hE20 hDg0 hS0 hCdom hE1 hE2 hDg hSlot
  /- the side condition, at the produced right-hand si -/
  have hK0 : (0 : ℝ) ≤ cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal :=
    cgTestConst_nonneg d (originCube d m) hlo
  have hstep : cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
      (Real.rpow 3 (s'.1 * (m : ℝ)) *
        (localCoarseGrainingLpRHS C (originCube d m) n hn a sigma0 hsigma0 g u
          s1' s' s2 p).toReal) ≤
      Real.rpow 3 (s.1 * (m : ℝ)) * (sigma0 * Level) := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hK0) hlevelDual
    exact mul_le_mul_of_nonneg_left hRle (three_rpow_nonneg _)
  exact weakNegDualBounds_endpointLevels_of_display M L omega hsigma0 s' s p hlo hhi
    hRtop hdisp hstep

/-! ## 3. Clause (C4) from the PRODUCED legs -/

/-- **Clause (C4) of the frozen root, with the duality clauses PRODUCED.**

`HomSpineFinalStepFour.exists_comparator_stepFourEnergy` with the
`GeneralCoarseGrainingFiniteP` conjunct of its comparator frame replaced by the
two `WeakNegDualBoundOn` slots themselves — the slots
`exists_weakNegDualBounds_of_cutoffPair` produces from the root's own binders.

So the `hC4ex` payload the spine's bundle currently carries as an item is
obtainable from: the Schauder external (which supplies the comparator and its
three data), the two `H¹`-level integrability facts, and the produced duality
legs.  No clause of `GeneralCoarseGrainingFiniteP` is used. -/
theorem exists_comparator_stepFourEnergy_of_dualBounds (dimension : 2 ≤ d) {s : ℝ}
    (s_pos : 0 < s) (s_le : s ≤ 1 / 2) :
    ∃ Csch : ℝ, 0 < Csch ∧
      ∀ (M : Section3.ABKModel d) (L m : ℤ) (omega : Section3.Cutoff.CutoffSample d)
        (sigmaBarM Kg Kh KhInf Cw EB : ℝ)
        (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        0 < sigmaBarM → 0 ≤ Cw → 0 ≤ EB →
        0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
        (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
        IsDirichletSolutionOn
          (Section3.Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) u h g →
        IntegrableOn (fun x => vecDot (u.grad x)
          (matVecMul ((Section3.Cutoff.coefficientCutoff M.nu L omega).toCoeffField x)
            (u.grad x))) (openCubeSet (originCube d m)) volume →
        (∀ v : H1Function (openCubeSet (originCube d m)),
          IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d))
              (originCube d m) v h g →
            IntegrableOn (fun x => vecDot (v.grad x) (sigmaBarM • v.grad x))
                (openCubeSet (originCube d m)) volume ∧
              IntegrableOn (fun x => vecDot
                  (matVecMul
                    ((Section3.Cutoff.coefficientCutoff M.nu L omega).toCoeffField x)
                    (u.grad x)) (v.grad x)) (openCubeSet (originCube d m)) volume ∧
                (WeakNegDualBoundOn (originCube d m) s
                    (Real.rpow 3 (s * (m : ℝ)) * sigmaBarM *
                      (Cw * EB *
                        dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                    (fun x => matVecMul
                      ((Section3.Cutoff.coefficientCutoff M.nu L omega).toCoeffField x)
                      (u.grad x) - sigmaBarM • v.grad x) ∧
                  WeakNegDualBoundOn (originCube d m) s
                    (Real.rpow 3 (s * (m : ℝ)) *
                      (Cw * EB *
                        dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                    (fun x => u.grad x - v.grad x))) →
        ∃ v : H1Function (openCubeSet (originCube d m)),
          IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d))
              (originCube d m) v h g ∧
            |volumeAverage (openCubeSet (originCube d m))
                  (fun y => M.nu * vecNormSq (u.grad y)) -
                volumeAverage (openCubeSet (originCube d m))
                  (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
              2 * Cw * Csch * EB *
                (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                    Real.sqrt sigmaBarM *
                      (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ) := by
  obtain ⟨Csch, hCschPos, hpack⟩ :=
    exists_comparator_schauder_package (d := d) dimension s_pos s_le
  refine ⟨Csch, hCschPos, ?_⟩
  intro M L m omega sigmaBarM Kg Kh KhInf Cw EB u h g hsig hCw hEB hD hKg hKhInf hKh
    hsol hiU hframe
  obtain ⟨v, hcomp, Ksup, KHol, hsup, hhol, hb, hH, hgauge⟩ :=
    hpack m sigmaBarM hsig g h Kg KhInf Kh hKg hKhInf hKh
  obtain ⟨hiV, hiC, hWf, hWg⟩ := hframe v hcomp
  exact ⟨v, hcomp, stepFourEnergyEndpoint M L m omega hsig hCw hEB hD hsup hhol hsol
    hcomp hiU hiV hiC hb hH hgauge hWf hWg⟩

end

end Algsuperdiff.Section4.Provider.Homogenization
