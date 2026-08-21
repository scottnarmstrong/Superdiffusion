/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxLane

/-!
# The re-cut bundle at `ã_{L,m}`, and the spine's clause supplier

## What this file supplies

`HomSchauderSwap.SpineDatumCoarseGrainingRecutU` is the §4.5 coarse-graining
bundle at the `s`-free Schauder constant, with all four error slots read at the
UNCUT field `a_L`.  This file carries its print-accurate sibling:

```text
  SpineDatumCoarseGrainingRecutFlux  —  the same bundle at ã_{L,m},
      with the EthmB base exponent left as a parameter `sb`.
```

Three bytes change and nothing else:

1. the two `𝓔` slots are the flux-corrected parent errors
   (`HomSeamFluxCoefficient.recutPinnedE1Flux/E2Flux`'s carriers);
2. the `Gen` slot is `printedLocalEnergy` at `ã` — which, by
   `HomSeamFluxCoefficient.printedLocalEnergy_fluxCorrected`, is the SAME
   function of cubes as at `a_L`, so this is a re-spelling, not a change;
3. the `Ccg` slot condition names `HomSeamFluxLane.cgDualBoundConstFlux`.

The base exponent of `EthmB(m)` is freed to a parameter `sb`, because the
re-pin moves it from the printed `s` to `s/8`.  At `sb = ⟨homS M, hs⟩` the
produced supplier IS the `HomSpineFinalEndpoint.HomSpineClauseSupplier`, so
`HomSpineCloseFinal.homogenization_spine_close` consumes it unchanged; at `sb =
homSeamBase M hs` the consumer is the re-pinned spine, whose only new
ingredient is the `s/8` Step-1 moment sibling (NOT carried here).

## Scope

Nothing here is a source-facing claim.  The bundle is a helper `Prop`; the
supplier and the endpoint are conditional APIs.  The endpoint's own
conditional `htail` and the bundle's items are unchanged, read at
the printed coefficient.
-/

open Homogenization Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The bundle at the printed coefficient -/

/-- **THE RE-CUT `hCG'` BUNDLE, AT `ã_{L,m}` AND THE `s`-FREE SCHAUDER
CONSTANT.**

`HomSchauderSwap.SpineDatumCoarseGrainingRecutU` with the four coefficient
occurrences moved to the printed flux-corrected field and the `EthmB(m)` base
exponent freed to `sb`.  Every order pin, window and sign condition is
verbatim. -/
def SpineDatumCoarseGrainingRecutFlux [NeZero d] (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (sb : {s : ℝ // 0 < s})
    (sigmaBarM : ℝ) (hsig : 0 < sigmaBarM) (Kabs : ℝ)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L →
    ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      ∃ (jn : ℕ) (Cw Ccg E1 E2 Dg S EB : ℝ) (p : FiniteLpExponent)
        (s s1' s' s2 : FractionalOrder) (Fflux : Vec d → Vec d),
        0 < jn ∧ s.1 + (d : ℝ) / p.exponent.toReal ≤ 1 / 2 ∧ 0 ≤ Cw ∧
        spineClauseConst d s.1 p.exponent.toReal Cw (stepFourSchauderConstU d) ≤ Kabs ∧
        0 ≤ EB ∧
        ENNReal.ofReal EB ≤ ethmB M Cgap Y m (homN M m) sb omega ∧
        s1'.1 = s.1 / 8 ∧ s'.1 = 7 * s.1 / 8 ∧
        s'.1 < s2.1 ∧ s2.1 < 1 / 2 ∧
        1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1 ∧
        (∀ G : Vec d → Vec d,
          (∀ x ∈ openCubeSet (originCube d m), G x = u.grad x - v.grad x) →
          CoarseGrainingFinitePMultiscale (originCube d m) jn Ccg s.1 (s.1 / 4) s2.1
            p.exponent.toReal sigmaBarM E1 E2 Dg
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
            G Fflux) ∧
        0 ≤ S ∧
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal
            (s.1 - s.1 / 4) jn N
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u) ≤
              S) ∧
        coarseGrainingFinitePRHS Ccg s.1 s2.1 sigmaBarM E1 E2 Dg S
            ((originCube d m).scale - (jn : ℤ)) ≤
          sigmaBarM *
            (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
        0 ≤ Ccg ∧ 0 ≤ E1 ∧ 0 ≤ E2 ∧ 0 ≤ Dg ∧
        cgDualBoundConstFlux d p ≤ ENNReal.ofReal Ccg ∧
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
            (fluxCorrectedCoeffOn M L m (originCube d m) omega) sigmaBarM hsig s1' ≤
          ENNReal.ofReal E1 ∧
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
            (fluxCorrectedCoeffOn M L m (originCube d m) omega) sigmaBarM hsig
            (fractionalOrderHalf s1') ≤ ENNReal.ofReal E2 ∧
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g ≤
          ENNReal.ofReal Dg ∧
        cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
            (Real.rpow 3 (s'.1 * (m : ℝ)) *
              coarseGrainingFinitePRHS Ccg s'.1 s2.1 sigmaBarM E1 E2 Dg S
                ((originCube d m).scale - (jn : ℤ))) ≤
          Real.rpow 3 (s.1 * (m : ℝ)) *
            (sigmaBarM *
              (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))

/-! ## 2. The clause supplier at a free `EthmB` base -/

/-- `HomSpineFinalEndpoint.HomSpineClauseSupplier` with the `EthmB(m)` base
exponent freed to a parameter.  At `sb = ⟨homS M, hs⟩` this is that definition,
byte for byte. -/
def HomSpineClauseSupplierAt (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (sb : {s : ℝ // 0 < s})
    (sigmaBarM Kabs : ℝ) (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L →
    ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      ∃ D : ℝ, 0 ≤ D ∧
        ENNReal.ofReal D ≤ ethmB M Cgap Y m (homN M m) sb omega ∧
        (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
          Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
            Kabs * D *
              dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
        |volumeAverage (openCubeSet (originCube d m))
              (fun y => M.nu * vecNormSq (u.grad y)) -
            volumeAverage (openCubeSet (originCube d m))
              (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
          Kabs * D *
            energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh ^ (2 : ℕ)

/-- At the printed base the free-base supplier IS the one. -/
theorem homSpineClauseSupplier_of_supplierAt (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (hs : 0 < homS M)
    (sigmaBarM Kabs : ℝ) (omega : Cutoff.CutoffSample d)
    (hsup : HomSpineClauseSupplierAt M Cgap Y m ⟨homS M, hs⟩ sigmaBarM Kabs omega) :
    HomSpineClauseSupplier M Cgap Y m hs sigmaBarM Kabs omega := hsup

/-! ## 3. The bundle produces the supplier -/

/-- **THE `ã` BUNDLE PRODUCES THE SPINE'S CLAUSE SUPPLIER.**

`HomSchauderSwap.homSpineClauseSupplier_of_datumRecutU` re-instantiated at the
printed coefficient.  Clause (C3) is unchanged (it never sees the coefficient
except through `Gen`, which is literally the same function); clause (C4) is the
`ã` endpoint of `HomSeamFluxLane`, whose conclusion is coefficient-free.

This is where the coefficient swap is machine-visible: the spine's Dirichlet
binder arrives at `a_L`, is transported to `ã` by the printed display's own
sentence, and never comes back — no `C∇u` shift is ever formed. -/
theorem homSpineClauseSupplierAt_of_datumRecutFlux [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs : ℝ} (hsig : 0 < sigmaBarM)
    (omega : Cutoff.CutoffSample d)
    (hcg : SpineDatumCoarseGrainingRecutFlux M Cgap Y m sb sigmaBarM hsig Kabs omega) :
    HomSpineClauseSupplierAt M Cgap Y m sb sigmaBarM Kabs omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨jn, Cw, Ccg, E1, E2, Dg, S, EB, p, s, s1', s', s2, Fflux,
    hjn0, hguard, hCw, hKabsC, hEB, hdom, hpin1, hpin2, hs's2, hs2lt, hs2gt,
    hCGm, hS0, hS, hlevel, hCcg0, hE10, hE20, hDg0, hCdom, hE1, hE2, hDg, hlevelDual⟩ :=
    hcg L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hprPos : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  have hs0 : 0 < s.1 := s.2.1
  have hdq : (0 : ℝ) ≤ (d : ℝ) / p.exponent.toReal :=
    div_nonneg (Nat.cast_nonneg d) hprPos.le
  have hsle : s.1 ≤ 1 / 2 := by linarith only [hguard, hdq]
  have hbr : 0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
    dataBracket_nonneg_of_binders (h := h) (g := g) hsig hKg hKh hKhInf
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  /- the printed Dirichlet datum, transported to `ã` ( -/
  have hsolFlux : IsDirichletSolutionOn
      (fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField
      (originCube d m) u h g :=
    isDirichletSolutionOn_fluxCorrected_of_cutoff M L m omega hsol
  /- the produced frame, and clause (C3) from the multiscale clause alo -/
  obtain ⟨W, G, hWval, hGval, hWout, hw, hwI, hwc, hGI, hGzero⟩ :=
    spineFrame_of_dirichletPair hsol hcomp
  have hC3 := spineClauseC3_of_multiscale hprPos hs0 hguard hsig (hCGm G hGval) hS hlevel
    hWval hWout hw hwI hwc hGI hGzero
  /- the produced duality legs at `ã`, at the display p -/
  have hp2 : (2 : ℝ≥0∞) ≤ p.exponent := two_le_exponent_of_guard hd1 hs0 hguard
  have hspecC := Classical.choose_spec (exists_weakNegDualBounds_of_fluxPair d hd p hp2)
  rw [← cgDualBoundConstFlux_eq d hd p hp2] at hspecC
  obtain ⟨_hCtop, hlegs⟩ := hspecC
  have hhalf : s.1 / 2 ≤ s'.1 := by
    rw [hpin2]; linarith only [hs0]
  have hlts : s'.1 < s.1 := by
    rw [hpin2]; linarith only [hs0]
  obtain ⟨hlo, hhi⟩ := cgOrderWindow_of_guard (p := p) hd1 hs0 hguard hhalf hlts
  have hs1s : s1'.1 < s'.1 := by
    rw [hpin1, hpin2]; linarith only [hs0]
  have hsc : (originCube d m).scale = m := rfl
  have hjnZ : (0 : ℤ) < (jn : ℤ) := by exact_mod_cast hjn0
  have hnm : (originCube d m).scale - (jn : ℤ) < m := by
    rw [hsc]; omega
  have hjn : (jn : ℤ) = m - ((originCube d m).scale - (jn : ℤ)) := by
    rw [hsc]; ring
  have hwgap : s.1 - s.1 / 4 ≤ s'.1 - s1'.1 := by
    rw [hpin1, hpin2]; linarith only [hs0]
  have hframe : ∀ v' : H1Function (openCubeSet (originCube d m)),
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v' h g →
        IntegrableOn (fun x => vecDot (v'.grad x) (sigmaBarM • v'.grad x))
            (openCubeSet (originCube d m)) volume ∧
          IntegrableOn (fun x => vecDot
              (matVecMul
                ((fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField x)
                (u.grad x)) (v'.grad x)) (openCubeSet (originCube d m)) volume ∧
            (WeakNegDualBoundOn (originCube d m) s.1
                (Real.rpow 3 (s.1 * (m : ℝ)) * sigmaBarM *
                  (Cw * EB *
                    dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                (fun x => matVecMul
                  ((fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField x)
                  (u.grad x) - sigmaBarM • v'.grad x) ∧
              WeakNegDualBoundOn (originCube d m) s.1
                (Real.rpow 3 (s.1 * (m : ℝ)) *
                  (Cw * EB *
                    dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                (fun x => u.grad x - v'.grad x)) := by
    intro v' hcomp'
    refine ⟨integrableOn_comparatorEnergy sigmaBarM v',
      integrableOn_crossEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u v',
      ?_⟩
    exact hlegs M L omega m ((originCube d m).scale - (jn : ℤ)) hnm jn s1' s' s2 s
      hs1s hs's2 hlo hhi hjn sigmaBarM hsig g u v' h hsol hcomp' Kg hKg0 hs2lt hs2gt hKg
      Ccg E1 E2 Dg S
      (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
      hCcg0 hE10 hE20 hDg0 hS0 hCdom hE1 hE2 hDg (s.1 - s.1 / 4)
      (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
      hwgap
      (printedLocalEnergy_nonneg (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
      (fun _ => le_rfl) hS hlevelDual
  /- clause (C4), from the `ã` legs and the `s`-FREE Schauder consta -/
  obtain ⟨v', hcomp', hC4⟩ := stepFourEnergyFlux_of_dualBounds_uniform hd hs0 hsle M L m
    omega sigmaBarM Kg Kh KhInf Cw EB u h g hsig hCw hEB hbr hKg hKhInf hKh hsolFlux
    (integrableOn_selfEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u) hframe
  have hCschNonneg : (0 : ℝ) ≤ stepFourSchauderConstU d := stepFourSchauderConstU_nonneg d
  refine ⟨EB, hEB, hdom, ?_, ?_⟩
  · refine hC3.mono fun x hx => ?_
    refine hx.trans ?_
    have hfac : 96 * (d : ℝ) ^ (2 : ℕ) *
        liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) * Cw ≤ Kabs := by
      have h1 : (0 : ℝ) ≤ 2 * Cw * stepFourSchauderConstU d :=
        mul_nonneg (by linarith only [hCw]) hCschNonneg
      rw [spineClauseConst] at hKabsC
      linarith only [h1, hKabsC]
    have hEBbr : (0 : ℝ) ≤
        EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
      mul_nonneg hEB hbr
    calc 96 * (d : ℝ) ^ (2 : ℕ) *
          liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) * Cw * EB *
            dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh
        = (96 * (d : ℝ) ^ (2 : ℕ) *
            liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) * Cw) *
            (EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by
          ring
      _ ≤ Kabs * (EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) :=
          mul_le_mul_of_nonneg_right hfac hEBbr
      _ = Kabs * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
          ring
  · rw [dirichletComparator_energyAverage_eq hsig hcomp hcomp']
    refine hC4.trans ?_
    have hlift : (0 : ℝ) ≤ liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) :=
      liftGeomFactor_nonneg (by linarith only [hguard])
    have hfac : 2 * Cw * stepFourSchauderConstU d ≤ Kabs := by
      have hd2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) := by
        have hsq : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
        linarith only [hsq]
      have h2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) *
          liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) * Cw :=
        mul_nonneg (mul_nonneg hd2 hlift) hCw
      rw [spineClauseConst] at hKabsC
      linarith only [h2, hKabsC]
    rw [energyBracket]
    calc 2 * Cw * stepFourSchauderConstU d * EB *
          (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
              Real.sqrt sigmaBarM *
                (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ)
        = (2 * Cw * stepFourSchauderConstU d) * (EB *
            (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                Real.sqrt sigmaBarM *
                  (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ)) := by ring
      _ ≤ Kabs * (EB *
            (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                Real.sqrt sigmaBarM *
                  (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hfac (mul_nonneg hEB (sq_nonneg _))
      _ = Kabs * EB *
            (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                Real.sqrt sigmaBarM *
                  (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ) := by ring

/-! ## 4. The spine endpoint, at the `ã` bundle and the printed base -/

/-- **THE SPINE, at `{htail, the `ã` bundle at the printed base}`.**

`HomSchauderSwap.homogenization_spine_close_of_coarseGrainingRecutU` with the
bundle replaced by its flux-corrected sibling.  The conclusion is
byte-identical; only the second conditional changes, and it changes exactly in
the direction the manuscript takes in the paper. -/
theorem homogenization_spine_close_of_coarseGrainingRecutFlux (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) {Cst Cgap Kabs : ℝ} (hCst : 1 ≤ Cst)
    (hCgap : 0 ≤ Cgap) (hKabs : 0 ≤ Kabs) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
          (∀ N : ℕ,
            (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
              ENNReal.ofReal (Cst *
                Real.exp (-((1 - homAlpha M) ^ (2 : ℕ) * ((N : ℝ) - Cst)) /
                  (Cst * M.gamma)))) →
          ∀ hs : 0 < homS M, ∀ m : ℤ,
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              SpineDatumCoarseGrainingRecutFlux M Cgap
                (homMinimalScaleFactor (1 - homAlpha M) X) m ⟨homS M, hs⟩
                ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 Kabs omega) →
            ∃ sigmaBar : ℝ, 0 < sigmaBar ∧
              |sigmaBar -
                  Real.sqrt (M.nu ^ (2 : ℕ) +
                    cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
                C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBar ∧
              ∃ EB : Cutoff.CutoffSample d → ℝ,
                (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
                (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
                  (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                    ENNReal.ofReal
                        (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                          Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) ^ p) ∧
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  ∀ L : ℤ, m ≤ L →
                    ∀ (u v h : H1Function (openCubeSet (originCube d m)))
                      (g : Vec d → Vec d) (Kg Kh KhInf : ℝ),
                      IsDirichletSolutionOn
                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                          (originCube d m) u h g →
                      IsDirichletSolutionOn
                          (fun _ => sigmaBar • (1 : Mat d)) (originCube d m) v h g →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kg g →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kh h.grad →
                      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
                      (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
                        Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                          EB omega *
                            (sigmaBar⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                              (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                        |volumeAverage (openCubeSet (originCube d m))
                              (fun y => M.nu * vecNormSq (u.grad y)) -
                            volumeAverage (openCubeSet (originCube d m))
                              (fun y => sigmaBar * vecNormSq (v.grad y))| ≤
                          EB omega *
                            (Real.sqrt sigmaBar⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                                Real.sqrt sigmaBar *
                                  (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                              (2 : ℕ) := by
  obtain ⟨g0, C, hg0, hC, hend⟩ :=
    homogenization_spine_close d cstar hcstar (Cst := Cst) (Cgap := Cgap) (Kabs := Kabs)
      hCst hCgap hKabs
  refine ⟨g0, C, hg0, hC, ?_⟩
  intro M hcs hgamma X hX htail hs m hcg
  refine hend M hcs hgamma X hX htail hs m ?_
  exact hcg.mono fun omega hb =>
    homSpineClauseSupplier_of_supplierAt M Cgap
      (homMinimalScaleFactor (1 - homAlpha M) X) m hs _ Kabs omega
      (homSpineClauseSupplierAt_of_datumRecutFlux hd M Cgap
        (homMinimalScaleFactor (1 - homAlpha M) X) m ⟨homS M, hs⟩
        (Annealed.sigmaBar M m).2 omega hb)

end

end Algsuperdiff.Section4.Provider.Homogenization
