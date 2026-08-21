/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamGradChain
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamSpineBase

/-!
# The clause supplier and the spine endpoint, re-threaded at the gradient binder

## What this file supplies

`HomSeamGradChain` re-threaded the display's classical-gradient binder through
the supply and the twelve-conjunct core.  This file carries it the rest of the
way to the spine endpoint:

```text
  HomSpineClauseSupplierAtGrad                     -- the supplier, gated
  homSpineClauseSupplierAtGrad_of_datumRecutFluxHalfGrad
  homogenization_spine_endpoint_of_displayGrad
  homogenization_spine_close_of_stepOneDisplayGrad
```

Each is the strict re-threading of its original: the binder list of the
per-`omega` body gains

```text
  HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad ->
```

after the `KhInf` sup binder, and the proof passes it straight through.  The
`E_B` witness, the two moment clauses and the `sigmaBar` clause of the endpoint
are BINDER-FREE and are re-used, not re-proved.
-/

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The clause supplier, gated -/

/-- `HomSeamFluxBundle.HomSpineClauseSupplierAt` with the display's
classical-gradient binder threaded through. -/
def HomSpineClauseSupplierAtGrad (M : ABKModel d) (Cgap : ℝ)
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
      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
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

/-! ## 2. The re-pinned bundle produces the gated supplier -/

/-- `HomSeamFluxHalfBundle.homSpineClauseSupplierAt_of_datumRecutFluxHalf`,
re-threaded.  The proof is the same, with the binder passed through. -/
theorem homSpineClauseSupplierAtGrad_of_datumRecutFluxHalfGrad [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs : ℝ} (hsig : 0 < sigmaBarM)
    (omega : Cutoff.CutoffSample d)
    (hcg : SpineDatumCoarseGrainingRecutFluxHalfGrad M Cgap Y m sb sigmaBarM hsig Kabs omega) :
    HomSpineClauseSupplierAtGrad M Cgap Y m sb sigmaBarM Kabs omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
  obtain ⟨jn, Cw, Ccg, E1, E2, Dg, S, EB, p, s, s1', s', s2, Fflux,
    hjn0, hguard, hCw, hKabsC, hEB, hdom, hpin1, hpin2, hs's2, hs2lt, hs2gt,
    hCGm, hS0, hS, hlevel, hCcg0, hE10, hE20, hDg0, hCdom, hE1, hE2, hDg, hlevelDual⟩ :=
    hcg L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
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
  have hsolFlux : IsDirichletSolutionOn
      (fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField
      (originCube d m) u h g :=
    isDirichletSolutionOn_fluxCorrected_of_cutoff M L m omega hsol
  /- the produced frame, and clause (C3) at the MULTISCALE order, unchang -/
  obtain ⟨W, G, hWval, hGval, hWout, hw, hwI, hwc, hGI, hGzero⟩ :=
    spineFrame_of_dirichletPair hsol hcomp
  have hC3 := spineClauseC3_of_multiscale hprPos hs0 hguard hsig (hCGm G hGval) hS hlevel
    hWval hWout hw hwI hwc hGI hGzero
  /- the produced duality legs at `ã`, now read at the SCHAUDER gau -/
  have hp2 : (2 : ℝ≥0∞) ≤ p.exponent := two_le_exponent_of_guard hd1 hs0 hguard
  have hspecC := Classical.choose_spec (exists_weakNegDualBounds_of_fluxPair d hd p hp2)
  rw [← cgDualBoundConstFlux_eq d hd p hp2] at hspecC
  obtain ⟨_hCtop, hlegs⟩ := hspecC
  have hlo : 0 < ((recutOrderHalf : FractionalOrder).1 - s'.1) *
      p.conjugate.exponent.toReal := by
    rw [recutOrderHalf_val, hpin2]
    exact mul_pos (by linarith only [hsle, hs0]) (finiteLpExponent_toReal_pos p.conjugate)
  have hhi : ((recutOrderHalf : FractionalOrder).1 - s'.1) *
      p.conjugate.exponent.toReal < (d : ℝ) := by
    rw [recutOrderHalf_val, hpin2]
    exact cgOrderWindowHi_half hd hs0 hp2
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
            (WeakNegDualBoundOn (originCube d m) (1 / 2)
                (Real.rpow 3 ((1 / 2 : ℝ) * (m : ℝ)) * sigmaBarM *
                  (Cw * EB *
                    dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                (fun x => matVecMul
                  ((fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField x)
                  (u.grad x) - sigmaBarM • v'.grad x) ∧
              WeakNegDualBoundOn (originCube d m) (1 / 2)
                (Real.rpow 3 ((1 / 2 : ℝ) * (m : ℝ)) *
                  (Cw * EB *
                    dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                (fun x => u.grad x - v'.grad x)) := by
    intro v' hcomp'
    refine ⟨integrableOn_comparatorEnergy sigmaBarM v',
      integrableOn_crossEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u v',
      ?_⟩
    exact hlegs M L omega m ((originCube d m).scale - (jn : ℤ)) hnm jn s1' s' s2
      recutOrderHalf hs1s hs's2 hlo hhi hjn sigmaBarM hsig g u v' h hsol hcomp' Kg hKg0
      hs2lt hs2gt hKg Ccg E1 E2 Dg S
      (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
      hCcg0 hE10 hE20 hDg0 hS0 hCdom hE1 hE2 hDg (s.1 - s.1 / 4)
      (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
      hwgap
      (printedLocalEnergy_nonneg (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
      (fun _ => le_rfl) hS hlevelDual
  /- clause (C4), at `α = 1/2` and the `s`-FREE Schauder consta -/
  obtain ⟨v', hcomp', hC4⟩ := stepFourEnergyFlux_of_dualBounds_uniform hd
    (by norm_num : (0 : ℝ) < 1 / 2) (le_refl (1 / 2 : ℝ)) M L m
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

/-! ## 3. The spine endpoint at the gated supplier -/

/-- `HomSeamSpineBase.homogenization_spine_endpoint_of_display`, re-threaded.
The defect witness `exists_spine_defect_witness_of_display` is binder-free and
is consumed verbatim. -/
theorem homogenization_spine_endpoint_of_displayGrad (d : ℕ) [NeZero d] (cstar : ℝ)
    (hcstar : 0 < cstar) {Cgap Kabs C0 Cflow : ℝ} (hCgap : 0 ≤ Cgap)
    (hKabs : 0 ≤ Kabs) (hC0 : 1 ≤ C0) (hCflow : 0 ≤ Cflow) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ Y : Cutoff.CutoffSample d → ℝ≥0∞, Measurable Y →
          ∀ (m : ℤ) (sb : {s : ℝ // 0 < s}),
            StepOneDisplayAt M Cgap Y m sb C0 →
            ∀ sigmaBarM : ℝ, 0 < sigmaBarM →
            |sigmaBarM -
                Real.sqrt (M.nu ^ (2 : ℕ) +
                  cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
              Cflow * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM →
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              HomSpineClauseSupplierAtGrad M Cgap Y m sb sigmaBarM Kabs omega) →
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
                      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
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
  obtain ⟨g0, Cwit, hg0, hCwit, hwit⟩ :=
    exists_spine_defect_witness_of_display d cstar hcstar hCgap hKabs hC0
  refine ⟨g0, Cwit + Cflow, hg0, by linarith only [hCwit, hCflow], ?_⟩
  intro M hcs hgamma Y hYm m sb hdisp sigmaBarM hsig hC1 hclauses
  obtain ⟨EB, hEB0, hEBm, hEBmom, hlink⟩ := hwit M hcs hgamma Y hYm m sb hdisp
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hginv : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.mpr hgpos).le
  have hLinv : (0 : ℝ) ≤ |Real.log M.gamma|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  refine ⟨sigmaBarM, hsig, ?_, EB, hEB0, hEBm, ?_, ?_⟩
  · /- (C1), re-based at the endpoint's own consta -/
    have hT : (0 : ℝ) ≤ Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hsig.le
    refine hC1.trans ?_
    calc Cflow * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM
        = Cflow * (Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM) := by ring
      _ ≤ (Cwit + Cflow) * (Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM) :=
          mul_le_mul_of_nonneg_right (by linarith only [hCwit]) hT
      _ = (Cwit + Cflow) * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM := by ring
  · /- (C2), re-based at the endpoint's own consta -/
    intro p hp hrange
    have hp0 : (0 : ℝ) ≤ p := by linarith only [hp]
    have hsub : p ≤ Cwit⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ :=
      range_mono_of_le hCwit (by linarith only [hCflow]) hginv hLinv hrange
    refine (hEBmom p hp hsub).trans ?_
    refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0
    have hT : (0 : ℝ) ≤ (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ) := by positivity
    calc Cwit * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
          Real.log M.gamma ^ (2 : ℕ)
        = Cwit * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
            Real.log M.gamma ^ (2 : ℕ)) := by ring
      _ ≤ (Cwit + Cflow) * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hCflow]) hT
      _ = (Cwit + Cflow) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ) := by ring
  · /- (C3) and (C4), through the linka -/
    refine (hlink.and hclauses).mono ?_
    rintro omega ⟨hlk, hsupply⟩ L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
    obtain ⟨D, hD0, hDdom, hC3, hC4⟩ :=
      hsupply L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
    have hKD : Kabs * D ≤ EB omega := hlk D hD0 hDdom
    have hbr : 0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
      dataBracket_nonneg_of_binders (h := h) (g := g) hsig hKg hKh hKhInf
    refine ⟨hC3.mono fun x hx => hx.trans ?_, hC4.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hKD hbr
    · exact mul_le_mul_of_nonneg_right hKD (sq_nonneg _)

/-! ## 4. The spine, with (C1) discharged, at the gated supplier -/

/-- `HomSeamSpineBase.homogenization_spine_close_of_stepOneDisplay`,
re-threaded. -/
theorem homogenization_spine_close_of_stepOneDisplayGrad (d : ℕ) [NeZero d] (cstar : ℝ)
    (hcstar : 0 < cstar) {Cgap Kabs C0 : ℝ} (hCgap : 0 ≤ Cgap) (hKabs : 0 ≤ Kabs)
    (hC0 : 1 ≤ C0) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ Y : Cutoff.CutoffSample d → ℝ≥0∞, Measurable Y →
          ∀ (m : ℤ) (sb : {s : ℝ // 0 < s}),
            StepOneDisplayAt M Cgap Y m sb C0 →
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              HomSpineClauseSupplierAtGrad M Cgap Y m sb
                ((Annealed.sigmaBar M m : ℝ)) Kabs omega) →
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
                      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
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
  obtain ⟨Cib, hCib, hbounds⟩ := Algsuperdiff.Frozen.Section3.induction_bounds d
  have hcinv : (0 : ℝ) ≤ cstar⁻¹ ^ (2 : ℕ) := pow_nonneg (inv_nonneg.mpr hcstar.le) 2
  have hCflow : (0 : ℝ) ≤ Cib * cstar⁻¹ ^ (2 : ℕ) := mul_nonneg hCib.le hcinv
  obtain ⟨g0, C, hg0, hC, hend⟩ :=
    homogenization_spine_endpoint_of_displayGrad d cstar hcstar (Cgap := Cgap)
      (Kabs := Kabs) (C0 := C0) (Cflow := Cib * cstar⁻¹ ^ (2 : ℕ)) hCgap hKabs hC0 hCflow
  have hreg0 : (0 : ℝ) < (Cib⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ) :=
    mul_pos (pow_pos (inv_pos.mpr hCib) 10) (pow_pos hcstar 10)
  refine ⟨min g0 ((Cib⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ)), C, lt_min hg0 hreg0, hC, ?_⟩
  intro M hcs hgamma Y hY m sb hdisp hclauses
  have hreg : M.gamma ≤ (Cib⁻¹) ^ (10 : ℕ) * (Disorder.cstar M) ^ (10 : ℕ) := by
    rw [hcs]
    exact le_trans hgamma (min_le_right _ _)
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hC1 := (hbounds M hreg).2 m
  rw [hcs] at hC1
  exact hend M hcs (le_trans hgamma (min_le_left _ _)) Y hY m sb hdisp
    ((Annealed.sigmaBar M m : ℝ)) hsig hC1 hclauses

end

end Algsuperdiff.Section4.Provider.Homogenization
