/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxHalfLevel

/-!
# The re-cut bundle with the Step-4 gauge re-pinned to `α = 1/2`

## The split this file performs

`HomSeamFluxBundle.SpineDatumCoarseGrainingRecutFlux` binds ONE order `s` and
uses it for THREE different jobs:

1. the multiscale/Step-3c base order (the coarse-graining clause, the energy
   partial sums, `hlevel`, and the lifting factor of `spineClauseConst`);
2. the Hölder gauge `α` of the Step-4 dual test (`cgTestConst d □_m α s′ p′` and
   the matching scale power `3^{αm}` in `hlevelDual`);
3. the order at which the produced `WeakNegDualBoundOn` is read, hence the
   Hölder order at which `∇v` is paired.

Job 1 is genuinely at `s = |log γ|⁻¹`.  Jobs 2 and 3 are at `1/2` in the print:
the Step-4 test is `∇v`, and its only regularity is the `C^{0,1/2}` Schauder
estimate.  Identifying 2 and 3 with 1 is OUR wiring, and it is what makes the
test-class conversion's order gap `α - s′ = s/8` close with `s`, which is the
divergence.

This file re-cuts jobs 2 and 3 at `1/2` and leaves job 1 alone.

## The cascade, measured

The split does NOT propagate:

* `HomSeamFluxLane.exists_weakNegDualBounds_of_fluxPair` already binds its four
  orders `(s₁′, s′, s₂, α)` SEPARATELY — no hypothesis ties `α` to the base
  order; only `0 < (α - s′)p′ < d` is asked, and at `α = 1/2` both halves are
  free (`cgOrderWindow_half`, `cgOrderWindowHi_half`);
* `HomSeamFluxLane.stepFourEnergyFlux_of_dualBounds_uniform` is stated for every
  `0 < α ≤ 1/2`, so `α = 1/2` is its own endpoint, at the `s`-FREE constant
  `stepFourSchauderConstU d` it already uses;
* `spineClauseConst d s p C_w C_sch` is untouched: its Step-4 leg `2 C_w C_sch`
  never mentions an order, and its Step-3c leg `96 d² liftGeomFactor(s + d/p)`
  is at job 1's order, unchanged;
* `HomSeamFluxBundle.HomSpineClauseSupplierAt`, the consumer, mentions no order
  at all.

So the re-cut stops one theorem below the supplier interface: the produced
`HomSpineClauseSupplierAt` is BYTE-IDENTICAL to the one.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The upper half of the conversion window at `α = 1/2` -/

/-- The Gagliardo window's upper end at the re-pin.  At `α = 1/2` the order gap
is at most `1/2` and the dual exponent at most `2`, so the product is at most
`1`, which is `< d` for every `d ≥ 2`.  (The `cgOrderWindow_of_guard`
needed the gap `≤ 1/4`; here the crude bound suffices.) -/
theorem cgOrderWindowHi_half {p : FiniteLpExponent} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s)
    (hp2 : (2 : ℝ≥0∞) ≤ p.exponent) :
    (1 / 2 - 7 * s / 8) * p.conjugate.exponent.toReal < (d : ℝ) := by
  have ht2 : p.conjugate.exponent.toReal ≤ 2 := conjugate_toReal_le_two hp2
  have htpos : 0 < p.conjugate.exponent.toReal :=
    finiteLpExponent_toReal_pos p.conjugate
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hgap : 1 / 2 - 7 * s / 8 < 1 / 2 := by linarith only [hs0]
  have hstep : (1 / 2 - 7 * s / 8) * p.conjugate.exponent.toReal <
      1 / 2 * p.conjugate.exponent.toReal :=
    mul_lt_mul_of_pos_right hgap htpos
  have hhalf : 1 / 2 * p.conjugate.exponent.toReal ≤ 1 := by linarith only [ht2]
  linarith only [hstep, hhalf, hdR]

/-! ## 2. The bundle at the re-pinned gauge -/

/-- **THE RE-CUT `hCG'` BUNDLE AT THE SCHAUDER GAUGE `α = 1/2`.**

`HomSeamFluxBundle.SpineDatumCoarseGrainingRecutFlux` with the `hlevelDual`
conjunct read at `α = 1/2`: the test-class constant is
`cgTestConst □_m (1/2) s′ p′` and the scale power on the right is the print's
own `3^{m/2}`.  EVERY other conjunct is verbatim. -/
def SpineDatumCoarseGrainingRecutFluxHalf [NeZero d] (M : ABKModel d) (Cgap : ℝ)
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
        cgTestConst d (originCube d m) (1 / 2) s'.1 p.conjugate.exponent.toReal *
            (Real.rpow 3 (s'.1 * (m : ℝ)) *
              coarseGrainingFinitePRHS Ccg s'.1 s2.1 sigmaBarM E1 E2 Dg S
                ((originCube d m).scale - (jn : ℤ))) ≤
          Real.rpow 3 ((1 / 2 : ℝ) * (m : ℝ)) *
            (sigmaBarM *
              (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))

/-! ## 3. THE CASCADE VERDICT: the re-pinned bundle produces the SAME supplier -/

/-- **THE RE-PINNED `ã` BUNDLE PRODUCES THE SPINE'S CLAUSE SUPPLIER.**

The conclusion is byte-identical to
`HomSeamFluxBundle.homSpineClauseSupplierAt_of_datumRecutFlux`'s: the `α`-split
is invisible to the consumer.  Inside, exactly three lines change — the two
order-window side conditions of the duality legs and the Schauder endpoint's own
order — and each is DISCHARGED MORE CHEAPLY at `α = 1/2` than at `α = s`. -/
theorem homSpineClauseSupplierAt_of_datumRecutFluxHalf [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs : ℝ} (hsig : 0 < sigmaBarM)
    (omega : Cutoff.CutoffSample d)
    (hcg : SpineDatumCoarseGrainingRecutFluxHalf M Cgap Y m sb sigmaBarM hsig Kabs omega) :
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

end

end Algsuperdiff.Section4.Provider.Homogenization
