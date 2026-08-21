/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineInstallData

/-!
# The INSTALLED bundle: the four dominations discharged at the printed carriers

## What this file supplies

The re-cut bundle's four slot dominations are PINNABLE but were not
INSTALLED.  This file installs them.  `SpineDatumRecutCore` is
`HomSpineRecutClose.SpineDatumCoarseGrainingRecut` with

* the abstract slots `Ccg, 𝓔₁, 𝓔₂, D_g` REPLACED by the printed carriers' own
  `toReal` (`recutPinnedCcg`, `recutPinnedE1`, `recutPinnedE2`,
  `recutPinnedDg`);
* the four dominations, the four sign conditions and the two pin equations
  DELETED — they are discharged by `HomSpineRecutSupport`'s `_dominates_self`
  corollaries at exactly those values;
* the order frame reduced to the two conditions that are not numerals: the
  bundle's own guard `s + d/p ≤ 1/2` and the window `7s/8 < s₂`.

What survives is the genuinely content-bearing core:

```text
  { the MULTISCALE clause, hS, hlevel, hlevelDual, hEB/hdom, (jn, s, Cw, S, EB, Fflux) }.
```

`spineDatumCoarseGrainingRecut_of_core` is the installation, general in `(p,
s₂)`; `spineDatumCoarseGrainingRecut_of_core_pinned` instantiates it at the
printed exponent `p = 4d` and the CORRECTED window pin `s₂ = 49/100`
(`HomSpineInstallData` machine-checks that the `s₂ = 3/8` cannot absorb the
forcing leg at the `γ⁵` rate and that `49/100` can).
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The display pin, as `FractionalOrder`s -/

/-- The display pin's low order `s₁′ = s/8` (the sharp choice). -/
def recutOrderLow (s : FractionalOrder) : FractionalOrder :=
  ⟨s.1 / 8, by have h := s.2.1; linarith only [h], by have h := s.2.2; linarith only [h]⟩

@[simp] theorem recutOrderLow_val (s : FractionalOrder) : (recutOrderLow s).1 = s.1 / 8 := rfl

/-- The display pin's dual order `s′ = 7s/8` (the sharp choice: the carrier
comparison's weight hypothesis holds with EQUALITY there). -/
def recutOrderDual (s : FractionalOrder) : FractionalOrder :=
  ⟨7 * s.1 / 8, by have h := s.2.1; linarith only [h],
    by have h := s.2.2; linarith only [h]⟩

@[simp] theorem recutOrderDual_val (s : FractionalOrder) :
    (recutOrderDual s).1 = 7 * s.1 / 8 := rfl

/-- **The CORRECTED window pin** `s₂ = 49/100`.  The earlier value `s₂ = 3/8` is
inside the membership band at `p = 4d` but fails the gap absorption's
exponent condition (`HomSpineInstallData.gapExponent_fails_at_threeEighths`).
`49/100` is inside the band AND absorbs at the `γ⁵` rate. -/
def recutOrderTop : FractionalOrder := ⟨49 / 100, by norm_num, by norm_num⟩

@[simp] theorem recutOrderTop_val : (recutOrderTop : FractionalOrder).1 = 49 / 100 := rfl

/-! ## 2. The four printed carriers, at their own `toReal` -/

/-- The `Ccg` slot, pinned to the produced constant `C(p,d)`. -/
def recutPinnedCcg (d : ℕ) (p : FiniteLpExponent) : ℝ := (cgDualBoundConst d p).toReal

/-- The `𝓔₁` slot, pinned to the printed carrier at the low order `s/8`. -/
def recutPinnedE1 [NeZero d] (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d)
    (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ} (hsig : 0 < sigmaBarM) (s : FractionalOrder) : ℝ :=
  (Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m)
      ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
      (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) sigmaBarM hsig
      (recutOrderLow s)).toReal

/-- The `𝓔₂` slot, pinned to the printed carrier at the half order `s/16`. -/
def recutPinnedE2 [NeZero d] (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d)
    (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ} (hsig : 0 < sigmaBarM) (s : FractionalOrder) : ℝ :=
  (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
      ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
      (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) sigmaBarM hsig
      (fractionalOrderHalf (recutOrderLow s))).toReal

/-- The `D_g` slot, pinned to the printed positive-Besov overlap seminorm. -/
def recutPinnedDg [NeZero d] (m : ℤ) (s2 : FractionalOrder) (p : FiniteLpExponent)
    (g : Vec d → Vec d) : ℝ :=
  (ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g).toReal

theorem recutPinnedCcg_nonneg (d : ℕ) (p : FiniteLpExponent) : 0 ≤ recutPinnedCcg d p :=
  ENNReal.toReal_nonneg

theorem recutPinnedE1_nonneg [NeZero d] (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) (s : FractionalOrder) :
    0 ≤ recutPinnedE1 M L omega m jn hsig s := ENNReal.toReal_nonneg

theorem recutPinnedE2_nonneg [NeZero d] (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) (s : FractionalOrder) :
    0 ≤ recutPinnedE2 M L omega m jn hsig s := ENNReal.toReal_nonneg

theorem recutPinnedDg_nonneg [NeZero d] (m : ℤ) (s2 : FractionalOrder)
    (p : FiniteLpExponent) (g : Vec d → Vec d) : 0 ≤ recutPinnedDg m s2 p g :=
  ENNReal.toReal_nonneg

/-! ## 3. THE REDUCED BUNDLE -/

/-- **THE CONTENT-BEARING CORE OF THE RE-CUT BUNDLE.**

`SpineDatumCoarseGrainingRecut` with every mechanical item pre-discharged: the
four slot dominations are gone (the slots ARE the printed carriers), the four
sign conditions are gone (a `toReal` is nonnegative), and the two pin equations
are gone (the orders ARE `s/8` and `7s/8`).

The remaining conjuncts are exactly:

* the frame `0 < jn`, the bundle's own guard `s + d/p ≤ 1/2`, the window
  `7s/8 < s₂`, and `0 ≤ C_w`, `spineClauseConst … ≤ K_abs`;
* `hEB`, `hdom` — the defect slot against `EthmB(m)`;
* the **MULTISCALE clause** at `Gen:= printedLocalEnergy` (the transcribed
  source hypothesis);
* `hS` — the energy partial-sum slot;
* `hlevel`, `hlevelDual` — the §4.5 level arithmetic
  (`HomSpineInstallArith` reduces both to their residues). -/
def SpineDatumRecutCore [NeZero d] (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (hs : 0 < homS M)
    (sigmaBarM : ℝ) (hsig : 0 < sigmaBarM) (Kabs : ℝ)
    (p : FiniteLpExponent) (s2 : FractionalOrder)
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
      ∃ (jn : ℕ) (Cw S EB : ℝ) (s : FractionalOrder) (Fflux : Vec d → Vec d),
        0 < jn ∧ s.1 + (d : ℝ) / p.exponent.toReal ≤ 1 / 2 ∧
        7 * s.1 / 8 < s2.1 ∧ 0 ≤ Cw ∧
        spineClauseConst d s.1 p.exponent.toReal Cw (stepFourSchauderConst d s.1) ≤ Kabs ∧
        0 ≤ EB ∧
        ENNReal.ofReal EB ≤ ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ∧
        (∀ G : Vec d → Vec d,
          (∀ x ∈ openCubeSet (originCube d m), G x = u.grad x - v.grad x) →
          CoarseGrainingFinitePMultiscale (originCube d m) jn (recutPinnedCcg d p)
            s.1 (s.1 / 4) s2.1 p.exponent.toReal sigmaBarM
            (recutPinnedE1 M L omega m jn hsig s) (recutPinnedE2 M L omega m jn hsig s)
            (recutPinnedDg m s2 p g)
            (printedLocalEnergy
              (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u) G Fflux) ∧
        0 ≤ S ∧
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal
            (s.1 - s.1 / 4) jn N
            (printedLocalEnergy
              (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u) ≤ S) ∧
        coarseGrainingFinitePRHS (recutPinnedCcg d p) s.1 s2.1 sigmaBarM
            (recutPinnedE1 M L omega m jn hsig s) (recutPinnedE2 M L omega m jn hsig s)
            (recutPinnedDg m s2 p g) S ((originCube d m).scale - (jn : ℤ)) ≤
          sigmaBarM *
            (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
        cgTestConst d (originCube d m) s.1 (7 * s.1 / 8)
            p.conjugate.exponent.toReal *
            (Real.rpow 3 (7 * s.1 / 8 * (m : ℝ)) *
              coarseGrainingFinitePRHS (recutPinnedCcg d p) (7 * s.1 / 8) s2.1 sigmaBarM
                (recutPinnedE1 M L omega m jn hsig s)
                (recutPinnedE2 M L omega m jn hsig s) (recutPinnedDg m s2 p g) S
                ((originCube d m).scale - (jn : ℤ))) ≤
          Real.rpow 3 (s.1 * (m : ℝ)) *
            (sigmaBarM *
              (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))

/-! ## 4. THE INSTALLATION -/

/-- **THE INSTALLED BUNDLE.**

The four slot dominations of `SpineDatumCoarseGrainingRecut` are DISCHARGED at
the printed carriers' own `toReal`, and the numeral frame is discharged from the
window hypotheses.  Nothing is assumed beyond `SpineDatumRecutCore`. -/
theorem spineDatumCoarseGrainingRecut_of_core [NeZero d] (hd : 2 ≤ d) (M : ABKModel d)
    (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (hs : 0 < homS M)
    {sigmaBarM Kabs : ℝ} (hsig : 0 < sigmaBarM) (p : FiniteLpExponent)
    (s2 : FractionalOrder) (hp2 : (2 : ℝ≥0∞) ≤ p.exponent) (hs2lt : s2.1 < 1 / 2)
    (hs2gt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1)
    (omega : Cutoff.CutoffSample d)
    (hcore : SpineDatumRecutCore M Cgap Y m hs sigmaBarM hsig Kabs p s2 omega) :
    SpineDatumCoarseGrainingRecut M Cgap Y m hs sigmaBarM hsig Kabs omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨jn, Cw, S, EB, s, Fflux, hjn0, hguard, hwin, hCw, hKabsC, hEB, hdom,
    hCGm, hS0, hS, hlevel, hlevelDual⟩ :=
    hcore L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  /- the data membership, from the root's own Hölder bind -/
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  have hgmem : MemCubeEuclideanFullWsp (originCube d m) s2 p g :=
    memCubeEuclideanFullWsp_of_holderHalf hKg0 hs2lt hs2gt hKg
  refine ⟨jn, Cw, recutPinnedCcg d p, recutPinnedE1 M L omega m jn hsig s,
    recutPinnedE2 M L omega m jn hsig s, recutPinnedDg m s2 p g, S, EB, p, s,
    recutOrderLow s, recutOrderDual s, s2, Fflux, hjn0, hguard, hCw, hKabsC, hEB, hdom,
    rfl, rfl, hwin, hs2lt, hs2gt, hCGm, hS0, hS, hlevel, recutPinnedCcg_nonneg d p,
    recutPinnedE1_nonneg M L omega m jn hsig s, recutPinnedE2_nonneg M L omega m jn hsig s,
    recutPinnedDg_nonneg m s2 p g, ?_, ?_, ?_, ?_, hlevelDual⟩
  · exact cgDualBoundConst_dominates_self d hd p hp2
  · exact parentErrorOne_dominates_self (originCube d m) (recutParentScale m jn)
      (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) hsig (recutOrderLow s)
  · exact parentErrorTwo_dominates_self (originCube d m) (recutParentScale m jn)
      (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) hsig
      (fractionalOrderHalf (recutOrderLow s))
  · exact overlapSeminorm_dominates_self (originCube d m) s2 p hgmem

/-! ## 5. The installation at the printed numeral pin -/

/-- The corrected numeral pin is inside the membership band at `p = 4d`. -/
theorem recutOrderTop_window (d : ℕ) (hd1 : 1 ≤ d) :
    (recutOrderTop : FractionalOrder).1 < 1 / 2 ∧
      1 / 2 - (d : ℝ) / (recutExponent d hd1).exponent.toReal <
        (recutOrderTop : FractionalOrder).1 := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith only [hdR]
  have hquot : (d : ℝ) / (recutExponent d hd1).exponent.toReal = 1 / 4 := by
    rw [recutExponent_toReal d hd1]
    field_simp
  refine ⟨by norm_num, ?_⟩
  rw [recutOrderTop_val, hquot]
  norm_num

/-- **THE INSTALLED BUNDLE AT THE PRINTED PIN** `p = 4d`, `s₁′ = s/8`,
`s′ = 7s/8`, `s₂ = 49/100`. -/
theorem spineDatumCoarseGrainingRecut_of_core_pinned [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (hs : 0 < homS M) {sigmaBarM Kabs : ℝ} (hsig : 0 < sigmaBarM)
    (omega : Cutoff.CutoffSample d)
    (hcore : SpineDatumRecutCore M Cgap Y m hs sigmaBarM hsig Kabs
      (recutExponent d (le_trans (by norm_num) hd)) recutOrderTop omega) :
    SpineDatumCoarseGrainingRecut M Cgap Y m hs sigmaBarM hsig Kabs omega := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  obtain ⟨hlt, hgt⟩ := recutOrderTop_window d hd1
  exact spineDatumCoarseGrainingRecut_of_core hd M Cgap Y m hs hsig
    (recutExponent d hd1) recutOrderTop (recutExponent_two_le d hd1) hlt hgt omega hcore

/-! ## 6. The two level conditions, at the INSTALLED carriers -/

/-- **`hlevel` AT THE INSTALLED CARRIERS, from the named residues alone.**

`HomSpineInstallArith.hlevel_of_energyBound` with the data-slot residue
DISCHARGED (`HomSpineInstallData.overlapSeminorm_toReal_le` bounds the pinned
`D_g` by `C_data · K_g · 3^{(1/2-s₂)m}` from the root's own `C^{0,1/2}` binder)
and every sign condition discharged from the carriers' `toReal`.

What is left is exactly the two named residues:

* `hSbound` — the Theorem-C Step-2 energy-density datum;
* `hA`, `hB`, `hsplit` — the `EthmB(m)` pairing. -/
theorem recutHlevel_of_residues [NeZero d] (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) (s : FractionalOrder) (p : FiniteLpExponent)
    (s2 : FractionalOrder) {g : Vec d → Vec d} {Kg Kh KhInf Cw EB S Cen A B : ℝ}
    (hss2 : s.1 < s2.1) (hs2lt : s2.1 < 1 / 2)
    (hs2gt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1)
    (hKg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKhInf0 : 0 ≤ KhInf) (hKh0 : 0 ≤ Kh) (hCen0 : 0 ≤ Cen)
    (hSbound : S ≤ Cen * energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hA : recutPinnedCcg d p * s.1⁻¹ * recutPinnedE1 M L omega m jn hsig s * Cen ≤ A)
    (hB : recutPinnedCcg d p * s.1 ^ (-(9 / 2) : ℝ) * (s2.1 - s.1)⁻¹ *
        (1 + recutPinnedE2 M L omega m jn hsig s ^ (2 : ℕ)) * cgOverlapDataConst d s2 p *
        (3 : ℝ) ^ (s2.1 * ((((originCube d m).scale - (jn : ℤ)) : ℤ) : ℝ) - s2.1 * (m : ℝ))
          ≤ B)
    (hsplit : A + B ≤ Cw * EB) :
    coarseGrainingFinitePRHS (recutPinnedCcg d p) s.1 s2.1 sigmaBarM
        (recutPinnedE1 M L omega m jn hsig s) (recutPinnedE2 M L omega m jn hsig s)
        (recutPinnedDg m s2 p g) S ((originCube d m).scale - (jn : ℤ)) ≤
      sigmaBarM *
        (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  obtain ⟨hlo, _hhi⟩ := holderHalf_window (p := p) hs2lt hs2gt
  refine hlevel_of_energyBound (Cdata := cgOverlapDataConst d s2 p) hsig s.2.1 hss2
    (recutPinnedCcg_nonneg d p) (recutPinnedE1_nonneg M L omega m jn hsig s)
    (recutPinnedE2_nonneg M L omega m jn hsig s) hKg0 hKhInf0 hKh0 hCen0
    (cgOverlapDataConst_nonneg d s2 p hlo) hSbound
    (overlapSeminorm_toReal_le m s2 p hKg0 hs2lt hs2gt hKg) hA ?_ hsplit
  refine le_trans (le_of_eq ?_) hB
  congr 2
  ring

/-- **`hlevelDual` AT THE INSTALLED CARRIERS, from the named residues alone.**

The same three residues, read at the dual order `s′ = 7s/8` and carrying the
one extra factor `cgTestConstBase d s (7s/8) p′` — the scale-free half of the
test-class constant, the scale half having cancelled exactly against the
display's own `3^{s′m}` (`HomSpineInstallArith.cgTestConst_mul_rpow_originCube`). -/
theorem recutHlevelDual_of_residues [NeZero d] (hd1 : 1 ≤ d) (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) (s : FractionalOrder) (p : FiniteLpExponent)
    (s2 : FractionalOrder) {g : Vec d → Vec d} {Kg Kh KhInf Cw EB S Cen A B : ℝ}
    (hguard : s.1 + (d : ℝ) / p.exponent.toReal ≤ 1 / 2)
    (hwin : 7 * s.1 / 8 < s2.1) (hs2lt : s2.1 < 1 / 2)
    (hs2gt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1)
    (hKg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKhInf0 : 0 ≤ KhInf) (hKh0 : 0 ≤ Kh) (hCen0 : 0 ≤ Cen)
    (hSbound : S ≤ Cen * energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hA : cgTestConstBase d s.1 (7 * s.1 / 8) p.conjugate.exponent.toReal *
        (recutPinnedCcg d p * (7 * s.1 / 8)⁻¹ *
          recutPinnedE1 M L omega m jn hsig s * Cen) ≤ A)
    (hB : cgTestConstBase d s.1 (7 * s.1 / 8) p.conjugate.exponent.toReal *
        (recutPinnedCcg d p * (7 * s.1 / 8) ^ (-(9 / 2) : ℝ) * (s2.1 - 7 * s.1 / 8)⁻¹ *
          (1 + recutPinnedE2 M L omega m jn hsig s ^ (2 : ℕ)) *
          cgOverlapDataConst d s2 p *
          (3 : ℝ) ^ (s2.1 * ((((originCube d m).scale - (jn : ℤ)) : ℤ) : ℝ) -
            s2.1 * (m : ℝ))) ≤ B)
    (hsplit : A + B ≤ Cw * EB) :
    cgTestConst d (originCube d m) s.1 (7 * s.1 / 8) p.conjugate.exponent.toReal *
        (Real.rpow 3 (7 * s.1 / 8 * (m : ℝ)) *
          coarseGrainingFinitePRHS (recutPinnedCcg d p) (7 * s.1 / 8) s2.1 sigmaBarM
            (recutPinnedE1 M L omega m jn hsig s) (recutPinnedE2 M L omega m jn hsig s)
            (recutPinnedDg m s2 p g) S ((originCube d m).scale - (jn : ℤ))) ≤
      Real.rpow 3 (s.1 * (m : ℝ)) *
        (sigmaBarM *
          (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)) := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  obtain ⟨hlo2, _hhi2⟩ := holderHalf_window (p := p) hs2lt hs2gt
  have hs0 : 0 < s.1 := s.2.1
  have hhalf : s.1 / 2 ≤ 7 * s.1 / 8 := by linarith only [hs0]
  have hlts : 7 * s.1 / 8 < s.1 := by linarith only [hs0]
  obtain ⟨hlo, _hhi⟩ := cgOrderWindow_of_guard (p := p) hd1 hs0 hguard hhalf hlts
  refine hlevelDual_of_energyBound (Cdata := cgOverlapDataConst d s2 p) hsig
    (by linarith only [hs0]) hwin hlo (recutPinnedCcg_nonneg d p)
    (recutPinnedE1_nonneg M L omega m jn hsig s)
    (recutPinnedE2_nonneg M L omega m jn hsig s) hKg0 hKhInf0 hKh0 hCen0
    (cgOverlapDataConst_nonneg d s2 p hlo2) hSbound
    (overlapSeminorm_toReal_le m s2 p hKg0 hs2lt hs2gt hKg) hA ?_ hsplit
  refine le_trans (le_of_eq ?_) hB
  congr 3
  ring

/-! ## 7. The successor endpoint, at the INSTALLED bundle -/

/-- **THE SPINE, at `{htail, the INSTALLED core}`.**

`HomSpineRecutClose.homogenization_spine_close_of_coarseGrainingRecut` with the
second conditional replaced by `SpineDatumRecutCore` at the printed pin: the
four slot dominations and the numeral frame no longer appear anywhere. -/
theorem homogenization_spine_close_of_recutCore (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (cstar : ℝ) (hcstar : 0 < cstar) {Cst Cgap Kabs : ℝ} (hCst : 1 ≤ Cst)
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
              SpineDatumRecutCore M Cgap
                (homMinimalScaleFactor (1 - homAlpha M) X) m hs
                ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 Kabs
                (recutExponent d (le_trans (by norm_num) hd)) recutOrderTop omega) →
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
    homogenization_spine_close_of_coarseGrainingRecut d hd cstar hcstar (Cst := Cst)
      (Cgap := Cgap) (Kabs := Kabs) hCst hCgap hKabs
  refine ⟨g0, C, hg0, hC, ?_⟩
  intro M hcs hgamma X hX htail hs m hcore
  refine hend M hcs hgamma X hX htail hs m ?_
  exact hcore.mono fun omega hb =>
    spineDatumCoarseGrainingRecut_of_core_pinned hd M Cgap
      (homMinimalScaleFactor (1 - homAlpha M) X) m hs (Annealed.sigmaBar M m).2 omega hb

end

end Algsuperdiff.Section4.Provider.Homogenization
