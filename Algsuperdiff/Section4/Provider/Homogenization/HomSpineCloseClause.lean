/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineFinalEndpoint
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineCloseUnique
import Algsuperdiff.Section4.Provider.Homogenization.HomFinitePConversion

/-!
# Theorem B, §4.5: the per-`ω` clause producer (C3 and C4 together)

## What this module is

`HomSpineFinalEndpoint`'s third conditional is `hclauses`, the per-`ω`
`HomSpineClauseSupplier`.  Its body — for one admissible datum — is produced
here from ONE application of the transcribed printed proposition `hCG'`
(`HomFinitePSource.GeneralCoarseGrainingFiniteP`), the Schauder external
(through `HomSpineFinalStepFour.exists_comparator_stepFourEnergy`), and the
Step-2b/3b data feed.

**Both clauses come from the SAME `hlevel`.**  That is the load-bearing
observation, and it is what makes one defect slot `D` serve both displays:

```text
  hlevel:  RHS_p  ≤  σ̄_m · (C_w · E_B · dataBracket)
```

* Step 4 consumes it through `weakNegDualBounds_of_coarseGraining` and gives
  clause (C4) at `2 C_w C_sch E_B · energyBracket²`;
* Step 3c consumes it at `A:= σ̄_m⁻¹ · RHS_p`, which is exactly the level
  `hCG'.gradPartial` gives the gradient leg, and `hlevel` makes
  `A ≤ C_w E_B dataBracket`; the `ae_linfty_of_negBesovLp` then gives clause
  (C3) at `96 d² γ_lift C_w E_B · dataBracket`.

So `D:= E_B` and the single absorbed constant is

```text
  K_abs:= 2 C_w C_sch + 96 d² · liftGeomFactor(s + d/p) · C_w   (`spineClauseConst`),
```

datum-independent, as `HomSpineClauseSupplier` requires.  This is the
hand-verified "`D = dataBracket` matches exactly", formalized.

## The comparator quantifier

`exists_comparator_stepFourEnergy` delivers (C4) at a PRODUCED comparator `v'`
while the root quantifies `∀ v`.  The uniqueness lemma
(`HomSpineCloseUnique.dirichletComparator_energyAverage_eq`) closes that gap:
the comparator's energy average is the same number for every solution of the
comparator problem.  Clause (C3) needs no transfer at all — the printed
proposition `hCG'` is itself `∀ v`, so the Step-3c chain is run directly at the
root's own `v`.

## The disclosed frame (per datum), and what it is

* `hCG'` — the one mathematical conditional, at THIS comparator;
* `hS` — the Step-2b energy-slot datum (see `HomSpineCloseRecut` for the
  `s₁ = s/4` pin the slot needs);
* `hlevel` — the single arithmetic condition, shared by both clauses;
* `hEB`, `hdom` — the defect and its `EthmB(m)` domination (the manuscript's
  "comparing to the definition of `EthmB(m)`");
* The Step-3c frame `hw`, `hwI`, `hwc`, `hGI`, `hGzero`, `hgc`, `hgw`,
  `hzero` — the rendering of `u - v ∈ H¹₀(□_m)` plus the `H¹₀` zero extension
  of the gradient, carried exactly as `ae_linfty_of_negBesovLp`
  carries it;
* `hC4ex` — the output of
  `HomCGCarrierLegs.exists_comparator_stepFourEnergy_of_dualBounds` at this
  datum.

Nothing is smuggled: the root's own five data binders (`hsol`, `hcomp`, `hKg`,
`hKh`, `hKhInf`) are the only data hypotheses, and the data-bracket
nonnegativity is DERIVED from them (`dataBracket_nonneg_of_binders`).
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The single absorbed constant -/

/-- **The absorbed constant of the two clause displays**, `K_abs`.

`2 C_w C_sch` is Step 4's (the Schauder external's constant times the level
constant), `96 d² · liftGeomFactor(s + d/p) · C_w` is Step 3c's (the finite-`p`
conversion's dimension-only factor times the same level constant).  Their SUM
dominates both, is datum-independent, and is the `K_abs` slot of
`HomSpineClauseSupplier`. -/
def spineClauseConst (d : ℕ) (s p Cw Csch : ℝ) : ℝ :=
  2 * Cw * Csch + 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw

theorem spineClauseConst_nonneg {s p Cw Csch : ℝ} (d : ℕ) (hCw : 0 ≤ Cw)
    (hCsch : 0 ≤ Csch) (hlift : 0 ≤ liftGeomFactor (s + (d : ℝ) / p)) :
    0 ≤ spineClauseConst d s p Cw Csch := by
  have h1 : (0 : ℝ) ≤ 2 * Cw * Csch := mul_nonneg (by linarith only [hCw]) hCsch
  have hd2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) := by
    have : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
    linarith only [this]
  have h2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw :=
    mul_nonneg (mul_nonneg hd2 hlift) hCw
  rw [spineClauseConst]
  linarith only [h1, h2]

/-! ## 2. Clause (C3) from `hCG'` at the printed level -/

/-- **Clause (C3), from ONE `hCG'` application.**

The gradient leg of the printed proposition at level
`A = σ̄_m⁻¹ · RHS_p` (`GeneralCoarseGrainingFiniteP.gradPartial`), pushed
through the finite-`p` conversion `ae_linfty_of_negBesovLp`, with `hlevel`
converting `A` into `C_w E_B · dataBracket`.  The continuous representative is
eliminated against the `H¹` difference, so the conclusion is stated at the
root's own `|u - v|`. -/
theorem spineClauseC3_of_coarseGraining [NeZero d] {m : ℤ} {jn : ℕ}
    {Ccg s s1 s2 p sigmaBarM E1 E2 Dg S Cw EB Kg Kh KhInf : ℝ}
    {Gen : TriadicCube d → ℝ} {Fflux : Vec d → Vec d}
    {u v : H1Function (openCubeSet (originCube d m))} {gc : Vec d → ℝ}
    (hp : 0 < p) (hs0 : 0 < s) (hguard : s + (d : ℝ) / p ≤ 1 / 2) (hsig : 0 < sigmaBarM)
    (hCG : GeneralCoarseGrainingFiniteP (originCube d m) jn Ccg s s1 s2 p sigmaBarM
      E1 E2 Dg Gen (fun x => u.grad x - v.grad x) Fflux)
    (hS : ∀ N : ℕ,
      coarseGrainingEnergyPartial (originCube d m) p (s - s1) jn N Gen ≤ S)
    (hlevel : coarseGrainingFinitePRHS Ccg s s2 sigmaBarM E1 E2 Dg S
        ((originCube d m).scale - (jn : ℤ)) ≤
      sigmaBarM *
        (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
    (hw : HasWeakGradientOn Set.univ (fun x => u.toFun x - v.toFun x)
      (fun x => u.grad x - v.grad x))
    (hwI : Integrable (fun x => u.toFun x - v.toFun x) volume)
    (hwc : HasCompactSupport (fun x => u.toFun x - v.toFun x))
    (hGI : ∀ i, Integrable (fun y => (u.grad y - v.grad y) i) volume)
    (hGzero : ∀ y, y ∉ cubeSet (originCube d m) → u.grad y - v.grad y = 0)
    (hgc : Continuous gc)
    (hgw : (fun x => u.toFun x - v.toFun x) =ᵐ[volume] gc)
    (hzero : ∀ y ∈ cubeFaceSet (originCube d m), gc y = 0) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
        (96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw) * EB *
          dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := div_nonneg (Nat.cast_nonneg d) hp.le
  have hs1 : s + (d : ℝ) / p < 1 := by linarith only [hguard]
  have hlift : (0 : ℝ) ≤ liftGeomFactor (s + (d : ℝ) / p) := liftGeomFactor_nonneg hs1
  have hd2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) := by
    have : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
    linarith only [this]
  have hK : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) :=
    mul_nonneg hd2 hlift
  /- the printed gradient lev -/
  have hgauge : ∀ N : ℕ,
      negBesovLpPartialNorm (originCube d m) s p N (fun x => u.grad x - v.grad x) ≤
        sigmaBarM⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigmaBarM E1 E2 Dg S
          ((originCube d m).scale - (jn : ℤ)) :=
    fun N => hCG.gradPartial hS hsig N
  have hres := ae_linfty_of_negBesovLp (d := d) m hp hs0 hguard hw hwI hwc hGI hGzero
    hgauge (g := gc) hgc hgw hzero
  /- `hlevel` converts the printed level into the printed data brack -/
  have hA : sigmaBarM⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigmaBarM E1 E2 Dg S
      ((originCube d m).scale - (jn : ℤ)) ≤
      Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
    have hstep := mul_le_mul_of_nonneg_left hlevel (inv_nonneg.mpr hsig.le)
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsig), one_mul] at hstep
  have hfinal : 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) *
        (sigmaBarM⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigmaBarM E1 E2 Dg S
          ((originCube d m).scale - (jn : ℤ))) ≤
      (96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw) * EB *
        dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
    refine (mul_le_mul_of_nonneg_left hA hK).trans (le_of_eq ?_)
    ring
  /- the continuous representative is eliminat -/
  have hgwR : (fun x => u.toFun x - v.toFun x) =ᵐ[volume.restrict
      (openCubeSet (originCube d m))] gc :=
    hgw.filter_mono (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
  refine (hres.and hgwR).mono fun x hx => ?_
  have hval : u.toFun x - v.toFun x = gc x := hx.2
  rw [hval]
  exact hx.1.trans hfinal

/-! ## 3. The supplier's body: both clauses at one defect slot -/

/-- **THE PER-`ω` CLAUSE BODY.**

For one admissible datum, the body of `HomSpineClauseSupplier` at
`K_abs = spineClauseConst d s p C_w C_sch` and `D = E_B`: the defect, its
`EthmB(m)` domination, and BOTH printed displays.

Quantifying this over the root's five data binders (and over `L ≥ m`) IS
`HomSpineClauseSupplier`, definitionally; `homSpineClauseSupplier_of_bodies`
records that identity by machine. -/
theorem spineClauseBody_of_coarseGraining [NeZero d] (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (hs : 0 < homS M) {jn : ℕ}
    {Ccg s s1 s2 p sigmaBarM E1 E2 Dg S Cw Csch EB Kg Kh KhInf : ℝ}
    {Gen : TriadicCube d → ℝ} {Fflux : Vec d → Vec d}
    {u v h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    {gc : Vec d → ℝ}
    (hp : 0 < p) (hs0 : 0 < s) (hguard : s + (d : ℝ) / p ≤ 1 / 2) (hsig : 0 < sigmaBarM)
    (hCw : 0 ≤ Cw) (hCsch : 0 ≤ Csch) (hEB : 0 ≤ EB)
    (hdom : ENNReal.ofReal EB ≤ ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega)
    (hKg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKh : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad)
    (hKhInf : ∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf)
    (hcomp : IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d))
      (originCube d m) v h g)
    (hC4ex : ∃ v' : H1Function (openCubeSet (originCube d m)),
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v' h g ∧
        |volumeAverage (openCubeSet (originCube d m))
              (fun y => M.nu * vecNormSq (u.grad y)) -
            volumeAverage (openCubeSet (originCube d m))
              (fun y => sigmaBarM * vecNormSq (v'.grad y))| ≤
          2 * Cw * Csch * EB *
            (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                Real.sqrt sigmaBarM *
                  (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ))
    (hCG : GeneralCoarseGrainingFiniteP (originCube d m) jn Ccg s s1 s2 p sigmaBarM
      E1 E2 Dg Gen (fun x => u.grad x - v.grad x) Fflux)
    (hS : ∀ N : ℕ,
      coarseGrainingEnergyPartial (originCube d m) p (s - s1) jn N Gen ≤ S)
    (hlevel : coarseGrainingFinitePRHS Ccg s s2 sigmaBarM E1 E2 Dg S
        ((originCube d m).scale - (jn : ℤ)) ≤
      sigmaBarM *
        (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
    (hw : HasWeakGradientOn Set.univ (fun x => u.toFun x - v.toFun x)
      (fun x => u.grad x - v.grad x))
    (hwI : Integrable (fun x => u.toFun x - v.toFun x) volume)
    (hwc : HasCompactSupport (fun x => u.toFun x - v.toFun x))
    (hGI : ∀ i, Integrable (fun y => (u.grad y - v.grad y) i) volume)
    (hGzero : ∀ y, y ∉ cubeSet (originCube d m) → u.grad y - v.grad y = 0)
    (hgc : Continuous gc)
    (hgw : (fun x => u.toFun x - v.toFun x) =ᵐ[volume] gc)
    (hzero : ∀ y ∈ cubeFaceSet (originCube d m), gc y = 0) :
    ∃ D : ℝ, 0 ≤ D ∧
      ENNReal.ofReal D ≤ ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ∧
      (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
        Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
          spineClauseConst d s p Cw Csch * D *
            dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
      |volumeAverage (openCubeSet (originCube d m))
            (fun y => M.nu * vecNormSq (u.grad y)) -
          volumeAverage (openCubeSet (originCube d m))
            (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
        spineClauseConst d s p Cw Csch * EB *
          energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh ^ (2 : ℕ) := by
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := div_nonneg (Nat.cast_nonneg d) hp.le
  have hs1 : s + (d : ℝ) / p < 1 := by linarith only [hguard]
  have hlift : (0 : ℝ) ≤ liftGeomFactor (s + (d : ℝ) / p) := liftGeomFactor_nonneg hs1
  have hbr : 0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
    dataBracket_nonneg_of_binders (h := h) (g := g) hsig hKg hKh hKhInf
  refine ⟨EB, hEB, hdom, ?_, ?_⟩
  · /- clause (C -/
    have hC3 := spineClauseC3_of_coarseGraining (d := d) (m := m) (Cw := Cw) (EB := EB)
      (Kg := Kg) (Kh := Kh) (KhInf := KhInf) (u := u) (v := v) (gc := gc)
      hp hs0 hguard hsig hCG hS hlevel hw hwI hwc hGI hGzero hgc hgw hzero
    refine hC3.mono fun x hx => ?_
    refine hx.trans ?_
    have hfac : 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw ≤
        spineClauseConst d s p Cw Csch := by
      have h1 : (0 : ℝ) ≤ 2 * Cw * Csch := mul_nonneg (by linarith only [hCw]) hCsch
      rw [spineClauseConst]
      linarith only [h1]
    have hEBbr : (0 : ℝ) ≤ EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
      mul_nonneg hEB hbr
    calc 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw * EB *
          dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh
        = (96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw) *
            (EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by ring
      _ ≤ spineClauseConst d s p Cw Csch *
            (EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) :=
          mul_le_mul_of_nonneg_right hfac hEBbr
      _ = spineClauseConst d s p Cw Csch * EB *
            dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by ring
  · /- clause (C4), moved from the produced comparator to the root's own `v` -/
    obtain ⟨v', hcomp', hC4⟩ := hC4ex
    rw [dirichletComparator_energyAverage_eq hsig hcomp hcomp']
    refine hC4.trans ?_
    have hfac : 2 * Cw * Csch ≤ spineClauseConst d s p Cw Csch := by
      have hd2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) := by
        have : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
        linarith only [this]
      have h2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw :=
        mul_nonneg (mul_nonneg hd2 hlift) hCw
      rw [spineClauseConst]
      linarith only [h2]
    have hsq : (0 : ℝ) ≤
        energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh ^ (2 : ℕ) :=
      sq_nonneg _
    rw [energyBracket]
    calc 2 * Cw * Csch * EB *
          (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
              Real.sqrt sigmaBarM *
                (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ)
        = (2 * Cw * Csch) * (EB *
            (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                Real.sqrt sigmaBarM *
                  (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ)) := by ring
      _ ≤ spineClauseConst d s p Cw Csch * (EB *
            (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                Real.sqrt sigmaBarM *
                  (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hfac
            (mul_nonneg hEB (sq_nonneg _))
      _ = spineClauseConst d s p Cw Csch * EB *
            (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                Real.sqrt sigmaBarM *
                  (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ) := by ring

/-! ## 4. The supplier is the `∀`-closure of the body -/

/-- **The supplier IS the `∀`-closure of the body.**

A machine-visible record that `HomSpineClauseSupplier` is exactly the universal
closure, over `L ≥ m` and the root's five data binders, of the `∃ D` body proved
in `spineClauseBody_of_coarseGraining`.  The proof is `id`: no bridging. -/
theorem homSpineClauseSupplier_of_bodies (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (hs : 0 < homS M)
    (sigmaBarM Kabs : ℝ) (omega : Cutoff.CutoffSample d)
    (hbody : ∀ L : ℤ, m ≤ L →
      ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
        (Kg Kh KhInf : ℝ),
        IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) u h g →
        IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
        (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
        ∃ D : ℝ, 0 ≤ D ∧
          ENNReal.ofReal D ≤ ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ∧
          (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
            Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
              Kabs * D *
                dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
          |volumeAverage (openCubeSet (originCube d m))
                (fun y => M.nu * vecNormSq (u.grad y)) -
              volumeAverage (openCubeSet (originCube d m))
                (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
            Kabs * D *
              energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh ^ (2 : ℕ)) :
    HomSpineClauseSupplier M Cgap Y m hs sigmaBarM Kabs omega :=
  hbody

end

end Algsuperdiff.Section4.Provider.Homogenization
