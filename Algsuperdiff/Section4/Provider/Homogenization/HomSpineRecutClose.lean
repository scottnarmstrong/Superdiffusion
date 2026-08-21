/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineRecutSupport
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineCloseFinal
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineRepChain

/-!
# Theorem B, §4.5: THE BUNDLE RE-CUT — the multiscale clause alone

## What changes

`HomSpineRepClose.SpineDatumCoarseGrainingGauge` carries the transcribed source
hypothesis `hCG'` at ALL THREE of its clauses and the Schauder external's
Step-4 output `hC4ex` as an item.  The two DUALITY clauses and `hC4ex` are
PRODUCIBLE from the root's own binders.  This module performs the resulting
re-cut:

```text
  SpineDatumCoarseGrainingRecut  =  SpineDatumCoarseGrainingGauge
      with  hCG'   ↦  its MULTISCALE clause alone
      with  hC4ex  DELETED
      plus  the four slot dominations + hlevelDual, at the display pin
            s₁′ = s/8, s′ = 7s/8, with Gen:= printedLocalEnergy.
```

* the two duality clauses come from the printed display through
  `HomCGCarrierLegs.exists_weakNegDualBounds_of_cutoffPair`, whose own inputs
  are the root's two `IsDirichletSolutionOn` binders and the root's `C^{0,1/2}`
  binder on `𝐠`;
* `hC4ex` comes from
  `HomCGCarrierLegs.exists_comparator_stepFourEnergy_of_dualBounds` — the
  external supplies the comparator, and the three `H¹`-level integrability facts
  are PRODUCED here (`memVectorL2_coeffFlux`), not assumed;
* the four slot dominations are the price of route (i): they tie the bundle's
  abstract numbers `Ccg, 𝓔₁, 𝓔₂, D_g` to the printed carriers of the display.
  `HomSpineRecutSupport` machine-checks that every one of those carriers is
  FINITE, so each domination is satisfiable by pinning the number to the
  carrier's own `toReal`.  No printed finiteness requirement survives.

### The order pin, and why it is forced

`HomCGCarrierEnergy`'s comparison needs `wgap ≤ s′ - s₁′`, and the bundle's own
`wgap` is `s - s/4 = 3s/4`.  The pin `s₁′ = s/8`, `s′ = 7s/8` meets it with
EQUALITY, and the order loss `s - s′ = s/8` keeps the duality window `0 <
(s-s′)p′ < d` open (`HomCGFinalDuality.cgOrderWindow_of_guard`).  The per-site
reading is the disposition of the correction.

## The final conditional set is still exactly two entries

1. `htail` — the Theorem-C minimal-scale tail, a declared dependency
   edge (Theorem C), not an internal §4.5 obligation;
2. `hcg` — the per-`ω` bundle `SpineDatumCoarseGrainingRecut`, whose items are
   the MULTISCALE clause of `hCG'` (a declared source hypothesis), the
   energy slot `hS`, the level conditions `hlevel`/`hlevelDual`, the four slot
   dominations, `hEB`/`hdom`, and the numerical frame.  NO duality clause, NO
   `hC4ex`, NO frame item.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The three `H¹`-level integrability facts, PRODUCED -/

/-- **The flux of an `H¹` function against a Chapter-2 coefficient is `L²`.**

The public coefficient object is only a.e.-elliptic, so the proof passes to the
internal pointwise-good representative and transports back — `CoarseGraining`'s
own route for `Solution.flux_memVectorL2`, here for a bare `H¹` function. -/
theorem memVectorL2_coeffFlux {Q : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (u : H1Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet Q) (fun x => matVecMul (a.toCoeffField x) (u.grad x)) := by
  let b : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn (Book.Ch02.cubeDomain Q) a
  have hb : Book.Ch02.CoeffOn.AEEq b a := by
    simpa [b] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Book.Ch02.cubeDomain Q) a
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet Q) b.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn (Book.Ch02.cubeDomain Q) a
  have hbase : MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul (b.toCoeffField x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  refine MeasureTheory.MemLp.ae_eq ?_ hbase
  exact hb.mono fun x hx => by simp [hx]

/-- The `u`-energy density is integrable on the window. -/
theorem integrableOn_selfEnergy {Q : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (u : H1Function (openCubeSet Q)) :
    IntegrableOn (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
      (openCubeSet Q) volume :=
  integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 (memVectorL2_coeffFlux a u)

/-- The comparator's energy density is integrable on the window. -/
theorem integrableOn_comparatorEnergy {Q : TriadicCube d} (sigma0 : ℝ)
    (v : H1Function (openCubeSet Q)) :
    IntegrableOn (fun x => vecDot (v.grad x) (sigma0 • v.grad x)) (openCubeSet Q) volume :=
  integrableOn_vecDot_of_memVectorL2 v.grad_memVectorL2
    (v.grad_memVectorL2.const_smul sigma0)

/-- The cross term is integrable on the window. -/
theorem integrableOn_crossEnergy {Q : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (u v : H1Function (openCubeSet Q)) :
    IntegrableOn (fun x => vecDot (matVecMul (a.toCoeffField x) (u.grad x)) (v.grad x))
      (openCubeSet Q) volume :=
  integrableOn_vecDot_of_memVectorL2 (memVectorL2_coeffFlux a u) v.grad_memVectorL2

/-! ## 2. The Step-3c leg from the MULTISCALE clause alone -/

/-- The scale index the display is entered at: `n = m - jn`. -/
theorem recutParentScale (m : ℤ) (jn : ℕ) :
    (originCube d m).scale - (jn : ℤ) ≤ (originCube d m).scale :=
  sub_le_self _ (Int.natCast_nonneg jn)

/-- **Clause (C3), from the MULTISCALE clause and the PRODUCED frame.**

`HomSpineFrameClose.spineClauseC3_of_frame` with the transcribed hypothesis
weakened to its multiscale clause: the proof used no other clause, and the
continuous representative is produced from the same clause rather than
assumed. -/
theorem spineClauseC3_of_multiscale [NeZero d] {m : ℤ} {jn : ℕ}
    {Ccg s s1 s2 p sigmaBarM E1 E2 Dg S Cw EB Kg Kh KhInf : ℝ}
    {Gen : TriadicCube d → ℝ} {Fflux : Vec d → Vec d}
    {u v : H1Function (openCubeSet (originCube d m))}
    {W : Vec d → ℝ} {G : Vec d → Vec d}
    (hp : 0 < p) (hs0 : 0 < s) (hguard : s + (d : ℝ) / p ≤ 1 / 2) (hsig : 0 < sigmaBarM)
    (hCG : CoarseGrainingFinitePMultiscale (originCube d m) jn Ccg s s1 s2 p sigmaBarM
      E1 E2 Dg Gen G Fflux)
    (hS : ∀ N : ℕ,
      coarseGrainingEnergyPartial (originCube d m) p (s - s1) jn N Gen ≤ S)
    (hlevel : coarseGrainingFinitePRHS Ccg s s2 sigmaBarM E1 E2 Dg S
        ((originCube d m).scale - (jn : ℤ)) ≤
      sigmaBarM *
        (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
    (hWval : ∀ x ∈ openCubeSet (originCube d m), W x = u.toFun x - v.toFun x)
    (hWout : ∀ x, x ∉ openCubeSet (originCube d m) → W x = 0)
    (hw : HasWeakGradientOn Set.univ W G) (hwI : Integrable W volume)
    (hwc : HasCompactSupport W) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hGzero : ∀ y, y ∉ cubeSet (originCube d m) → G y = 0) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
        (96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw) * EB *
          dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
  have hgauge : ∀ N : ℕ,
      negBesovLpPartialNorm (originCube d m) s p N G ≤
        sigmaBarM⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigmaBarM E1 E2 Dg S
          ((originCube d m).scale - (jn : ℤ)) :=
    fun N => hCG.gradPartial hS hsig N
  obtain ⟨gc, hgc, hgw⟩ :=
    hasContinuousRepresentative_of_negBesovLp m hp hs0 hguard hw hwI hwc hGI hGzero hgauge
  have hzero : ∀ y ∈ cubeFaceSet (originCube d m), gc y = 0 :=
    faceZero_of_continuousRepresentative hWout hgc hgw
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := div_nonneg (Nat.cast_nonneg d) hp.le
  have hs1 : s + (d : ℝ) / p < 1 := by linarith only [hguard]
  have hlift : (0 : ℝ) ≤ liftGeomFactor (s + (d : ℝ) / p) := liftGeomFactor_nonneg hs1
  have hd2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) := by
    have hsq : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
    linarith only [hsq]
  have hK : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) :=
    mul_nonneg hd2 hlift
  have hres := ae_linfty_of_negBesovLp (d := d) m hp hs0 hguard hw hwI hwc hGI hGzero
    hgauge (g := gc) hgc hgw hzero
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
  have hgwR : W =ᵐ[volume.restrict (openCubeSet (originCube d m))] gc :=
    hgw.filter_mono (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
  have hmem : ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      x ∈ openCubeSet (originCube d m) :=
    MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet _)
  refine ((hres.and hgwR).and hmem).mono fun x hx => ?_
  have hval : u.toFun x - v.toFun x = gc x := by
    rw [← hWval x hx.2]
    exact hx.1.2
  rw [hval]
  exact hx.1.1.trans hfinal

/-! ## 3. THE RE-CUT BUNDLE -/

/-- **THE RE-CUT `hCG'` BUNDLE.**

`HomSpineRepClose.SpineDatumCoarseGrainingGauge` with

* the `hCG'` conjunct carrying its MULTISCALE clause ALONE — the two duality
  clauses are produced by `HomCGCarrierLegs`, from the root's own binders;
* `hC4ex` DELETED — it is produced by
  `HomCGCarrierLegs.exists_comparator_stepFourEnergy_of_dualBounds`;
* in their place the four slot dominations and the arithmetic condition
  `hlevelDual`, at the display pin `s₁′ = s/8`, `s′ = 7s/8`, with
  `Gen:= printedLocalEnergy`.

Every other conjunct is carried verbatim from the bundle, up to two carrier
upgrades that cost nothing: the exponent is a `FiniteLpExponent` (`1 < p` is
FORCED by the bundle's own guard `s + d/p ≤ 1/2` for `d ≥ 1`) and the orders
are `FractionalOrder`s (`0 < s` was already a conjunct, `s < 1` again forced by
the guard).  The Schauder slot is no longer existential: it is the external's
own constant `stepFourSchauderConst d s`. -/
def SpineDatumCoarseGrainingRecut [NeZero d] (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (hs : 0 < homS M)
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
        spineClauseConst d s.1 p.exponent.toReal Cw (stepFourSchauderConst d s.1) ≤ Kabs ∧
        0 ≤ EB ∧
        ENNReal.ofReal EB ≤ ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ∧
        s1'.1 = s.1 / 8 ∧ s'.1 = 7 * s.1 / 8 ∧
        s'.1 < s2.1 ∧ s2.1 < 1 / 2 ∧
        1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1 ∧
        (∀ G : Vec d → Vec d,
          (∀ x ∈ openCubeSet (originCube d m), G x = u.grad x - v.grad x) →
          CoarseGrainingFinitePMultiscale (originCube d m) jn Ccg s.1 (s.1 / 4) s2.1
            p.exponent.toReal sigmaBarM E1 E2 Dg
            (printedLocalEnergy
              (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u) G Fflux) ∧
        0 ≤ S ∧
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal
            (s.1 - s.1 / 4) jn N
            (printedLocalEnergy
              (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u) ≤ S) ∧
        coarseGrainingFinitePRHS Ccg s.1 s2.1 sigmaBarM E1 E2 Dg S
            ((originCube d m).scale - (jn : ℤ)) ≤
          sigmaBarM *
            (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
        0 ≤ Ccg ∧ 0 ≤ E1 ∧ 0 ≤ E2 ∧ 0 ≤ Dg ∧
        cgDualBoundConst d p ≤ ENNReal.ofReal Ccg ∧
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
            (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) sigmaBarM hsig
            s1' ≤ ENNReal.ofReal E1 ∧
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
            (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) sigmaBarM hsig
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

/-! ## 4. The re-cut bundle supplies the clause supplier -/

/-- **THE RE-CUT BUNDLE PRODUCES THE SPINE'S CLAUSE SUPPLIER.**

Clause (C3) comes from the multiscale clause alone (through the produced frame
and the produced continuous representative); clause (C4) from the produced
duality legs and the Schauder external.  No duality clause and no `hC4ex` is
assumed. -/
theorem homSpineClauseSupplier_of_datumRecut [NeZero d] (hd : 2 ≤ d) (M : ABKModel d)
    (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (hs : 0 < homS M)
    {sigmaBarM Kabs : ℝ} (hsig : 0 < sigmaBarM) (omega : Cutoff.CutoffSample d)
    (hcg : SpineDatumCoarseGrainingRecut M Cgap Y m hs sigmaBarM hsig Kabs omega) :
    HomSpineClauseSupplier M Cgap Y m hs sigmaBarM Kabs omega := by
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
  /- the produced frame, and clause (C3) from the multiscale clause alo -/
  obtain ⟨W, G, hWval, hGval, hWout, hw, hwI, hwc, hGI, hGzero⟩ :=
    spineFrame_of_dirichletPair hsol hcomp
  have hC3 := spineClauseC3_of_multiscale hprPos hs0 hguard hsig (hCGm G hGval) hS hlevel
    hWval hWout hw hwI hwc hGI hGzero
  /- the produced duality legs, at the display p -/
  have hp2 : (2 : ℝ≥0∞) ≤ p.exponent := two_le_exponent_of_guard hd1 hs0 hguard
  have hspecC := Classical.choose_spec (exists_weakNegDualBounds_of_cutoffPair d hd p hp2)
  rw [← cgDualBoundConst_eq d hd p hp2] at hspecC
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
              (matVecMul ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField x)
                (u.grad x)) (v'.grad x)) (openCubeSet (originCube d m)) volume ∧
            (WeakNegDualBoundOn (originCube d m) s.1
                (Real.rpow 3 (s.1 * (m : ℝ)) * sigmaBarM *
                  (Cw * EB *
                    dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                (fun x => matVecMul
                  ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField x) (u.grad x) -
                  sigmaBarM • v'.grad x) ∧
              WeakNegDualBoundOn (originCube d m) s.1
                (Real.rpow 3 (s.1 * (m : ℝ)) *
                  (Cw * EB *
                    dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                (fun x => u.grad x - v'.grad x)) := by
    intro v' hcomp'
    refine ⟨integrableOn_comparatorEnergy sigmaBarM v',
      integrableOn_crossEnergy
        (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u v', ?_⟩
    exact hlegs M L omega m ((originCube d m).scale - (jn : ℤ)) hnm jn s1' s' s2 s
      hs1s hs's2 hlo hhi hjn sigmaBarM hsig g u v' h hsol hcomp' Kg hKg0 hs2lt hs2gt hKg
      Ccg E1 E2 Dg S
      (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
      hCcg0 hE10 hE20 hDg0 hS0 hCdom hE1 hE2 hDg (s.1 - s.1 / 4)
      (printedLocalEnergy (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u)
      hwgap
      (printedLocalEnergy_nonneg (Cutoff.coefficientCutoffCoeffOn M L omega
        (originCube d m)) u)
      (fun _ => le_rfl) hS hlevelDual
  /- clause (C4), from the produced legs and the Schauder extern -/
  have hspecS := Classical.choose_spec
    (exists_comparator_stepFourEnergy_of_dualBounds (d := d) hd hs0 hsle)
  rw [← stepFourSchauderConst_eq hd hs0 hsle] at hspecS
  obtain ⟨hCschPos, hC4gen⟩ := hspecS
  obtain ⟨v', hcomp', hC4⟩ := hC4gen M L m omega sigmaBarM Kg Kh KhInf Cw EB u h g hsig
    hCw hEB hbr hKg hKhInf hKh hsol
    (integrableOn_selfEnergy
      (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u) hframe
  /- assemb -/
  refine ⟨EB, hEB, hdom, ?_, ?_⟩
  · refine hC3.mono fun x hx => ?_
    refine hx.trans ?_
    have hlift : (0 : ℝ) ≤ liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) :=
      liftGeomFactor_nonneg (by linarith only [hguard])
    have hfac : 96 * (d : ℝ) ^ (2 : ℕ) *
        liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) * Cw ≤ Kabs := by
      have h1 : (0 : ℝ) ≤ 2 * Cw * stepFourSchauderConst d s.1 :=
        mul_nonneg (by linarith only [hCw]) hCschPos.le
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
    have hfac : 2 * Cw * stepFourSchauderConst d s.1 ≤ Kabs := by
      have hd2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) := by
        have hsq : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
        linarith only [hsq]
      have h2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) *
          liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) * Cw :=
        mul_nonneg (mul_nonneg hd2 hlift) hCw
      rw [spineClauseConst] at hKabsC
      linarith only [h2, hKabsC]
    rw [energyBracket]
    calc 2 * Cw * stepFourSchauderConst d s.1 * EB *
          (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
              Real.sqrt sigmaBarM *
                (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ)
        = (2 * Cw * stepFourSchauderConst d s.1) * (EB *
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

/-! ## 5. THE SUCCESSOR ENDPOINT, at `{htail, the re-cut bundle}` -/

/-- **THE SPINE, at `{htail, the RE-CUT bundle}`.**

`HomSpineRepClose.homogenization_spine_close_of_coarseGrainingGauge` with the
bundle re-cut: the transcribed source hypothesis appears with its MULTISCALE
clause alone, and the Schauder external's Step-4 output is PRODUCED. The
conclusion is byte-identical to the predecessor's; only the second conditional
changes.  The predecessor endpoint stays in place as a regression witness; this
one supersedes it as the consumer-facing surface.

**The final conditional set is exactly two entries:**

1. `htail` — the Theorem-C minimal-scale tail, a declared dependency
   edge (Theorem C), not an internal §4.5 obligation;
2. `hcg` — the per-`ω` bundle `SpineDatumCoarseGrainingRecut`, whose items are
   the MULTISCALE clause of `hCG'` (a declared source hypothesis), the
   energy slot `hS`, the two level conditions `hlevel` and `hlevelDual`, the
   four slot dominations (all PINNABLE — see `HomSpineRecutSupport`), `hEB`
   and `hdom`, and the numerical frame.  No duality clause, no `hC4ex`, and no
   frame item. -/
theorem homogenization_spine_close_of_coarseGrainingRecut (d : ℕ) [NeZero d]
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
              SpineDatumCoarseGrainingRecut M Cgap
                (homMinimalScaleFactor (1 - homAlpha M) X) m hs
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
    homSpineClauseSupplier_of_datumRecut hd M Cgap
      (homMinimalScaleFactor (1 - homAlpha M) X) m hs (Annealed.sigmaBar M m).2 omega hb

end

end Algsuperdiff.Section4.Provider.Homogenization
