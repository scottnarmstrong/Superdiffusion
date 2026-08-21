/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineRecutSupport
import Homogenization.Book.Ch03.ABK26.LocalCoarseGraining

/-!
# The multiscale clause: reduced to the Calderón--Zygmund flux comparison lemma at the multiscale reading

## What this file does to `RecutCoreSupply`'s multiscale clause

`HomSpineRecutSupport.CoarseGrainingFinitePMultiscale` is clause 1 of the
transcribed source hypothesis `HomFinitePSource.GeneralCoarseGrainingFiniteP`,
i.e. the general coarse-graining proposition at finite `p` read at the
MULTISCALE reading of its undefined negative-norm symbol.  Until now it was
carried as an undischarged hypothesis of `RecutCoreSupply`.

The print proves the Proposition from exactly TWO lemmas:

```text
  l.gen.coarse.grain     -- the flux defect against the coarse-grained RHS
  l.cz.flux.estimates    -- the duality/CZ step: the two printed legs against
                            the flux defect, at C·3^{s(m-n)}
```

`exists_localCoarseGrainingLp` (`CoarseGraining`,
`Book.Ch03.ABK26.LocalCoarseGraining`) IS the first one at finite `p`: for
every `FiniteLpExponent p` with `2 ≤ p`, every `n < m`, every `s₁ < s < s₂`,
every uniformly elliptic `𝐚`, every `σ₀ > 0` and every `𝐠 ∈ W^{s₂,p}(□_m)`,

```text
  localFluxDefectNegativeBesovLpAverage □_m n 𝐚 σ₀ u s p
      ≤ localCoarseGrainingLpRHS C □_m n 𝐚 σ₀ 𝐠 u s₁ s s₂ p,
```

with `C(p,d) < ∞` fixed before everything.  It is UNCONDITIONAL.  So the only
missing half is the CZ step, and this file makes that exact:

`coarseGrainingFinitePMultiscale_of_cz` produces the clause from
`CzFluxMultiscale` — the Calderón--Zygmund flux comparison lemma with its
undefined left-hand symbol read as `HomFinitePGauge.negBesovLpPartialNorm`, at
the printed constant.  Both the `3^{-ms}` of the printed left-hand side and the
`3^{-sn}` `CoarseGraining` carries in front of the descendant average are
already in the two carriers, so the printed `3^{s(m-n)}` is absorbed exactly
and `C_cz` is a genuine `C(p,d)`.

## Status of the two halves

* the coarse-graining half: PROVED (`CoarseGraining`, unconditional);
* the CZ half at the multiscale reading: the ONE named input.  It is NOT
  implied by the smooth-dual CZ step `CoarseGraining` proves
  (`exists_centeredCubeFluxComparison_cz`, which is what
  `HomCGDischargeAssembly.exists_printedCoarseGrainingFiniteP_smoothDual`
  consumes): the two readings of `‖·‖_{Ŵ̲^{-s,p}}` are inequivalent, which is
  the content of the two-readings correction.
-/

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The named input -/

/-- **the Calderón--Zygmund flux comparison lemma at the MULTISCALE reading**.

The printed duality step

```text
  σ₀‖∇u - ∇v‖_{Ŵ̲^{-s,p}(□_m)} + ‖𝐚∇u - σ₀∇v‖_{Ŵ̲^{-s,p}(□_m)}
      ≤ C 3^{s(m-n)} ( avsum_{z ∈ 3ⁿℤᵈ ∩ □_m} ‖(𝐚-σ₀)∇u‖^p_{Ŵ̲^{-s,p}(z+□_n)} )^{1/p}
```

with the undefined symbol read as the finite-`p` grid gauge
`negBesovLpPartialNorm` on the left and `CoarseGraining`'s
`localFluxDefectNegativeBesovLpAverage` on the right.  Both carriers already
carry their scale normalizations (`3^{-ms}` and `3^{-sn}` respectively), so the
printed `3^{s(m-n)}` is absorbed and `Ccz` is the printed `C(p,d)`.

THIS IS A HYPOTHESIS.  It is never proved in this repository. -/
def CzFluxMultiscale [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (sigma0 : ℝ)
    (u : H1Function (openCubeSet Q)) (s : FractionalOrder) (p : FiniteLpExponent)
    (Ccz : ℝ) (Fgrad Fflux : Vec d → Vec d) : Prop :=
  ∀ N : ℕ,
    sigma0 * negBesovLpPartialNorm Q s.1 p.exponent.toReal N Fgrad +
        negBesovLpPartialNorm Q s.1 p.exponent.toReal N Fflux ≤
      Ccz * (localFluxDefectNegativeBesovLpAverage Q n hn a sigma0 u s p).toReal

/-! ## 2. The printed right-hand side is linear in its constant -/

/-- Scaling the printed constant scales the printed right-hand side. -/
theorem coarseGrainingFinitePRHS_const_mul (c Ccg s s2 sigma E1 E2 Dg S : ℝ) (n : ℤ) :
    coarseGrainingFinitePRHS (c * Ccg) s s2 sigma E1 E2 Dg S n =
      c * coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S n := by
  rw [coarseGrainingFinitePRHS_def, coarseGrainingFinitePRHS_def]; ring

/-! ## 3. The clause, produced from the CZ step alone -/

/-- **THE MULTISCALE CLAUSE, PRODUCED** from the Calderón--Zygmund flux comparison lemma at the
multiscale reading.

Everything else is discharged: the coarse-graining half is `CoarseGraining`'s
unconditional `exists_localCoarseGrainingLp`, the right-hand-side transfer is
`HomCGCarrierRHS.localCoarseGrainingLpRHS_toReal_le`, and the energy slot is
`HomCGCarrierEnergy.weightedLocalSymmetricEnergyLp_le_ofReal` fed by the
clause's OWN `S`-hypothesis.  The `n`-slot is the clause's own `Q.scale - jn`. -/
theorem exists_coarseGrainingFinitePMultiscale_of_cz (d : ℕ) (hd : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Ccg0 : ℝ, 0 ≤ Ccg0 ∧
      ∀ (m : ℤ) (jn : ℕ), 0 < jn →
      ∀ (p : FiniteLpExponent), (2 : ℝ≥0∞) ≤ p.exponent →
      ∀ (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
      ∀ (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ) (hsigma0 : 0 < sigma0) (g : Vec d → Vec d)
        (u : H1Function (openCubeSet (originCube d m))),
        MemCubeEuclideanFullWsp (originCube d m) s2 p g →
        IsForcedEquation (originCube d m) a u g →
      ∀ (Ccz E1 E2 Dg : ℝ) (Gen : TriadicCube d → ℝ) (Fgrad Fflux : Vec d → Vec d),
        0 ≤ Ccz → 0 ≤ E1 → 0 ≤ E2 → 0 ≤ Dg →
        (∀ R, 0 ≤ Gen R) →
        (∀ R, printedLocalEnergy a u R ≤ Gen R) →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (by omega) a sigma0 hsigma0 s1 ≤
          ENNReal.ofReal E1 →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (by omega) a sigma0 hsigma0
            (fractionalOrderHalf s1) ≤ ENNReal.ofReal E2 →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g ≤
          ENNReal.ofReal Dg →
        CzFluxMultiscale (originCube d m) ((originCube d m).scale - (jn : ℤ)) (by omega)
          a sigma0 u s p Ccz Fgrad Fflux →
          CoarseGrainingFinitePMultiscale (originCube d m) jn (Ccz * Ccg0) s.1 s1.1 s2.1
            p.exponent.toReal sigma0 E1 E2 Dg Gen Fgrad Fflux := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCtop, hlcg⟩ := exists_localCoarseGrainingLp d hd
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro m jn hjn p hp s1 s s2 hs1s hss2 a sigma0 hsigma0 g u hg hu Ccz E1 E2 Dg Gen
    Fgrad Fflux hCcz hE10 hE20 hDg0 hGen0 hGen hE1 hE2 hDg hcz S hS N
  have hCeq : C ≤ ENNReal.ofReal C.toReal :=
    le_of_eq (ENNReal.ofReal_toReal hCtop.ne).symm
  have hscale : (originCube d m).scale = m := rfl
  have hnm : (originCube d m).scale - (jn : ℤ) < m := by rw [hscale]; omega
  have hn : (originCube d m).scale - (jn : ℤ) ≤ (originCube d m).scale := by omega
  /- the energy slot, from the clause's own hypothes -/
  have hS0 : (0 : ℝ) ≤ S := by
    have hge := hS 0
    have h0 : (0 : ℝ) ≤ coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal
        (s.1 - s1.1) jn 0 Gen := by
      rw [coarseGrainingEnergyPartial_def]
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
        mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (descendantsAverage_nonneg _ _ _ fun R _ => Real.rpow_nonneg (hGen0 R) _)) _
    linarith only [hge, h0]
  have hSlot : weightedLocalSymmetricEnergyLp (originCube d m)
      ((originCube d m).scale - (jn : ℤ)) hn a u s1 s p ≤ ENNReal.ofReal S :=
    weightedLocalSymmetricEnergyLp_le_ofReal hn a u s1 s p (wgap := s.1 - s1.1) le_rfl
      (by omega) hGen0 hGen hS0 hS
  /- `CoarseGraining`'s unconditional coarse-graining ha -/
  have hlcgm := hlcg p hp m ((originCube d m).scale - (jn : ℤ)) hnm s1 s s2 hs1s hss2 a
    sigma0 hsigma0 g hg u hu
  have hrhsne : localCoarseGrainingLpRHS C (originCube d m)
      ((originCube d m).scale - (jn : ℤ)) hn a sigma0 hsigma0 g u s1 s s2 p ≠ ⊤ :=
    localCoarseGrainingLpRHS_ne_top hn a hsigma0 g u s1 s s2 p hss2
      ENNReal.toReal_nonneg hE10 hE20 hDg0 hS0 hCeq hE1 hE2 hDg hSlot
  have hreal : (localFluxDefectNegativeBesovLpAverage (originCube d m)
        ((originCube d m).scale - (jn : ℤ)) hn a sigma0 u s p).toReal ≤
      coarseGrainingFinitePRHS C.toReal s.1 s2.1 sigma0 E1 E2 Dg S
        ((originCube d m).scale - (jn : ℤ)) := by
    refine le_trans (ENNReal.toReal_mono hrhsne hlcgm) ?_
    exact localCoarseGrainingLpRHS_toReal_le hn a hsigma0 g u s1 s s2 p hss2
      ENNReal.toReal_nonneg hE10 hE20 hDg0 hS0 hCeq hE1 hE2 hDg hSlot
  /- the CZ step, and the consta -/
  have hfinal := hcz N
  rw [coarseGrainingFinitePRHS_const_mul]
  exact hfinal.trans (mul_le_mul_of_nonneg_left hreal hCcz)

end

end Algsuperdiff.Section4.Provider.Homogenization
