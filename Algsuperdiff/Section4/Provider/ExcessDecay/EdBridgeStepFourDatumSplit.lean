/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeStepFourGeneral
import Algsuperdiff.Section4.Provider.ExcessDecay.EdAssemblyJoinDatumSplit

/-!
# The Step-4 bridge with the printed datum leg threaded through

`EdBridgeStepFourGeneral.excessDecay_stepFour_slot_general` runs the residue
chain against the join and delivers the Step-4 slot at every centre.  Its join
input is the two-leg one-step; this module runs the same chain against
`EdAssemblyJoinDatumSplit.excessDecay_oneStep_anchored_datumSplit`, whose
boundary disjunct carries its binders honestly and whose conclusion carries the
printed third leg

```text
   C_t(d) · (3^{n-k})^{1/2} · (boundaryDatumLegConst d C k · K_h) .
```

## The additive ride

One risk has to be excluded: the datum leg's fixed-`k` factor `3^{3k/2}` would
be fatal if the leg ever entered the bridge's **absorption inequality** — the `k₀`
selection of `exists_edBridgeStepGen`, which is what forces `k` large enough
that the contraction is `≤ ½·3^{-(k+1)/4}`.  It does not.  The machine witness
is the shape of the generalized recombination `edBridge_recombine_datum`: the
leg appears as a *single free real* `Leg` which

* occurs in exactly two places — the hypothesis `hmain` and the conclusion — both additively;
* occurs in **no** other hypothesis: not in `hgate` (the `δ`-absorption
  `Crem·(P·(Sq·B₁)) ≤ th₂`), not in `hcon` (the contraction absorption
  `Acon·Ejm1 ≤ th₁·Ej`), not in `hth` (`th₁ + th₂ ≤ th`), and not in `hBig`;
* is multiplied by nothing and compared with nothing.

Since `k₀` is chosen by `exists_edBridgeStepGen` from `Cs` alone — a statement this module does
not touch and whose proof mentions no datum object — the `3^{3k/2}` cannot interact with the
selection.  Concretely: `k₀` is fixed first, `k ≥ k₀` is arbitrary, and the leg's constant is
then evaluated at that `k`.  The leg is a `δ`-side summand, not an `E`-side coefficient.

## The consumption shape

`edBridgeDatumLeg_eq` rewrites the leg into's `A^h` shape exactly: at the
slot's own index `j = n+1`,

```text
   C_t(d)·(3^{n-k})^{1/2}·(C_bd(d,C,k)·K_h)  =  edBridgeDatumLegConst d C k · (3^{j/2} · K_h) ,
```

a constant times `3^{j/2}` times the same datum `K_h` the budget's `A^h_j` leg
carries.  So the leg is absorbed by **widening `A^h`'s constant**, not by
touching the `ε`-free flat slot `F` (which is the anchor's `K_hinf` leg).
measured this; the identity proves it.

## References

* ABK26, `l.excess.decay.good.scales`; `t.regularity` Step 4.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The four-leg recombination: the datum leg rides additively -/

/-- **`EdBridgeStepFour.edBridge_recombine` with a fourth, purely additive leg.**

`Leg` occurs only in `hmain` and in the conclusion, in both cases as a bare
additive summand.  It touches neither the `δ`-gate `hgate` nor the contraction
absorption `hcon` nor the step budget `hth` — this is the machine form's "the
datum leg rides additively through the `k₀` selection". -/
theorem edBridge_recombine_datum
    {Elhs Acon Ejm1 Ej pj Big Rhat P Crem Sq B₁ B₂ th₁ th₂ th eps Wd Leg : ℝ}
    (hCrem : 0 ≤ Crem) (hSq : 0 ≤ Sq) (hP : 0 ≤ P) (hEj : 0 ≤ Ej)
    (hmain : Elhs ≤ Acon * Ejm1 + Crem * (P * (Sq * Big)) + Leg)
    (hBig : Big ≤ B₁ * Ej + B₂ * pj + Rhat)
    (hcon : Acon * Ejm1 ≤ th₁ * Ej)
    (hgate : Crem * (P * (Sq * B₁)) ≤ th₂)
    (heps : Crem * (P * (Sq * B₂)) = eps)
    (hWd : Crem * (P * (Sq * Rhat)) = Wd)
    (hth : th₁ + th₂ ≤ th) :
    Elhs ≤ th * Ej + eps * pj + (Wd + Leg) := by
  have hstep : Crem * (P * (Sq * Big)) ≤ Crem * (P * (Sq * (B₁ * Ej + B₂ * pj + Rhat))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBig hSq) hP) hCrem
  have hexp : Crem * (P * (Sq * (B₁ * Ej + B₂ * pj + Rhat)))
      = Crem * (P * (Sq * B₁)) * Ej + Crem * (P * (Sq * B₂)) * pj
        + Crem * (P * (Sq * Rhat)) := by ring
  rw [heps, hWd] at hexp
  have hgm : Crem * (P * (Sq * B₁)) * Ej ≤ th₂ * Ej := mul_le_mul_of_nonneg_right hgate hEj
  have hthm : (th₁ + th₂) * Ej ≤ th * Ej := mul_le_mul_of_nonneg_right hth hEj
  have hdis : (th₁ + th₂) * Ej = th₁ * Ej + th₂ * Ej := by ring
  linarith only [hmain, hstep, hexp, hcon, hgm, hthm, hdis]

/-! ## 2. The datum leg and its `A^h` shape -/

/-- The datum leg the bridge's slot carries, at the one-step's own scale `n`:
`C_t(d) · (3^{n-k})^{1/2} · (C_bd(d,Cs,k) · K_h)`. -/
def edBridgeDatumLeg (d : ℕ) (Cs : ℝ) (k : ℕ) (n : ℤ) (Kh : ℝ) : ℝ :=
  taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
    * (boundaryDatumLegConst d Cs k * Kh)

/-- The datum leg's constant once the slot's own `3^{j/2}` is factored out
(`j = n+1`): `C_t(d) · (3^{-(k+1)})^{1/2} · C_bd(d,Cs,k)`. -/
def edBridgeDatumLegConst (d : ℕ) (Cs : ℝ) (k : ℕ) : ℝ :=
  taylorContractionConst d * ((3 : ℝ) ^ (-((k : ℤ) + 1))) ^ (1 / 2 : ℝ)
    * boundaryDatumLegConst d Cs k

theorem edBridgeDatumLegConst_nonneg (d : ℕ) {Cs : ℝ} (hCs : 0 ≤ Cs) (k : ℕ) :
    0 ≤ edBridgeDatumLegConst d Cs k :=
  mul_nonneg (mul_nonneg (taylorContractionConst_nonneg d)
    (Real.rpow_nonneg (zpow_pos (by norm_num) _).le _))
    (boundaryDatumLegConst_nonneg d hCs k)

/-- `(3^m)^{1/2} = 3^{m/2}` for an integer power. -/
theorem zpow_rpow_half_eq_rpow_div_two (m : ℤ) :
    ((3 : ℝ) ^ m) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ ((m : ℝ) / 2) := by
  rw [← Real.rpow_intCast (3 : ℝ) m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- **The datum leg is exactly's `A^h_j` shape at `j = n+1`.**

`edBridgeDatumLeg d Cs k n K_h = edBridgeDatumLegConst d Cs k · (3^{j/2} · K_h)` — a constant
times `3^{j/2}` times the same datum `K_h` the budget's `A^h` leg carries.  So the new leg is
absorbed by widening `A^h`'s constant, not by touching the `ε`-free flat slot. -/
theorem edBridgeDatumLeg_eq (d : ℕ) (Cs : ℝ) (k : ℕ) (n : ℤ) (Kh : ℝ) :
    edBridgeDatumLeg d Cs k n Kh
      = edBridgeDatumLegConst d Cs k * ((3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) / 2) * Kh) := by
  have hsplit : ((3 : ℝ) ^ (-((k : ℤ) + 1))) ^ (1 / 2 : ℝ)
        * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) / 2)
      = ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) := by
    rw [zpow_rpow_half_eq_rpow_div_two, zpow_rpow_half_eq_rpow_div_two,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [edBridgeDatumLeg, edBridgeDatumLegConst, ← hsplit]
  ring

/-! ## 3. The Step-4 slot with the datum leg -/

/-- ** unit 2: the Step-4 decay slot at every centre, with the printed datum leg.**

`EdBridgeStepFourGeneral.excessDecay_stepFour_slot_general` run against the
datum-split join.  The window hypothesis is the join's own disjunction's honest
binders; the conclusion is the interior slot's, with the `δ` leg gaining the
additive summand `edBridgeDatumLeg d (max (schauderWindowConst d) C_b) k n
K_h`. -/
theorem excessDecay_stepFour_slot_general_datumSplit (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Ccap Cb : ℝ, 0 < C ∧ 0 < Ccap ∧ 0 ≤ Cb ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
          M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          ∀ hs : 0 < s,
          ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) 1 →
            delta ≤ 64 * (C ^ (2 : ℕ))⁻¹ * s ^ (6 : ℕ) →
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                  (s / 8 * Real.sqrt delta) →
            edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k * Ccap *
                  Real.rpow s (-(3 : ℝ)) * Real.sqrt delta ≤
                (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) →
            ∀ L m : ℤ, m ≤ L →
              ∀ z : Vec d, z ∈ openCubeSet (originCube d m) →
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  ∀ n : ℤ, n + 1 ≤ m →
                    omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                        (cgEllipLowerConstant d) (n + 1) z ⟨s / 8, by linarith only [hs]⟩
                        (s / 8 * Real.sqrt delta) →
                    ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                      (gflux : Vec d → Vec d),
                      IsDirichletSolutionOn
                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                          (originCube d m) u hdat gflux →
                      MemLp gflux 2
                          (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel s 2 gflux) 2
                          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                      ∀ (v : H1Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                              openCubeSet (originCube d (n - 2))))
                        (w : H10Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                              openCubeSet (originCube d (n - 2)))),
                        IsWeaklyHarmonicOn ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                          openCubeSet (originCube d (n - 2))) v →
                        (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                        (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                        ∀ Kh : ℝ, 0 ≤ Kh →
                        ((fun y => z + y) '' openCubeSet (originCube d (n - 2)) ⊆
                            openCubeSet (originCube d m) ∨
                          (∃ (i : Fin d) (V v₁ : Vec d → ℝ) (cl : ℝ) (Al : Vec d),
                            (MeetsUpperFace z m (n - 2) i ∨
                              MeetsLowerFace z m (n - 2) i) ∧
                            MemLp v.toFun 2 (volume.restrict (truncatedWindow z m n)) ∧
                            MemLp V 2
                              (volume.restrict (reflectedWindow z m (n - 2))) ∧
                            V =ᵐ[volume.restrict (truncatedWindow z m (n - 2))]
                              (fun y => v.toFun y - affineLift z cl Al y - v₁ y) ∧
                            (∀ᵐ y ∂(volume.restrict (truncatedWindow z m (n - 2))),
                              |v₁ y| ≤ datumResidualBound d n Kh) ∧
                            (∀ l : Fin d, MeetsUpperFace z m (n - 2) l →
                              ∀ y ∈ reflectedWindow z m (n - 2),
                                V (coordFaceReflection
                                  ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
                            (∀ l : Fin d, MeetsLowerFace z m (n - 2) l →
                              ∀ y ∈ reflectedWindow z m (n - 2),
                                V (coordFaceReflection
                                  (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
                            HarmonicOnNhd
                              (V ∘
                                (Schauder.toEuc.symm :
                                  EuclideanSpace ℝ (Fin d) → Vec d))
                              ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
                                reflectedWindow z m (n - 2)))) →
                        ∀ (c : ℝ) (gmin : Vec d),
                          IsAffineMinimizer (truncatedWindow z m (n + 1)) u.toFun c gmin →
                          affineExcess (truncatedWindow z m (n + 1 - ((k + 1 : ℕ) : ℤ)))
                              u.toFun ≤
                            (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) *
                                affineExcess (truncatedWindow z m (n + 1)) u.toFun +
                              edBridgeEps M
                                    (edBridgeEpsConstGen d
                                      (max (schauderWindowConst d) Cb) C k) L s
                                    ⟨s / 8, by linarith only [hs]⟩ z omega n *
                                  slopeMagnitude gmin +
                              (edBridgeDelta M C
                                  (edBridgeRemWeightGen d
                                    (max (schauderWindowConst d) Cb) k) L m s
                                  ⟨s / 8, by linarith only [hs]⟩ z gflux hdat.grad omega n
                                + edBridgeDatumLeg d
                                    (max (schauderWindowConst d) Cb) k n Kh) := by
  classical
  obtain ⟨C, Cb, hC, hCb, hjoin⟩ := excessDecay_oneStep_anchored_datumSplit d hd
  obtain ⟨Ccap, hCcap, hcapAe⟩ := ae_errorRepresentative_le_goodEventDeltaSlot d
  obtain ⟨k₀, hk₀, habsorb⟩ := exists_edBridgeStepGen d (max (schauderWindowConst d) Cb)
  refine ⟨C, Ccap, Cb, hC, hCcap, hCb, k₀, hk₀, ?_⟩
  intro k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap hgate L m hmL z hz
  set Cs : ℝ := max (schauderWindowConst d) Cb with hCsdef
  have hCsnn : (0 : ℝ) ≤ Cs :=
    le_trans (schauderWindowConst_nonneg d) (le_max_left _ _)
  have hk3 : 3 ≤ k := le_trans hk₀ hk
  have hrep : s / 8 * Real.sqrt delta ≤ C⁻¹ * s ^ (4 : ℕ) :=
    excessDecayDelta_repriced hC hs.le hprice
  have hpre : (0 : ℝ) ≤ Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) :=
    mul_nonneg (Real.rpow_nonneg (by linarith only [hs]) _) (sq_nonneg _)
  have hfund : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (C⁻¹ * s ^ (4 : ℕ)) :=
    le_trans hfundcap (mul_le_mul_of_nonneg_left hrep hpre)
  rw [ae_all_iff]
  intro n
  by_cases hnm : n + 1 ≤ m
  · have hnm3 : n - 2 + 3 ≤ m := by omega
    have hzmem : z ∈ truncatedWindow z m (n - 3) := mem_truncatedWindow_self (n - 3) hz
    filter_upwards [hjoin M s hsrange hregime hfund hs delta hdelta.2 hprice L m n hmL hnm3
      z z hzmem hz,
      hcapAe M hregimecap s hsrange hs delta hdelta hfundcap (n + 1) z] with omega hom hcapOm
    intro _hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv Kh hKh hwin c gmin hmin
    -- the good-event cap at the supply index, and the join at `x := z`
    have hEcap := hcapOm hmem L (by omega)
    have hmem' : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
        (cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
        (s / 8 * Real.sqrt delta) := by
      rw [show n - 2 + 3 = n + 1 from by ring]
      exact hmem
    have hmain := hom hmem' u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv Kh hKh
      hwin k hk3
    simp only [show n - 2 + 3 = n + 1 from by ring, show n - 2 + 2 = n from by ring,
      show (((fun y' : Vec d => z + y') '' openCubeSet (originCube d (n + 1))) ∩
          openCubeSet (originCube d m)) = truncatedWindow z m (n + 1) from rfl,
      show (((fun y' : Vec d => z + y') '' openCubeSet (originCube d n)) ∩
          openCubeSet (originCube d m)) = truncatedWindow z m n from rfl] at hmain
    -- the data of the two windows
    have hu1 : MemLp u.toFun 2 (volume.restrict (truncatedWindow z m (n + 1))) :=
      u.memL2.mono_measure
        (Measure.restrict_mono (truncatedWindow_subset_domain z m (n + 1)) le_rfl)
    have hEj : (0 : ℝ) ≤ affineExcess (truncatedWindow z m (n + 1)) u.toFun :=
      affineExcess_nonneg _ _
    have hCi : (1 : ℝ) ≤ endpointConst d (1 / 9 : ℝ) := one_le_endpointConst (by norm_num)
    have hEcalnn : (0 : ℝ) ≤ fluxCorrectedErrorRepresentative M L (n + 1)
        ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
      fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
    have hCEnn : (0 : ℝ) ≤ C * Real.rpow s (-(4 : ℝ)) *
        fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
          (Cutoff.translateCutoffSample z omega) :=
      mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hs.le _)) hEcalnn
    -- residue 2: the oscillation-to-excess fold on `U_{n+1}`
    have hOSC := eLpNorm_sub_average_truncatedWindow_le hd hz (by omega : n + 1 - 1 ≤ m)
      hu1 hmin
    -- residue 3: the one-scale window move
    have hqm := affineExcess_reindex_le z hz (by omega : n + 1 - 1 ≤ m) hu1
    -- residue 4: the contraction absorption at the join's constant
    have hrate : (0 : ℝ) ≤ ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (zpow_pos (by norm_num) _).le _
    have hAcon : taylorContractionConst d * Cs * windowRatioConst d 2 *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * affineExcess (truncatedWindow z m n) u.toFun
        ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) *
            affineExcess (truncatedWindow z m (n + 1)) u.toFun := by
      have hpos : (0 : ℝ) ≤ taylorContractionConst d * Cs *
          windowRatioConst d 2 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) :=
        mul_nonneg (mul_nonneg (mul_nonneg (taylorContractionConst_nonneg d)
          hCsnn) (windowRatioConst_nonneg d 2)) hrate
      have h1 := mul_le_mul_of_nonneg_left hqm hpos
      have h2 := mul_le_mul_of_nonneg_right (habsorb k hk) hEj
      have hid : taylorContractionConst d * Cs * windowRatioConst d 2 *
            ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
            (windowRatioConst d 1 * affineExcess (truncatedWindow z m (n + 1)) u.toFun)
          = taylorContractionConst d * Cs * windowRatioConst d 2 *
            windowRatioConst d 1 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
            affineExcess (truncatedWindow z m (n + 1)) u.toFun := by ring
      linarith only [h1, h2, hid]
    -- the two bookkeeping identities and the gate, all through `3^{-n}·3^{n+1}=3`
    have hz3 := zpow_reindex n
    rw [show n + 1 - ((k + 1 : ℕ) : ℤ) = n - (k : ℤ) from by push_cast; ring,
      edBridgeEps, edBridgeEpsConstGen, edBridgeDelta, edBridgeRemWeightGen, edBridgeDatumLeg]
    refine edBridge_recombine_datum
      (B₁ := C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
        ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))
      (B₂ := C * Real.rpow s (-(4 : ℝ)) *
        fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
          (Cutoff.translateCutoffSample z omega) *
        ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))
      (Rhat := edBridgeDeltaBracket M C L m s ⟨s / 8, by linarith only [hs]⟩ z gflux
        hdat.grad omega n)
      (th₂ := (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)))
      (triangleRemainderConst_nonneg d hCsnn k)
      (Real.sqrt_nonneg _) (zpow_nonneg (by norm_num) (-n)) hEj hmain ?_ hAcon ?_ ?_ ?_ ?_
    · -- residues 1 and 2 folded into the four-leg bracket
      rw [edBridgeDeltaBracket]
      have hXnn : (0 : ℝ) ≤ (3 : ℝ) ^ (n + 1) *
          (endpointConst d (1 / 9 : ℝ) * affineExcess (truncatedWindow z m (n + 1)) u.toFun) :=
        mul_nonneg (zpow_nonneg (by norm_num) _)
          (mul_nonneg (by linarith only [hCi]) hEj)
      have hcapmul := rpow_neg_four_mul_le_of_cap (Cc := C) hs hEcap hXnn hC.le
      have hA0 : C * Real.rpow s (-(4 : ℝ)) *
            fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
              (Cutoff.translateCutoffSample z omega) *
            ((eLpNorm (fun y => u.toFun y -
                  volumeAverage (truncatedWindow z m (n + 1)) u.toFun) 2
                (normalizedVolumeMeasureOn (truncatedWindow z m (n + 1)))).toReal +
              Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖)
          ≤ C * Real.rpow s (-(4 : ℝ)) *
            fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
              (Cutoff.translateCutoffSample z omega) *
            ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
                (affineExcess (truncatedWindow z m (n + 1)) u.toFun + slopeMagnitude gmin)) +
              Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖) :=
        mul_le_mul_of_nonneg_left (by linarith only [hOSC]) hCEnn
      have hid1 : C * Real.rpow s (-(4 : ℝ)) *
            fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
              (Cutoff.translateCutoffSample z omega) *
            ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
                (affineExcess (truncatedWindow z m (n + 1)) u.toFun + slopeMagnitude gmin)) +
              Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖)
          = C * Real.rpow s (-(4 : ℝ)) *
              fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega) *
              ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
                affineExcess (truncatedWindow z m (n + 1)) u.toFun))
            + (C * Real.rpow s (-(4 : ℝ)) *
                fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                  (Cutoff.translateCutoffSample z omega) *
                ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ))) * slopeMagnitude gmin
            + C * Real.rpow s (-(4 : ℝ)) *
                fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                  (Cutoff.translateCutoffSample z omega) *
                (Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                  ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖) := by ring
      have hid2 : C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
            ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
              affineExcess (truncatedWindow z m (n + 1)) u.toFun))
          = (C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
              ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ))) *
            affineExcess (truncatedWindow z m (n + 1)) u.toFun := by ring
      linarith only [hA0, hcapmul, hid1, hid2]
    · -- the `δ`-gate: the datum leg does NOT appear here
      have hlin : triangleRemainderConst d Cs k *
            ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
              (C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
                ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))))
          = ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n + 1)) *
            (triangleRemainderConst d Cs k *
              Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * C * endpointConst d (1 / 9 : ℝ) * Ccap *
              Real.rpow s (-(3 : ℝ)) * Real.sqrt delta) := by ring
      rw [hlin, hz3]
      rw [edBridgeEpsConstGen, edBridgeRemWeightGen] at hgate
      linarith only [hgate]
    · -- the `ε` identity
      have hlin : triangleRemainderConst d Cs k *
            ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
              (C * Real.rpow s (-(4 : ℝ)) *
                fluxCorrectedErrorRepresentative M L (n + 1)
                  ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
                ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))))
          = ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n + 1)) *
            (triangleRemainderConst d Cs k *
              Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * C * endpointConst d (1 / 9 : ℝ) *
              Real.rpow s (-(4 : ℝ)) *
              fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by ring
      rw [hlin, hz3]
      ring
    · -- the `δ` identity
      ring
    · -- the two halves of `θ^{k+1}`
      exact le_of_eq (by ring)
  · exact Filter.Eventually.of_forall fun _ hc => absurd hc hnm

end

end Algsuperdiff.Section4.Provider.ExcessDecay
