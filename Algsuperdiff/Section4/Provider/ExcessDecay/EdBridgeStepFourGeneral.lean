/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeStepFour
import Algsuperdiff.Section4.Provider.ExcessDecay.EdAssemblyJoin

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The bridge's constants at a general Schauder constant -/

/-- The one-step remainder's weight at a general Schauder constant `Cs`:
`C_r(d, Cs, k) · √((3²)^d)`.  At `Cs = schauderWindowConst d` this is `edBridgeRemWeight`. -/
def edBridgeRemWeightGen (d : ℕ) [NeZero d] (Cs : ℝ) (k : ℕ) : ℝ :=
  triangleRemainderConst d Cs k * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d)

theorem edBridgeRemWeight_eq_gen (d : ℕ) [NeZero d] (k : ℕ) :
    edBridgeRemWeight d k = edBridgeRemWeightGen d (schauderWindowConst d) k := rfl

theorem edBridgeRemWeightGen_nonneg (d : ℕ) [NeZero d] {Cs : ℝ} (hCs : 0 ≤ Cs) (k : ℕ) :
    0 ≤ edBridgeRemWeightGen d Cs k :=
  mul_nonneg (triangleRemainderConst_nonneg d hCs k) (Real.sqrt_nonneg _)

/-- The `ε` constant of the bridge at a general Schauder constant `Cs`. -/
def edBridgeEpsConstGen (d : ℕ) [NeZero d] (Cs C : ℝ) (k : ℕ) : ℝ :=
  3 * edBridgeRemWeightGen d Cs k * C * endpointConst d (1 / 9 : ℝ)

theorem edBridgeEpsConst_eq_gen (d : ℕ) [NeZero d] (C : ℝ) (k : ℕ) :
    edBridgeEpsConst d C k = edBridgeEpsConstGen d (schauderWindowConst d) C k := rfl

/-- ** residue 4 at a general Schauder constant.**

`EdBridgeFolds.exists_edBridgeStep` with `schauderWindowConst d` replaced by an arbitrary `Cs`:
the step size `k₀` depends on `Cs`, nothing else in the argument does.  The join runs at
`Cs = max (schauderWindowConst d) C_bdry`. -/
theorem exists_edBridgeStepGen (d : ℕ) [NeZero d] (Cs : ℝ) :
    ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      taylorContractionConst d * Cs * windowRatioConst d 2
            * windowRatioConst d 1 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
        ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) := by
  classical
  obtain ⟨hq0, hq1⟩ := rpow_quarter_mem
  set q : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ)) with hqdef
  set A : ℝ := max (taylorContractionConst d * Cs * windowRatioConst d 2
    * windowRatioConst d 1) 1 with hAdef
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hAle : taylorContractionConst d * Cs * windowRatioConst d 2
      * windowRatioConst d 1 ≤ A := le_max_left _ _
  obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one (x := 1 / 2 * q / A) (y := q)
    (div_pos (by linarith only [hq0] : (0 : ℝ) < 1 / 2 * q) hApos) hq1
  refine ⟨max k₁ 3, le_max_right _ _, ?_⟩
  intro k hk
  have hk1 : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hqk : q ^ k ≤ q ^ k₁ := pow_le_pow_of_le_one hq0.le hq1.le hk1
  have hqklt : q ^ k < 1 / 2 * q / A := lt_of_le_of_lt hqk hk₁
  have hqkpos : (0 : ℝ) < q ^ k := pow_pos hq0 k
  have hkey : A * q ^ k ≤ 1 / 2 * q := by
    have h := (le_div_iff₀ hApos).1 (le_of_lt hqklt)
    linarith only [h]
  have hmul : A * q ^ k * q ^ k ≤ 1 / 2 * q * q ^ k :=
    mul_le_mul_of_nonneg_right hkey hqkpos.le
  have hL : ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = q ^ k * q ^ k := by
    rw [zpow_neg_rpow_half_eq k, rpow_half_eq_quarter_sq, ← hqdef, mul_pow]
  have hR : (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) = q * q ^ k := by
    rw [rpow_quarter_succ_eq k, ← hqdef]
  rw [hL, hR]
  have hqq : (0 : ℝ) ≤ q ^ k * q ^ k := mul_nonneg hqkpos.le hqkpos.le
  have hleft : taylorContractionConst d * Cs * windowRatioConst d 2
        * windowRatioConst d 1 * (q ^ k * q ^ k) ≤ A * (q ^ k * q ^ k) :=
    mul_le_mul_of_nonneg_right hAle hqq
  linarith only [hleft, hmul]

/-! ## 2. The endpoint: the anchored one-step in the Step-4 slot, at every window -/

/-- **: the anchored one-step delivered in the `IterationDecay` slot, on the JOIN
route.**

For one `ω` and every scale `n` with `n+1 ≤ m` at which the supply event holds,
and every harmonic replacement `v` whose window clears the interior gate **or**
meets a face of `∂□_m` with's competitor data, the one-step contraction reads

```text
   E(u, U_{n+1-(k+1)}) ≤ 3^{-(k+1)/4} E(u, U_{n+1}) + ε · |∇ℓ(u,U_{n+1})| + δ ,
```

i.e. `e.Ej.decay.assumption` at `j := n+1`, `h := k+1`, `θ := 3^{-1/4}`, with `ε` and `δ` the
same explicit legs `edBridgeEps`, `edBridgeDelta` the interior slot delivers, at the join's
constant `max (schauderWindowConst d) C_bdry`.  There is **no** interior-gate hypothesis: the
window may sit anywhere in `□_m`, boundary lattice centres included. -/
theorem excessDecay_stepFour_slot_general (d : ℕ) [NeZero d] (hd : d ≠ 0) :
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
                        ((fun y => z + y) '' openCubeSet (originCube d (n - 2)) ⊆
                            openCubeSet (originCube d m) ∨
                          (∃ i : Fin d,
                            (MeetsUpperFace z m (n - 2) i ∨
                              MeetsLowerFace z m (n - 2) i) ∧
                            MemLp v.toFun 2 (volume.restrict (truncatedWindow z m n)) ∧
                            MemLp v.toFun 2
                              (volume.restrict (reflectedWindow z m (n - 2))) ∧
                            (∀ l : Fin d, MeetsUpperFace z m (n - 2) l →
                              ∀ y ∈ reflectedWindow z m (n - 2),
                                v.toFun (coordFaceReflection
                                  ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v.toFun y) ∧
                            (∀ l : Fin d, MeetsLowerFace z m (n - 2) l →
                              ∀ y ∈ reflectedWindow z m (n - 2),
                                v.toFun (coordFaceReflection
                                  (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v.toFun y) ∧
                            HarmonicOnNhd
                              (v.toFun ∘
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
                              edBridgeDelta M C
                                (edBridgeRemWeightGen d
                                  (max (schauderWindowConst d) Cb) k) L m s
                                ⟨s / 8, by linarith only [hs]⟩ z gflux hdat.grad omega n := by
  classical
  obtain ⟨C, Cb, hC, hCb, hjoin⟩ := excessDecay_oneStep_anchored d hd
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
    intro _hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv hwin c gmin hmin
    -- the good-event cap at the supply index, and the join at `x := z`
    have hEcap := hcapOm hmem L (by omega)
    have hmem' : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
        (cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
        (s / 8 * Real.sqrt delta) := by
      rw [show n - 2 + 3 = n + 1 from by ring]
      exact hmem
    have hmain := hom hmem' u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv hwin k hk3
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
      edBridgeEps, edBridgeEpsConstGen, edBridgeDelta, edBridgeRemWeightGen]
    refine edBridge_recombine
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
    · -- the `δ`-gate
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
