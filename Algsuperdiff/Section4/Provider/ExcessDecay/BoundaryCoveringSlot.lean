/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorPrefactor
import Algsuperdiff.Section4.Provider.ExcessDecay.CoveringSlotObstruction
import Algsuperdiff.Section4.Provider.ExcessDecay.InteriorEllipticity
import Algsuperdiff.Section4.Provider.ExcessDecay.ReindexSlot

/-!
# The boundary lane's covering cube, read at the slot `n+3`

`CoveringSlotObstruction` measured exactly this: on the
boundary branch the covering cube `c + □_{n+2}`, `c = wellPlacedCentre x m
(n+2)`, **leaves** the `n+2` good-event slot's cube, and **always** sits inside
the `n+3` one.  The frozen general clause puts its slot at
`n+3` precisely so that this positive half is usable.  This module cashes
it in, at the level the boundary Caccioppoli step consumes.

Three steps, each proved elsewhere and composed here:

1. **the half-open containment** — `CoveringSlotObstruction`'s open-cube
   containment `c + □_{n+2} ⊆ z + □_{n+3}` re-derived in the *half-open*
   realization the off-grid transports require (the margin is ample: the centre
   moves by less than `6·3^n` and the half-open child reaches `4.5·3^n`, against
   the parent's `13.5·3^n`);
2. **the off-grid transport at depth `1`** — `OffGridErrorFluxCorrected`'s root
   transport at `K = □_{n+3}`, `P = □_{n+2}`, so the depth factor is a single
   `3^{u·1}`, i.e. `3^{s/8} ≤ 3^{1/8} < 1.15`;
3. **the good event at the `n+3` slot** — `ReindexSlot`'s `(n+3)` caps, read at
   `L ≥ n+3` (the frozen binder `n + 3 ≤ m ≤ L`).

**No antisymmetric-shift conversion is used**: nothing below converts `Λ` or `λ`
by the antisymmetric-shift invariance.  The whole chain runs at the `(n+3)`
family `parentRebasedFamily M L (n+3) c z ω` — the covering cube's own frame
*at the parent's constant* — which is the family `InteriorRebase` builds and the
one the equation transports to for free.

**The `q = 1` ingredients are supplied here**, at the covering cube:
`CaccioppoliInteriorPrefactor`'s constant-`1` comparisons `Λ_{u,1} ≤ Λ_{u/2,2}`
and `λ_{u,1}^{-1} ≤ λ_{u/2,2}^{-1}` turn the `q = 2` ratio cap into the `q = 1`
ingredients `Λ_{u,1}`, `λ_{u,1}^{-1}` and `Θ` that
`caccioppoliWithRHSPrefactor` reads.

## What this does *not* do

It does not prove the boundary clause.  The boundary lane still needs its
analytic half (the trace-measure Poincaré and the Stampacchia step), the
boundary energy assembly at this family, and the `L²`/window transport onto the
general clause's window.  Nothing below is an instance, or a fraction, of any
source node.

## References

* ABK26, `e.mathcalE.stability.applied`; the boundary application of
  `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open Homogenization Homogenization.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

private theorem isotropicComparator_eq_scalarMatrix_covering (sigma : PositiveScalar) :
    isotropicComparatorMatrix (d := d) sigma = scalarMatrix (d := d) (sigma : ℝ) := rfl

/-! ## 1. The half-open containment of the covering cube in the `n+3` parent -/

/-- **The covering cube inside the `n+3` parent, half-open.** -/
theorem translateSet_cubeSet_coveringCube_subset_anchorParent {n m : ℤ} {x z : Vec d}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    translateSet (wellPlacedCentre x m (n + 2) - z) (cubeSet (originCube d (n + 2))) ⊆
      cubeSet (originCube d (n + 3)) := by
  have hw : x - z ∈ openCubeSet (originCube d (n + 1)) :=
    sub_mem_openCubeSet_of_anchorGeometry hgeom
  rw [mem_openCubeSet_originCube_iff] at hw
  have h1 : (3 : ℝ) ^ (n + 1) = 3 ^ n * 3 := by
    rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have h2 : (3 : ℝ) ^ (n + 2) = 3 ^ n * 9 := by
    have hn : n + 2 = n + 1 + 1 := by ring
    rw [hn, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0), h1]
    ring
  have h3 : (3 : ℝ) ^ (n + 3) = 3 ^ n * 27 := by
    have hn : n + 3 = n + 2 + 1 := by ring
    rw [hn, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0), h2]
    ring
  have hpos : (0 : ℝ) < 3 ^ n := zpow_pos (by norm_num) n
  rintro p ⟨y, hy, rfl⟩
  rw [mem_cubeSet_originCube_iff] at hy ⊢
  intro i
  have hyi := hy i
  have hwi := hw i
  have hci := sub_wellPlacedCentre_coord_bound hnm hx i
  simp only [Pi.sub_apply] at hwi
  rw [h1] at hwi
  rw [h2] at hyi hci
  rw [h3]
  refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.sub_apply] <;>
    linarith only [hyi.1, hyi.2, hwi.1, hwi.2, hci.1, hci.2, hpos]

/-! ## 2. The off-grid transport at depth one -/

/-- The scale gap of the `n+3` parent/covering pair, as a natural number. -/
private theorem originCube_scale_gap_one (n : ℤ) :
    ((originCube d (n + 3)).scale - (originCube d (n + 2)).scale).toNat = 1 := by
  have h : (originCube d (n + 3)).scale - (originCube d (n + 2)).scale = 1 := by
    simp only [originCube]
    ring
  rw [h]
  rfl

/-- **The covering cube's coarse-graining error against the general clause's
representative.**

At every index `t` strictly above the good-event index `s/8` and at most `1/2`,
the covering cube's `q = 2` error at the `(n+3)` re-based family is bounded by
the frozen clause's own `fluxCorrectedErrorRepresentative M L (n+3) ⟨s/8⟩`,
with the **depth-one** factor `3^{s/8}` (at most `3^{1/8} < 1.15`). -/
theorem ae_coveringCubeError_le_representative [NeZero d] (M : ABKModel d)
    (L n m : ℤ) (z : Vec d) {s t : ℝ} (hs : 0 < s) (hst : s / 8 < t) (ht : t ≤ 1 / 2) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, n + 2 ≤ m → x ∈ openCubeSet (originCube d m) →
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) t .infinity (.finite 2)
            (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
          Real.sqrt (offGridStabilityConst d t (s / 8)) *
            ((3 : ℝ) ^ (s / 8) *
              fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  have hbase := (GoodEvents.measurePreserving_translateCutoffSample M
      z).quasiMeasurePreserving.ae
    (ae_offGridErrorFunctional_le_fluxCorrectedErrorFunctionalAtRoot
      M L (n + 3) (originCube d (n + 3))
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3)))
      (by linarith only [hs] : (0 : ℝ) < s / 8) hst ht)
  filter_upwards [hbase] with omega hall
  intro x hnm hx hgeom
  have hstep := hall (wellPlacedCentre x m (n + 2) - z) (originCube d (n + 2))
    (originCube d (n + 3))
    (translateSet_cubeSet_coveringCube_subset_anchorParent hnm hx hgeom)
  rw [originCube_scale_gap_one (d := d) n,
    fluxCorrectedErrorFunctionalAtRoot_eq_representative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩] at hstep
  have hexp : (s / 8 * ((1 : ℕ) : ℝ)) = s / 8 := by
    push_cast
    ring
  rw [hexp] at hstep
  rwa [homogenizationErrorOnCube_parentRebasedFamily_eq_offGrid M L (n + 3) (n + 2)
    (wellPlacedCentre x m (n + 2)) z omega (by linarith only [hs, hst] : (0 : ℝ) < t)
    (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3)))]

/-! ## 3. The covering cube's ellipticity data, capped on the good event -/

/-- **The covering cube's `q = 2` ratio pair, capped, and the three `q = 1`
ingredients.**

On the frozen general clause's own good event `𝒢(n+3, z; s/8, 1/2)`, at the
coarse-graining slot index `s/6`, the coarse-grained ellipticity ratios of the
`(n+3)` re-based family on the **covering** cube are bounded by an absolute
constant `K(d)`; the three `q = 1` quantities the boundary Caccioppoli prefactor
reads — `Λ_{s/3,1}`, `λ_{s/3,1}^{-1}` and `Θ_{s/3,s/3}` — follow at the same
constant through `CaccioppoliInteriorPrefactor`'s constant-`1` comparisons
(at the covering cube). -/
theorem ae_coveringCubeCaps_le (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ z : Vec d,
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 3) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                (fun y => x + y) '' openCubeSet (originCube d n) ⊆
                    ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                      openCubeSet (originCube d m) →
                ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                      Ch02.LambdaSq (originCube d (n + 2)) (s / 6) (.finite 2)
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega) ≤ K ∧
                  (Annealed.sigmaBar M (n + 3) : ℝ) *
                      (Ch02.lambdaSq (originCube d (n + 2)) (s / 6) (.finite 2)
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega))⁻¹ ≤ K ∧
                  Ch02.LambdaS (originCube d (n + 2)) (s / 3)
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega) ≤
                      K * (Annealed.sigmaBar M (n + 3) : ℝ) ∧
                  (Ch02.lambdaS (originCube d (n + 2)) (s / 3)
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega))⁻¹ ≤
                      K * ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ ∧
                  Ch02.ThetaRatio (originCube d (n + 2)) (s / 3) (s / 3)
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega) ≤ K * K := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorRepresentative_le_harmonicSlot_addThree d
  have hd : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set kappa : ℝ := Real.sqrt (192 * (d : ℝ)) * 3 with hkappadef
  have hkappa : 0 ≤ kappa := by positivity
  refine ⟨C, 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1), hCpos, ?_, ?_⟩
  · have h1 : (0 : ℝ) < (kappa * (C * (1 / 2))) ^ 2 + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (d : ℝ) := by linarith only [hd]
    exact mul_pos h2 h1
  intro M s hsrange hregime hsmall hs L m n hmL hnm z
  have hs1 : s ≤ 1 := hsrange.2
  have hs6 : (0 : ℝ) < s / 6 := by linarith only [hs]
  have hs3 : (0 : ℝ) < s / 3 := by linarith only [hs]
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) := (Annealed.sigmaBar M (n + 3)).2
  filter_upwards [hC M s hsrange hregime hsmall hs n z,
    ae_coveringCubeError_le_representative M L n m z hs
      (by linarith only [hs] : s / 8 < s / 6) (by linarith only [hs1] : s / 6 ≤ 1 / 2)]
    with omega hcap herr
  intro hmem x hx hgeom
  have hErep0 : (0 : ℝ) ≤ fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hErepCap := hcap hmem L (le_trans hnm hmL)
  have hE : Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) (s / 6) .infinity
      (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
      kappa * (C * (1 / 2)) := by
    refine (herr x (by omega) hx hgeom).trans ?_
    have h1 : Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) ≤
        Real.sqrt (192 * (d : ℝ)) :=
      Real.sqrt_le_sqrt (offGridStabilityConst_slot_le hs hs1)
    have h2 : ((3 : ℝ) ^ (s / 8)) ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith only [hs1] : s / 8 ≤ (1 : ℝ))
      rwa [Real.rpow_one] at h
    have h3 : (3 : ℝ) ^ (s / 8) *
        fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
          (Cutoff.translateCutoffSample z omega) ≤ 3 * (C * (1 / 2)) := by
      have hstepa : (3 : ℝ) ^ (s / 8) *
          fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
            (Cutoff.translateCutoffSample z omega) ≤
          3 * fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
            (Cutoff.translateCutoffSample z omega) :=
        mul_le_mul_of_nonneg_right h2 hErep0
      have hstepb : (3 : ℝ) *
          fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
            (Cutoff.translateCutoffSample z omega) ≤ 3 * (C * (1 / 2)) := by
        linarith only [hErepCap]
      linarith only [hstepa, hstepb]
    have h4 : (0 : ℝ) ≤ (3 : ℝ) ^ (s / 8) *
        fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
          (Cutoff.translateCutoffSample z omega) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hErep0
    calc Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
          ((3 : ℝ) ^ (s / 8) *
            fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
              (Cutoff.translateCutoffSample z omega))
        ≤ Real.sqrt (192 * (d : ℝ)) * (3 * (C * (1 / 2))) :=
          mul_le_mul h1 h3 h4 (Real.sqrt_nonneg _)
      _ = kappa * (C * (1 / 2)) := by rw [hkappadef]; ring
  have hEnn : 0 ≤ Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) (s / 6) .infinity
      (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) :=
    homogenizationErrorOnCube_infinity_two_nonneg (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) hs6
  have hratio := max_ellipticityRatio_le_homogenizationError (d := d)
    (originCube d (n + 2))
    (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) hs6
    (Annealed.sigmaBar M (n + 3)).2
  rw [← isotropicComparator_eq_scalarMatrix_covering] at hratio
  have hmax := hratio.trans (two_mul_dim_mul_sq_add_one_le_of_le hEnn hE)
  have hU := le_trans (le_max_left _ _) hmax
  have hL := le_trans (le_max_right _ _) hmax
  have hB1 : Ch02.LambdaS (originCube d (n + 2)) (s / 3)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) ≤
      2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        (Annealed.sigmaBar M (n + 3) : ℝ) := by
    refine LambdaS_le_of_ratio_cap (originCube d (n + 2)) _ hs3 hsig ?_
    rwa [show s / 3 / 2 = s / 6 by ring]
  have hB2 : (Ch02.lambdaS (originCube d (n + 2)) (s / 3)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega))⁻¹ ≤
      2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ := by
    refine lambdaS_inv_le_of_ratio_cap (originCube d (n + 2)) _ hs3 hsig ?_
    rwa [show s / 3 / 2 = s / 6 by ring]
  refine ⟨hU, hL, hB1, hB2, ?_⟩
  refine (thetaRatio_le_of_caps (originCube d (n + 2)) _ hs3 hs3 hB1 hB2).trans
    (le_of_eq ?_)
  have hsne : ((Annealed.sigmaBar M (n + 3) : ℝ)) ≠ 0 := ne_of_gt hsig
  calc 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        (Annealed.sigmaBar M (n + 3) : ℝ) *
        (2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
          ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹)
      = 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
          (2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1)) *
          ((Annealed.sigmaBar M (n + 3) : ℝ) *
            ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹) := by ring
    _ = 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
          (2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1)) := by
        rw [mul_inv_cancel₀ hsne, mul_one]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
