/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.SlopeStabilityEndpoints
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryGradH
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundarySplit

/-!
# The boundary Caccioppoli's `L²` object, reduced to the escalated scalar

```text
  S₀ = |(u − h)_{c + □_{n+2}}| ,   c = wellPlacedCentre x m (n+2) ,
```

This module carries out the composition **parametrized by that scalar**: with
`S` an abstract bound for it, the boundary Caccioppoli's `L²` object splits
into three frozen shapes plus `S`,

```text
  ‖u(·+c) − V‖_{L̲²(□_{n+2})}
      ≤ 2·3^d ‖u − (u)_{W'}‖_{L̲²(W')}          (the FIRST leg)
        + C(d)·3^{n+2}·3^d Σᵢ ‖∂ᵢh‖_{L̲²(W')}    (the FIFTH leg shape)
        + S                                       (the escalated scalar)
        + ‖σ‖_{L̲²(□_{n+2})} ,                     (the σ leg)
```

`W' = (z+□_{n+3}) ∩ □_m`, `σ = V − h(·+c) ∈ H¹₀(□_{n+2})`.

## The disclosed slot

`S` enters the conclusion **additively, in its own leg**, at coefficient `1`.
That is the honest reading: the scalar is an additive normalization defect of the
`L²` object, not a multiplier of any datum.  A producer supplying
`hmean` at some `S` together with a bound of `S` by the frozen bracket closes the
composition at twice the constant; a producer supplying `S = 0` closes it by
`add_zero`.

## What remains after this module

Exactly two inputs, both already named:

2. **the `σ`-leg choice** — `BoundaryGradH` section 4's fork, i.e. whether the
   `ν`-division is authorized.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2;
  `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Jensen in the normalized carrier -/

/-- **Jensen for the normalized `L²` carrier**: `|⨍_W f| ≤ ‖f‖_{L̲²(W)}`, with the
right-hand side read as the `toReal` of an `eLpNorm` against
`Support.normalizedVolumeMeasureOn W`. -/
theorem abs_volumeAverage_le_toReal_eLpNorm_normalized {W : Set (Vec d)}
    (hWm : MeasurableSet W) (hWpos : 0 < volume W) (hWtop : volume W ≠ ⊤)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict W)) :
    |volumeAverage W f| ≤
      (eLpNorm f 2 (Support.normalizedVolumeMeasureOn W)).toReal := by
  haveI : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hWtop
  have hreal : (0 : ℝ) < (volume W).toReal := ENNReal.toReal_pos hWpos.ne' hWtop
  have hint : IntegrableOn f W volume := hf.integrable (by norm_num)
  have hint2 : IntegrableOn (fun x => f x ^ 2) W volume := by
    have h := hf.integrable_sq
    simpa [IntegrableOn] using h
  rw [← Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn hWpos hWtop hf]
  exact abs_volumeAverage_le_normalizedL2On hWm hreal hint hint2

/-! ## 2. The mean-zero Poincaré on the boundary covering cube -/

/-- **The mean-subtracted `L²` Poincaré inequality on the covering cube.**

The covering cube `c + □_{n+2}` is an axis cube of side `3^{n+2}`, so
CoarseGraining's scaled mean-zero Poincaré applies verbatim; the normalization
cancels between the two sides because the same cube carries both. -/
theorem eLpNorm_sub_average_coveringCube_le_meanZeroPoincare {n m : ℤ} {x : Vec d}
    (hnm : n + 2 ≤ m) (h : H1Function (openCubeSet (originCube d m))) :
    (eLpNorm (fun y => h.toFun y -
          volumeAverage ((fun y' => wellPlacedCentre x m (n + 2) + y') ''
            openCubeSet (originCube d (n + 2))) h.toFun) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y' => wellPlacedCentre x m (n + 2) + y') ''
            openCubeSet (originCube d (n + 2))))).toReal ≤
      unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) *
        ∑ i : Fin d,
          (eLpNorm (fun y => h.grad y i) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y' => wellPlacedCentre x m (n + 2) + y') ''
                openCubeSet (originCube d (n + 2))))).toReal := by
  classical
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  set cc : Set (Vec d) :=
    (fun y' => c + y') '' openCubeSet (originCube d (n + 2)) with hcc
  set Lc : ℝ := (3 : ℝ) ^ (n + 2) with hLc
  set A : Vec d := fun i => c i - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 2) with hA
  have hLpos : (0 : ℝ) < Lc := zpow_pos (by norm_num) _
  have hcube : cc = axisCube A Lc := by
    rw [hcc, hA, hLc]
    exact image_add_openCubeSet_eq_axisCube c (n + 2)
  have hccsub : cc ⊆ openCubeSet (originCube d m) := by
    rw [hcc]
    exact image_add_wellPlacedCentre_subset_openCubeSet x hnm
  have hsubA : axisCube A Lc ⊆ openCubeSet (originCube d m) := by
    rw [← hcube]
    exact hccsub
  -- CoarseGraining's scaled mean-zero Poincaré on the axis realization
  have hraw : (eLpNorm (fun y => h.toFun y - integralAverage cc h.toFun) 2
        (volumeMeasureOn cc)).toReal ≤
      unitMeanZeroPoincareConst d * Lc *
        ∑ i : Fin d,
          (eLpNorm (fun y => h.grad y i) 2 (volumeMeasureOn cc)).toReal := by
    rw [hcube]
    have hpo := scaled_meanZero_poincare A hLpos
      (h.restrict (isOpen_axisCube A Lc) hsubA)
    have hfun : ((h.restrict (isOpen_axisCube A Lc) hsubA).subAverage).toFun =
        fun y => h.toFun y - integralAverage (axisCube A Lc) h.toFun := by
      funext y
      exact H1Function.subAverage_apply _ y
    rwa [hfun] at hpo
  -- the normalization cancels
  have hiv : integralAverage cc h.toFun = volumeAverage cc h.toFun := rfl
  rw [hiv] at hraw
  have hrestrict : volumeMeasureOn cc = volume.restrict cc := rfl
  rw [hrestrict] at hraw
  simp only [eLpNorm_normalizedVolumeMeasureOn_eq, ENNReal.toReal_mul]
  have hr : (0 : ℝ) ≤ (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal := ENNReal.toReal_nonneg
  calc (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal *
        (eLpNorm (fun y => h.toFun y - volumeAverage cc h.toFun) 2
          (volume.restrict cc)).toReal
      ≤ (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal *
          (unitMeanZeroPoincareConst d * Lc *
            ∑ i : Fin d,
              (eLpNorm (fun y => h.grad y i) 2 (volume.restrict cc)).toReal) :=
        mul_le_mul_of_nonneg_left hraw hr
    _ = unitMeanZeroPoincareConst d * Lc *
          ∑ i : Fin d,
            (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal *
              (eLpNorm (fun y => h.grad y i) 2 (volume.restrict cc)).toReal := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring

/-! ## 3. The covering-cube transport, in real form -/

theorem toReal_eLpNorm_coveringCube_le_anchorWindow {n m : ℤ} {x z : Vec d}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    {f : Vec d → ℝ}
    (hfin : eLpNorm f 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤) :
    (eLpNorm f 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => wellPlacedCentre x m (n + 2) + y) ''
            openCubeSet (originCube d (n + 2))))).toReal ≤
      (3 : ℝ) ^ d *
        (eLpNorm f 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
  have hbase := eLpNorm_coveringCube_le_anchorWindow hnm hx hgeom f
  have hRne : ENNReal.ofReal ((3 : ℝ) ^ d) *
      eLpNorm f 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m)))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hstep := ENNReal.toReal_mono hRne hbase
  rwa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d)] at hstep

/-! ## 4. The mean-control reduction -/

/-- **The boundary Caccioppoli's `L²` object, reduced to the escalated scalar.** -/
theorem eLpNorm_coveringCube_sub_le_meanControl {n m : ℤ} {x z : Vec d} {S : ℝ}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (u h : H1Function (openCubeSet (originCube d m)))
    (V : H1Function (openCubeSet (originCube d (n + 2))))
    (sigma : H10Function (openCubeSet (originCube d (n + 2))))
    (hsigval : ∀ y, sigma.toFun y =
      V.toFun y - h.toFun (y + wellPlacedCentre x m (n + 2)))
    (hmean : |volumeAverage
        ((fun y' => wellPlacedCentre x m (n + 2) + y') ''
          openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y - h.toFun y)| ≤ S) :
    (eLpNorm (fun y => u.toFun (y + wellPlacedCentre x m (n + 2)) - V.toFun y) 2
        (Support.normalizedVolumeMeasureOn
          (openCubeSet (originCube d (n + 2))))).toReal ≤
      2 * ((3 : ℝ) ^ d *
          (eLpNorm (fun y => u.toFun y -
              volumeAverage
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))) u.toFun) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal) +
        (unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) * (3 : ℝ) ^ d *
            ∑ i : Fin d,
              (eLpNorm (fun y => h.grad y i) 2
                (Support.normalizedVolumeMeasureOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))))).toReal +
          (S +
            (eLpNorm sigma.toFun 2
              (Support.normalizedVolumeMeasureOn
                (openCubeSet (originCube d (n + 2))))).toReal)) := by
  classical
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  set cc : Set (Vec d) :=
    (fun y' => c + y') '' openCubeSet (originCube d (n + 2)) with hcc
  set W : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) with hW
  set mu : Measure (Vec d) :=
    Support.normalizedVolumeMeasureOn (openCubeSet (originCube d (n + 2))) with hmu
  have hmuEq : mu = normalizedCubeMeasure (originCube d (n + 2)) := by
    rw [hmu, normalizedVolumeMeasureOn_openCubeSet]
  letI : IsProbabilityMeasure (normalizedCubeMeasure (originCube d (n + 2))) :=
    ⟨normalizedCubeMeasure_apply_univ (originCube d (n + 2))⟩
  -- the two carriers
  have hccsub : cc ⊆ openCubeSet (originCube d m) := by
    rw [hcc]
    exact image_add_wellPlacedCentre_subset_openCubeSet x hnm
  have hccm : MeasurableSet cc := by
    rw [hcc]
    exact (isOpen_image_add_openCubeSet_originCube c (n + 2)).measurableSet
  have hccne : volume cc ≠ 0 := by
    rw [hcc]
    exact volume_image_add_openCubeSet_ne_zero c (originCube d (n + 2))
  have hcctop : volume cc ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_openCubeSet_ne_top (originCube d m))
      (measure_mono hccsub)
  have hccpos : 0 < volume cc := pos_iff_ne_zero.mpr hccne
  have hWsub : W ⊆ openCubeSet (originCube d m) := by
    rw [hW]; exact Set.inter_subset_right
  have hWtop : volume W ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_openCubeSet_ne_top (originCube d m))
      (measure_mono hWsub)
  -- the anchor's `L²` data, restricted
  haveI : IsFiniteMeasure (volume.restrict cc) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hcctop
  have humemcc : MemLp u.toFun 2 (volume.restrict cc) :=
    u.memL2.mono_measure (Measure.restrict_mono hccsub le_rfl)
  have hhmemcc : MemLp h.toFun 2 (volume.restrict cc) :=
    h.memL2.mono_measure (Measure.restrict_mono hccsub le_rfl)
  have humemW : MemLp u.toFun 2 (volume.restrict W) :=
    u.memL2.mono_measure (Measure.restrict_mono hWsub le_rfl)
  have huint : IntegrableOn u.toFun cc volume := humemcc.integrable (by norm_num)
  have hhint : IntegrableOn h.toFun cc volume := hhmemcc.integrable (by norm_num)
  have hconstint : IntegrableOn (fun _ : Vec d => volumeAverage W u.toFun) cc volume :=
    integrable_const _
  have hccvol : (volume cc).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hccne hcctop)
  -- the mean-subtracted datum on `W`, and its finiteness
  have hmemsub : MemLp (fun y => u.toFun y - volumeAverage W u.toFun) 2
      (volume.restrict W) := by
    haveI : IsFiniteMeasure (volume.restrict W) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.2 hWtop
    exact humemW.sub (memLp_const _)
  have hfinsub : eLpNorm (fun y => u.toFun y - volumeAverage W u.toFun) 2
      (Support.normalizedVolumeMeasureOn W) ≠ ⊤ :=
    eLpNorm_normalizedVolumeMeasureOn_ne_top hmemsub.2.ne
  set X : ℝ := (eLpNorm (fun y => u.toFun y - volumeAverage W u.toFun) 2
    (Support.normalizedVolumeMeasureOn W)).toReal with hX
  have hXtrans : (eLpNorm (fun y => u.toFun y - volumeAverage W u.toFun) 2
      (Support.normalizedVolumeMeasureOn cc)).toReal ≤ (3 : ℝ) ^ d * X :=
    toReal_eLpNorm_coveringCube_le_anchorWindow hnm hx hgeom hfinsub
  -- the four legs, in the cube's own frame
  set utr : H1Function (openCubeSet (originCube d (n + 2))) :=
    H1Function.untranslate c
      (u.restrict (isOpen_translateSet_openCubeSet c (n + 2))
        (translateSet_wellPlacedCentre_subset x hnm)) with hutr
  set htr : H1Function (openCubeSet (originCube d (n + 2))) :=
    H1Function.untranslate c
      (h.restrict (isOpen_translateSet_openCubeSet c (n + 2))
        (translateSet_wellPlacedCentre_subset x hnm)) with hhtr
  set a1 : ℝ := volumeAverage W u.toFun with ha1
  set a2 : ℝ := volumeAverage cc h.toFun with ha2
  have hmemU : MemLp (fun y => utr.toFun y - a1) 2 mu := by
    rw [hmuEq]
    exact (memLp_two_normalizedCubeMeasure_of_h1 (originCube d (n + 2)) utr).sub
      (memLp_const _)
  have hmemH : MemLp (fun y => htr.toFun y - a2) 2 mu := by
    rw [hmuEq]
    exact (memLp_two_normalizedCubeMeasure_of_h1 (originCube d (n + 2)) htr).sub
      (memLp_const _)
  have hmemC : MemLp (fun _ : Vec d => a2 - a1) 2 mu := by
    rw [hmuEq]; exact memLp_const _
  have hmemS : MemLp sigma.toFun 2 mu := by
    rw [hmuEq]
    exact memLp_two_normalizedCubeMeasure_of_h1 (originCube d (n + 2)) sigma.toH1Function
  have hmem12 : MemLp (fun y => (utr.toFun y - a1) - (htr.toFun y - a2)) 2 mu :=
    hmemU.sub hmemH
  have hmem123 : MemLp
      (fun y => ((utr.toFun y - a1) - (htr.toFun y - a2)) - (a2 - a1)) 2 mu :=
    hmem12.sub hmemC
  -- the pointwise decomposition
  have hdecomp : (fun y => u.toFun (y + c) - V.toFun y) =
      fun y => (((utr.toFun y - a1) - (htr.toFun y - a2)) - (a2 - a1)) -
        sigma.toFun y := by
    funext y
    have hu : utr.toFun y = u.toFun (y + c) := rfl
    have hh : htr.toFun y = h.toFun (y + c) := rfl
    rw [hu, hh, hsigval y]
    ring
  -- the triangle inequality, three times, in `ℝ≥0∞`
  have htri : (eLpNorm (fun y => u.toFun (y + c) - V.toFun y) 2 mu).toReal ≤
      (eLpNorm (fun y => utr.toFun y - a1) 2 mu).toReal +
        (eLpNorm (fun y => htr.toFun y - a2) 2 mu).toReal +
        (eLpNorm (fun _ : Vec d => a2 - a1) 2 mu).toReal +
        (eLpNorm sigma.toFun 2 mu).toReal := by
    have hstep1 := eLpNorm_sub_le (μ := mu) (p := 2) hmem123.1 hmemS.1 (by norm_num)
    have hstep2 := eLpNorm_sub_le (μ := mu) (p := 2) hmem12.1 hmemC.1 (by norm_num)
    have hstep3 := eLpNorm_sub_le (μ := mu) (p := 2) hmemU.1 hmemH.1 (by norm_num)
    have hchain : eLpNorm (fun y => u.toFun (y + c) - V.toFun y) 2 mu ≤
        eLpNorm (fun y => utr.toFun y - a1) 2 mu +
          eLpNorm (fun y => htr.toFun y - a2) 2 mu +
          eLpNorm (fun _ : Vec d => a2 - a1) 2 mu +
          eLpNorm sigma.toFun 2 mu := by
      rw [hdecomp]
      calc eLpNorm (fun y =>
              (((utr.toFun y - a1) - (htr.toFun y - a2)) - (a2 - a1)) - sigma.toFun y) 2 mu
          ≤ eLpNorm (fun y => ((utr.toFun y - a1) - (htr.toFun y - a2)) - (a2 - a1)) 2 mu +
              eLpNorm sigma.toFun 2 mu := hstep1
        _ ≤ (eLpNorm (fun y => (utr.toFun y - a1) - (htr.toFun y - a2)) 2 mu +
              eLpNorm (fun _ : Vec d => a2 - a1) 2 mu) +
              eLpNorm sigma.toFun 2 mu := add_le_add hstep2 le_rfl
        _ ≤ ((eLpNorm (fun y => utr.toFun y - a1) 2 mu +
                eLpNorm (fun y => htr.toFun y - a2) 2 mu) +
              eLpNorm (fun _ : Vec d => a2 - a1) 2 mu) +
              eLpNorm sigma.toFun 2 mu := add_le_add (add_le_add hstep3 le_rfl) le_rfl
    have hne : eLpNorm (fun y => utr.toFun y - a1) 2 mu +
        eLpNorm (fun y => htr.toFun y - a2) 2 mu +
        eLpNorm (fun _ : Vec d => a2 - a1) 2 mu +
        eLpNorm sigma.toFun 2 mu ≠ ⊤ := by
      refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
        ⟨hmemU.eLpNorm_ne_top, hmemH.eLpNorm_ne_top⟩, hmemC.eLpNorm_ne_top⟩,
        hmemS.eLpNorm_ne_top⟩
    have h := ENNReal.toReal_mono hne hchain
    rwa [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
        ⟨hmemU.eLpNorm_ne_top, hmemH.eLpNorm_ne_top⟩, hmemC.eLpNorm_ne_top⟩)
      hmemS.eLpNorm_ne_top,
      ENNReal.toReal_add (ENNReal.add_ne_top.2
        ⟨hmemU.eLpNorm_ne_top, hmemH.eLpNorm_ne_top⟩) hmemC.eLpNorm_ne_top,
      ENNReal.toReal_add hmemU.eLpNorm_ne_top hmemH.eLpNorm_ne_top] at h
  -- leg 1: the mean-subtracted `L²` datum, transported
  have hframeU : eLpNorm (fun y => utr.toFun y - a1) 2 mu =
      eLpNorm (fun y => u.toFun y - a1) 2
        (Support.normalizedVolumeMeasureOn cc) := by
    rw [hmu, hcc,
      eLpNorm_normalizedVolumeMeasureOn_image_add c
        (openCubeSet (originCube d (n + 2))) (by norm_num) (by norm_num)]
    rfl
  have hleg1 : (eLpNorm (fun y => utr.toFun y - a1) 2 mu).toReal ≤ (3 : ℝ) ^ d * X := by
    rw [hframeU]
    exact hXtrans
  -- leg 2: the mean-zero Poincaré on the covering cube, transported
  have hframeH : eLpNorm (fun y => htr.toFun y - a2) 2 mu =
      eLpNorm (fun y => h.toFun y - a2) 2
        (Support.normalizedVolumeMeasureOn cc) := by
    rw [hmu, hcc,
      eLpNorm_normalizedVolumeMeasureOn_image_add c
        (openCubeSet (originCube d (n + 2))) (by norm_num) (by norm_num)]
    rfl
  have hgradfin : ∀ i : Fin d, eLpNorm (fun y => h.grad y i) 2
      (Support.normalizedVolumeMeasureOn W) ≠ ⊤ := by
    intro i
    refine eLpNorm_normalizedVolumeMeasureOn_ne_top ?_
    exact ((h.gradMemL2 i).mono_measure (Measure.restrict_mono hWsub le_rfl)).2.ne
  have hgradtrans : ∀ i : Fin d,
      (eLpNorm (fun y => h.grad y i) 2
        (Support.normalizedVolumeMeasureOn cc)).toReal ≤
      (3 : ℝ) ^ d * (eLpNorm (fun y => h.grad y i) 2
        (Support.normalizedVolumeMeasureOn W)).toReal := fun i =>
    toReal_eLpNorm_coveringCube_le_anchorWindow hnm hx hgeom (hgradfin i)
  have hleg2 : (eLpNorm (fun y => htr.toFun y - a2) 2 mu).toReal ≤
      unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) * (3 : ℝ) ^ d *
        ∑ i : Fin d,
          (eLpNorm (fun y => h.grad y i) 2
            (Support.normalizedVolumeMeasureOn W)).toReal := by
    rw [hframeH]
    have hbase := eLpNorm_sub_average_coveringCube_le_meanZeroPoincare
      (x := x) (n := n) (m := m) hnm h
    have hsum : ∑ i : Fin d,
        (eLpNorm (fun y => h.grad y i) 2
          (Support.normalizedVolumeMeasureOn cc)).toReal ≤
        (3 : ℝ) ^ d * ∑ i : Fin d,
          (eLpNorm (fun y => h.grad y i) 2
            (Support.normalizedVolumeMeasureOn W)).toReal := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hgradtrans i
    have hcnn : (0 : ℝ) ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) := by
      have h1 : (0 : ℝ) ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
      have h2 : (0 : ℝ) < (3 : ℝ) ^ (n + 2) := zpow_pos (by norm_num) _
      exact mul_nonneg h1 h2.le
    calc (eLpNorm (fun y => h.toFun y - a2) 2
          (Support.normalizedVolumeMeasureOn cc)).toReal
        ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) *
            ∑ i : Fin d,
              (eLpNorm (fun y => h.grad y i) 2
                (Support.normalizedVolumeMeasureOn cc)).toReal := hbase
      _ ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) *
            ((3 : ℝ) ^ d * ∑ i : Fin d,
              (eLpNorm (fun y => h.grad y i) 2
                (Support.normalizedVolumeMeasureOn W)).toReal) :=
          mul_le_mul_of_nonneg_left hsum hcnn
      _ = unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) * (3 : ℝ) ^ d *
            ∑ i : Fin d,
              (eLpNorm (fun y => h.grad y i) 2
                (Support.normalizedVolumeMeasureOn W)).toReal := by ring
  -- leg 3: the scalar
  have hconstnorm : (eLpNorm (fun _ : Vec d => a2 - a1) 2 mu).toReal = |a2 - a1| := by
    rw [hmuEq, eLpNorm_const _ (by norm_num) (by
      exact (IsProbabilityMeasure.ne_zero
        (normalizedCubeMeasure (originCube d (n + 2)))))]
    simp [Real.norm_eq_abs]
  have hsplit : a2 - a1 =
      -volumeAverage cc (fun y => u.toFun y - h.toFun y) +
        volumeAverage cc (fun y => u.toFun y - a1) := by
    rw [show (fun y => u.toFun y - h.toFun y) = u.toFun - h.toFun from rfl,
      volumeAverage_sub huint hhint,
      show (fun y => u.toFun y - a1) = u.toFun - (fun _ => a1) from rfl,
      volumeAverage_sub huint hconstint, volumeAverage_const hccvol, ha2]
    ring
  have hjen : |volumeAverage cc (fun y => u.toFun y - a1)| ≤
      (eLpNorm (fun y => u.toFun y - a1) 2
        (Support.normalizedVolumeMeasureOn cc)).toReal := by
    refine abs_volumeAverage_le_toReal_eLpNorm_normalized hccm hccpos hcctop ?_
    exact humemcc.sub (memLp_const _)
  have hleg3 : (eLpNorm (fun _ : Vec d => a2 - a1) 2 mu).toReal ≤
      S + (3 : ℝ) ^ d * X := by
    rw [hconstnorm, hsplit]
    have hjen' := hjen.trans hXtrans
    have hmean' : |volumeAverage cc (fun y => u.toFun y - h.toFun y)| ≤ S := hmean
    have h1 := neg_abs_le (volumeAverage cc (fun y => u.toFun y - h.toFun y))
    have h2 := le_abs_self (volumeAverage cc (fun y => u.toFun y - h.toFun y))
    have h3 := neg_abs_le (volumeAverage cc (fun y => u.toFun y - a1))
    have h4 := le_abs_self (volumeAverage cc (fun y => u.toFun y - a1))
    rw [abs_le]
    constructor <;> linarith only [h1, h2, h3, h4, hjen', hmean']
  -- assemble
  linarith only [htri, hleg1, hleg2, hleg3]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
