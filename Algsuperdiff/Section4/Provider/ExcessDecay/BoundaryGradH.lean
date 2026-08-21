/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryEnergyRebase
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryTransports

/-!
# The two `∇h` conversions of the boundary Caccioppoli, and the `σ`-leg fork

The boundary Caccioppoli's data leg is CoarseGraining's `dirichletEnergyWith`,
whose second summand carries the **full** Besov norm of the transported
boundary gradient,

```text
  ‖∇h̃‖_{B^r} = √(|(∇h̃)_{□_{n+2}}|²) + [∇h̃]_{B^r} ,   h̃ = h(· + c) ,
```

`c = wellPlacedCentre x m (n+2)`.

* **the seminorm half** — the same lemma read at `g := −∇h`, together with the
  `gagliardoKernel` negation congruence it needs to see that `[−∇h] = [∇h]`.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2; `e.cg.RHS`, the Dirichlet
  energy display.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The `gagliardoKernel` negation congruence, on the datum -/

/-- **The Gagliardo `L²` datum does not see a sign.** -/
theorem memLp_gagliardoKernel_neg (A : Set (Vec d)) (s : ℝ) {F : Vec d → E}
    (h : MemLp (Gagliardo.gagliardoKernel s 2 F) 2
      (Support.normalizedGagliardoMeasureOn A)) :
    MemLp (Gagliardo.gagliardoKernel s 2 (fun y => -F y)) 2
      (Support.normalizedGagliardoMeasureOn A) := by
  have hneg : (fun y => -F y) = -F := rfl
  rw [hneg, Gagliardo.gagliardoKernel_neg]
  exact h.neg

/-! ## 2. The seminorm half of the `∇h` leg -/

/-- **The transported boundary gradient's cube Besov seminorm, priced on the
anchor window.** -/
theorem besovVectorSeminormTwo_datumGrad_coveringCube_le_anchorWindow [NeZero d]
    {n m : ℤ} {x z : Vec d} {s : ℝ} {H : Vec d → Vec d} (hnm : n + 2 ≤ m)
    (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hL2 : MemLp H 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hWcov : MemLp (Gagliardo.gagliardoKernel s 2 H) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 H) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s
        (fun y => H (y + wellPlacedCentre x m (n + 2))) ≤
      besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
        (gagliardoWindowConst d *
          (Support.normalizedGagliardoESeminormOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) s H).toReal) := by
  have hbase := besovVectorSeminormTwo_coveringCube_le_anchorWindow
    (g := fun y => -H y) hnm hx hgeom hs hs1 hL2.neg
    (memLp_gagliardoKernel_neg _ s hWcov) (memLp_gagliardoKernel_neg _ s hW)
  rw [normalizedGagliardoESeminormOn_neg] at hbase
  simpa only [neg_neg] using hbase

/-! ## 3. The average half of the `∇h` leg -/

/-- The Euclidean length of a vector is at most `√d` times its ambient (sup)
norm. -/
theorem sqrt_vecNormSq_le_sqrt_dim_mul_norm (v : Vec d) :
    Real.sqrt (vecNormSq v) ≤ Real.sqrt (d : ℝ) * ‖v‖ := by
  have hcoord : ∀ i : Fin d, v i * v i ≤ ‖v‖ * ‖v‖ := by
    intro i
    have h1 : |v i| ≤ ‖v‖ := by
      have h := norm_le_pi_norm v i
      rwa [Real.norm_eq_abs] at h
    have h2 : (0 : ℝ) ≤ |v i| := abs_nonneg _
    have h3 : v i * v i = |v i| * |v i| := (abs_mul_abs_self (v i)).symm
    rw [h3]
    exact mul_le_mul h1 h1 h2 (norm_nonneg v)
  have hsum : vecNormSq v ≤ (d : ℝ) * (‖v‖ * ‖v‖) := by
    rw [vecNormSq, vecDot]
    calc ∑ i : Fin d, v i * v i ≤ ∑ _i : Fin d, ‖v‖ * ‖v‖ :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * (‖v‖ * ‖v‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (vecNormSq v) ≤ Real.sqrt ((d : ℝ) * (‖v‖ * ‖v‖)) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * ‖v‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_mul_self (norm_nonneg v)]

/-- **The transported boundary gradient's cube average, priced on the anchor
window.** -/
theorem sqrt_vecNormSq_cubeAverageVec_coveringCube_le_anchorWindow {n m : ℤ}
    {x z : Vec d} {H : Vec d → Vec d} (hnm : n + 2 ≤ m)
    (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (hL2W : MemLp H 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    Real.sqrt (vecNormSq (cubeAverageVec (originCube d (n + 2))
        (fun y => H (y + wellPlacedCentre x m (n + 2))))) ≤
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
        (eLpNorm H 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
  classical
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  set cov : Set (Vec d) :=
    (fun y => c + y) '' openCubeSet (originCube d (n + 2)) with hcov
  set W : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) with hW
  have hsubcov : cov ⊆ W := image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom
  have hcovne : volume cov ≠ 0 :=
    volume_image_add_openCubeSet_ne_zero c (originCube d (n + 2))
  have hWne : volume W ≠ 0 := by
    intro h0
    exact hcovne (le_antisymm (h0 ▸ measure_mono hsubcov) (zero_le _))
  have hWtop : volume W ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_openCubeSet_ne_top (originCube d m))
      (measure_mono Set.inter_subset_right)
  have hL2cov : MemLp H 2 (Support.normalizedVolumeMeasureOn cov) :=
    memLp_normalizedVolumeMeasureOn_subset hsubcov hWne hWtop hcovne hL2W
  have hL2cube : MemLp (fun y => H (y + c)) 2
      (normalizedCubeMeasure (originCube d (n + 2))) := by
    have h := memLp_normalizedVolumeMeasureOn_image_add (p := 2) (by norm_num)
      (by norm_num) hL2cov
    rwa [normalizedVolumeMeasureOn_openCubeSet] at h
  -- the vector Jensen step on the covering cube
  have hjen : ‖cubeAverageVec (originCube d (n + 2)) (fun y => H (y + c))‖ ≤
      (eLpNorm (fun y => H (y + c)) 2
        (normalizedCubeMeasure (originCube d (n + 2)))).toReal :=
    norm_cubeAverageVec_le_cubeLpNorm_two (originCube d (n + 2)) _ hL2cube
  have hframe : eLpNorm (fun y => H (y + c)) 2
      (normalizedCubeMeasure (originCube d (n + 2))) =
      eLpNorm H 2 (Support.normalizedVolumeMeasureOn cov) := by
    rw [hcov, eLpNorm_normalizedVolumeMeasureOn_image_add c
      (openCubeSet (originCube d (n + 2))) (by norm_num) (by norm_num),
      normalizedVolumeMeasureOn_openCubeSet]
  have hmove : (eLpNorm H 2 (Support.normalizedVolumeMeasureOn cov)).toReal ≤
      (3 : ℝ) ^ d * (eLpNorm H 2 (Support.normalizedVolumeMeasureOn W)).toReal := by
    have hbase := eLpNorm_coveringCube_le_anchorWindow hnm hx hgeom H
    have hne : eLpNorm H 2 (Support.normalizedVolumeMeasureOn W) ≠ ⊤ :=
      hL2W.eLpNorm_ne_top
    have hRHSne : ENNReal.ofReal ((3 : ℝ) ^ d) *
        eLpNorm H 2 (Support.normalizedVolumeMeasureOn W) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne
    have hstep := ENNReal.toReal_mono hRHSne hbase
    rwa [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d)] at hstep
  have hsqrtd : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  calc Real.sqrt (vecNormSq (cubeAverageVec (originCube d (n + 2))
        (fun y => H (y + c))))
      ≤ Real.sqrt (d : ℝ) *
          ‖cubeAverageVec (originCube d (n + 2)) (fun y => H (y + c))‖ :=
        sqrt_vecNormSq_le_sqrt_dim_mul_norm _
    _ ≤ Real.sqrt (d : ℝ) *
          (eLpNorm (fun y => H (y + c)) 2
            (normalizedCubeMeasure (originCube d (n + 2)))).toReal :=
        mul_le_mul_of_nonneg_left hjen hsqrtd
    _ = Real.sqrt (d : ℝ) * (eLpNorm H 2 (Support.normalizedVolumeMeasureOn cov)).toReal := by
        rw [hframe]
    _ ≤ Real.sqrt (d : ℝ) *
          ((3 : ℝ) ^ d * (eLpNorm H 2 (Support.normalizedVolumeMeasureOn W)).toReal) :=
        mul_le_mul_of_nonneg_left hmove hsqrtd
    _ = Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
          (eLpNorm H 2 (Support.normalizedVolumeMeasureOn W)).toReal := by ring

/-! ## 4. The `σ` leg: the honest form and the `ν`-divided fork -/

/-- CoarseGraining's Dirichlet energy estimate at the parent-rebased family, read
through the `ν`-identification of that family: the coefficient energy of the
comparison solution *is* `ν ⨍|∇v|²`, and it is at most the square of
`dirichletEnergyWithRHSRHS`.  **Nothing is divided**: `ν` stands exactly where
CoarseGraining puts it, and no `ν⁻¹` enters any constant. -/
theorem exists_nu_mul_normalizedSetAverage_grad_le_dirichletEnergySq (d : ℕ)
    [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (L k : ℤ) (x z : Vec d) (omega : Cutoff.CutoffSample d)
        (Q : TriadicCube d) (r : ℝ) (g : Vec d → Vec d)
        (v : DirichletForcedCubeSolution Q (parentRebasedFamily M L k x z omega) g),
        0 < r → r < 1 → ForceBesovRegularity Q r g →
        ForceBesovRegularity Q r (dirichletBoundaryGradientField v) →
          M.nu * normalizedSetAverage (openCubeSet Q)
              (fun y => vecNormSq (v.toH1.grad y)) ≤
            dirichletEnergyWithRHSRHS C Q (parentRebasedFamily M L k x z omega) r g v ^
              2 := by
  obtain ⟨C, hCpos, hmain⟩ :=
    exists_localizedCoeffEnergyValue_openCubeSet_le_dirichletEnergyWithRHSRHS_sq d
  refine ⟨C, hCpos, ?_⟩
  intro M L k x z omega Q r g v hr hr1 hg hh
  have hbase := hmain (Q := Q) (a := parentRebasedFamily M L k x z omega) (r := r)
    (g := g) v hr hr1 hg hh
  rwa [localizedCoeffEnergyValue_parentRebasedFamily_eq M L k x z omega Q] at hbase

/-- **The `ν`-divided form.**  Divides the homogenized `ν · ⨍|∇v|² ≤ DirE²` by
the deterministic `ν`, introducing `ν⁻¹` into a constant the frozen clause
prices as `C(d)`.  The division is carried by the explicitly named hypothesis `hnudiv :
(M.nu)⁻¹ ≤ Knu`; no declaration of this repository supplies it, and nothing
here chooses between this form and
`exists_nu_mul_normalizedSetAverage_grad_le_dirichletEnergySq`. -/
theorem exists_normalizedSetAverage_grad_le_dirichletEnergySq_of_nuDivision (d : ℕ)
    [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (L k : ℤ) (x z : Vec d) (omega : Cutoff.CutoffSample d)
        (Q : TriadicCube d) (r : ℝ) (g : Vec d → Vec d)
        (v : DirichletForcedCubeSolution Q (parentRebasedFamily M L k x z omega) g)
        (Knu : ℝ), (M.nu : ℝ)⁻¹ ≤ Knu →
        0 < r → r < 1 → ForceBesovRegularity Q r g →
        ForceBesovRegularity Q r (dirichletBoundaryGradientField v) →
          normalizedSetAverage (openCubeSet Q)
              (fun y => vecNormSq (v.toH1.grad y)) ≤
            Knu *
              dirichletEnergyWithRHSRHS C Q (parentRebasedFamily M L k x z omega) r g
                v ^ 2 := by
  obtain ⟨C, hCpos, hmain⟩ :=
    exists_nu_mul_normalizedSetAverage_grad_le_dirichletEnergySq d
  refine ⟨C, hCpos, ?_⟩
  intro M L k x z omega Q r g v Knu hnudiv hr hr1 hg hh
  have hbase := hmain M L k x z omega Q r g v hr hr1 hg hh
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hsq : (0 : ℝ) ≤
      dirichletEnergyWithRHSRHS C Q (parentRebasedFamily M L k x z omega) r g v ^ 2 :=
    sq_nonneg _
  have hstep := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hnu.le)
  rw [inv_mul_cancel_left₀ (ne_of_gt hnu)] at hstep
  exact hstep.trans (mul_le_mul_of_nonneg_right hnudiv hsq)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
