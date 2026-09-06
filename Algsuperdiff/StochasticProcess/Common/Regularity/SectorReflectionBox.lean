/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Algsuperdiff.StochasticProcess.Common.Regularity.SectorReflectionGeometry
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryWindowPoincare

/-!
# Axis-cube windows as Euclidean ball sectors

This file constructs the face set and signs for a point in the closure of an
axis cube.  Under the explicit clearance from every face not passing through
the point, intersection with a centred Euclidean ball is exactly the canonical
`ballSector` used by the reflection layer.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity

open Homogenization
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-- Coordinate faces of `axisCube z L` which pass through `x₀`. -/
def axisCubeFaceSet (z : Vec d) (L : ℝ) (x₀ : Vec d) : Finset (Fin d) :=
  Finset.univ.filter fun i => x₀ i = z i ∨ x₀ i = z i + L

/-- The sign selecting the cube side at a face through `x₀`: `-1` at a
lower face and `1` at an upper face. -/
def axisCubeFaceOrientation (z : Vec d) (x₀ : Vec d) : Fin d → ℝ :=
  fun i => if x₀ i = z i then -1 else 1

theorem mem_axisCubeFaceSet_iff {z : Vec d} {L : ℝ} {x₀ : Vec d} {i : Fin d} :
    i ∈ axisCubeFaceSet z L x₀ ↔ x₀ i = z i ∨ x₀ i = z i + L := by
  simp only [axisCubeFaceSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem abs_axisCubeFaceOrientation (z x₀ : Vec d) (i : Fin d) :
    |axisCubeFaceOrientation z x₀ i| = 1 := by
  unfold axisCubeFaceOrientation
  by_cases hi : x₀ i = z i
  · rw [if_pos hi]
    norm_num
  · rw [if_neg hi]
    norm_num

/-- Explicit closure-coordinate data for an axis cube. -/
def MemAxisCubeClosure (z : Vec d) (L : ℝ) (x₀ : Vec d) : Prop :=
  ∀ i, z i ≤ x₀ i ∧ x₀ i ≤ z i + L

/-- The ball radius does not reach a lower or upper coordinate face unless
that face passes through `x₀`. -/
def AxisCubeFaceClearance (z : Vec d) (L r : ℝ) (x₀ : Vec d) : Prop :=
  (∀ i, x₀ i ≠ z i → r ≤ x₀ i - z i) ∧
    ∀ i, x₀ i ≠ z i + L → r ≤ z i + L - x₀ i

/-- A ball meeting no unlisted axis-cube face cuts out precisely the sector
selected by the faces through its centre. -/
theorem euclideanBall_inter_axisCube_eq_ballSector
    (z : Vec d) {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (x₀ : Vec d)
    (hclear : AxisCubeFaceClearance z L r x₀) :
    euclideanBall x₀ r ∩ axisCube z L =
      ballSector x₀ r (axisCubeFaceSet z L x₀)
        (axisCubeFaceOrientation z x₀) := by
  ext y
  rw [Set.mem_inter_iff, mem_axisCube_iff, mem_ballSector_iff]
  constructor
  · rintro ⟨hyB, hyQ⟩
    refine ⟨hyB, fun i hiFace => ?_⟩
    rw [mem_axisCubeFaceSet_iff] at hiFace
    rcases hiFace with hiLower | hiUpper
    · unfold axisCubeFaceOrientation
      rw [if_pos hiLower]
      have hyLower := (hyQ i).1
      rw [← hiLower] at hyLower
      linarith only [hyLower]
    · have hiNotLower : x₀ i ≠ z i := by
        intro hiLower
        have hLzero : L = 0 := by linarith only [hiLower, hiUpper]
        have hy := hyQ i
        rw [← hiLower, hLzero, add_zero] at hy
        exact lt_asymm hy.1 hy.2
      unfold axisCubeFaceOrientation
      rw [if_neg hiNotLower]
      have hyUpper := (hyQ i).2
      rw [← hiUpper] at hyUpper
      linarith only [hyUpper]
  · rintro ⟨hyB, hySector⟩
    refine ⟨hyB, fun i => ?_⟩
    have habs : |y i - x₀ i| < r := by
      apply abs_lt_of_sq_lt_sq _ hr.le
      exact (sq_coord_sub_le_euclideanSqDist y x₀ i).trans_lt hyB
    have hleft : -r < y i - x₀ i := (abs_lt.mp habs).1
    have hright : y i - x₀ i < r := (abs_lt.mp habs).2
    constructor
    · by_cases hiLower : x₀ i = z i
      · have hiFace : i ∈ axisCubeFaceSet z L x₀ :=
          mem_axisCubeFaceSet_iff.mpr (Or.inl hiLower)
        have hs := hySector i hiFace
        unfold axisCubeFaceOrientation at hs
        rw [if_pos hiLower] at hs
        linarith only [hs, hiLower.le, hiLower.symm.le]
      · have hc := hclear.1 i hiLower
        linarith only [hleft, hc]
    · by_cases hiUpper : x₀ i = z i + L
      · have hiFace : i ∈ axisCubeFaceSet z L x₀ :=
          mem_axisCubeFaceSet_iff.mpr (Or.inr hiUpper)
        have hs := hySector i hiFace
        have hiNotLower : x₀ i ≠ z i := by
          intro hiLower
          have hLzero : L = 0 := by linarith only [hiLower, hiUpper]
          linarith only [hL, hLzero]
        unfold axisCubeFaceOrientation at hs
        rw [if_neg hiNotLower] at hs
        linarith only [hs, hiUpper.le, hiUpper.symm.le]
      · have hc := hclear.2 i hiUpper
        linarith only [hright, hc]

end

end Algsuperdiff.StochasticProcess.Common.Regularity
