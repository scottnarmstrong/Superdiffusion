/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringGeometry

/-!
# Where the boundary covering cube sits relative to the good-event slot

```text
  max { σ̄_{n+2}⁻¹ Λ_{s/8,2}(□_{n+2}; ã) , σ̄_{n+2} λ_{s/8,2}(□_{n+2}; ã)⁻¹ }
```

at the sample `τ_z ω` — physically the cube `z + □_{n+2}`.  So the question is
one about **two cubes of the same scale**:
`c + □_{n+2}` versus `z + □_{n+2}`.

This module answers it geometrically, in both directions.

* `eq_of_image_add_openCubeSet_subset` — two open triadic cubes of the *same*
  scale are nested only when their centres coincide.
* `inter_frontier_eq_empty_of_subset_openCubeSet` — a set inside the open cube
  `□_m` misses `∂□_m`.
* `gate_of_coveringCube_subset_slot` — **the obstruction.**  Any centre `c` whose
  cube `c + □_{n+2}` both (i) stays inside `□_m` (which the boundary lane
  *requires*: the anchor's solution `u` lives on `□_m` only) and (ii) stays
  inside the good-event slot's cube `z + □_{n+2}`, forces the anchor's own
  **interior gate** `(z + □_{n+2}) ∩ ∂□_m = ∅`.  Contrapositive: on the branch
  the interior chain leaves open — the boundary regime — *no* admissible covering
  cube of the covering scale fits inside the slot cube, so no covering,
  subadditivity or descendant argument indexed by `𝒢(n+2, z)` can reach the
  covering cube's ellipticity data.
* `image_add_wellPlacedCentre_subset_image_add_openCubeSet_succ` — **the
  positive half.**  The covering cube always fits inside `z + □_{k+1}`; at `k =
  n+2` that is `z + □_{n+3}`, the anchor's own window cube.  So a slot at index `n+3`
  *does* reach it, and the proved off-grid transport
  (`OffGridComposeAssembly`/`OffGridErrorFluxCorrected`, which require exactly
  a containment `w + □_k ⊆ □_K` of the off-grid cube in a grid cube) applies
  with `K = n+3` at depth one.

Nothing here transports any coefficient, error or ellipticity quantity: this
module is pure cube geometry, exactly like `BoundaryCoveringGeometry`.  In
particular nothing below is an instance, or a fraction, of any source node.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the boundary application of
  `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Two open cubes of the same scale -/

/-- If a real number can be shifted by every element of `(-H, H)` and stay in
`(-H, H)`, it is zero. -/
private theorem eq_zero_of_shift_bounds {H delta : ℝ} (hH : 0 < H)
    (h : ∀ t : ℝ, -H < t → t < H → -H < delta + t ∧ delta + t < H) : delta = 0 := by
  rcases lt_trichotomy delta 0 with hd | hd | hd
  · exfalso
    rcases le_or_gt H (-delta) with hb | hb
    · have hzero := (h 0 (by linarith only [hH]) hH).1
      linarith only [hzero, hb]
    · have h1 : -H < -H + (-delta) / 2 := by linarith only [hd]
      have h2 : -H + (-delta) / 2 < H := by linarith only [hb, hH]
      have hstep := (h (-H + (-delta) / 2) h1 h2).1
      linarith only [hstep, hd]
  · exact hd
  · exfalso
    rcases le_or_gt H delta with hb | hb
    · have hzero := (h 0 (by linarith only [hH]) hH).2
      linarith only [hzero, hb]
    · have h1 : -H < H - delta / 2 := by linarith only [hb, hH]
      have h2 : H - delta / 2 < H := by linarith only [hd]
      have hstep := (h (H - delta / 2) h1 h2).2
      linarith only [hstep, hd]

/-- Half the side of `□_j` is positive. -/
private theorem half_three_zpow_pos (j : ℤ) : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  linarith only [h3]

/-- **Same-scale translates are nested only when equal.**

`a + □_j ⊆ b + □_j` forces `a = b`.  This is the geometric core: the
boundary covering cube and the good-event slot's cube have the *same* scale
`n+2`, so one sits inside the other only in the degenerate case. -/
theorem eq_of_image_add_openCubeSet_subset {j : ℤ} {a b : Vec d}
    (h : (fun y => a + y) '' openCubeSet (originCube d j) ⊆
      (fun y => b + y) '' openCubeSet (originCube d j)) : a = b := by
  classical
  funext i
  have hH : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ j := half_three_zpow_pos j
  have hkey : a i - b i = 0 := by
    refine eq_zero_of_shift_bounds hH (fun t ht1 ht2 => ?_)
    have hmem : Pi.single i t ∈ openCubeSet (originCube d j) := by
      rw [mem_openCubeSet_originCube_iff]
      intro l
      by_cases hl : l = i
      · subst hl
        rw [Pi.single_eq_same]
        exact ⟨by linarith only [ht1], by linarith only [ht2]⟩
      · rw [Pi.single_eq_of_ne hl]
        exact ⟨by linarith only [hH], hH⟩
    have hp : a + Pi.single i t ∈ (fun y => a + y) '' openCubeSet (originCube d j) :=
      ⟨Pi.single i t, hmem, rfl⟩
    have hq := h hp
    rw [mem_image_add_iff, mem_openCubeSet_originCube_iff] at hq
    have hqi := hq i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.single_eq_same] at hqi
    exact ⟨by linarith only [hqi.1], by linarith only [hqi.2]⟩
  linarith only [hkey]

/-! ## 2. The frontier gate from a containment in `□_m` -/

/-- A set contained in the *open* cube `□_m` misses `∂□_m`. -/
theorem inter_frontier_eq_empty_of_subset_openCubeSet {m : ℤ} {S : Set (Vec d)}
    (h : S ⊆ openCubeSet (originCube d m)) :
    S ∩ frontier (openCubeSet (originCube d m)) = ∅ := by
  have hopen : IsOpen (openCubeSet (originCube d m)) := isOpen_openCubeSet _
  refine Set.eq_empty_of_subset_empty ?_
  rw [← hopen.inter_frontier_eq]
  exact Set.inter_subset_inter_left _ h

/-! ## 3. The obstruction -/

/-- **The obstruction.**

If some centre `c` has its covering cube `c + □_{n+2}` inside the anchor's domain
`□_m` *and* inside the good-event slot's cube `z + □_{n+2}`, then the anchor's own
**interior gate** holds.

Read contrapositively: on the boundary branch — the one the interior chain
(`GeneralClauseInteriorFinal`) leaves open, where `(z+□_{n+2}) ∩ ∂□_m ≠ ∅` —
every admissible covering cube of the covering scale leaves the slot cube.
Since every proved transport of the flux-corrected error to an off-grid cube
(`OffGridComposeAssembly`, `OffGridErrorFluxCorrected`) requires the off-grid
cube to be *contained* in the grid cube carrying the error, the good event
`𝒢(n+2, z; s/8, 1/2)` cannot supply the covering cube's ellipticity data. -/
theorem gate_of_coveringCube_subset_slot {k m : ℤ} {c z : Vec d}
    (hdom : (fun y => c + y) '' openCubeSet (originCube d k) ⊆
      openCubeSet (originCube d m))
    (hslot : (fun y => c + y) '' openCubeSet (originCube d k) ⊆
      (fun y => z + y) '' openCubeSet (originCube d k)) :
    ((fun y => z + y) '' openCubeSet (originCube d k)) ∩
      frontier (openCubeSet (originCube d m)) = ∅ := by
  have hcz : c = z := eq_of_image_add_openCubeSet_subset hslot
  refine inter_frontier_eq_empty_of_subset_openCubeSet ?_
  rw [← hcz]
  exact hdom

/-- The obstruction at the boundary lane's own covering cube: the well-placed
cube always satisfies the domain requirement, so the slot containment alone
forces the interior gate. -/
theorem gate_of_wellPlacedCentre_subset_slot {k m : ℤ} {x z : Vec d} (hkm : k ≤ m)
    (hslot : (fun y => wellPlacedCentre x m k + y) '' openCubeSet (originCube d k) ⊆
      (fun y => z + y) '' openCubeSet (originCube d k)) :
    ((fun y => z + y) '' openCubeSet (originCube d k)) ∩
      frontier (openCubeSet (originCube d m)) = ∅ :=
  gate_of_coveringCube_subset_slot
    (image_add_wellPlacedCentre_subset_openCubeSet x hkm) hslot

/-! ## 4. The positive half: the covering cube fits one scale up -/

private theorem three_zpow_succ (j : ℤ) : (3 : ℝ) ^ (j + 1) = 3 * (3 : ℝ) ^ j := by
  rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) j 1, zpow_one]
  ring

/-- The clamp moves each coordinate by less than half a side of `□_k`. -/
theorem sub_wellPlacedCentre_coord_bound {m k : ℤ} (hkm : k ≤ m) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (i : Fin d) :
    -((1 / 2 : ℝ) * (3 : ℝ) ^ k) < x i - wellPlacedCentre x m k i ∧
      x i - wellPlacedCentre x m k i < (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
  have hA : (0 : ℝ) ≤ wellPlacedHalfGap m k := wellPlacedHalfGap_nonneg hkm
  have hAdef : wellPlacedHalfGap m k =
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k := rfl
  have hk : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ k := half_three_zpow_pos k
  rw [mem_openCubeSet_originCube_iff] at hx
  have hxi := hx i
  rcases le_total (x i) (-wellPlacedHalfGap m k) with h1 | h1
  · have hc : wellPlacedCentre x m k i = -wellPlacedHalfGap m k := by
      rw [wellPlacedCentre, min_eq_right (h1.trans (by linarith only [hA]))]
      exact max_eq_left h1
    rw [hc, hAdef] at *
    exact ⟨by linarith only [hxi.1], by linarith only [h1, hk]⟩
  · rcases le_total (x i) (wellPlacedHalfGap m k) with h2 | h2
    · have hc : wellPlacedCentre x m k i = x i := by
        rw [wellPlacedCentre, min_eq_right h2]
        exact max_eq_right h1
      rw [hc]
      exact ⟨by linarith only [hk], by linarith only [hk]⟩
    · have hc : wellPlacedCentre x m k i = wellPlacedHalfGap m k := by
        rw [wellPlacedCentre, min_eq_left h2]
        exact max_eq_right (by linarith only [h2, hA])
      rw [hc, hAdef] at *
      exact ⟨by linarith only [h2, hk], by linarith only [hxi.2]⟩

/-- **The positive half.**

The boundary covering cube always sits inside `z + □_{k+1}`, provided the window
centre `x` is within half a side of `□_{k-1}` of `z` — which is exactly what the
anchor's geometry binder gives at `k = n+2`.

Consequently a good-event slot at index `n+3` *does* reach the covering cube:
the proved off-grid transports require precisely a containment of the off-grid
cube in a grid cube, and this is that containment at depth one. -/
theorem image_add_wellPlacedCentre_subset_image_add_openCubeSet_succ {m k : ℤ}
    {x z : Vec d} (hkm : k ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hxz : x - z ∈ openCubeSet (originCube d (k - 1))) :
    (fun y => wellPlacedCentre x m k + y) '' openCubeSet (originCube d k) ⊆
      (fun y => z + y) '' openCubeSet (originCube d (k + 1)) := by
  have hkk : (3 : ℝ) ^ k = 3 * (3 : ℝ) ^ (k - 1) := by
    have hrw : k = (k - 1) + 1 := by ring
    rw [hrw, three_zpow_succ (k - 1)]
    ring_nf
  have hk1 : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := three_zpow_succ k
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (k - 1) := zpow_pos (by norm_num) (k - 1)
  rw [mem_openCubeSet_originCube_iff] at hxz
  intro p hp
  rw [mem_image_add_iff, mem_openCubeSet_originCube_iff] at hp
  rw [mem_image_add_iff, mem_openCubeSet_originCube_iff]
  intro i
  have h1 := hp i
  have h2 := sub_wellPlacedCentre_coord_bound hkm hx i
  have h3 := hxz i
  simp only [Pi.sub_apply] at h1 h3 ⊢
  constructor
  · linarith only [h1.1, h2.2, h3.1, hkk, hk1, hpos]
  · linarith only [h1.2, h2.1, h3.2, hkk, hk1, hpos]

/-- The anchor's geometry binder, read as a bound on `x - z`. -/
theorem sub_mem_openCubeSet_of_anchorGeometry {n m : ℤ} {x z : Vec d}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    x - z ∈ openCubeSet (originCube d (n + 1)) := by
  have hzero : (0 : Vec d) ∈ openCubeSet (originCube d n) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have h := half_three_zpow_pos n
    refine ⟨?_, ?_⟩ <;> simp only [Pi.zero_apply] <;> linarith only [h]
  have hx : x ∈ (fun y => x + y) '' openCubeSet (originCube d n) :=
    ⟨0, hzero, by simp⟩
  have h := (hgeom hx).1
  rwa [mem_image_add_iff] at h

/-- **The covering cube inside the anchor's own window cube.**

At the boundary lane's covering scale `k = n+2`, under the frozen theorem's own
binders, `c + □_{n+2} ⊆ z + □_{n+3}`.  Together with
`gate_of_wellPlacedCentre_subset_slot` this is the exact measurement: the
covering cube is outside the `n+2` slot on the boundary branch, and inside the
`n+3` one always. -/
theorem image_add_wellPlacedCentre_subset_anchorParent {n m : ℤ} {x z : Vec d}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    (fun y => wellPlacedCentre x m (n + 2) + y) '' openCubeSet (originCube d (n + 2)) ⊆
      (fun y => z + y) '' openCubeSet (originCube d (n + 3)) := by
  have hxz : x - z ∈ openCubeSet (originCube d (n + 2 - 1)) := by
    have h := sub_mem_openCubeSet_of_anchorGeometry hgeom
    have hrw : n + 2 - 1 = n + 1 := by ring
    rw [hrw]
    exact h
  have hbase := image_add_wellPlacedCentre_subset_image_add_openCubeSet_succ
    (k := n + 2) (m := m) hnm hx hxz
  have hrw : n + 2 + 1 = n + 3 := by ring
  rwa [hrw] at hbase

end

end Algsuperdiff.Section4.Provider.ExcessDecay
