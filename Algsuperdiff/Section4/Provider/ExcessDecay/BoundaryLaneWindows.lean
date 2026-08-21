/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorGeometry

/-!
# The truncated comparison windows of the boundary lane, and the choice `y := x`

The §4.3 boundary regime works on the *truncated* windows

```text
  W_j := (x + □_{n-j}) ∩ □_m ,        V := W_2 = (x + □_{n-2}) ∩ □_m ,
```

which are the windows of `l.excess.decay.good.scales` read through the replacement draft's
item 2 (the lemma `l.comparison.reduction`).  This
module proves their geometry and the one statement the draft calls the *window choice*.

## The window choice

The printed proof asks for a point `y ∈ □_m` with **both**

```text
  y + □_{n-2} ⊆ (z + □_n) ∩ □_m       and      (x + □_{n-2}) ∩ □_m ⊆ y + □_{n-2} ,
```

and the graph records the gap: "the existence of `y` with BOTH inclusions is
asserted with no construction, and in the boundary case the two requirements
pull against each other" — indeed the first inclusion is *false* at a boundary
point `x`, because the full cube `y + □_{n-2}` then leaves `□_m`.

The draft's correction is `y := x` together with the move of the
comparison function onto the truncated window: the pair of requirements
becomes

```text
  V = (x + □_{n-2}) ∩ □_m ⊆ (z + □_n) ∩ □_m       and      W_2 = V ,
```

and both are then immediate from `x ∈ (z + □_{n-3}) ∩ □_m`.  That is
`truncatedWindow_subset_of_windowChoice` and `truncatedWindow_two_eq_V` below;
`windowChoice_y_eq_x` packages the pair.

## What is not done here

Nothing analytic: no harmonic function, no excess, no Caccioppoli estimate.  In
particular this module does **not** provide the volume-ratio (`window sandwich`)
constant `K_vol` of the draft's §0 — only the qualitative positivity of the
window volume, which is what the excess normalizers need to be finite.

## References

* ABK26, `l.excess.decay.good.scales`, (windows).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization Homogenization.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. A general inclusion for translated origin cubes -/

/-- **A translated cube inside a bigger cube.**  If the centre `w` lies in
`□_a` and the side lengths satisfy `3^a + 3^k ≤ 3^b`, then `w + □_k ⊆ □_b`.

This is the only cube arithmetic the boundary lane's window choice needs; the
interior lane's `image_add_openCubeSet_subset_succ_succ` is the special case
`a = n+1`, `b = n+2`. -/
theorem image_add_openCubeSet_subset_of_mem {a b k : ℤ} {w : Vec d}
    (hw : w ∈ openCubeSet (originCube d a))
    (hside : (3 : ℝ) ^ a + (3 : ℝ) ^ k ≤ (3 : ℝ) ^ b) :
    (fun y => w + y) '' openCubeSet (originCube d k) ⊆
      openCubeSet (originCube d b) := by
  rintro p ⟨y, hy, rfl⟩
  rw [mem_openCubeSet_originCube_iff] at hw hy ⊢
  intro i
  have h1 := hw i
  have h2 := hy i
  refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply] <;>
    linarith only [h1.1, h1.2, h2.1, h2.2, hside]

/-! ## 2. The truncated windows -/

/-- **The truncated window** `(x + □_k) ∩ □_m` of the §4.3 boundary regime, in the
frozen theorem's own carrier shape (a translation *image* of an origin cube,
intersected with the domain cube). -/
def truncatedWindow (x : Vec d) (m k : ℤ) : Set (Vec d) :=
  ((fun y => x + y) '' openCubeSet (originCube d k)) ∩
    openCubeSet (originCube d m)

theorem truncatedWindow_eq_inter_openCubeAtScale (x : Vec d) (m k : ℤ) :
    truncatedWindow x m k =
      openCubeAtScale x k ∩ openCubeSet (originCube d m) := by
  rw [truncatedWindow, openCubeAtScale_eq_image_add]

theorem truncatedWindow_subset_translate (x : Vec d) (m k : ℤ) :
    truncatedWindow x m k ⊆ (fun y => x + y) '' openCubeSet (originCube d k) :=
  Set.inter_subset_left

theorem truncatedWindow_subset_domain (x : Vec d) (m k : ℤ) :
    truncatedWindow x m k ⊆ openCubeSet (originCube d m) :=
  Set.inter_subset_right

/-- The truncated windows are nested in the scale. -/
theorem truncatedWindow_mono (x : Vec d) (m : ℤ) {k l : ℤ} (hkl : k ≤ l) :
    truncatedWindow x m k ⊆ truncatedWindow x m l := by
  refine Set.inter_subset_inter_left _ ?_
  rintro p ⟨y, hy, rfl⟩
  exact ⟨y, openCubeSet_originCube_subset_of_le hkl hy, rfl⟩

/-- The centre of a truncated window lies in it, as soon as it lies in the
domain cube. -/
theorem mem_truncatedWindow_self {x : Vec d} {m : ℤ} (k : ℤ)
    (hx : x ∈ openCubeSet (originCube d m)) : x ∈ truncatedWindow x m k :=
  ⟨⟨0, zero_mem_openCubeSet_originCube d k, by simp⟩, hx⟩

theorem truncatedWindow_nonempty {x : Vec d} {m : ℤ} (k : ℤ)
    (hx : x ∈ openCubeSet (originCube d m)) :
    (truncatedWindow x m k).Nonempty :=
  ⟨x, mem_truncatedWindow_self k hx⟩

/-! ## 3. The windows are open bounded convex domains -/

/-- The intersection of two open bounded convex domains is one. -/
theorem isOpenBoundedConvexDomain_inter {U V : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hV : IsOpenBoundedConvexDomain V) :
    IsOpenBoundedConvexDomain (U ∩ V) := by
  obtain ⟨R, hRpos, hR⟩ := hU.isBoundedDomain
  exact ⟨hU.isOpen.inter hV.isOpen, ⟨R, hRpos, fun y hy i => hR y hy.1 i⟩,
    hU.convex.inter hV.convex⟩

theorem isOpenBoundedConvexDomain_truncatedWindow (x : Vec d) (m k : ℤ) :
    IsOpenBoundedConvexDomain (truncatedWindow x m k) := by
  refine isOpenBoundedConvexDomain_inter ?_ (isOpenBoundedConvexDomain_openCubeSet _)
  rw [image_add_eq_translateSet]
  exact (isOpenBoundedConvexDomain_openCubeSet (originCube d k)).translateSet x

theorem isOpen_truncatedWindow (x : Vec d) (m k : ℤ) :
    IsOpen (truncatedWindow x m k) :=
  (isOpenBoundedConvexDomain_truncatedWindow x m k).isOpen

theorem convex_truncatedWindow (x : Vec d) (m k : ℤ) :
    Convex ℝ (truncatedWindow x m k) :=
  (isOpenBoundedConvexDomain_truncatedWindow x m k).convex

theorem volume_truncatedWindow_lt_top (x : Vec d) (m k : ℤ) :
    MeasureTheory.volume (truncatedWindow x m k) < ⊤ :=
  (isOpenBoundedConvexDomain_truncatedWindow x m k).volume_lt_top

/-- A truncated window centred in the domain cube has positive volume: it is a
nonempty open set. -/
theorem volume_truncatedWindow_pos {x : Vec d} {m : ℤ} (k : ℤ)
    (hx : x ∈ openCubeSet (originCube d m)) :
    0 < MeasureTheory.volume (truncatedWindow x m k) :=
  (isOpen_truncatedWindow x m k).measure_pos MeasureTheory.volume
    (truncatedWindow_nonempty k hx)

/-! ## 4. The window choice `y := x` -/

/-- The printed hypothesis `x ∈ (z + □_j) ∩ □_m` in its difference form. -/
theorem sub_mem_openCubeSet_of_mem_truncatedWindow {j m : ℤ} {x z : Vec d}
    (hx : x ∈ truncatedWindow z m j) :
    x - z ∈ openCubeSet (originCube d j) := by
  obtain ⟨y0, hy0mem, hy0⟩ := hx.1
  have hxy : x - z = y0 := by
    rw [← hy0]
    exact add_sub_cancel_left z y0
  rwa [hxy]

/-- **The window choice, first inclusion.**

If `x` lies in the printed window `(z + □_{n-3}) ∩ □_m`, then every truncated
window `(x + □_k) ∩ □_m` with `k ≤ n-2` sits inside `(z + □_{n-1}) ∩ □_m`, and
hence (`truncatedWindow_mono`) inside `(z + □_n) ∩ □_m`.

This is the inclusion the printed proof asks of its auxiliary point `y`, now
proved at `y := x` on the truncated window; the printed requirement on the
*full* cube `y + □_{n-2}` is not available in the boundary regime and is not
used. -/
theorem truncatedWindow_subset_of_windowChoice {m n k : ℤ} {x z : Vec d}
    (hx : x ∈ truncatedWindow z m (n - 3)) (hk : k ≤ n - 2) :
    truncatedWindow x m k ⊆ truncatedWindow z m (n - 1) := by
  have hside : (3 : ℝ) ^ (n - 3) + (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (n - 1) := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
    have hkle : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (n - 2) :=
      zpow_le_zpow_right₀ (by norm_num) hk
    have h2 : (3 : ℝ) ^ (n - 2) = (3 : ℝ) ^ (n - 3) * 3 := by
      rw [show n - 2 = n - 3 + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    have h1 : (3 : ℝ) ^ (n - 1) = (3 : ℝ) ^ (n - 3) * 9 := by
      rw [show n - 1 = n - 3 + 2 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [h1]
    linarith only [hkle, h2, h3]
  have hkey : (fun y => (x - z) + y) '' openCubeSet (originCube d k) ⊆
      openCubeSet (originCube d (n - 1)) :=
    image_add_openCubeSet_subset_of_mem
      (sub_mem_openCubeSet_of_mem_truncatedWindow hx) hside
  refine Set.inter_subset_inter_left _ ?_
  rintro p ⟨y, hy, rfl⟩
  refine ⟨(x - z) + y, hkey ⟨y, hy, rfl⟩, ?_⟩
  show z + ((x - z) + y) = x + y
  abel

/-- **The window choice, packaged.**

At `y := x` both requirements hold on the truncated windows: `V:= (x + □_{n-2})
∩ □_m` is contained in `(z + □_n) ∩ □_m` (the printed first inclusion, read on
the truncated window), and `V ⊆ x + □_{n-2}` (the printed second inclusion at
`y := x`, which is now definitional).  This is the window choice the printed
proof asks for. -/
theorem windowChoice_y_eq_x {m n : ℤ} {x z : Vec d}
    (hx : x ∈ truncatedWindow z m (n - 3)) :
    truncatedWindow x m (n - 2) ⊆ truncatedWindow z m n ∧
      truncatedWindow x m (n - 2) ⊆
        (fun y => x + y) '' openCubeSet (originCube d (n - 2)) := by
  refine ⟨?_, truncatedWindow_subset_translate x m (n - 2)⟩
  refine subset_trans (truncatedWindow_subset_of_windowChoice hx le_rfl) ?_
  exact truncatedWindow_mono z m (by linarith only [] : n - 1 ≤ n)

/-- The comparison window `V` sits inside the *outer* window `W_0 = (x+□_n) ∩ □_m`
of the boundary lane: the draft's `W_j` family is nested. -/
theorem truncatedWindow_two_subset_zero (x : Vec d) (m n : ℤ) :
    truncatedWindow x m (n - 2) ⊆ truncatedWindow x m n :=
  truncatedWindow_mono x m (by linarith only [] : n - 2 ≤ n)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
