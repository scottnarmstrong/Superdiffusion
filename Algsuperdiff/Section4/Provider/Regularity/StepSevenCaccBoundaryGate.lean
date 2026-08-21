/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootInterfaceGate
import Algsuperdiff.Section4.Provider.ExcessDecay.CoveringSlotObstruction

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 0. Triadic arithmetic -/

/-- `3^j = 3·3^{j-1}`, the only scale identity this module uses. -/
theorem three_zpow_pred (j : ℤ) : (3 : ℝ) ^ j = 3 * (3 : ℝ) ^ (j - 1) := by
  rw [show j = (j - 1) + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  ring_nf

/-- Half a triadic side is positive. -/
theorem half_three_zpow_pos' (j : ℤ) : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  linarith only [h3]

/-- Scale monotonicity of the translated open cubes. -/
theorem openCubeAtScale_mono {k l : ℤ} (hkl : k ≤ l) (x : Vec d) :
    openCubeAtScale x k ⊆ openCubeAtScale x l := by
  rw [openCubeAtScale_eq_image_add, openCubeAtScale_eq_image_add]
  exact Set.image_mono (openCubeSet_originCube_subset_of_le hkl)

/-! ## 1. The positive half: the clamped outer cube at the sharp gate -/

/-- **The clamp displacement is exactly the Dirichlet-patch budget.**

Under the gate `z + □_{j-1} ⊆ □_m` the well-placed centre `c` moves `z` by at
most `3^{j-1} = ½(3^j − 3^{j-1})`, which is precisely the room CoarseGraining's
patch binder leaves. -/
theorem abs_sub_wellPlacedCentre_le_of_gate {m j : ℤ} (hjm : j ≤ m) {z : Vec d}
    (hgate : (fun y => z + y) '' openCubeSet (originCube d (j - 1)) ⊆
      openCubeSet (originCube d m)) (i : Fin d) :
    |z i - wellPlacedCentre z m j i| ≤ (3 : ℝ) ^ (j - 1) := by
  have hcoord := (image_add_subset_openCubeSet_iff.mp hgate) i
  have hG : 0 ≤ wellPlacedHalfGap m j := wellPlacedHalfGap_nonneg hjm
  have hGdef : wellPlacedHalfGap m j =
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ j := rfl
  have hstep : (3 : ℝ) ^ j = 3 * (3 : ℝ) ^ (j - 1) := three_zpow_pred j
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (j - 1) := zpow_pos (by norm_num) (j - 1)
  have hzu : z i ≤ |z i| := le_abs_self _
  have hzl : -(z i) ≤ |z i| := neg_le_abs _
  rw [abs_le]
  rcases le_total (z i) (-wellPlacedHalfGap m j) with h1 | h1
  · have hc : wellPlacedCentre z m j i = -wellPlacedHalfGap m j := by
      rw [wellPlacedCentre, min_eq_right (h1.trans (by linarith only [hG]))]
      exact max_eq_left h1
    rw [hGdef] at h1
    rw [hc, hGdef]
    constructor
    · linarith only [hcoord, hzl, hstep]
    · linarith only [h1, hpos]
  · rcases le_total (z i) (wellPlacedHalfGap m j) with h2 | h2
    · have hc : wellPlacedCentre z m j i = z i := by
        rw [wellPlacedCentre, min_eq_right h2]
        exact max_eq_right h1
      rw [hc]
      constructor <;> linarith only [hpos]
    · have hc : wellPlacedCentre z m j i = wellPlacedHalfGap m j := by
        rw [wellPlacedCentre, min_eq_left h2]
        exact max_eq_right (by linarith only [h2, hG])
      rw [hGdef] at h2
      rw [hc, hGdef]
      constructor
      · linarith only [h2, hpos]
      · linarith only [hcoord, hzu, hstep]

/-- **CoarseGraining's Dirichlet-patch binder at the clamped outer cube.**

`(z − c) + □_{j-1} ⊆ □_j` — the hypothesis `openCubeAtScale x (Q.scale − 1) ⊆
openCubeSet Q` of the zero-datum coarse Caccioppoli, discharged at `Q = □_j`,
`x = z − c`. -/
theorem openCubeAtScale_sub_wellPlacedCentre_subset_of_gate {m j : ℤ} (hjm : j ≤ m)
    {z : Vec d} (hgate : (fun y => z + y) '' openCubeSet (originCube d (j - 1)) ⊆
      openCubeSet (originCube d m)) :
    openCubeAtScale (z - wellPlacedCentre z m j) (j - 1) ⊆
      openCubeSet (originCube d j) := by
  rw [openCubeAtScale_eq_image_add]
  refine image_add_subset_openCubeSet_of_forall_abs_le fun i => ?_
  have hd := abs_sub_wellPlacedCentre_le_of_gate hjm hgate i
  have hstep : (3 : ℝ) ^ j = 3 * (3 : ℝ) ^ (j - 1) := three_zpow_pred j
  have hrw : (z - wellPlacedCentre z m j) i = z i - wellPlacedCentre z m j i := rfl
  rw [hrw]
  linarith only [hd, hstep]

/-- **The core is the untruncated small cube.**  With the patch binder in force
CoarseGraining's intersection is inert: `caccioppoliCoreSet (□_j) x = x +
□_{j-2}`. -/
theorem caccioppoliCoreSet_eq_of_patch {j : ℤ} {x : Vec d}
    (hpatch : openCubeAtScale x (j - 1) ⊆ openCubeSet (originCube d j)) :
    caccioppoliCoreSet (originCube d j) x = openCubeAtScale x (j - 2) := by
  have hsc : (originCube d j).scale = j := scale_originCube d j
  have hsub : openCubeAtScale x ((originCube d j).scale - 2) ⊆
      openCubeSet (originCube d j) := by
    rw [hsc]
    exact (openCubeAtScale_mono (by omega) x).trans hpatch
  rw [caccioppoliCoreSet_eq_of_subset hsub, hsc]

/-- **The window IS the Caccioppoli core, in the global frame.**

Under the gate `z + □_{j-1} ⊆ □_m`, the core of CoarseGraining's theorem at the
clamped outer cube `c + □_j` and the patch centre `z − c`, transported back to
the global frame, is exactly the §4.4 window `U_{j-2} = (z + □_{j-2}) ∩ □_m` —
no covering, no volume constant, no residual intersection. -/
theorem image_add_caccioppoliCoreSet_eq_truncatedWindow_of_gate {m j : ℤ}
    (hjm : j ≤ m) {z : Vec d}
    (hgate : (fun y => z + y) '' openCubeSet (originCube d (j - 1)) ⊆
      openCubeSet (originCube d m)) :
    (fun y => wellPlacedCentre z m j + y) ''
        caccioppoliCoreSet (originCube d j) (z - wellPlacedCentre z m j) =
      truncatedWindow z m (j - 2) := by
  set c : Vec d := wellPlacedCentre z m j with hc
  have hcore := caccioppoliCoreSet_eq_of_patch
    (openCubeAtScale_sub_wellPlacedCentre_subset_of_gate hjm hgate)
  have hsmall : (fun y => z + y) '' openCubeSet (originCube d (j - 2)) ⊆
      openCubeSet (originCube d m) :=
    (Set.image_mono (openCubeSet_originCube_subset_of_le (by omega))).trans hgate
  have hwin : truncatedWindow z m (j - 2) =
      (fun y => z + y) '' openCubeSet (originCube d (j - 2)) :=
    truncatedWindow_eq_image_add_iff.mpr hsmall
  rw [hcore, openCubeAtScale_eq_image_add, hwin, ← Set.image_comp]
  refine Set.image_congr' fun w => ?_
  simp only [Function.comp_apply]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- **The clamped outer cube sits inside the next window up.**  This is where the
right-hand side of the boundary `hcacc` is read: `c + □_j ⊆ U_{j+1}`. -/
theorem image_add_wellPlacedCentre_subset_truncatedWindow_succ {m j : ℤ}
    (hjm : j ≤ m) {z : Vec d} (hz : z ∈ openCubeSet (originCube d m)) :
    (fun y => wellPlacedCentre z m j + y) '' openCubeSet (originCube d j) ⊆
      truncatedWindow z m (j + 1) := by
  have hzz : z - z ∈ openCubeSet (originCube d (j - 1)) := by
    rw [sub_self, mem_openCubeSet_originCube_iff]
    intro i
    have h := half_three_zpow_pos' (j - 1)
    exact ⟨by simp only [Pi.zero_apply]; linarith only [h],
      by simp only [Pi.zero_apply]; linarith only [h]⟩
  have hin := image_add_wellPlacedCentre_subset_image_add_openCubeSet_succ
    (k := j) (m := m) (x := z) (z := z) hjm hz hzz
  exact Set.subset_inter hin (image_add_wellPlacedCentre_subset_openCubeSet z hjm)

/-! ## 2. The negative half: the depth confinement of every admissible core -/

/-- **Every CoarseGraining-admissible core sits at ℓ^∞-depth at least `3^{j-2}` in
`□_m`.**

If the outer cube `y + □_j` stays inside `□_m` (binder (i)) and the patch
binder (ii) holds at `x`, then every point of the transported core obeys `|p_i|
< ½·3^m − 3^{j-2}`.  The bound depends on the outer scale ONLY, so it applies
verbatim to every member of a family of admissible cores. -/
theorem image_add_caccioppoliCoreSet_subset_shrunkBox {m j : ℤ} {x y : Vec d}
    (houter : (fun v => y + v) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m))
    (hpatch : openCubeAtScale x (j - 1) ⊆ openCubeSet (originCube d j)) :
    (fun v => y + v) '' caccioppoliCoreSet (originCube d j) x ⊆
      {p : Vec d | ∀ i, |p i| < (1 / 2 : ℝ) * (3 : ℝ) ^ m - (3 : ℝ) ^ (j - 2)} := by
  have hstepj : (3 : ℝ) ^ j = 3 * (3 : ℝ) ^ (j - 1) := three_zpow_pred j
  have hstepj1 : (3 : ℝ) ^ (j - 1) = 3 * (3 : ℝ) ^ (j - 2) := by
    have h := three_zpow_pred (j - 1)
    rwa [show j - 1 - 1 = j - 2 by ring] at h
  have hy := image_add_subset_openCubeSet_iff.mp houter
  have hx : ∀ i, |x i| + (1 / 2 : ℝ) * (3 : ℝ) ^ (j - 1) ≤
      (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
    intro i
    rw [openCubeAtScale_eq_image_add] at hpatch
    exact (image_add_subset_openCubeSet_iff.mp hpatch) i
  rw [caccioppoliCoreSet_eq_of_patch hpatch, openCubeAtScale_eq_image_add,
    ← Set.image_comp]
  rintro p ⟨w, hw, rfl⟩
  rw [mem_openCubeSet_originCube_iff] at hw
  intro i
  have hwi := hw i
  have hyi := hy i
  have hxi := hx i
  have hyu : y i ≤ |y i| := le_abs_self _
  have hyl : -(y i) ≤ |y i| := neg_le_abs _
  have hxu : x i ≤ |x i| := le_abs_self _
  have hxl : -(x i) ≤ |x i| := neg_le_abs _
  simp only [Function.comp_apply, Pi.add_apply]
  rw [abs_lt]
  constructor
  · linarith only [hwi.1, hyi, hxi, hyl, hxl, hstepj, hstepj1]
  · linarith only [hwi.2, hyi, hxi, hyu, hxu, hstepj, hstepj1]

/-! ## 3. The negative half: a flush centre's window escapes every core -/

/-- **A centre failing the gate has window points shallower than `3^{j-2}`.**

If `|z_i| + ½·3^{j-1} > ½·3^m` for some `i` — i.e. `z + □_{j-1} ⊄ □_m`, the
exact negation of the gate — then the window `U_{j-2}` contains a point `p`
with `|p_i| ≥ ½·3^m − 3^{j-2}`. -/
theorem exists_mem_truncatedWindow_shallow {m j : ℤ} {z : Vec d}
    {i : Fin d} (hz : z ∈ openCubeSet (originCube d m))
    (hfail : (1 / 2 : ℝ) * (3 : ℝ) ^ m < |z i| + (1 / 2 : ℝ) * (3 : ℝ) ^ (j - 1)) :
    ∃ p ∈ truncatedWindow z m (j - 2),
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - (3 : ℝ) ^ (j - 2) ≤ |p i| := by
  classical
  have hstepj1 : (3 : ℝ) ^ (j - 1) = 3 * (3 : ℝ) ^ (j - 2) := by
    have h := three_zpow_pred (j - 1)
    rwa [show j - 1 - 1 = j - 2 by ring] at h
  have hpos2 : (0 : ℝ) < (3 : ℝ) ^ (j - 2) := zpow_pos (by norm_num) (j - 2)
  have hzc := mem_openCubeSet_originCube_iff.mp hz
  have hzu : z i ≤ |z i| := le_abs_self _
  have hzl : -(z i) ≤ |z i| := neg_le_abs _
  have habs : |z i| < (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
    abs_lt.mpr ⟨by linarith only [(hzc i).1], (hzc i).2⟩
  -- the admissible push interval
  set delta : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ m - (3 : ℝ) ^ (j - 2) - |z i| with hdelta
  set eps : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ m - |z i| with heps
  have hdlt : delta < (1 / 2 : ℝ) * (3 : ℝ) ^ (j - 2) := by
    rw [hdelta]; linarith only [hfail, hstepj1]
  have hepspos : (0 : ℝ) < eps := by rw [heps]; linarith only [habs]
  have hdeps : delta < eps := by rw [hdelta, heps]; linarith only [hpos2]
  set t : ℝ := (max delta 0 + min ((1 / 2 : ℝ) * (3 : ℝ) ^ (j - 2)) eps) / 2 with ht
  have hmax1 : delta ≤ max delta 0 := le_max_left _ _
  have hmax2 : (0 : ℝ) ≤ max delta 0 := le_max_right _ _
  have hminlt : max delta 0 < min ((1 / 2 : ℝ) * (3 : ℝ) ^ (j - 2)) eps :=
    max_lt (lt_min hdlt hdeps) (lt_min (by linarith only [hpos2]) hepspos)
  have hmin1 : min ((1 / 2 : ℝ) * (3 : ℝ) ^ (j - 2)) eps ≤
      (1 / 2 : ℝ) * (3 : ℝ) ^ (j - 2) := min_le_left _ _
  have hmin2 : min ((1 / 2 : ℝ) * (3 : ℝ) ^ (j - 2)) eps ≤ eps := min_le_right _ _
  have htlo : delta < t := by rw [ht]; linarith only [hmax1, hminlt]
  have htpos : (0 : ℝ) < t := by rw [ht]; linarith only [hmax2, hminlt]
  have hthi : t < (1 / 2 : ℝ) * (3 : ℝ) ^ (j - 2) := by
    rw [ht]; linarith only [hminlt, hmin1]
  have hteps : t < eps := by rw [ht]; linarith only [hminlt, hmin2]
  -- the pushed point, moved away from the origin in coordinate `i`
  set s : ℝ := if 0 ≤ z i then t else -t with hs
  set p : Vec d := Function.update z i (z i + s) with hp
  have hpi : p i = z i + s := by rw [hp]; simp
  have hpk : ∀ k, k ≠ i → p k = z k := by
    intro k hk; rw [hp]; simp [Function.update_of_ne hk]
  have habsp : |p i| = |z i| + t := by
    rw [hpi, hs]
    rcases le_or_gt 0 (z i) with hsign | hsign
    · rw [if_pos hsign, abs_of_nonneg (by linarith only [hsign, htpos]),
        abs_of_nonneg hsign]
    · rw [if_neg (by linarith only [hsign]),
        abs_of_neg (by linarith only [hsign, htpos]), abs_of_neg hsign]
      ring
  have habss : |s| = t := by
    rw [hs]
    rcases le_or_gt 0 (z i) with hsign | hsign
    · rw [if_pos hsign, abs_of_nonneg htpos.le]
    · rw [if_neg (by linarith only [hsign]), abs_neg, abs_of_nonneg htpos.le]
  refine ⟨p, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨p - z, ?_, by ring⟩
    rw [mem_openCubeSet_originCube_iff]
    intro k
    by_cases hk : k = i
    · subst hk
      have h1 : (p - z) k = s := by simp only [Pi.sub_apply, hpi]; ring
      have h2 := abs_lt.mp (habss ▸ hthi : |s| < (1 / 2 : ℝ) * (3 : ℝ) ^ (j - 2))
      rw [h1]
      exact ⟨by linarith only [h2.1], h2.2⟩
    · have h1 : (p - z) k = 0 := by simp only [Pi.sub_apply, hpk k hk]; ring
      have h := half_three_zpow_pos' (j - 2)
      rw [h1]
      exact ⟨by linarith only [h], by linarith only [h]⟩
  · rw [mem_openCubeSet_originCube_iff]
    intro k
    by_cases hk : k = i
    · subst hk
      have hpabs : |p k| < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
        rw [habsp]; linarith only [hteps, heps]
      have h := abs_lt.mp hpabs
      exact ⟨by linarith only [h.1], h.2⟩
    · rw [hpk k hk]
      exact hzc k
  · rw [habsp]
    linarith only [htlo, hdelta]

/-- If the sharp gate fails at some coordinate — `z + □_{j-1} ⊄ □_m` — then no
outer centre `y` and no Dirichlet-patch centre `x` satisfying CoarseGraining's
own two geometric binders produce a core containing the §4.4 window `U_{j-2}`.
Since the confinement `image_add_caccioppoliCoreSet_subset_shrunkBox` is
uniform over `(y, x)` at a fixed outer scale, the same escaping point defeats
every family of admissible cores of that scale simultaneously, so no covering
argument at a fixed scale exists either. -/
theorem not_truncatedWindow_subset_image_add_caccioppoliCoreSet_of_gate_fails
    {m j : ℤ} {z : Vec d} {i : Fin d}
    (hz : z ∈ openCubeSet (originCube d m))
    (hfail : (1 / 2 : ℝ) * (3 : ℝ) ^ m < |z i| + (1 / 2 : ℝ) * (3 : ℝ) ^ (j - 1))
    (x y : Vec d)
    (houter : (fun v => y + v) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m))
    (hpatch : openCubeAtScale x (j - 1) ⊆ openCubeSet (originCube d j)) :
    ¬ (truncatedWindow z m (j - 2) ⊆
      (fun v => y + v) '' caccioppoliCoreSet (originCube d j) x) := by
  intro hcov
  obtain ⟨p, hpmem, hpdeep⟩ := exists_mem_truncatedWindow_shallow hz hfail
  have hshrunk := image_add_caccioppoliCoreSet_subset_shrunkBox houter hpatch (hcov hpmem)
  exact absurd (hshrunk i) (not_lt.mpr hpdeep)

end

end Algsuperdiff.Section4.Provider.Regularity
