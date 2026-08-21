/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepPartialReflection
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddCompose

/-!
# The operator reconciliation, and the multi-face boundary producer

The closing half B ("the multi-face corner obstruction measured"): the
multi-face `H¹` extension of `OneStepPartialReflection` is reconciled with the
proved **partial odd reflection operator** `oddExtend` (`OddReflectionMap`),
and the result is composed into the proved Schauder consumers, so that the
boundary branch's reflection apparatus takes no undischarged analytic input
beyond the base competitor's data.

## The reconciliation

`oddExtend_eq_self_of_faceOdd_forall`: any function that is pointwise odd under
*every* met-face reflection is a fixed point of `oddExtend x m k`, off the met
hyperplanes.  This is the multi-face generalization's one-face interface atoms
(`oddExtend_eq_self_of_faceOdd_upper`/`_lower`), and — like them — it needs
**no membership hypothesis**: the proof is a strong induction on the number of
coordinates at which the point lies beyond a met face, each step reflecting one
such coordinate back (`windowFold` and `windowFoldSign` are invariant up to the
reflected factor's sign, and the oddness pays the sign).
`oddExtend_ae_eq_self_of_faceOdd_forall` is the global a.e. form (the met
hyperplanes are Lebesgue-null).

## The composed endpoint

`exists_classicalCompetitor_gradientHolder_boundary_zeroTrace`: from

* `v ∈ H¹((x+□_{n-2}) ∩ □_m)` weakly harmonic (`hv`),
* an odd affine datum `(c, A) ∈ 𝕃_odd`,

it produces the classical competitor `V` on the doubled window with the full
four-slot Schauder package of
`OneStepOddCompose.exists_classicalCompetitor_gradientHolder_boundary_odd` —
**with no met-face restriction**: interior, one-face, edge and corner windows
are all served by the same statement.  The chain: the multi-face `H¹` endpoint
supplies the weakly harmonic reflected datum `w`; the reconciliation supplies
`hOodd` at `O := w.toFun`, `c₀ := 0`; the proved consumer does the rest.  The
conclusion's a.e. link is stated on the *window* (`V =ᵐ v` there), which is
what the excess and defect transfers (`affineExcess_congr_ae`,
`affineDistOn_congr_ae`) consume.

What remains on the boundary branch after this module is exactly the corner
pricing of `oddClassDefect` (the odd affine class collapses to `{0}` at two met
faces, `affineLift_eq_zero_of_two_met` — a property of the class, not of this
assembly) —'s disclosed residue (2), out of scope here.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. Points not beyond any met face are fixed by the fold -/

private theorem oddExtend_eq_self_of_not_beyond {x : Vec d} {m k : ℤ}
    (O : Vec d → ℝ) {y : Vec d}
    (hnb : ∀ i : Fin d,
      (MeetsUpperFace x m k i → ¬ ((1 / 2 : ℝ) * (3 : ℝ) ^ m < y i)) ∧
      (MeetsLowerFace x m k i → ¬ (y i < -(1 / 2 : ℝ) * (3 : ℝ) ^ m))) :
    oddExtend x m k O y = O y := by
  have hfold : windowFold x m k y = y := by
    funext j
    by_cases hup : MeetsUpperFace x m k j
    · have h1 := (hnb j).1 hup
      push_neg at h1
      rw [windowFold_apply, foldCoord_of_meetsUpperFace hup]
      exact min_eq_left (by linarith only [h1])
    · by_cases hlow : MeetsLowerFace x m k j
      · have h2 := (hnb j).2 hlow
        push_neg at h2
        rw [windowFold_apply, foldCoord_of_meetsLowerFace hup hlow]
        exact max_eq_left (by linarith only [h2])
      · rw [windowFold_apply, foldCoord_of_unmet hup hlow]
  have hsign : windowFoldSign x m k y = 1 := by
    rw [windowFoldSign]
    refine Finset.prod_eq_one fun j _ => ?_
    by_cases hup : MeetsUpperFace x m k j
    · rw [foldSignCoord_of_meetsUpperFace hup, if_neg ((hnb j).1 hup)]
    · by_cases hlow : MeetsLowerFace x m k j
      · rw [foldSignCoord_of_meetsLowerFace hup hlow, if_neg ((hnb j).2 hlow)]
      · rw [foldSignCoord_of_unmet hup hlow]
  rw [oddExtend_apply, hfold, hsign, one_mul]

/-! ## 2. The operator reconciliation -/

/-- **The reconciliation, pointwise.**  A function pointwise odd under every
met-face reflection is fixed by the partial odd reflection `oddExtend x m k`,
at every point off the met hyperplanes.  The multi-face generalization of the
one-face interface atoms `oddExtend_eq_self_of_faceOdd_upper`/`_lower`; as
there, no membership hypothesis appears. -/
theorem oddExtend_eq_self_of_faceOdd_forall {x : Vec d} {m k : ℤ} (hkm : k < m)
    {O : Vec d → ℝ}
    (hupO : ∀ i, MeetsUpperFace x m k i → ∀ z : Vec d,
      O (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z)
    (hlowO : ∀ i, MeetsLowerFace x m k i → ∀ z : Vec d,
      O (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z)
    {y : Vec d}
    (hney : ∀ i, (MeetsUpperFace x m k i → y i ≠ (1 / 2 : ℝ) * (3 : ℝ) ^ m) ∧
      (MeetsLowerFace x m k i → y i ≠ -(1 / 2 : ℝ) * (3 : ℝ) ^ m)) :
    oddExtend x m k O y = O y := by
  classical
  set P : Vec d → Fin d → Prop := fun w i =>
    (MeetsUpperFace x m k i ∧ (1 / 2 : ℝ) * (3 : ℝ) ^ m < w i) ∨
      (MeetsLowerFace x m k i ∧ w i < -(1 / 2 : ℝ) * (3 : ℝ) ^ m) with hPdef
  suffices h : ∀ n : ℕ, ∀ y : Vec d, (Finset.univ.filter (P y)).card ≤ n →
      (∀ i, (MeetsUpperFace x m k i → y i ≠ (1 / 2 : ℝ) * (3 : ℝ) ^ m) ∧
        (MeetsLowerFace x m k i → y i ≠ -(1 / 2 : ℝ) * (3 : ℝ) ^ m)) →
      oddExtend x m k O y = O y by
    exact h _ y le_rfl hney
  intro n
  induction n with
  | zero =>
      intro y hcard _hne
      have hempty : Finset.univ.filter (P y) = ∅ := by
        rw [← Finset.card_eq_zero]
        omega
      refine oddExtend_eq_self_of_not_beyond O fun i => ?_
      have hnP : ¬ P y i := fun hP => (Finset.notMem_empty i)
        (hempty ▸ Finset.mem_filter.2 ⟨Finset.mem_univ i, hP⟩)
      exact ⟨fun hup hlt => hnP (Or.inl ⟨hup, hlt⟩),
        fun hlow hlt => hnP (Or.inr ⟨hlow, hlt⟩)⟩
  | succ n ih =>
      intro y hcard hne
      by_cases h0 : Finset.univ.filter (P y) = ∅
      · refine oddExtend_eq_self_of_not_beyond O fun i => ?_
        have hnP : ¬ P y i := fun hP => (Finset.notMem_empty i)
          (h0 ▸ Finset.mem_filter.2 ⟨Finset.mem_univ i, hP⟩)
        exact ⟨fun hup hlt => hnP (Or.inl ⟨hup, hlt⟩),
          fun hlow hlt => hnP (Or.inr ⟨hlow, hlt⟩)⟩
      · obtain ⟨i, hi⟩ := Finset.nonempty_of_ne_empty h0
        have hcard1 : 0 < (Finset.univ.filter (P y)).card := Finset.card_pos.2 ⟨i, hi⟩
        have hPi : P y i := (Finset.mem_filter.1 hi).2
        rcases hPi with ⟨hup, hyi⟩ | ⟨hlow, hyi⟩
        · -- beyond the met upper `i`-face: reflect back
          set y' : Vec d := coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y
            with hy'def
          have hlownot : ¬ MeetsLowerFace x m k i :=
            not_meetsLowerFace_of_meetsUpperFace hkm hup
          have hy'j : ∀ j, j ≠ i → y' j = y j := fun j hj => by
            rw [hy'def, coordFaceReflection_apply, if_neg hj]
          have hy'i : y' i = (3 : ℝ) ^ m - y i := by
            rw [hy'def, coordFaceReflection_apply, if_pos rfl]
            ring
          have hy'lt : y' i < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
            rw [hy'i]
            linarith only [hyi]
          have hsubset : Finset.univ.filter (P y')
              ⊆ (Finset.univ.filter (P y)).erase i := by
            intro j hj
            have hPj : P y' j := (Finset.mem_filter.1 hj).2
            by_cases hji : j = i
            · subst hji
              exfalso
              rcases hPj with ⟨_, hlt⟩ | ⟨hjlow, _⟩
              · exact absurd hlt (not_lt.2 hy'lt.le)
              · exact hlownot hjlow
            · refine Finset.mem_erase.2 ⟨hji, Finset.mem_filter.2
                ⟨Finset.mem_univ j, ?_⟩⟩
              rcases hPj with ⟨hjup, hlt⟩ | ⟨hjlow, hlt⟩
              · exact Or.inl ⟨hjup, by rwa [hy'j j hji] at hlt⟩
              · exact Or.inr ⟨hjlow, by rwa [hy'j j hji] at hlt⟩
          have hcard' : (Finset.univ.filter (P y')).card ≤ n := by
            have h1 := Finset.card_le_card hsubset
            have h2 := Finset.card_erase_of_mem hi
            omega
          have hne' : ∀ j, (MeetsUpperFace x m k j →
              y' j ≠ (1 / 2 : ℝ) * (3 : ℝ) ^ m) ∧
              (MeetsLowerFace x m k j → y' j ≠ -(1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
            intro j
            by_cases hji : j = i
            · subst hji
              exact ⟨fun _ => ne_of_lt hy'lt, fun hjlow => absurd hjlow hlownot⟩
            · exact ⟨fun hjup => by rw [hy'j j hji]; exact (hne j).1 hjup,
                fun hjlow => by rw [hy'j j hji]; exact (hne j).2 hjlow⟩
          have hfold : windowFold x m k y' = windowFold x m k y := by
            funext j
            by_cases hji : j = i
            · subst hji
              rw [windowFold_apply, windowFold_apply,
                foldCoord_of_meetsUpperFace hup, foldCoord_of_meetsUpperFace hup,
                hy'i]
              have hexp : (3 : ℝ) ^ m - ((3 : ℝ) ^ m - y j) = y j := by ring
              rw [hexp, min_comm]
            · rw [windowFold_apply, windowFold_apply, hy'j j hji]
          have hsign : windowFoldSign x m k y' = -windowFoldSign x m k y := by
            rw [windowFoldSign, windowFoldSign,
              ← Finset.mul_prod_erase Finset.univ
                (fun j => foldSignCoord x m k j (y' j)) (Finset.mem_univ i),
              ← Finset.mul_prod_erase Finset.univ
                (fun j => foldSignCoord x m k j (y j)) (Finset.mem_univ i)]
            have hrest : ∏ j ∈ Finset.univ.erase i, foldSignCoord x m k j (y' j)
                = ∏ j ∈ Finset.univ.erase i, foldSignCoord x m k j (y j) :=
              Finset.prod_congr rfl fun j hj => by
                rw [hy'j j (Finset.ne_of_mem_erase hj)]
            rw [hrest, foldSignCoord_of_meetsUpperFace hup,
              foldSignCoord_of_meetsUpperFace hup, if_pos hyi,
              if_neg (not_lt.2 hy'lt.le)]
            ring
          have hIH := ih y' hcard' hne'
          rw [oddExtend_apply] at hIH ⊢
          calc windowFoldSign x m k y * O (windowFold x m k y)
              = -(windowFoldSign x m k y' * O (windowFold x m k y')) := by
                rw [hfold, hsign]
                ring
            _ = -O y' := by rw [hIH]
            _ = O y := by
                rw [hy'def, hupO i hup y, neg_neg]
        · -- beyond the met lower `i`-face: reflect back
          set y' : Vec d := coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y
            with hy'def
          have hupnot : ¬ MeetsUpperFace x m k i := fun h =>
            not_meetsLowerFace_of_meetsUpperFace hkm h hlow
          have hy'j : ∀ j, j ≠ i → y' j = y j := fun j hj => by
            rw [hy'def, coordFaceReflection_apply, if_neg hj]
          have hy'i : y' i = -(3 : ℝ) ^ m - y i := by
            rw [hy'def, coordFaceReflection_apply, if_pos rfl]
            ring
          have hy'gt : -(1 / 2 : ℝ) * (3 : ℝ) ^ m < y' i := by
            rw [hy'i]
            linarith only [hyi]
          have hsubset : Finset.univ.filter (P y')
              ⊆ (Finset.univ.filter (P y)).erase i := by
            intro j hj
            have hPj : P y' j := (Finset.mem_filter.1 hj).2
            by_cases hji : j = i
            · subst hji
              exfalso
              rcases hPj with ⟨hjup, _⟩ | ⟨_, hlt⟩
              · exact hupnot hjup
              · exact absurd hlt (not_lt.2 hy'gt.le)
            · refine Finset.mem_erase.2 ⟨hji, Finset.mem_filter.2
                ⟨Finset.mem_univ j, ?_⟩⟩
              rcases hPj with ⟨hjup, hlt⟩ | ⟨hjlow, hlt⟩
              · exact Or.inl ⟨hjup, by rwa [hy'j j hji] at hlt⟩
              · exact Or.inr ⟨hjlow, by rwa [hy'j j hji] at hlt⟩
          have hcard' : (Finset.univ.filter (P y')).card ≤ n := by
            have h1 := Finset.card_le_card hsubset
            have h2 := Finset.card_erase_of_mem hi
            omega
          have hne' : ∀ j, (MeetsUpperFace x m k j →
              y' j ≠ (1 / 2 : ℝ) * (3 : ℝ) ^ m) ∧
              (MeetsLowerFace x m k j → y' j ≠ -(1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
            intro j
            by_cases hji : j = i
            · subst hji
              exact ⟨fun hjup => absurd hjup hupnot,
                fun _ => (ne_of_lt hy'gt).symm⟩
            · exact ⟨fun hjup => by rw [hy'j j hji]; exact (hne j).1 hjup,
                fun hjlow => by rw [hy'j j hji]; exact (hne j).2 hjlow⟩
          have hfold : windowFold x m k y' = windowFold x m k y := by
            funext j
            by_cases hji : j = i
            · subst hji
              rw [windowFold_apply, windowFold_apply,
                foldCoord_of_meetsLowerFace hupnot hlow,
                foldCoord_of_meetsLowerFace hupnot hlow, hy'i]
              have hexp : -(3 : ℝ) ^ m - (-(3 : ℝ) ^ m - y j) = y j := by ring
              rw [hexp, max_comm]
            · rw [windowFold_apply, windowFold_apply, hy'j j hji]
          have hsign : windowFoldSign x m k y' = -windowFoldSign x m k y := by
            rw [windowFoldSign, windowFoldSign,
              ← Finset.mul_prod_erase Finset.univ
                (fun j => foldSignCoord x m k j (y' j)) (Finset.mem_univ i),
              ← Finset.mul_prod_erase Finset.univ
                (fun j => foldSignCoord x m k j (y j)) (Finset.mem_univ i)]
            have hrest : ∏ j ∈ Finset.univ.erase i, foldSignCoord x m k j (y' j)
                = ∏ j ∈ Finset.univ.erase i, foldSignCoord x m k j (y j) :=
              Finset.prod_congr rfl fun j hj => by
                rw [hy'j j (Finset.ne_of_mem_erase hj)]
            rw [hrest, foldSignCoord_of_meetsLowerFace hupnot hlow,
              foldSignCoord_of_meetsLowerFace hupnot hlow, if_pos hyi,
              if_neg (not_lt.2 hy'gt.le)]
            ring
          have hIH := ih y' hcard' hne'
          rw [oddExtend_apply] at hIH ⊢
          calc windowFoldSign x m k y * O (windowFold x m k y)
              = -(windowFoldSign x m k y' * O (windowFold x m k y')) := by
                rw [hfold, hsign]
                ring
            _ = -O y' := by rw [hIH]
            _ = O y := by
                rw [hy'def, hlowO i hlow y, neg_neg]

/-- **The reconciliation, almost everywhere.**  The met hyperplanes are
Lebesgue-null. -/
theorem oddExtend_ae_eq_self_of_faceOdd_forall {x : Vec d} {m k : ℤ} (hkm : k < m)
    {O : Vec d → ℝ}
    (hupO : ∀ i, MeetsUpperFace x m k i → ∀ z : Vec d,
      O (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z)
    (hlowO : ∀ i, MeetsLowerFace x m k i → ∀ z : Vec d,
      O (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z) :
    oddExtend x m k O =ᵐ[volume] O := by
  have hnull : volume (⋃ i : Fin d,
      ({y : Vec d | y i = (1 / 2 : ℝ) * (3 : ℝ) ^ m}
        ∪ {y : Vec d | y i = -(1 / 2 : ℝ) * (3 : ℝ) ^ m})) = 0 :=
    measure_iUnion_null fun i => measure_union_null
      (volume_coordLevel_eq_zero i _) (volume_coordLevel_eq_zero i _)
  refine MeasureTheory.ae_iff.2 (measure_mono_null ?_ hnull)
  intro y hy
  by_contra hcon
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq, not_exists,
    not_or] at hcon
  exact hy (oddExtend_eq_self_of_faceOdd_forall hkm hupO hlowO fun i =>
    ⟨fun _ => (hcon i).1, fun _ => (hcon i).2⟩)

end

end Algsuperdiff.Section4.Provider.ExcessDecay

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec vecDot openCubeSet originCube coordFaceReflection H1Function
  LocalizedZeroTraceFunctionOn)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 3. The multi-face boundary producer -/

/-- **The boundary producer from the face-only zero trace, any met
configuration.**  The composed endpoint of the reflection apparatus: from a
weakly harmonic `v ∈ H¹((x+□_{n-2}) ∩ □_m)` with face-only zero trace on the
met faces, and an odd affine datum, it delivers the classical competitor on the
doubled window with the full four-slot Schauder package of
`exists_classicalCompetitor_gradientHolder_boundary_odd` — with **no
met-face restriction** (interior, one-face, edge and corner windows alike), and
with the a.e. link stated on the window itself, ready for
`affineExcess_congr_ae`/`affineDistOn_congr_ae`. -/
theorem exists_classicalCompetitor_gradientHolder_boundary_zeroTrace [NeZero d]
    (hd : d ≠ 0) {m n : ℤ} {x : Vec d} (hx : x ∈ openCubeSet (originCube d m))
    (hmn : n - 2 < m)
    (v : H1Function (truncatedWindow x m (n - 2)))
    (hv : IsWeaklyHarmonicOn (truncatedWindow x m (n - 2)) v)
    (hzt : LocalizedZeroTraceFunctionOn (truncatedWindow x m (n - 2))
      (reflectedWindow x m (n - 2)) v.toFun)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m (n - 2) c A) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) ∧
      MemLp V 2 (volume : Measure (Vec d)) ∧
      V =ᵐ[volume.restrict (truncatedWindow x m (n - 2))] v.toFun ∧
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ i, IntegrableOn (fun p => gradField V p i)
          (truncatedWindow x m (n - 3)) volume) ∧
        HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
        HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K
          (gradField V) ∧
        K ≤ boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m (n - 2)) V
            + boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) := by
  obtain ⟨w, hwharm, hwpin, hwodd⟩ :=
    exists_h1_oddReflection_reflectedWindow hmn v hv hzt
  have hOodd : oddExtend x m (n - 2) w.toFun =ᵐ[volume] w.toFun :=
    oddExtend_ae_eq_self_of_faceOdd_forall hmn
      (fun i hi => (hwodd i).1 hi) (fun i hi => (hwodd i).2 hi)
  have hodd0 : IsOddAffineData x m (n - 2) (c - 0) A := by rwa [sub_zero]
  obtain ⟨V, hVharm, hVmem, hVae, K, hK0, hint, hgrad, hhol, hbound⟩ :=
    exists_classicalCompetitor_gradientHolder_boundary_odd hd hx hmn hwharm
      (O := w.toFun) (c₀ := 0) (fun y => (add_zero (w.toFun y)).symm) hOodd hodd0
  have hae : V =ᵐ[volume.restrict (truncatedWindow x m (n - 2))] v.toFun := by
    have h1 : V =ᵐ[volume.restrict (truncatedWindow x m (n - 2))] w.toFun :=
      hVae.filter_mono (MeasureTheory.ae_mono (Measure.restrict_mono
        (truncatedWindow_subset_reflectedWindow x m (n - 2)) le_rfl))
    filter_upwards [h1, MeasureTheory.self_mem_ae_restrict
      (measurableSet_truncatedWindow x m (n - 2))] with y hy hymem
    rw [hy, hwpin y hymem]
  exact ⟨V, hVharm, hVmem, hae, K, hK0, hint, hgrad, hhol, hbound⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
