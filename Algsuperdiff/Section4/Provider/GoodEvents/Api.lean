/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Frozen.Section4.GoodEvents
import Algsuperdiff.Section4.Provider.GoodEvents.Translate

/-!
# The consumption A of the frozen good event `𝒢(m, y; s, ε)`

`Algsuperdiff.Frozen.Section4.goodEventAt` (`d.good.event.for.lambda`) is a
*final frozen definition*: the translated good event is the
`Cutoff.translateCutoffSample y` preimage of the Section 4 support layer's
`goodEventBase`.  This module supplies the four things every Section 4 lane
does with it:

* **read it** — `mem_goodEventAt_iff`, the three-component membership
  characterization obtained by composing the support layer's
  `mem_goodEventBase_iff` with the translate preimage;
* **measure it** — `measurableSet_goodEventAt`;
* **compare two of them** — monotonicity in the coarse-ellipticity constant
  `Ccg` and in the threshold `ε` (and hence in the `𝒢₁` threshold
  `s ε c⋆^{1/2} γ^{-1/2}`, which is increasing in `ε`), plus the three
  component projections;

The last item is the input of every lattice maximum in §4.1--§4.2: the union
bound over `z ∈ 3^j ℤ^d ∩ S` needs each summand's mass to be the mass at the
origin.

## What is *not* here

Monotonicity in the scale `m` is not stated, and none is claimed in either
direction.  `𝒢₀(m)` weights the `k`-supremum by `3^{-γ(m-k)/4}` and ranges `z`
over the annulus `□_m ∖ □_k`; `𝒢₁`'s second condition weights by
`3^{-s(m-n)/4}` and its first condition sums from `k = m`; `𝒢₂`'s double sum is
over `j ≤ m`.  Changing `m` moves the weights and the index sets at once, so
nothing here is a set inclusion in `m`; any `m`-comparison a lane needs is a
per-display estimate, to be produced where it is used.

## References

* ABK26, `d.good.event.for.lambda`; `e.lambda.good.events`.
-/

namespace Algsuperdiff.Section4.Provider.GoodEvents

open Algsuperdiff.Section3
open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The `𝒢₁` threshold of `e.lambda.good.events`

`goodEventBase` instantiates `𝒢₁`'s threshold at `T = s ε √c⋆ (√γ)⁻¹`.  Its two
sign facts are used by every monotonicity statement below, so they are isolated
once. -/

/-- The `𝒢₁` threshold `s ε √c⋆ (√γ)⁻¹` of `e.lambda.good.events`. -/
def goodEventThreshold (M : ABKModel d) (s : {s : ℝ // 0 < s}) (ep : ℝ) : ℝ :=
  (s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹

theorem goodEventBase_eq (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Support.goodEventBase M Ccg m s ep =
      (Support.eventG0 M Ccg m ∩
          Support.eventG1 M m (s : ℝ) (goodEventThreshold M s ep)) ∩
        Support.eventG2 M m s ep :=
  rfl

/-- The threshold is nonnegative as soon as the printed `ε` is. -/
theorem goodEventThreshold_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {ep : ℝ} (hep : 0 ≤ ep) : 0 ≤ goodEventThreshold M s ep :=
  mul_nonneg
    (mul_nonneg (mul_nonneg s.2.le hep) (Real.sqrt_nonneg _))
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- The threshold is monotone in `ε`. -/
theorem goodEventThreshold_mono (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {ep ep' : ℝ} (h : ep ≤ ep') :
    goodEventThreshold M s ep ≤ goodEventThreshold M s ep' :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h s.2.le)
      (Real.sqrt_nonneg _))
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-! ## 2. Membership and measurability -/

/-- The frozen event is a translate preimage, by definition. -/
theorem goodEventAt_eq_preimage (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep =
      Cutoff.translateCutoffSample y ⁻¹' Support.goodEventBase M Ccg m s ep :=
  rfl

/-- Membership in the translated event is membership of the translated sample in
the untranslated event. -/
theorem mem_goodEventAt_iff_mem_goodEventBase (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (omega : Cutoff.CutoffSample d) :
    omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep ↔
      Cutoff.translateCutoffSample y omega ∈ Support.goodEventBase M Ccg m s ep :=
  Iff.rfl

/-- **The membership characterization.**  The support layer's
`mem_goodEventBase_iff` composed with the translate preimage: `ω` lies in
`𝒢(m, y; s, ε)` exactly when the translated sample lies in each of `𝒢₀(m)`,
`𝒢₁(m; s, s ε √c⋆ (√γ)⁻¹)` and `𝒢₂(m; s, ε)`. -/
theorem mem_goodEventAt_iff (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) (omega : Cutoff.CutoffSample d) :
    omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep ↔
      (Cutoff.translateCutoffSample y omega ∈ Support.eventG0 M Ccg m ∧
          Cutoff.translateCutoffSample y omega ∈
            Support.eventG1 M m (s : ℝ) (goodEventThreshold M s ep)) ∧
        Cutoff.translateCutoffSample y omega ∈ Support.eventG2 M m s ep :=
  Support.mem_goodEventBase_iff M Ccg m s ep (Cutoff.translateCutoffSample y omega)

/-- **The translated event is measurable.**  The support layer's measurability
transported through the proved measurability of `translateCutoffSample`. -/
theorem measurableSet_goodEventAt (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    MeasurableSet (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep) :=
  (Support.measurableSet_goodEventBase M Ccg m s ep).preimage
    (Cutoff.measurable_translateCutoffSample y)

/-! ## 3. The component decomposition -/

/-- The translated event is the intersection of the three translated
components. -/
theorem goodEventAt_eq_inter (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep =
      (Cutoff.translateCutoffSample y ⁻¹' Support.eventG0 M Ccg m ∩
          Cutoff.translateCutoffSample y ⁻¹'
            Support.eventG1 M m (s : ℝ) (goodEventThreshold M s ep)) ∩
        Cutoff.translateCutoffSample y ⁻¹' Support.eventG2 M m s ep := by
  rw [goodEventAt_eq_preimage, goodEventBase_eq, Set.preimage_inter,
    Set.preimage_inter]

theorem goodEventAt_subset_eventG0 (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep ⊆
      Cutoff.translateCutoffSample y ⁻¹' Support.eventG0 M Ccg m :=
  Set.preimage_mono (Support.goodEventBase_subset_eventG0 M Ccg m s ep)

theorem goodEventAt_subset_eventG1 (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep ⊆
      Cutoff.translateCutoffSample y ⁻¹'
        Support.eventG1 M m (s : ℝ) (goodEventThreshold M s ep) :=
  Set.preimage_mono (Support.goodEventBase_subset_eventG1 M Ccg m s ep)

theorem goodEventAt_subset_eventG2 (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep ⊆
      Cutoff.translateCutoffSample y ⁻¹' Support.eventG2 M m s ep :=
  Set.preimage_mono (Support.goodEventBase_subset_eventG2 M Ccg m s ep)

/-! ## 4. Monotonicity in the two displayed parameters -/

/-- **Monotonicity of the untranslated event.**  Raising the
coarse-ellipticity constant lowers `𝒢₀`'s positive parts, and raising `ε`
raises both `𝒢₁`'s threshold and `𝒢₂`'s. -/
theorem goodEventBase_subset_of_le (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) {Ccg Ccg' ep ep' : ℝ} (hC : Ccg ≤ Ccg')
    (hep : 0 ≤ ep) (heple : ep ≤ ep') :
    Support.goodEventBase M Ccg m s ep ⊆ Support.goodEventBase M Ccg' m s ep' := by
  rintro omega ⟨⟨h0, h1⟩, h2⟩
  exact ⟨⟨Support.eventG0_subset_of_le M m hC h0,
      Support.eventG1_subset_of_le M m (s : ℝ)
        (goodEventThreshold_nonneg M s hep)
        (goodEventThreshold_mono M s heple) h1⟩,
    Support.eventG2_subset_of_le M m s hep heple h2⟩

/-- **Monotonicity of the translated event.**  The preimage of an inclusion. -/
theorem goodEventAt_subset_of_le (M : ABKModel d) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) {Ccg Ccg' ep ep' : ℝ} (hC : Ccg ≤ Ccg')
    (hep : 0 ≤ ep) (heple : ep ≤ ep') :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep ⊆
      Algsuperdiff.Frozen.Section4.goodEventAt M Ccg' m y s ep' :=
  Set.preimage_mono (goodEventBase_subset_of_le M m s hC hep heple)

/-- Monotonicity in `C_{(e.cg.ellip.lower)}` alone. -/
theorem goodEventAt_mono_Ccg (M : ABKModel d) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) {Ccg Ccg' : ℝ} (hC : Ccg ≤ Ccg') :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep ⊆
      Algsuperdiff.Frozen.Section4.goodEventAt M Ccg' m y s ep :=
  Set.preimage_mono
    (Set.inter_subset_inter_left _
      (Set.inter_subset_inter_left _ (Support.eventG0_subset_of_le M m hC)))

/-- Monotonicity in the threshold `ε` alone. -/
theorem goodEventAt_mono_ep (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) {ep ep' : ℝ} (hep : 0 ≤ ep) (heple : ep ≤ ep') :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep ⊆
      Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep' :=
  goodEventAt_subset_of_le M m y s le_rfl hep heple

/-! ## 5. The translate calculus of the event -/

/-- At `y = 0` the frozen event is the untranslated `goodEventBase`. -/
theorem goodEventAt_zero (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m (0 : Vec d) s ep =
      Support.goodEventBase M Ccg m s ep :=
  preimage_translateCutoffSample_zero _

/-- Translating the translated event adds the vectors. -/
theorem preimage_translateCutoffSample_goodEventAt (M : ABKModel d) (Ccg : ℝ)
    (m : ℤ) (y z : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Cutoff.translateCutoffSample z ⁻¹'
        Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep =
      Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m (y + z) s ep :=
  preimage_translateCutoffSample_preimage z y _

/-! ## 6. The per-`z` transfer of the probability

The lattice maxima of §4.1--§4.2 are unions over `z ∈ 3^j ℤ^d ∩ S`; a union
bound needs each term's mass at the origin.  The proved real-translation
invariance of `cutoffSampleLaw` supplies it without any lattice hypothesis. -/

/-- **The good event has the same probability at every centre.** -/
theorem measure_goodEventAt (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep) =
      (Cutoff.cutoffSampleLaw M).toMeasure (Support.goodEventBase M Ccg m s ep) :=
  measure_preimage_translateCutoffSample M y
    (Support.measurableSet_goodEventBase M Ccg m s ep)

/-- **`P[𝒢(m, y; s, ε)] = P[𝒢(m, 0; s, ε)]`** — the per-`z` tail transfer every
lattice maximum consumes. -/
theorem measure_goodEventAt_eq_measure_goodEventAt_zero (M : ABKModel d)
    (Ccg : ℝ) (m : ℤ) (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep) =
      (Cutoff.cutoffSampleLaw M).toMeasure
        (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m (0 : Vec d) s ep) := by
  rw [measure_goodEventAt, goodEventAt_zero]

/-- The complementary form: the *bad* event has the same probability at every
centre.  This is the shape a union bound over a lattice consumes. -/
theorem measure_compl_goodEventAt (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)ᶜ =
      (Cutoff.cutoffSampleLaw M).toMeasure
        (Support.goodEventBase M Ccg m s ep)ᶜ :=
  measure_compl_preimage_translateCutoffSample M y
    (Support.measurableSet_goodEventBase M Ccg m s ep)

/-- The complementary transfer, stated between two centres. -/
theorem measure_compl_goodEventAt_eq_zero (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)ᶜ =
      (Cutoff.cutoffSampleLaw M).toMeasure
        (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m (0 : Vec d) s ep)ᶜ := by
  rw [measure_compl_goodEventAt, goodEventAt_zero]

/-- The transfer read at the triadic lattice points that index the maxima of
`d.good.event.for.lambda` (`Support.latticeCubeSet` / `latticeAnnulusSet`). -/
theorem measure_goodEventAt_triadicLatticePoint (M : ABKModel d) (Ccg : ℝ)
    (m j : ℤ) (v : Fin d → ℤ) (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m
          (Support.triadicLatticePoint j v) s ep) =
      (Cutoff.cutoffSampleLaw M).toMeasure
        (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m (0 : Vec d) s ep) :=
  measure_goodEventAt_eq_measure_goodEventAt_zero M Ccg m _ s ep

end

end Algsuperdiff.Section4.Provider.GoodEvents
