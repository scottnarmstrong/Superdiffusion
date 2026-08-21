/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Probability.RDependent
import Algsuperdiff.Section4.Probability.AnnulusSeparation

/-!
# `r`-dependence of the annular per-scale atoms

ABK26 applies Proposition `p.concentration` to the per-scale annular atoms three
times, each time through the sentence "since the sequence `{X_j}` is
`2`-dependent".  The abstract hypothesis is
`Algsuperdiff.Probability.RDependent`; the geometry is
`AnnulusSeparation.separatedBy_annulusRegion_of_gap`; the probability is
`ShellActiveSigma.iIndepFun_of_local_cutoffSample`.  This module is the one
bridge that joins them, and nothing else.

## The statement

`rDependent_of_annulusLocalSigma`: if every `X n` is measurable for the single
sigma-field `cutoffSampleLocalSigma M (n − c) (annulusRegion d n)` — i.e. `X n`
reads only truncations at or below level `n − c`, and only on the annulus of its
own index — then `X` is `r`-dependent for every `r ≥ 1` with
`3 + 2·3^{1−c}·√d ≤ 3^r`.

The truncation offset `c` and the count `r` are **free**.

## Who supplies the hypothesis

`hX` is exactly the `hloc` slot the proved `𝒢₂` lane already discharges:

* `Provider.Proportion.G2Locality.measurable_Xcal_annulusRegion_local` — the
  §4.1 atom `X_j` at `c = 2`;
* `Provider.Proportion.G2Locality.measurable_errorAnnMax_annulusRegion_local` —
  its per-inner-scale summand, same offset;

## The measurability companion

`cutoffSampleLocalSigma` is the `Subtype.val`-comap of a *null-completed*
sigma-field, so it is **not** contained in the ambient sigma-field of
`Cutoff.CutoffSample d`: "local-sigma measurable ⟹ ambient measurable" is false
as stated at this carrier.  The true and consumable form is a.e.-measurability,
recorded here as `nullMeasurableSet_of_cutoffSampleLocalSigma` and
`aemeasurable_of_cutoffSampleLocalSigma`.  Consumers that need genuine ambient
measurability get it from the observable's own construction
(`Support.measurable_annularErrorObservable`), not from locality.

## Main results

* `rDependent_of_annulusLocalSigma` — the bridge, free `c` and free `r`.
* `twoDependent_of_annulusLocalSigma` — the manuscript's `r = 2` instance at the
  `𝒢₂` offset `c = 2`, with its `d ≤ 81` caveat made explicit.
* `nullMeasurableSet_of_cutoffSampleLocalSigma`,
  `aemeasurable_of_cutoffSampleLocalSigma` — the measurability companion.

## References

* ABK26, `p.concentration`.
* ABK26, `l.minimal.scale.sep`, Step 1 (the separation claim).
-/

namespace Algsuperdiff.Section4.Probability

open MeasureTheory
open Homogenization
open Algsuperdiff.Section3

variable {d : ℕ}

/-! ## The bridge -/

/-- **The `r`-dependence of the annular atoms.**  A family `X : ℤ → Ω → ℝ` on the
genuine cutoff carrier, each member of which reads only truncations at or below
its own level `n − c` and only on the annulus `annulusRegion d n` of its own
index, is `r`-dependent for the cutoff law, for every `r ≥ 1` with
`3 + 2·3^{1−c}·√d ≤ 3^r`.

The proof is the composition of the two proved halves: the finite set of
pairwise `≥ r`-separated indices carried is turned into the pairwise geometric
separation `separatedBy_annulusRegion_of_gap` at the shared-shell threshold `√d
· 3^{min (n−c) (n'−c)}`, which is verbatim the `hsep` hypothesis of
`iIndepFun_of_local_cutoffSample` at `Lidx n = n − c`. -/
theorem rDependent_of_annulusLocalSigma (M : ABKModel d) (c : ℤ) {r : ℕ}
    (hr1 : 1 ≤ r)
    (hr : 3 + 2 * (3 : ℝ) ^ (1 - c) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ))
    {X : ℤ → Cutoff.CutoffSample d → ℝ}
    (hX : ∀ n : ℤ, Measurable[Cutoff.cutoffSampleLocalSigma M (n - c)
      (annulusRegion d n)] (X n)) :
    Algsuperdiff.Probability.RDependent (Cutoff.cutoffSampleLaw M).toMeasure X r := by
  intro s hs
  exact iIndepFun_of_local_cutoffSample M (fun i : {i // i ∈ s} => i.1 - c)
    (U := fun i : {i // i ∈ s} => annulusRegion d i.1)
    (fun i => measurableSet_annulusRegion d i.1)
    (fun i j hij => separatedBy_annulusRegion_of_gap hr1 hr
      (hs i.1 i.2 j.1 j.2 fun h => hij (Subtype.ext h)))
    (fun i => hX i.1)

/-- **The manuscript's `2`-dependence at the `𝒢₂` truncation offset.**  At `c = 2`
— the offset of the proved `𝒢₂` locality exports — the count `r = 2` is
available exactly for `d ≤ 81`.  This is the printed claim; the free-`r` bridge
above is what the development consumes, so that no dimension restriction
enters. -/
theorem twoDependent_of_annulusLocalSigma (M : ABKModel d) (hd : d ≤ 81)
    {X : ℤ → Cutoff.CutoffSample d → ℝ}
    (hX : ∀ n : ℤ, Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2)
      (annulusRegion d n)] (X n)) :
    Algsuperdiff.Probability.TwoDependent (Cutoff.cutoffSampleLaw M).toMeasure X :=
  rDependent_of_annulusLocalSigma M 2 (by norm_num)
    (three_add_two_thirds_sqrt_le_nine hd) hX

/-! ## The measurability companion -/

/-- A locally measurable set of the genuine cutoff carrier is null-measurable for
the cutoff law.  It is **not** measurable: `cutoffSampleLocalSigma` is the
`Subtype.val`-comap of the null-completion `lowerShellLocalCompletion`, so its
members are only a.e. equal to genuinely measurable sets. -/
theorem nullMeasurableSet_of_cutoffSampleLocalSigma (M : ABKModel d) (m : ℤ)
    (U : Set (Vec d)) {A : Set (Cutoff.CutoffSample d)}
    (hA : MeasurableSet[Cutoff.cutoffSampleLocalSigma M m U] A) :
    NullMeasurableSet A (Cutoff.cutoffSampleLaw M).toMeasure := by
  obtain ⟨B, hB, hBA⟩ := MeasurableSpace.measurableSet_comap.1 hA
  obtain ⟨t, ht, hBt⟩ := hB
  have hmt : MeasurableSet t := Cutoff.lowerShellLocalSigma_le_borel m U t ht
  have hpre : (Subtype.val : Cutoff.CutoffSample d → Cutoff.ShellSeq d) ⁻¹' B
      =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
    (Subtype.val : Cutoff.CutoffSample d → Cutoff.ShellSeq d) ⁻¹' t := by
    rw [← Cutoff.map_cutoffSampleLaw_val M] at hBt
    exact (Measure.tendsto_ae_map measurable_subtype_coe.aemeasurable).eventually hBt
  refine (measurable_subtype_coe hmt).nullMeasurableSet.congr ?_
  rw [← hBA]
  exact hpre.symm

/-- **A locally measurable real observable of the genuine cutoff carrier is
a.e.-measurable for the cutoff law.**  This is the honest replacement for
"local-sigma measurable ⟹ ambient measurable", which fails at this carrier
because the local sigma-field is a comap of a null-completion.  The passage from
null-measurability to a.e.-measurability is Mathlib's
`NullMeasurable.aemeasurable`, available because the Borel sigma-field of `ℝ` is
countably generated. -/
theorem aemeasurable_of_cutoffSampleLocalSigma (M : ABKModel d) (m : ℤ)
    (U : Set (Vec d)) {f : Cutoff.CutoffSample d → ℝ}
    (hf : Measurable[Cutoff.cutoffSampleLocalSigma M m U] f) :
    AEMeasurable f (Cutoff.cutoffSampleLaw M).toMeasure := by
  refine MeasureTheory.NullMeasurable.aemeasurable (f := f) ?_
  intro S hS
  exact nullMeasurableSet_of_cutoffSampleLocalSigma M m U (hf hS)

end Algsuperdiff.Section4.Probability
