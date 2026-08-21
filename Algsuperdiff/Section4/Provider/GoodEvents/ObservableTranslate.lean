/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.GoodEvents.Api
import Algsuperdiff.Section4.Support.FluxCorrectedRepresentative

/-!
# The per-observable translation identities of the Section 4.2 lattice maxima

`Provider/GoodEvents/Translate.lean` supplies the *law-level* half of the
translation calculus and states explicitly that the remaining half — the
per-observable pointwise identities `observable(z+□)(ω) =
observable(□)(translate z ω)` — is supplied by the individual Section 4 modules.
This module discharges that half for the three observables the §4.2 lattice
maxima read, and packages the compositions with the proved measure
preservation.

## What the frozen displays actually contain

Throughout, the *sample* is translated, never the cube: the
manuscript's `𝓔(z+□_m)`, `λ_{γ,2}^{-1}(z+□_{k−2})` and
`𝒢(m, y; s, ε)` are rendered as compositions with
`Cutoff.translateCutoffSample`.  Consequently

* the public flux observables `Support.fluxCorrectedErrorObservableSup` /
  `…SqSup` are hard-wired to the origin cube (`originCube d m` throughout
  `fluxCorrectedErrorRepresentative`), and **no public Section 4 observable
  exposes a cube parameter**, so there is no second, cube-indexed observable
  that a translation identity could compare them to.  (The atom layer beneath
  them is cube-indexed — `Support.fluxCorrectedCoeffFamily M L m Q omega` takes
  `Q : TriadicCube d` — so a literal `𝓔(z+□_m)` could in principle be written
  at the triadic cube of scale `m` and index `v`; no frozen §4 statement does.)
  For these two observables the frozen composition *is* the rendering, so the
  identities below are the definitional ones a proof actually needs: the
  translation passes inside the `L`-supremum, the translations compose
  additively, and `y = 0` is the identity;

**Not required by any frozen statement.**  The lift of that
coefficient covariance *through* the Ch02 error functional — i.e. a theorem
"the `(∞,2)` error on `y+□_m` at `a(ω)` equals the error on `□_m` at
`a(translate y ω)`" — is **not proved** and is **not** proved here.  No frozen
§4 statement needs it: every one of them composes with `translateCutoffSample`.
Any future statement that wants to read the composition as a literal cube
translation must prove that lemma first.

## The shell gauges are covariant, not invariant

`Support.shellW2InfNormAt z k j` carries its base point, and the sample
translation *shifts that base point additively*:
`shellW2InfNormAt z k ((translate y ω).1 l) = shellW2InfNormAt (z + y) k (ω.1 l)`
(`shellW2InfNormAt_translateCutoffSample`).  `Support.shellW1InfGradNorm m j`
carries **no** base point (it is the gauge on the origin cube `□_m`), so the
naive invariance `shellW1InfGradNorm m ((translate y ω).1 l) = shellW1InfGradNorm m (ω.1 l)`
is **not available and is not claimed**: it would assert that every shell's
`□_m`-supremum of `∇²j` equals its `y+□_m`-supremum, which no property of the
carrier supplies.  The honest law is that the sample translation replaces the
shell `j` by `ShellField.translate y j`, i.e. moves the gauge from `□_m` to
`y+□_m`, which is exactly the first leg of `shellW2InfNormAt y m`.  This is
what the frozen `𝒢₁(m)` at a centre `y` means, so nothing is blocked; the
translated gauge is stated here together with its `W̲^{1,∞} ≤ W̲^{2,∞}`
comparison.  The shell *index* is untouched: translation is spatial only.

## Consumers

* `mul_sum_indicator_goodEventAt_comp_translate` and
  `measure_lt_mul_sum_indicator_goodEventAt` are what the centre-union step
  reads: the two clauses of `Frozen.Section4.minimal_scale_separation` at the
  centre `Support.triadicLatticePoint (n-1) z` have the same law as at the
  origin.
* `measure_lt_comp_translateCutoffSample` and
  `measurable_fluxCorrectedErrorObservableSup_translate` are what the tail step
  reads.

## References

* ABK26, `d.good.event.for.lambda`, (the translate convention).
* ABK26, `p.minimal.scale.separation.sec4`.
-/

namespace Algsuperdiff.Section4.Provider.GoodEvents

open Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The flux-corrected error observables at a translated sample

The two public observables of `p.mathcalE.annular.decomp` are the ones the
frozen `minimal_scale_separation` composes with
`Cutoff.translateCutoffSample`.  All four identities per observable are
definitional (`rfl`, or `congrArg` over the proved group action). -/

/-- **The translation passes inside the `L`-supremum.**  The shape a per-`L`
estimate at a translated centre consumes. -/
theorem fluxCorrectedErrorObservableSup_translate (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (y : Vec d) (omega : Cutoff.CutoffSample d) :
    Support.fluxCorrectedErrorObservableSup M m s
        (Cutoff.translateCutoffSample y omega) =
      ⨆ L : {L : ℤ // m ≤ L},
        ENNReal.ofReal
          (Support.fluxCorrectedErrorRepresentative M L.1 m s
            (Cutoff.translateCutoffSample y omega)) :=
  rfl

/-- The observable at the `0`-translated sample is the observable. -/
theorem fluxCorrectedErrorObservableSup_translate_zero (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) :
    Support.fluxCorrectedErrorObservableSup M m s
        (Cutoff.translateCutoffSample (0 : Vec d) omega) =
      Support.fluxCorrectedErrorObservableSup M m s omega :=
  congrArg (Support.fluxCorrectedErrorObservableSup M m s)
    (translateCutoffSample_zero omega)

/-- Two successive translations of the sample add: the identity a nested
lattice maximum (a centre inside a coarser centre) consumes. -/
theorem fluxCorrectedErrorObservableSup_translate_translate (M : ABKModel d)
    (m : ℤ) (s : {s : ℝ // 0 < s}) (y z : Vec d)
    (omega : Cutoff.CutoffSample d) :
    Support.fluxCorrectedErrorObservableSup M m s
        (Cutoff.translateCutoffSample y (Cutoff.translateCutoffSample z omega)) =
      Support.fluxCorrectedErrorObservableSup M m s
        (Cutoff.translateCutoffSample (y + z) omega) :=
  congrArg (Support.fluxCorrectedErrorObservableSup M m s)
    (translateCutoffSample_add y z omega)

/-- The observable at a translated sample is measurable in the sample. -/
theorem measurable_fluxCorrectedErrorObservableSup_translate (M : ABKModel d)
    (m : ℤ) (s : {s : ℝ // 0 < s}) (y : Vec d) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      Support.fluxCorrectedErrorObservableSup M m s
        (Cutoff.translateCutoffSample y omega) :=
  (Support.measurable_fluxCorrectedErrorObservableSup M m s).comp
    (Cutoff.measurable_translateCutoffSample y)

/-- The squared-supremum observable at a translated sample, with the
translation inside the `L`-supremum. -/
theorem fluxCorrectedErrorObservableSqSup_translate (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (y : Vec d) (omega : Cutoff.CutoffSample d) :
    Support.fluxCorrectedErrorObservableSqSup M m s
        (Cutoff.translateCutoffSample y omega) =
      ⨆ L : {L : ℤ // m ≤ L},
        ENNReal.ofReal
          (Support.fluxCorrectedErrorRepresentative M L.1 m s
            (Cutoff.translateCutoffSample y omega) ^ 2) :=
  rfl

/-- The squared observable at the `0`-translated sample. -/
theorem fluxCorrectedErrorObservableSqSup_translate_zero (M : ABKModel d)
    (m : ℤ) (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) :
    Support.fluxCorrectedErrorObservableSqSup M m s
        (Cutoff.translateCutoffSample (0 : Vec d) omega) =
      Support.fluxCorrectedErrorObservableSqSup M m s omega :=
  congrArg (Support.fluxCorrectedErrorObservableSqSup M m s)
    (translateCutoffSample_zero omega)

/-- Two successive translations add, for the squared observable. -/
theorem fluxCorrectedErrorObservableSqSup_translate_translate (M : ABKModel d)
    (m : ℤ) (s : {s : ℝ // 0 < s}) (y z : Vec d)
    (omega : Cutoff.CutoffSample d) :
    Support.fluxCorrectedErrorObservableSqSup M m s
        (Cutoff.translateCutoffSample y (Cutoff.translateCutoffSample z omega)) =
      Support.fluxCorrectedErrorObservableSqSup M m s
        (Cutoff.translateCutoffSample (y + z) omega) :=
  congrArg (Support.fluxCorrectedErrorObservableSqSup M m s)
    (translateCutoffSample_add y z omega)

/-- The squared observable at a translated sample is measurable. -/
theorem measurable_fluxCorrectedErrorObservableSqSup_translate (M : ABKModel d)
    (m : ℤ) (s : {s : ℝ // 0 < s}) (y : Vec d) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      Support.fluxCorrectedErrorObservableSqSup M m s
        (Cutoff.translateCutoffSample y omega) :=
  (Support.measurable_fluxCorrectedErrorObservableSqSup M m s).comp
    (Cutoff.measurable_translateCutoffSample y)

/-- **Why translating the sample is translating the cube.**  The applied form of
the proved `Cutoff.coefficientCutoff_translateCutoffSample`: the coefficient
field of the `y`-translated sample is the coefficient field of the sample read
at `x + y`.  This is the pointwise covariance that justifies the convention;
lifting it through the Ch02 error functional is not proved and is not needed by
any frozen §4 statement (see the module note). -/
theorem coefficientCutoff_translateCutoffSample_apply (M : ABKModel d) (m : ℤ)
    (y : Vec d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    Cutoff.coefficientCutoff M.nu m (Cutoff.translateCutoffSample y omega) x =
      Cutoff.coefficientCutoff M.nu m omega (x + y) := by
  rw [Cutoff.coefficientCutoff_translateCutoffSample, translateReg_apply]

/-! ## 2. The good-event indicator at a translated centre

The frozen `goodEventAt` is preimage-shaped, so an indicator of the event at
centre `y` composed with the `y`-translated observable is the indicator of the
*untranslated* event at the translated sample.  This is the workhorse of every
§4.2 lattice maximum: it turns each summand of
`minimal_scale_separation` into the origin summand evaluated at
`translateCutoffSample y ω`. -/

/-- **The indicator-composition identity.**  Verifies and uses the
preimage shape of the frozen definition (`Api.goodEventAt_eq_preimage`). -/
theorem indicator_goodEventAt_comp_translate {beta : Type*} [Zero beta]
    (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d) (s : {s : ℝ // 0 < s})
    (ep : ℝ) (f : Cutoff.CutoffSample d → beta)
    (omega : Cutoff.CutoffSample d) :
    Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)
        (fun omega' => f (Cutoff.translateCutoffSample y omega')) omega =
      Set.indicator (Support.goodEventBase M Ccg m s ep) f
        (Cutoff.translateCutoffSample y omega) := by
  by_cases h : Cutoff.translateCutoffSample y omega ∈
      Support.goodEventBase M Ccg m s ep
  · have h' : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep := h
    rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
  · have h' : omega ∉ Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep := h
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]

/-- The identity at the observable of `minimal_scale_separation`'s first
conclusion: the `k`-th summand at centre `y` is the origin summand at the
`y`-translated sample. -/
theorem indicator_goodEventAt_fluxCorrectedErrorObservableSup (M : ABKModel d)
    (Ccg : ℝ) (m : ℤ) (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ)
    (omega : Cutoff.CutoffSample d) :
    Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)
        (fun omega' =>
          Support.fluxCorrectedErrorObservableSup M m s
            (Cutoff.translateCutoffSample y omega')) omega =
      Set.indicator (Support.goodEventBase M Ccg m s ep)
        (Support.fluxCorrectedErrorObservableSup M m s)
        (Cutoff.translateCutoffSample y omega) :=
  indicator_goodEventAt_comp_translate M Ccg m y s ep
    (Support.fluxCorrectedErrorObservableSup M m s) omega

/-- The complement of the frozen event is the preimage of the complement. -/
theorem compl_goodEventAt_eq_preimage (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)ᶜ =
      Cutoff.translateCutoffSample y ⁻¹'
        (Support.goodEventBase M Ccg m s ep)ᶜ :=
  Set.preimage_compl.symm

/-- The indicator-composition identity on the *bad* event. -/
theorem indicator_compl_goodEventAt_comp_translate {beta : Type*} [Zero beta]
    (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d) (s : {s : ℝ // 0 < s})
    (ep : ℝ) (f : Cutoff.CutoffSample d → beta)
    (omega : Cutoff.CutoffSample d) :
    Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)ᶜ
        (fun omega' => f (Cutoff.translateCutoffSample y omega')) omega =
      Set.indicator (Support.goodEventBase M Ccg m s ep)ᶜ f
        (Cutoff.translateCutoffSample y omega) := by
  by_cases h : Cutoff.translateCutoffSample y omega ∈
      (Support.goodEventBase M Ccg m s ep)ᶜ
  · have h' : omega ∈ (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)ᶜ := h
    rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
  · have h' : omega ∉ (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)ᶜ := h
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]

/-- The identity at the constant `1` of `minimal_scale_separation`'s second
conclusion: the bad-event count at centre `y` is the origin bad-event count at
the `y`-translated sample. -/
theorem indicator_compl_goodEventAt_one (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ)
    (omega : Cutoff.CutoffSample d) :
    Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)ᶜ
        (fun _ => (1 : ℝ≥0∞)) omega =
      Set.indicator (Support.goodEventBase M Ccg m s ep)ᶜ
        (fun _ => (1 : ℝ≥0∞)) (Cutoff.translateCutoffSample y omega) :=
  indicator_compl_goodEventAt_comp_translate M Ccg m y s ep
    (fun _ => (1 : ℝ≥0∞)) omega

/-- Membership at a composed centre: the event at `y + z` read at `ω` is the
event at `y` read at the `z`-translated sample. -/
theorem mem_goodEventAt_add_iff (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y z : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) (omega : Cutoff.CutoffSample d) :
    omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m (y + z) s ep ↔
      Cutoff.translateCutoffSample z omega ∈
        Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep := by
  rw [← preimage_translateCutoffSample_goodEventAt M Ccg m y z s ep]
  exact Iff.rfl

/-- **The iterated-translate indicator identity.**  The summand at the composed
centre `y + z` read at `ω` is the summand at centre `y` read at the
`z`-translated sample.  This is the shape a lattice maximum nested inside a
coarser lattice maximum consumes. -/
theorem indicator_goodEventAt_add_comp_translate {beta : Type*} [Zero beta]
    (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y z : Vec d) (s : {s : ℝ // 0 < s})
    (ep : ℝ) (f : Cutoff.CutoffSample d → beta)
    (omega : Cutoff.CutoffSample d) :
    Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m (y + z) s ep)
        (fun omega' => f (Cutoff.translateCutoffSample (y + z) omega')) omega =
      Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)
        (fun omega'' => f (Cutoff.translateCutoffSample y omega''))
        (Cutoff.translateCutoffSample z omega) := by
  rw [indicator_goodEventAt_comp_translate M Ccg m (y + z) s ep f omega,
    indicator_goodEventAt_comp_translate M Ccg m y s ep f
      (Cutoff.translateCutoffSample z omega), translateCutoffSample_add y z omega]

/-! ## 3. The shell gauges at a translated sample

`ShellNorms.lean`'s two gauges behave differently under
`translateCutoffSample`, because only the second carries a base point.  The
shell index is untouched throughout: the action is spatial. -/

/-- The frozen translation action on a single shell composes.  A `private`
re-proof of `Section3.Provider.Stream.translate_translate`. -/
private theorem shellField_translate_translate (a b : Vec d) (j : ShellField d) :
    ShellField.translate a (ShellField.translate b j) =
      ShellField.translate (a + b) j :=
  ShellField.ext fun x => by
    simp only [ShellField.translate_apply, add_assoc]

/-- **The `W̲^{2,∞}` gauge is covariant: the sample translation shifts the base
point additively.**  `‖j‖_{W̲^{2,∞}(z+□_k)}` of the `y`-translated sample is
`‖j‖_{W̲^{2,∞}((z+y)+□_k)}` of the sample. -/
theorem shellW2InfNormAt_translateCutoffSample (y z : Vec d) (k l : ℤ)
    (omega : Cutoff.CutoffSample d) :
    Support.shellW2InfNormAt z k
        ((Cutoff.translateCutoffSample y omega).1 l) =
      Support.shellW2InfNormAt (z + y) k (omega.1 l) := by
  show Support.shellW2InfNormAt z k (ShellField.translate y (omega.1 l)) = _
  rw [Support.shellW2InfNormAt_def, Support.shellW2InfNormAt_def,
    shellField_translate_translate]

/-- **The `W̲^{1,∞}` gauge has no base point, so it is covariant only through
the shell.**  The sample translation replaces the shell `j_l` by
`ShellField.translate y j_l`, i.e. moves the gauge from `□_m` to `y+□_m`; the
naive invariance in `y` is false. -/
theorem shellW1InfGradNorm_translateCutoffSample (y : Vec d) (m l : ℤ)
    (omega : Cutoff.CutoffSample d) :
    Support.shellW1InfGradNorm m
        ((Cutoff.translateCutoffSample y omega).1 l) =
      Support.shellW1InfGradNorm m (ShellField.translate y (omega.1 l)) :=
  rfl

theorem shellW1InfGradNorm_translateCutoffSample_le_shellW2InfNormAt
    (y : Vec d) (m l : ℤ) (omega : Cutoff.CutoffSample d) :
    Support.shellW1InfGradNorm m
        ((Cutoff.translateCutoffSample y omega).1 l) ≤
      Support.shellW2InfNormAt y m (omega.1 l) :=
  Support.shellW1InfGradNorm_translate_le_shellW2InfNormAt y m (omega.1 l)

/-- The triadic lattice `3^j ℤ^d` is closed under addition. -/
theorem triadicLatticePoint_add (j : ℤ) (v w : Fin d → ℤ) :
    Support.triadicLatticePoint j v + Support.triadicLatticePoint j w =
      Support.triadicLatticePoint j (v + w) := by
  funext i
  show (3 : ℝ) ^ j * (v i : ℝ) + (3 : ℝ) ^ j * (w i : ℝ) =
    (3 : ℝ) ^ j * (((v + w) i : ℤ) : ℝ)
  rw [Pi.add_apply, Int.cast_add]
  ring

/-- A point of the coarse lattice `3^k ℤ^d` is a point of the finer lattice
`3^i ℤ^d` whenever `i ≤ k`.  The hypothesis is supplied by `Finset.mem_Icc` at
every §4.2 consumer (the centre lattice of `minimal_scale_separation` is
`3^{n-1}ℤ^d` and the inner scales run over `Finset.Icc n m`). -/
theorem triadicLatticePoint_of_le {i k : ℤ} (hik : i ≤ k) (v : Fin d → ℤ) :
    Support.triadicLatticePoint k v =
      Support.triadicLatticePoint i (fun a => 3 ^ (k - i).toNat * v a) := by
  have hcast : (((k - i).toNat : ℤ)) = k - i := Int.toNat_of_nonneg (by omega)
  have hsum : i + (k - i) = k := by omega
  funext a
  show (3 : ℝ) ^ k * (v a : ℝ) =
    (3 : ℝ) ^ i * (((3 ^ (k - i).toNat * v a : ℤ) : ℝ))
  rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, ← mul_assoc,
    ← zpow_natCast (3 : ℝ) (k - i).toNat, hcast,
    ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), hsum]

/-- **The lattice-maximum shape.**  After a translation by a centre of the
finer lattice `3^i ℤ^d`, the `W̲^{2,∞}` gauge at a coarse centre
`3^k v` is the gauge at a single point of `3^i ℤ^d`. -/
theorem shellW2InfNormAt_triadicLatticePoint_translateCutoffSample {i k : ℤ}
    (hik : i ≤ k) (v w : Fin d → ℤ) (l : ℤ) (omega : Cutoff.CutoffSample d) :
    Support.shellW2InfNormAt (Support.triadicLatticePoint k v) k
        ((Cutoff.translateCutoffSample
          (Support.triadicLatticePoint i w) omega).1 l) =
      Support.shellW2InfNormAt
        (Support.triadicLatticePoint i (fun a => 3 ^ (k - i).toNat * v a + w a))
        k (omega.1 l) := by
  rw [shellW2InfNormAt_translateCutoffSample, triadicLatticePoint_of_le hik v,
    triadicLatticePoint_add]
  rfl

/-! ## 4. Transport of the law

Thin wrappers over the proved `measurePreserving_translateCutoffSample` of
`Translate.lean`, composed with the pointwise identities above.  Nothing about
the measure is re-proved here. -/

/-- Integrals are unchanged by a translation of the sample. -/
theorem lintegral_comp_translateCutoffSample (M : ABKModel d) (y : Vec d)
    {f : Cutoff.CutoffSample d → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ omega, f (Cutoff.translateCutoffSample y omega)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      ∫⁻ omega, f omega ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
  (measurePreserving_translateCutoffSample M y).lintegral_comp hf

/-- **The level sets of an observable at a translated sample carry the origin
mass.**  The general form; the two threshold specializations follow. -/
theorem measure_comp_translateCutoffSample (M : ABKModel d) (y : Vec d)
    {f : Cutoff.CutoffSample d → ℝ≥0∞} (hf : Measurable f) {B : Set ℝ≥0∞}
    (hB : MeasurableSet B) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | f (Cutoff.translateCutoffSample y omega) ∈ B} =
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | f omega ∈ B} :=
  measure_preimage_translateCutoffSample M y (hf hB)

/-- The `t ≤ ·` level set transfers. -/
theorem measure_le_comp_translateCutoffSample (M : ABKModel d) (y : Vec d)
    {f : Cutoff.CutoffSample d → ℝ≥0∞} (hf : Measurable f) (t : ℝ≥0∞) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t ≤ f (Cutoff.translateCutoffSample y omega)} =
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | t ≤ f omega} :=
  measure_comp_translateCutoffSample M y hf measurableSet_Ici

/-- The `t < ·` level set transfers: the shape a union bound over centres
consumes: the `Z₁` tail and the `Z₂` centre union. -/
theorem measure_lt_comp_translateCutoffSample (M : ABKModel d) (y : Vec d)
    {f : Cutoff.CutoffSample d → ℝ≥0∞} (hf : Measurable f) (t : ℝ≥0∞) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < f (Cutoff.translateCutoffSample y omega)} =
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | t < f omega} :=
  measure_comp_translateCutoffSample M y hf measurableSet_Ioi

/-- **The transport wrapper.**  If `f` is pointwise the origin observable `g`
read at the translated sample, its `t < ·` set carries the origin mass.  The
hypotheses are discharged by §2's indicator identities and by the
measurability lemmas below. -/
theorem measure_lt_of_eq_comp_translateCutoffSample (M : ABKModel d) (y : Vec d)
    {f g : Cutoff.CutoffSample d → ℝ≥0∞} (hg : Measurable g)
    (hfg : ∀ omega, f omega = g (Cutoff.translateCutoffSample y omega))
    (t : ℝ≥0∞) :
    (Cutoff.cutoffSampleLaw M).toMeasure {omega | t < f omega} =
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | t < g omega} := by
  have hset : {omega | t < f omega} =
      {omega | t < g (Cutoff.translateCutoffSample y omega)} :=
    Set.ext fun omega => by rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hfg omega]
  rw [hset]
  exact measure_lt_comp_translateCutoffSample M y hg t

/-! ### The two clauses of `minimal_scale_separation` at a centre -/

/-- The window sum of `minimal_scale_separation`'s first conclusion at
centre `y` is the origin window sum at the `y`-translated sample. -/
theorem sum_indicator_goodEventAt_comp_translate (M : ABKModel d) (Ccg : ℝ)
    (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    (∑ k ∈ Finset.Icc n m,
        Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)
          (fun omega' =>
            Support.fluxCorrectedErrorObservableSup M k s
              (Cutoff.translateCutoffSample y omega')) omega) =
      ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)
          (Support.fluxCorrectedErrorObservableSup M k s)
          (Cutoff.translateCutoffSample y omega) :=
  Finset.sum_congr rfl fun k _ =>
    indicator_goodEventAt_fluxCorrectedErrorObservableSup M Ccg k y s ep omega

/-- The Cesàro-normalized form, with the frozen prefactor left free. -/
theorem mul_sum_indicator_goodEventAt_comp_translate (M : ABKModel d) (Ccg : ℝ)
    (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ) (c : ℝ≥0∞)
    (omega : Cutoff.CutoffSample d) :
    c * (∑ k ∈ Finset.Icc n m,
        Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)
          (fun omega' =>
            Support.fluxCorrectedErrorObservableSup M k s
              (Cutoff.translateCutoffSample y omega')) omega) =
      c * ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)
          (Support.fluxCorrectedErrorObservableSup M k s)
          (Cutoff.translateCutoffSample y omega) :=
  congrArg (fun x => c * x)
    (sum_indicator_goodEventAt_comp_translate M Ccg y s ep n m omega)

/-- The bad-event count of the second conclusion at centre `y` is the origin
count at the `y`-translated sample. -/
theorem sum_indicator_compl_goodEventAt_comp_translate (M : ABKModel d)
    (Ccg : ℝ) (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    (∑ k ∈ Finset.Icc n m,
        Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)ᶜ
          (fun _ => (1 : ℝ≥0∞)) omega) =
      ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)ᶜ
          (fun _ => (1 : ℝ≥0∞)) (Cutoff.translateCutoffSample y omega) :=
  Finset.sum_congr rfl fun k _ =>
    indicator_compl_goodEventAt_one M Ccg k y s ep omega

/-- The Cesàro-normalized bad-event count. -/
theorem mul_sum_indicator_compl_goodEventAt_comp_translate (M : ABKModel d)
    (Ccg : ℝ) (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ) (c : ℝ≥0∞)
    (omega : Cutoff.CutoffSample d) :
    c * (∑ k ∈ Finset.Icc n m,
        Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)ᶜ
          (fun _ => (1 : ℝ≥0∞)) omega) =
      c * ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)ᶜ
          (fun _ => (1 : ℝ≥0∞)) (Cutoff.translateCutoffSample y omega) :=
  congrArg (fun x => c * x)
    (sum_indicator_compl_goodEventAt_comp_translate M Ccg y s ep n m omega)

/-- The origin window average is measurable. -/
theorem measurable_mul_sum_indicator_goodEventBase (M : ABKModel d) (Ccg : ℝ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ) (c : ℝ≥0∞) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      c * ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)
          (Support.fluxCorrectedErrorObservableSup M k s) omega := by
  refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => ?_) _
  exact (Support.measurable_fluxCorrectedErrorObservableSup M k s).indicator
    (Support.measurableSet_goodEventBase M Ccg k s ep)

/-- The origin bad-event count is measurable. -/
theorem measurable_mul_sum_indicator_compl_goodEventBase (M : ABKModel d)
    (Ccg : ℝ) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ) (c : ℝ≥0∞) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      c * ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)ᶜ
          (fun _ => (1 : ℝ≥0∞)) omega := by
  refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => ?_) _
  exact measurable_const.indicator
    (Support.measurableSet_goodEventBase M Ccg k s ep).compl

/-- **The `Z₂` centre union, first clause.**  The bad set of the window average at
centre `y` has exactly the mass of the bad set at the origin — the per-centre
input of the union bound over `z ∈ 3^{n-1}ℤ^d ∩ □_m`. -/
theorem measure_lt_mul_sum_indicator_goodEventAt (M : ABKModel d) (Ccg : ℝ)
    (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ) (c t : ℝ≥0∞) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < c * ∑ k ∈ Finset.Icc n m,
          Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)
            (fun omega' =>
              Support.fluxCorrectedErrorObservableSup M k s
                (Cutoff.translateCutoffSample y omega')) omega} =
      (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < c * ∑ k ∈ Finset.Icc n m,
          Set.indicator (Support.goodEventBase M Ccg k s ep)
            (Support.fluxCorrectedErrorObservableSup M k s) omega} :=
  measure_lt_of_eq_comp_translateCutoffSample M y
    (measurable_mul_sum_indicator_goodEventBase M Ccg s ep n m c)
    (fun omega =>
      mul_sum_indicator_goodEventAt_comp_translate M Ccg y s ep n m c omega) t

/-- **The `Z₂` centre union, second clause.**  The same transfer for the
bad-event count. -/
theorem measure_lt_mul_sum_indicator_compl_goodEventAt (M : ABKModel d)
    (Ccg : ℝ) (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ)
    (c t : ℝ≥0∞) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < c * ∑ k ∈ Finset.Icc n m,
          Set.indicator
            (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)ᶜ
            (fun _ => (1 : ℝ≥0∞)) omega} =
      (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < c * ∑ k ∈ Finset.Icc n m,
          Set.indicator (Support.goodEventBase M Ccg k s ep)ᶜ
            (fun _ => (1 : ℝ≥0∞)) omega} :=
  measure_lt_of_eq_comp_translateCutoffSample M y
    (measurable_mul_sum_indicator_compl_goodEventBase M Ccg s ep n m c)
    (fun omega =>
      mul_sum_indicator_compl_goodEventAt_comp_translate M Ccg y s ep n m c
        omega) t

end

end Algsuperdiff.Section4.Provider.GoodEvents
