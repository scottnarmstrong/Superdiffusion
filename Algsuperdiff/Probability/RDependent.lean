import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.Independence.Basic

/-!
# `r`-dependence of a `ℤ`-indexed family, and the `ZMod (r+1)` colouring

ABK26, Proposition `p.concentration`, specialised to a `ℤ`-indexed sequence.

> "Since the sequence `{X_j}` is **2-dependent**, we may apply Proposition
> `p.concentration` …"

## Why `r` and not `2`

The manuscript's "`2`-dependent" is dimension-restricted: the honest count
gives `r`-dependence for any `r` with `3^r > 3 + ⅔√d`, i.e. `r(d) = max{2,
⌈log₃(3 + ⅔√d)⌉}`, which equals `2` exactly for `d ≤ 80`.  The separation
geometry at our carrier is `Section4/Probability/AnnulusSeparation.lean`
(`separatedBy_annulusRegion_of_gap`, with the concrete `d ≤ 81` / `d ≤ 729`
instances).  `TwoDependent` is retained as the `r = 2` instance the
manuscript's regime uses.

## The colouring

Splitting a window `[n, m] ⊆ ℤ` into the `r+1` residue classes mod `r+1` makes
two distinct indices of one class differ by a nonzero multiple of `r+1`, hence be
`≥ r`-separated, hence make the class mutually independent. That separation
property is `le_abs_sub_of_intCast_zmod_eq`; the palette size is
`card_zmod_succ`.

## Main results

* `Algsuperdiff.Probability.RDependent.of_iIndepFun`, `.comp`, `.mono`
* `Algsuperdiff.Probability.le_abs_sub_of_intCast_zmod_eq`
* `Algsuperdiff.Probability.card_zmod_succ`

## References

* ABK26, Proposition `p.concentration`.
* ABK26, `l.minimal.scale.sep`, Step 1 (for the separation claim).
-/

namespace Algsuperdiff.Probability

open MeasureTheory

/-! ## The `r`-dependence hypothesis -/

/-- A family `X : ℤ → Ω → ℝ` is **`r`-dependent**: any finite set of pairwise `≥
r`-separated indices is mutually independent.  This is the hypothesis of ABK26
`p.concentration` specialised to a `ℤ`-indexed sequence, and the hypothesis
under which Step 1 of `l.minimal.scale.sep` invokes it. -/
def RDependent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℤ → Ω → ℝ)
    (r : ℕ) : Prop :=
  ∀ s : Finset ℤ, (∀ i ∈ s, ∀ j ∈ s, i ≠ j → (r : ℤ) ≤ |i - j|) →
    ProbabilityTheory.iIndepFun (fun (i : {i // i ∈ s}) => X i.1) P

/-- **The `r = 2` instance** — the manuscript's regime (`d ≤ 80`). `X_n` and
`X_{n'}` are independent whenever `|n − n'| ≥ 2`. -/
def TwoDependent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℤ → Ω → ℝ) : Prop :=
  RDependent P X 2

/-- Full independence is `r`-dependence, for every `r`. -/
theorem RDependent.of_iIndepFun {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℤ → Ω → ℝ} (h : ProbabilityTheory.iIndepFun X P) (r : ℕ) : RDependent P X r :=
  fun s _ => h.precomp (g := (Subtype.val : {i // i ∈ s} → ℤ)) Subtype.val_injective

/-- `r`-dependence is stable under composing each coordinate with a measurable map
(used to pass from `X` to the centred family `X − E X`). -/
theorem RDependent.comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℤ → Ω → ℝ} {r : ℕ} (h : RDependent P X r) (g : ℤ → ℝ → ℝ)
    (hg : ∀ j, Measurable (g j)) :
    RDependent P (fun j ω => g j (X j ω)) r := by
  intro s hs
  exact (h s hs).comp (fun (i : {i // i ∈ s}) => g i.1) (fun i => hg i.1)

/-- `r`-dependence weakens as `r` grows. -/
theorem RDependent.mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℤ → Ω → ℝ} {r r' : ℕ} (h : RDependent P X r) (hrr : r ≤ r') :
    RDependent P X r' := by
  intro s hs
  refine h s (fun i hi j hj hij => le_trans ?_ (hs i hi j hj hij))
  exact_mod_cast hrr

/-! ## The `ZMod (r+1)` colouring of a window -/

/-- **The colouring's separation property.** Two distinct integers with the same
residue mod `r+1` differ by a nonzero multiple of `r+1`, hence by at least
`r+1`. (For `r = 2` this is "same residue mod `3` ⟹ `|i − j| > 1`".) -/
theorem le_abs_sub_of_intCast_zmod_eq {r : ℕ} {i j : ℤ}
    (h : ((i : ZMod (r + 1))) = ((j : ZMod (r + 1)))) (hij : i ≠ j) :
    ((r : ℤ) + 1) ≤ |i - j| := by
  have hmod : Int.ModEq ((r : ℤ) + 1) i j := by
    have h' := (ZMod.intCast_eq_intCast_iff i j (r + 1)).mp h
    have hcast : (((r + 1 : ℕ) : ℤ)) = (r : ℤ) + 1 := by push_cast; ring
    rwa [hcast] at h'
  have hdvd : ((r : ℤ) + 1) ∣ (i - j) := (Int.ModEq.dvd hmod.symm)
  have hpos : (0 : ℤ) < |i - j| := abs_pos.mpr (sub_ne_zero.2 hij)
  exact Int.le_of_dvd hpos ((dvd_abs _ _).mpr hdvd)

/-- The `ZMod (r+1)` palette has exactly `r+1` colours. -/
theorem card_zmod_succ (r : ℕ) : ((Fintype.card (ZMod (r + 1)) : ℕ) : ℝ) = (r : ℝ) + 1 := by
  rw [ZMod.card]
  push_cast
  ring

end Algsuperdiff.Probability
