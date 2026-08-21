/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# The countable-`L` almost-everywhere merge

## The gap this module closes

flagged, for the future `hstep4` supplier, that the proved §4.3 producers put
the infrared-cutoff quantifier OUTSIDE the almost-everywhere quantifier.  For
instance the excess-decay lane's harmonic-approximation provider concludes

```text
  ∀ L m n : ℤ, m ≤ L → … → ∀ᵐ ω ∂(law M), P L m n ω ,
```

whereas the §4.4 consumer needs the SINGLE null set

```text
  ∀ᵐ ω ∂(law M), ∀ L : ℤ, m ≤ L → P L m n ω .
```

The exchange is legitimate because `ℤ` is countable, and it is exactly
Mathlib's `MeasureTheory.ae_all_iff` / `MeasureTheory.ae_ball_iff`.  The merge
is proved here as a standalone
measure-theoretic lemma: this module imports only Mathlib, in particular no
§4.3 file, so no §4.3 statement is touched or re-elaborated.

## What is provided

* `ae_forall_of_forall_ae_of_countable` — the plain countable-index exchange
  with a guard predicate: from `∀ i, Q i → ∀ᵐ a, P i a` conclude
  `∀ᵐ a, ∀ i, Q i → P i a`.  The guard `Q` is arbitrary; the guarded index need
  not range over a subtype.
* `ae_forall_ge_of_forall_ge_ae` — the `ℤ` instance at the guard `m ≤ L`, i.e.
  the exact shape the `hstep4` supplier needs.
* `ae_forall_ge_ge_of_forall_ge_ge_ae` — the same with the two integer binders
  `m ≤ L` and `n ≤ m` merged simultaneously, since the §4.3 producers carry
  both.
* `ae_ball_of_forall_mem_ae` — the `Set.Countable` variant, for callers whose
  index range is a set rather than a predicate.

No measurability hypothesis appears anywhere: the a.e. filter is a
`CountableInterFilter`, and the merge uses nothing else.

## References

* Mathlib, `MeasureTheory.ae_all_iff`, `MeasureTheory.ae_ball_iff`.
* The excess-decay seal-distance lane (the consumer whose quantifier order
  motivates this file; NOT imported).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ## 1. The guarded countable exchange -/

/-- **The countable a.e. merge, with a guard.**

```text
  (∀ i, Q i → ∀ᵐ a ∂μ, P i a)   ⟹   ∀ᵐ a ∂μ, ∀ i, Q i → P i a .
```

The guarded indices form a countable subfamily of a countable family, so the
exceptional set is a countable union of null sets.  No measurability of `P` is
needed. -/
theorem ae_forall_of_forall_ae_of_countable {ι : Sort*} [Countable ι] {Q : ι → Prop}
    {P : ι → α → Prop} (h : ∀ i, Q i → ∀ᵐ a ∂μ, P i a) :
    ∀ᵐ a ∂μ, ∀ i, Q i → P i a := by
  classical
  have hstep : ∀ i : ι, ∀ᵐ a ∂μ, Q i → P i a := by
    intro i
    by_cases hi : Q i
    · exact (h i hi).mono fun a ha => fun _ => ha
    · exact Filter.Eventually.of_forall fun _ hQ => absurd hQ hi
  exact (ae_all_iff (p := fun a i => Q i → P i a)).2 hstep

/-- **The a.e. merge over `{L : ℤ // m ≤ L}`** — the exact shape the `hstep4`
supplier needs.

The §4.3 producers conclude `∀ L : ℤ, m ≤ L → ∀ᵐ ω ω`; the §4.4 consumer needs
the single null set.  `ℤ` is countable, so the two are interchangeable. -/
theorem ae_forall_ge_of_forall_ge_ae {m : ℤ} {P : ℤ → α → Prop}
    (h : ∀ L : ℤ, m ≤ L → ∀ᵐ a ∂μ, P L a) :
    ∀ᵐ a ∂μ, ∀ L : ℤ, m ≤ L → P L a :=
  ae_forall_of_forall_ae_of_countable (Q := fun L : ℤ => m ≤ L) h

/-- **The a.e. merge over the two integer binders at once.**

The §4.3 boundary producers carry `∀ L m : ℤ, m ≤ L → n ≤ m → ∀ᵐ ω m ω` (the
cutoff scale above the window scale, the window scale above the inner scale);
the consumer needs one null set for the whole pair.  `ℤ × ℤ` is countable. -/
theorem ae_forall_ge_ge_of_forall_ge_ge_ae {n : ℤ} {P : ℤ → ℤ → α → Prop}
    (h : ∀ L m : ℤ, m ≤ L → n ≤ m → ∀ᵐ a ∂μ, P L m a) :
    ∀ᵐ a ∂μ, ∀ L m : ℤ, m ≤ L → n ≤ m → P L m a := by
  have hpair : ∀ᵐ a ∂μ, ∀ p : ℤ × ℤ, (p.2 ≤ p.1 ∧ n ≤ p.2) → P p.1 p.2 a :=
    ae_forall_of_forall_ae_of_countable
      (Q := fun p : ℤ × ℤ => p.2 ≤ p.1 ∧ n ≤ p.2)
      (P := fun p : ℤ × ℤ => fun a => P p.1 p.2 a)
      (fun p hp => h p.1 p.2 hp.1 hp.2)
  exact hpair.mono fun a ha => fun L m hLm hnm => ha (L, m) ⟨hLm, hnm⟩

/-! ## 2. The set-indexed variant -/

/-- **The a.e. merge over a countable index S.**  The same exchange for callers
whose index range is a `Set.Countable` set rather than a predicate. -/
theorem ae_ball_of_forall_mem_ae {ι : Type*} {S : Set ι} (hS : S.Countable)
    {P : ι → α → Prop} (h : ∀ i ∈ S, ∀ᵐ a ∂μ, P i a) :
    ∀ᵐ a ∂μ, ∀ i ∈ S, P i a :=
  (ae_ball_iff (p := fun a i (_ : i ∈ S) => P i a) hS).2 h

end Algsuperdiff.Section4.Provider.Regularity
