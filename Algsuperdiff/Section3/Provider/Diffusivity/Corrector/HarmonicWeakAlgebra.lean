import Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicWeak

/-!
# Additive algebra of the distributional harmonicity predicate

`HarmonicWeak` proves that `IsWeaklyHarmonicOn` is stable under restriction to a
subset, under multiplication by a constant, and that constants are weakly
harmonic.  It does **not** prove stability under addition or subtraction, and
that is the one closure property the nested-recentring route of
`OscillationTelescope` cannot do without: the harmonic increment born at scale
`j` is the difference `h_j - h_{j+1}` of two harmonic replacements built at
consecutive scales, and its harmonicity on the finer cube is what feeds the
arbitrary-gap decay.

Additivity is *not* formal here.  `IsWeaklyHarmonicOn U u` asserts that the
Green pairing `int_U u * (Delta psi)` vanishes; splitting that pairing for a sum
requires knowing that each half is separately integrable, which does not follow
from the vanishing of the sum.  The minimal hypothesis that supplies it is
integrability of each summand on `U` alone: the multiplier `Delta psi` is
continuous with compact support, hence bounded, so a merely integrable function
stays integrable after multiplication by it.  In the intended application `u`
and `v` are `H^1(U)` functions on a bounded cube, for which `L^2(U) subset
L^1(U)` gives the hypothesis for free.

## Contents

* `integrableOn_mul_euclideanCoordLaplacian` -- the Green integrand of an
  integrable function against a smooth compactly supported test is integrable.
* `IsWeaklyHarmonicOn.add`, `IsWeaklyHarmonicOn.sub` -- the two closure
  properties, each under integrability of the two summands on `U`.

## Portability

This file depends only on **Mathlib**, on **CoarseGraining**
(`Homogenization.*`) and on the harmonic layer of this same directory.  It
mentions no object of the manuscript: no model, no cutoff, no shell, no
corrector, no `sigmaBar`.  It is intended to be portable into CoarseGraining by
a single mechanical namespace rename.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open Homogenization MeasureTheory

variable {d : ℕ}

/-- **The Green integrand of an integrable function is integrable.**

The coordinate Laplacian of a smooth compactly supported test function is
continuous with compact support, hence bounded; multiplying an integrable
function by a bounded measurable one preserves integrability. -/
theorem integrableOn_mul_euclideanCoordLaplacian {U : Set (Vec d)} {u ψ : Vec d → ℝ}
    (hu : IntegrableOn u U volume) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    IntegrableOn (fun x => u x * euclideanCoordLaplacian ψ x) U volume := by
  have hψ2 : ContDiff ℝ (2 : ℕ) ψ := hψ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hcont : Continuous (euclideanCoordLaplacian ψ) :=
    continuous_euclideanCoordLaplacian_of_contDiff_two hψ2
  obtain ⟨C, hC⟩ :=
    (hasCompactSupport_euclideanCoordLaplacian hψc).exists_bound_of_continuous hcont
  exact hu.mul_bdd hcont.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- **Weak harmonicity is additive.**

If `u` and `v` are weakly harmonic on `U` and each is integrable on `U`, then so
is `u + v`.  The integrability hypotheses are exactly what is needed to split the
Green pairing of the sum. -/
theorem IsWeaklyHarmonicOn.add {U : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : IsWeaklyHarmonicOn U u) (hv : IsWeaklyHarmonicOn U v)
    (hui : IntegrableOn u U volume) (hvi : IntegrableOn v U volume) :
    IsWeaklyHarmonicOn U (fun x => u x + v x) := by
  intro ψ hψ hψc hsupp
  have hiu : IntegrableOn (fun x => u x * euclideanCoordLaplacian ψ x) U volume :=
    integrableOn_mul_euclideanCoordLaplacian hui hψ hψc
  have hiv : IntegrableOn (fun x => v x * euclideanCoordLaplacian ψ x) U volume :=
    integrableOn_mul_euclideanCoordLaplacian hvi hψ hψc
  have hpt : ∀ x : Vec d, (u x + v x) * euclideanCoordLaplacian ψ x =
      u x * euclideanCoordLaplacian ψ x + v x * euclideanCoordLaplacian ψ x := by
    intro x
    ring
  simp only [hpt]
  rw [integral_add hiu hiv, hu ψ hψ hψc hsupp, hv ψ hψ hψc hsupp, add_zero]

/-- **Weak harmonicity is stable under subtraction.**

The closure property consumed by the nested-recentring telescope: the harmonic
increment `h_j - h_{j+1}` of two harmonic replacements born at consecutive scales
is weakly harmonic on the finer cube, where both are defined. -/
theorem IsWeaklyHarmonicOn.sub {U : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : IsWeaklyHarmonicOn U u) (hv : IsWeaklyHarmonicOn U v)
    (hui : IntegrableOn u U volume) (hvi : IntegrableOn v U volume) :
    IsWeaklyHarmonicOn U (fun x => u x - v x) := by
  intro ψ hψ hψc hsupp
  have hiu : IntegrableOn (fun x => u x * euclideanCoordLaplacian ψ x) U volume :=
    integrableOn_mul_euclideanCoordLaplacian hui hψ hψc
  have hiv : IntegrableOn (fun x => v x * euclideanCoordLaplacian ψ x) U volume :=
    integrableOn_mul_euclideanCoordLaplacian hvi hψ hψc
  have hpt : ∀ x : Vec d, (u x - v x) * euclideanCoordLaplacian ψ x =
      u x * euclideanCoordLaplacian ψ x - v x * euclideanCoordLaplacian ψ x := by
    intro x
    ring
  simp only [hpt]
  rw [integral_sub hiu hiv, hu ψ hψ hψc hsupp, hv ψ hψ hψc hsupp, sub_zero]

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
