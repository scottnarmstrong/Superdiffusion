/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Log-subexponential tail profiles

This file supplies the deterministic integrability input for the localized
stream-field resolvent tail.  The profile has the form

`C (1 + s₊)^n exp (-c s₊ / (1 + log (1 + s₊)))`,

where `s₊ = max s 0`.  The natural algebraic prefactor is retained explicitly.
The logarithmic denominator still leaves a finite cubic layer-cake integral.
-/

namespace Algsuperdiff.Section5.Field

open MeasureTheory Set

noncomputable section

/-- A log-subexponential profile with an explicit algebraic prefactor. -/
def logSubexponentialProfile (C c : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  C * (1 + max s 0) ^ n *
    Real.exp (-c * max s 0 / (1 + Real.log (1 + max s 0)))

/-- The profile is nonnegative when its amplitude is nonnegative. -/
theorem logSubexponentialProfile_nonneg {C : ℝ} (hC : 0 ≤ C)
    (c : ℝ) (n : ℕ) (s : ℝ) :
    0 ≤ logSubexponentialProfile C c n s := by
  unfold logSubexponentialProfile
  positivity

end

end Algsuperdiff.Section5.Field
