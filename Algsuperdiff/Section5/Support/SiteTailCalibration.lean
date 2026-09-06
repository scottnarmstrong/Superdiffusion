/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Algsuperdiff.Section5.Support.SiteTails

/-!
# Elementary bounds used by site-tail calibration

This module retains the two dimension and gate-factor bounds shared with the
active calibration modules.
-/
namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3

/-! ## Elementary bounds -/

/-- The shift factor `3^{a · sepShift d}` is at least one. -/
theorem one_le_shiftFactor (d : ℕ) :
    (1 : ℝ) ≤ (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) := by
  refine Real.one_le_rpow (by norm_num) ?_
  have h : (0 : ℝ) ≤ (Provider.Percolation.sepShift d : ℝ) := Nat.cast_nonneg _
  have ha : (0 : ℝ) < sitePathExponent := by rw [sitePathExponent]; norm_num
  positivity

/-- The bracket of the constant is at least one. -/
theorem one_le_gateBracket (Cpath : ℝ) : (1 : ℝ) ≤ 1 + Real.log 3 + (16 * Cpath) ^ 2 := by
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hsq : (0 : ℝ) ≤ (16 * Cpath) ^ 2 := sq_nonneg _
  linarith only [hlog, hsq]

end Algsuperdiff.Section5.Support
