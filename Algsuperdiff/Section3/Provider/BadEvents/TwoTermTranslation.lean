import Algsuperdiff.Section3.Probability.TwoTermOrlicz
import Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

/-!
# Translation of two-term weak-Orlicz bounds

This module transports a two-term weak-Orlicz bound along the
measure-preserving translation action on cutoff samples. Both measurable
witnesses are translated together, so their pointwise domination and their
individual tail scales are unchanged.

## Main result

* `isTwoTermBigOWith_comp_translateCutoffSample`: translation preserves an
  `IsTwoTermBigOWith` bound without changing either profile or amplitude.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open Homogenization
open Algsuperdiff.Section3.Cutoff

variable {d : ℕ}

/-- A two-term weak-Orlicz bound on the cutoff carrier is preserved under every
real translation of the sample, with the same two profiles and amplitudes. -/
theorem isTwoTermBigOWith_comp_translateCutoffSample
    (M : ABKModel d) (z : Vec d)
    {Ψ₁ Ψ₂ : ℝ → ℝ} {X : CutoffSample d → ℝ} {A₁ A₂ : ℝ}
    (h : Probability.IsTwoTermBigOWith
      (cutoffSampleLaw M).toMeasure Ψ₁ Ψ₂ X A₁ A₂) :
    Probability.IsTwoTermBigOWith
      (cutoffSampleLaw M).toMeasure Ψ₁ Ψ₂
      (fun omega => X (translateCutoffSample z omega)) A₁ A₂ := by
  obtain ⟨Y, Z, hΨ₁, hΨ₂, hA₁, hA₂, hX, hY, hZ, hdom, hYtail, hZtail⟩ := h
  refine ⟨fun omega => Y (translateCutoffSample z omega),
    fun omega => Z (translateCutoffSample z omega),
    hΨ₁, hΨ₂, hA₁, hA₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hX.comp (measurable_translateCutoffSample z)
  · exact hY.comp (measurable_translateCutoffSample z)
  · exact hZ.comp (measurable_translateCutoffSample z)
  · exact fun omega => hdom (translateCutoffSample z omega)
  · exact Stream.isBigOWith_comp_translateCutoffSample M z hY hYtail
  · exact Stream.isBigOWith_comp_translateCutoffSample M z hZ hZtail

end Algsuperdiff.Section3.Provider.BadEvents
