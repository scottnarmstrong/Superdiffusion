import Algsuperdiff.Frozen.Section3.CoarseEllipticityBounds

/-!
# The definite coarse-ellipticity display constant

The manuscript's `C_{(e.cg.ellip.lower)}` inside the good event `𝒢₀`
(definition `d.good.event.for.lambda`) is "the" constant of the Section 3
display `e.cg.ellip.lower`.  The Section 3 anchor `coarse_ellipticity_bounds`
is (proved), so the definite constant is extracted by choice from the proved
existential; positivity is the first projection of the chosen witness's
specification.  Every Section 4 frozen statement that mentions the constant
references this one shared definition, so no cross-anchor existential-witness
mismatch is possible.  The full defining property is
`(coarse_ellipticity_bounds d).choose_spec`.
-/

noncomputable def Algsuperdiff.Section4.Support.cgEllipLowerConstant (d : ℕ) : ℝ :=
  (Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds d).choose

theorem Algsuperdiff.Section4.Support.cgEllipLowerConstant_pos (d : ℕ) :
    0 < Algsuperdiff.Section4.Support.cgEllipLowerConstant d :=
  (Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds d).choose_spec.1
