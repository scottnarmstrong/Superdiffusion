import Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationErrorLocality

/-! # Well-definedness of the origin-cube homogenization error -/

namespace Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError

open Homogenization Homogenization.Book.Ch02 MeasureTheory

variable {d : ℕ}

/-- The unique-value proof used by the frozen origin-cube homogenization-error
anchor. -/
theorem existsUnique [NeZero d]
    (s : ℝ) (p q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) (a0 : Mat d) :
    ∃! value : ℝ, ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
        value = Book.Ch02.HomogenizationErrorOnCube
          (originCube d 0) s p q F a0 := by
  let F₀ := Classical.choose
    (Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a)
  have hF₀ : CoeffOn.AEEq (F₀.coeffOn (originCube d 0)) a :=
    Classical.choose_spec
      (Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a)
  refine ⟨Book.Ch02.HomogenizationErrorOnCube
      (originCube d 0) s p q F₀ a0, ?_, ?_⟩
  · intro F hF
    exact Algsuperdiff.Section24.UnitCubeMultiscale.homogenizationErrorOnCube_eq_of_root_aeeq
      a F₀ F hF₀ hF s p q a0
  · intro value hvalue
    exact hvalue F₀ hF₀

end Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError
