/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Algsuperdiff.StochasticProcess.Common.Regularity.SectorReflectionBox
import Algsuperdiff.StochasticProcess.Common.Regularity.Ported.GradientScaleReadout

/-!
# Gap scales and snapped centres for axis cubes

This file isolates the finite-dimensional geometry used to pass from estimates
centred on cube faces to estimates centred at arbitrary points of the cube.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity

open Homogenization
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-- Every point of an open axis cube belongs to its coordinatewise closure. -/
theorem axisCube_subset_closureSet (z : Vec d) (L : ℝ) :
    axisCube z L ⊆ {x | MemAxisCubeClosure z L x} := by
  intro x hx i
  have hi := mem_axisCube_iff.mp hx i
  exact ⟨hi.1.le, hi.2.le⟩

end

end Algsuperdiff.StochasticProcess.Common.Regularity
