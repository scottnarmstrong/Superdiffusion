/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExcessiveC0
import MarkovProcess.Kernel.OnePointExtension
import MarkovProcess.Semigroup.ExponentialComparison
import MarkovProcess.Trajectory.ExcessiveStopping
import Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Process
import MarkovProcess.Trajectory.FeynmanKacResolvent
import MarkovProcess.Trajectory.ResolventExitDecomposition

/-!
# The process-side lower resolvent comparison

The excessive analytic remainder controls the restart term in the resolvent
decomposition at the first exit from a bounded part domain.  Consequently the
resolvent of the process killed on that domain dominates the continuous zero
extension of the part resolvent.
-/

namespace DivergenceFormProcess.Form

open Homogenization MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d}

namespace WholeSpaceBarrierData

end WholeSpaceBarrierData

omit [NeZero d] in
/-- Zero extension at infinity does not change the resolvent at a live
starting point: the defect mass at infinity carries the vanishing value of the
extension there. -/
theorem onePointKernelResolvent_liveExtension_eq
    (R : PositiveC0ContractiveResolvent (Vec d)) (lam : ℝ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) (x : Vec d) :
    R.onePointKernelSemigroup.kernelResolvent lam
        (PositiveC0ContractiveResolvent.onePointLiveExtension f) (x : OnePoint (Vec d)) =
      R.kernelSemigroup.kernelResolvent lam f x := by
  unfold SubMarkovKernelSemigroup.kernelResolvent
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  dsimp only
  congr 1
  rw [R.onePointKernelSemigroup_apply_coe, lintegral_add_measure,
    lintegral_smul_measure,
    lintegral_dirac' _
      (PositiveC0ContractiveResolvent.measurable_onePointLiveExtension hf),
    PositiveC0ContractiveResolvent.onePointLiveExtension_infty, smul_zero,
    add_zero,
    lintegral_map (PositiveC0ContractiveResolvent.measurable_onePointLiveExtension hf)
      OnePoint.continuous_coe.measurable]
  rfl

namespace WholeSpaceBarrierData

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form
