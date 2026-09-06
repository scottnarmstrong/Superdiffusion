import Algsuperdiff.StochasticProcess.Common.Regularity.Ported.EnergyMinimality
import Algsuperdiff.StochasticProcess.Common.Regularity.Ported.Carrier
import Algsuperdiff.Section4.Provider.Schauder.CubeSchauderFreezing
import Algsuperdiff.Section4.Provider.ExcessDecay.HarmonicReplacement
import Homogenization.Book.Ch01.Theorems.MeanSquareDeviation

/-!
# Harmonic replacement on Euclidean balls

This is the Dirichlet comparison used in the small-contrast Schauder estimate.
The local Section 4 Dirichlet solver is reused; only the ball-specific package
and its retained zero-trace witness are adapted here.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory Homogenization
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.Schauder

noncomputable section

variable {d : ℕ}

/-- Explicit Euclidean balls are open bounded convex domains. -/
theorem isOpenBoundedConvexDomain_euclideanBall (z : Vec d) {r : ℝ}
    (hr : 0 < r) : IsOpenBoundedConvexDomain (euclideanBall z r) := by
  refine ⟨isOpen_euclideanBall z r, ?_, convex_euclideanBall z r⟩
  exact Bornology.IsBounded.isBoundedDomain
    (Metric.isBounded_ball.subset (euclideanBall_subset_metricBall hr))

/-- A weakly harmonic replacement with its concrete zero-trace witness and
pointwise gradient identity. -/
theorem exists_unitHarmonicReplacement_withGradient [NeZero d]
    {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (Phi : H1Function V) :
    ∃ h : H1Function V, ∃ rho : H10Function V,
      IsUnitWeaklyHarmonicOn V h ∧
      (∀ x, h.toFun x = Phi.toFun x + rho.toH1Function.toFun x) ∧
      ∀ x, h.grad x = Phi.grad x + rho.toH1Function.grad x := by
  letI : IsFiniteMeasure (volumeMeasureOn V) := hV.isFiniteMeasure_restrict_volume
  have hgrad : MemVectorL2 V Phi.grad := Phi.grad_memVectorL2
  obtain ⟨rho, hrho⟩ := exists_h10_isDivFormWeakSolutionOn_one hV hne hgrad
  have hrhoL2 : MemVectorL2 V rho.toH1Function.grad :=
    rho.toH1Function.grad_memVectorL2
  let h : H1Function V := Phi + rho.toH1Function
  have hharm : IsUnitWeaklyHarmonicOn V h := by
    intro phi
    have hsplit := integral_vecDot_add_left_split (U := V) hgrad hrhoL2
      (H := h.grad) (fun x => by simp [h]) phi
    have hid := isDivFormWeakSolutionOn_one_iff.1 hrho phi
    rw [hsplit, hid]
    ring
  refine ⟨h, rho, hharm, ?_, ?_⟩
  · intro x
    simp [h, H1Function.add_toFun]
  · intro x
    simp [h, H1Function.add_grad]

/-- Harmonic replacement on a Euclidean ball, including the exact Dirichlet
energy comparison with the datum. -/
theorem exists_unitHarmonicReplacement_euclideanBall [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall z r)) :
    ∃ h : H1Function (euclideanBall z r), ∃ rho : H10Function (euclideanBall z r),
      IsUnitWeaklyHarmonicOn (euclideanBall z r) h ∧
      (∀ x, h.toFun x = u.toFun x + rho.toH1Function.toFun x) ∧
      (∀ x, h.grad x = u.grad x + rho.toH1Function.grad x) ∧
      (∫ x in euclideanBall z r, vecDot (h.grad x) (h.grad x) ∂volume ≤
        ∫ x in euclideanBall z r, vecDot (u.grad x) (u.grad x) ∂volume) := by
  obtain ⟨h, rho, hharm, hfun, hgrad⟩ :=
    exists_unitHarmonicReplacement_withGradient
      (isOpenBoundedConvexDomain_euclideanBall z hr)
      (euclideanBall_nonempty z hr) u
  refine ⟨h, rho, hharm, hfun, hgrad, ?_⟩
  exact integral_vecDot_grad_self_le_of_isUnitWeaklyHarmonicOn hharm rho hgrad

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
