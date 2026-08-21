import Mathlib
import Algsuperdiff.MainTheorems
import Audit.GeneratorRenormalization.SolutionBasic
import Audit.Support.GeneratorRenormalizationBridge

/-!
# Solution: GeneratorRenormalization

The challenge module `Audit/GeneratorRenormalization/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the
repository together with `Audit.GeneratorRenormalization.SolutionBasic` — a verbatim copy of the
challenge's statement vocabulary — and proves the audited theorem with a
byte-identical statement, through the bridges in `Audit/Support/`.
-/

namespace Algsuperdiff
namespace StatementAudit
namespace GeneratorRenormalization

open Audit.Support.GRBridge
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

theorem generator_renormalization
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : Model d, RealizesCstar d M.P cstar → M.gamma ≤ gamma0 →
        ∀ m : ℤ, ∃ sigmaBarM : ℝ, 0 < sigmaBarM ∧
          |sigmaBarM -
              Real.sqrt (M.nu ^ (2 : ℕ) +
                cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
            C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM ∧
          ∃ EB : CutoffSample d → ℝ,
            (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
            (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
              (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                  ∂cutoffSampleMeasure M.P) ≤
                ENNReal.ofReal
                    (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                      Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
            ∀ᵐ omega ∂cutoffSampleMeasure M.P,
              ∀ L : ℤ, m ≤ L →
                ∀ (u v h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d)
                  (Kg Kh KhInf : ℝ),
                  IsDirichletSolutionOn (coefficientCutoff M.nu L omega)
                    (originCube d m) u h g →
                  IsDirichletSolutionOn
                    (fun _ : Vec d => sigmaBarM • (1 : Mat d))
                    (originCube d m) v h g →
                  HolderSeminormBoundOn (openCubeSet (originCube d m))
                    (1 / 2) Kg g →
                  HolderSeminormBoundOn (openCubeSet (originCube d m))
                    (1 / 2) Kh h.grad →
                  (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
                  HasGradientOn (openCubeSet (originCube d m))
                    h.toFun h.grad →
                  (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
                      Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                        EB omega *
                          (sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                            (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                    |volumeAverage (openCubeSet (originCube d m))
                          (fun y => M.nu * vecNormSq (u.grad y)) -
                        volumeAverage (openCubeSet (originCube d m))
                          (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
                      EB omega *
                        (Real.sqrt sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                            Real.sqrt sigmaBarM *
                              (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                          (2 : ℕ) := by
  obtain ⟨gamma0, C, hgamma0, hC, hmain⟩ :=
    _root_.Algsuperdiff.generator_renormalization d cstar _hcstar
  refine ⟨gamma0, C, hgamma0, hC, ?_⟩
  intro M hreal hgamma m
  have hcs : _root_.Algsuperdiff.Section3.Disorder.cstar (toABKModel M) = cstar :=
    (realizesCstar_iff_cstar_eq (toABKModel M) _hcstar).mp hreal
  obtain ⟨sigmaBarM, hsig, hband, EB, hEB0, hEBm, hEBmom, hae⟩ :=
    hmain (toABKModel M) hcs hgamma m
  refine ⟨sigmaBarM, hsig, hband, EB, hEB0, hEBm, hEBmom, ?_⟩
  filter_upwards [hae] with omega homega
  intro L hL u v h g Kg Kh KhInf hdir1 hdir2 hHg hHh hKinf hgrad
  exact homega L hL (toRepoH1 u) (toRepoH1 v) (toRepoH1 h) g Kg Kh KhInf
    ((isDirichletSolutionOn_iff _ _ _ _ _).mp hdir1)
    ((isDirichletSolutionOn_iff _ _ _ _ _).mp hdir2)
    hHg hHh hKinf hgrad


end

end GeneratorRenormalization
end StatementAudit
end Algsuperdiff
