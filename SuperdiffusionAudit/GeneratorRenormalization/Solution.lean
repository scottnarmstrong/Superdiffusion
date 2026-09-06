import Mathlib
import Algsuperdiff.Frozen.Introduction.GeneratorRenormalization
import SuperdiffusionAudit.GeneratorRenormalization.SolutionBasic
import SuperdiffusionAudit.Support.GeneratorRenormalizationBridge

/-!
# Solution: GeneratorRenormalization

The challenge module `SuperdiffusionAudit/GeneratorRenormalization/Challenge.lean` imports only
Mathlib and states the theorem with one intentional `sorry`.  This solution
imports the repository together with
`SuperdiffusionAudit.GeneratorRenormalization.SolutionBasic` — a verbatim copy of the challenge's
statement vocabulary — and proves the audited theorem with a byte-identical
statement, through the bridges in `SuperdiffusionAudit/Support/`.

The repository theorem consumed is
`Algsuperdiff.Frozen.Introduction.generator_renormalization`, the introduction's
form of [ABK] Theorem B: the estimate for the coefficient field
`a = ν·Id + k` itself, read on the full-tail carrier under its law, with no
infrared cutoff.  Four bridge families carry the statement across.

* **The model.**  `toABKModel` assembles the challenge's flat `Model` into the
  repository's nested `ABKModel`, and `realizesCstar_iff_cstar_eq` turns the
  challenge's corrector-energy display into the repository's
  `Disorder.cstar M = cstar`.
* **The carrier, the law and the field.**  `fullSample_eq`,
  `fullSampleMeasure_toABKModel`, `streamField_eq` and `streamCoefficient_eq`
  identify the full-tail subtype, the annealed law and the stream coefficient
  with the repository's; all four are definitional.  The law is rewritten
  along the second of them before the error amplitude is supplied, so that the
  moment bound and the almost-sure clause are matched syntactically rather
  than unfolded; the carrier and the field are left to definitional unfolding.
* **The Dirichlet problem.**  `toRepoH1` copies an `H1Function` across, and
  `isDirichletSolutionOn_iff` matches the two weak-solution predicates; the
  triadic cube of the challenge is the repository's by `toRepoCube_originCube`.
* **The displays.**  The Hölder seminorm bound, the classical gradient, the
  volume average and the squared Euclidean length are shared definitionally
  (`holderSeminormBoundOn_eq`, `hasGradientOn_eq`, `volumeAverage_eq`,
  `vecNormSq_eq`).
-/

namespace Algsuperdiff
namespace StatementAudit
namespace GeneratorRenormalization

open SuperdiffusionAudit.Support.GRBridge
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
          ∃ EB : FullSample d M.gamma → ℝ,
            (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
            (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
              (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                  ∂fullSampleMeasure M.gamma M.P) ≤
                ENNReal.ofReal
                    (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                      Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
            ∀ᵐ omega ∂fullSampleMeasure M.gamma M.P,
              ∀ (u v h : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d)
                (Kg Kh KhInf : ℝ),
                IsDirichletSolutionOn (streamCoefficient M.nu omega)
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
    _root_.Algsuperdiff.Frozen.Introduction.generator_renormalization d cstar _hcstar
  refine ⟨gamma0, C, hgamma0, hC, ?_⟩
  intro M hreal hgamma m
  have hcs : _root_.Algsuperdiff.Section3.Disorder.cstar (toABKModel M) = cstar :=
    (realizesCstar_iff_cstar_eq (toABKModel M) _hcstar).mp hreal
  obtain ⟨sigmaBarM, hsig, hband, EB, hEB0, hEBm, hEBmom, hae⟩ :=
    hmain (toABKModel M) hcs hgamma m
  -- The challenge's annealed law is the repository's; naming that identity
  -- here leaves the moment bound and the almost-sure clause to be matched
  -- against the repository's on the nose.
  rw [fullSampleMeasure_toABKModel M]
  refine ⟨sigmaBarM, hsig, hband, EB, hEB0, hEBm, hEBmom, ?_⟩
  filter_upwards [hae] with omega homega
  intro u v h g Kg Kh KhInf hdir1 hdir2 hHg hHh hKinf hgrad
  exact homega (toRepoH1 u) (toRepoH1 v) (toRepoH1 h) g Kg Kh KhInf
    ((isDirichletSolutionOn_iff _ _ _ _ _).mp hdir1)
    ((isDirichletSolutionOn_iff _ _ _ _ _).mp hdir2)
    hHg hHh hKinf hgrad

end

end GeneratorRenormalization
end StatementAudit
end Algsuperdiff
