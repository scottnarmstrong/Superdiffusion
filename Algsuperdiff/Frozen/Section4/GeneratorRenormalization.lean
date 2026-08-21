import Algsuperdiff.Section4.Support.Dirichlet
import Algsuperdiff.Section4.Support.ClassicalGradient
import Algsuperdiff.Section4.Support.ErrorAtoms
import Algsuperdiff.Section3.Disorder.Cstar
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamProviderFinal

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

/-!
# Generator renormalization — [ABK] Theorem B (`t.homogenization`)

At every scale `m` the coarse-grained generator is a constant multiple
`sigmaBar` of the identity, quantitatively close to
`sqrt (nu^2 + cstar gamma^{-1} 3^{2 gamma m})`, and the disorder solution `u`
is compared with the homogenized solution `v` of the same Dirichlet problem:
a single random error amplitude with Gaussian-type moments controls both the
uniform difference `u - v` and the difference of the two Dirichlet energies.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.generator_renormalization
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ m : ℤ, ∃ sigmaBarM : ℝ, 0 < sigmaBarM ∧
          |sigmaBarM -
              Real.sqrt (M.nu ^ (2 : ℕ) +
                cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
            C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM ∧
          ∃ EB : Cutoff.CutoffSample d → ℝ,
            (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
            (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
              (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                ENNReal.ofReal
                    (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                      Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ L : ℤ, m ≤ L →
                ∀ (u v h : Homogenization.H1Function
                      (Homogenization.openCubeSet (Homogenization.originCube d m)))
                  (g : Homogenization.Vec d → Homogenization.Vec d)
                  (Kg Kh KhInf : ℝ),
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (Homogenization.originCube d m) u h g →
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (fun _ : Homogenization.Vec d => sigmaBarM • (1 : Homogenization.Mat d))
                      (Homogenization.originCube d m) v h g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      (1 / 2) Kg g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      (1 / 2) Kh h.grad →
                  (∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d m),
                    ‖h.grad x‖ ≤ KhInf) →
                  Algsuperdiff.Section4.Support.HasGradientOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      h.toFun h.grad →
                  (∀ᵐ x ∂(MeasureTheory.volume.restrict
                        (Homogenization.openCubeSet (Homogenization.originCube d m))),
                      Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                        EB omega *
                          (sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                            (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                    |Homogenization.volumeAverage
                          (Homogenization.openCubeSet (Homogenization.originCube d m))
                          (fun y => M.nu * Homogenization.vecNormSq (u.grad y)) -
                        Homogenization.volumeAverage
                          (Homogenization.openCubeSet (Homogenization.originCube d m))
                          (fun y => sigmaBarM * Homogenization.vecNormSq (v.grad y))| ≤
                      EB omega *
                        (Real.sqrt sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                            Real.sqrt sigmaBarM *
                              (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                          (2 : ℕ)
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.Homogenization.generator_renormalization_provider_final
    d cstar _hcstar
