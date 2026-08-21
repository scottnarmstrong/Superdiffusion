import Algsuperdiff.Frozen.Section4.GoodEvents
import Algsuperdiff.Section4.Support.CgEllipLowerConstant
import Algsuperdiff.Section4.Support.FluxCorrectedRepresentative
import Algsuperdiff.Section4.Support.Dirichlet
import Algsuperdiff.Section4.Provider.ExcessDecay.HarmonicApproximationProvider

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

/-!
# Harmonic approximation at good scales — [ABK] `l.harmonic.approximation.good.scales`

On a good scale, a Dirichlet solution on a triadic cube is approximated in
`L^2` by a harmonic replacement on the child cube, with an error controlled by
the flux-corrected coarse-graining error together with the oscillation of the
solution, the fractional force seminorm and the boundary gradient data.  Two
clauses are stated: a general one valid up to the boundary, and a sharper
frontier-empty specialization carrying no gradient-of-datum legs.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.harmonic_approximation_good_scales
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (C⁻¹ * s ^ (4 : ℕ)) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m →
          ∀ x z : Homogenization.Vec d,
            x ∈ Homogenization.openCubeSet (Homogenization.originCube d m) →
            z ∈ Homogenization.openCubeSet (Homogenization.originCube d m) →
            (fun y => x + y) '' Homogenization.openCubeSet (Homogenization.originCube d n) ⊆
              ((fun y => z + y) ''
                  Homogenization.openCubeSet (Homogenization.originCube d (n + 1))) ∩
                Homogenization.openCubeSet (Homogenization.originCube d m) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (u h : Homogenization.H1Function
                    (Homogenization.openCubeSet (Homogenization.originCube d m)))
                (g : Homogenization.Vec d → Homogenization.Vec d),
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                    (Homogenization.originCube d m) u h g →
                MeasureTheory.MemLp g 2
                    (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))) →
                MeasureTheory.MemLp (Homogenization.Gagliardo.gagliardoKernel s 2 g) 2
                    (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))) →
                MeasureTheory.MemLp (Homogenization.Gagliardo.gagliardoKernel s 2 h.grad) 2
                    (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))) →
                ∀ (v : Homogenization.H1Function
                      ((fun y => x + y) ''
                        Homogenization.openCubeSet (Homogenization.originCube d n)))
                  (w : Homogenization.H10Function
                      ((fun y => x + y) ''
                        Homogenization.openCubeSet (Homogenization.originCube d n))),
                  Algsuperdiff.Section4.Support.IsWeaklyHarmonicOn
                      ((fun y => x + y) ''
                        Homogenization.openCubeSet (Homogenization.originCube d n)) v →
                  (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                  (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                  (Set.indicator
                        (Algsuperdiff.Frozen.Section4.goodEventAt M
                          (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
                          ⟨s / 8, by linarith only [hs]⟩ (C⁻¹ * s ^ (4 : ℕ)))
                        (fun _omega' =>
                          MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              ((fun y => x + y) ''
                                Homogenization.openCubeSet (Homogenization.originCube d n))))
                        omega ≤
                      ENNReal.ofReal
                          (C * Real.rpow s (-(4 : ℝ)) *
                            Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
                              (n + 3) ⟨s / 8, by linarith only [hs]⟩
                              (Cutoff.translateCutoffSample z omega)) *
                        (MeasureTheory.eLpNorm
                            (fun y =>
                              u.toFun y -
                                Homogenization.volumeAverage
                                  (((fun y' => z + y') ''
                                      Homogenization.openCubeSet
                                        (Homogenization.originCube d (n + 3))) ∩
                                    Homogenization.openCubeSet (Homogenization.originCube d m))
                                  u.toFun)
                            2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y' => z + y') ''
                                  Homogenization.openCubeSet
                                    (Homogenization.originCube d (n + 3))) ∩
                                Homogenization.openCubeSet (Homogenization.originCube d m))) +
                          ENNReal.ofReal
                            (Real.rpow s (-(3 / 2 : ℝ)) *
                              Real.rpow (3 : ℝ) (n : ℝ) *
                              ‖Homogenization.volumeAverageVec
                                  (((fun y' => z + y') ''
                                      Homogenization.openCubeSet
                                        (Homogenization.originCube d (n + 2))) ∩
                                    Homogenization.openCubeSet (Homogenization.originCube d m))
                                  h.grad‖)) +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(7 : ℝ)) *
                              (Annealed.sigmaBar M n : ℝ)⁻¹ *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                          Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                Homogenization.openCubeSet
                                  (Homogenization.originCube d (n + 3))) ∩
                              Homogenization.openCubeSet (Homogenization.originCube d m)) s g +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(6 : ℝ)) *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                          Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                Homogenization.openCubeSet
                                  (Homogenization.originCube d (n + 3))) ∩
                              Homogenization.openCubeSet (Homogenization.originCube d m)) s
                            h.grad +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(6 : ℝ)) *
                              Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
                                (n + 3) ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) *
                              Real.rpow (3 : ℝ) (n : ℝ) *
                              ‖Homogenization.volumeAverageVec
                                  (((fun y' => z + y') ''
                                      Homogenization.openCubeSet
                                        (Homogenization.originCube d (n + 2))) ∩
                                    Homogenization.openCubeSet (Homogenization.originCube d m))
                                  h.grad‖)) ∧
                    ((((fun y' => z + y') ''
                            Homogenization.openCubeSet
                              (Homogenization.originCube d (n + 2))) ∩
                          frontier
                            (Homogenization.openCubeSet (Homogenization.originCube d m)) =
                        ∅) →
                      Set.indicator
                          (Algsuperdiff.Frozen.Section4.goodEventAt M
                            (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 2) z
                            ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
                          (fun _omega' =>
                            MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                              (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                ((fun y => x + y) ''
                                  Homogenization.openCubeSet (Homogenization.originCube d n))))
                          omega ≤
                        ENNReal.ofReal
                            (C * Real.rpow s (-(4 : ℝ)) *
                              Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
                                (n + 2) ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega)) *
                          MeasureTheory.eLpNorm
                            (fun y =>
                              u.toFun y -
                                Homogenization.volumeAverage
                                  (((fun y' => z + y') ''
                                      Homogenization.openCubeSet
                                        (Homogenization.originCube d (n + 2))) ∩
                                    Homogenization.openCubeSet (Homogenization.originCube d m))
                                  u.toFun)
                            2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y' => z + y') ''
                                  Homogenization.openCubeSet
                                    (Homogenization.originCube d (n + 2))) ∩
                                Homogenization.openCubeSet (Homogenization.originCube d m))) +
                          ENNReal.ofReal
                              (C * Real.rpow s (-(19 / 2 : ℝ)) *
                                (Annealed.sigmaBar M n : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                            Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                              (((fun y' => z + y') ''
                                  Homogenization.openCubeSet
                                    (Homogenization.originCube d (n + 2))) ∩
                                Homogenization.openCubeSet (Homogenization.originCube d m)) s g)
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.ExcessDecay.harmonic_approximation_provider d
