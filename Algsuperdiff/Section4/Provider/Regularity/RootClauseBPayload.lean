/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBChain
import Algsuperdiff.Section4.Provider.Regularity.StepNineOffGridGeometry

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The payload -/

/-- **The Step-7 payload of the clause-(B) display**, at the lattice centre
`z = offGridCentre n x` the root's display is stated at.

Five fields, and every one of them is either a proved producer's conclusion or
a named transport:

* `caps` / `capsCacc` — the clause-(B) records at `□_m` and `□_{n'+1}`,
  which `StepSevenLambdaGoodEvent.ae_stepSevenLambdaCaps` produces a.e. on the
  §4.4 good event at exactly these cubes, families and `σ̄`'s;
* `dataB` — the Step-7d data transport, the `K_d`-domination left as a caller
  obligation;
* `dataM` — the Caccioppoli's own data leg against the printed `K_g`-leg; -/
structure RootClauseBPayload [NeZero d] (M : ABKModel d) (L : ℤ)
    (Khol Kd CB CBc Cdel Cosc CdM alpha : ℝ) (n m n' : ℤ) (x : Vec d)
    (omega : Cutoff.CutoffSample d)
    (uglob : H1Function (openCubeSet (originCube d m)))
    (gsrc : Vec d → Vec d) : Prop where
  /-- The clause-(B) record on the chain's own cube `□_m`. -/
  caps : StepSevenLambdaCaps (originCube d m)
    (Support.fluxCorrectedCoeffFamily M L m (originCube d m)
      (Cutoff.translateCutoffSample (offGridCentre n x) omega))
    ((Annealed.sigmaBar M m : ℝ)) CB
  /-- The clause-(B) record on the Caccioppoli's cube `□_{n'+1}`. -/
  capsCacc : StepSevenLambdaCaps (originCube d (n' + 1))
    (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
      (Cutoff.translateCutoffSample (offGridCentre n x) omega))
    ((Annealed.sigmaBar M (n' + 1) : ℝ)) CBc
  /-- The Step-7d data transport. -/
  dataB : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (m - 1))
      stepSevenCgS (fun y => -gsrc (y + offGridCentre n x)) ≤
    Kd * edFinalDataOscG Khol m
  /-- The Caccioppoli's data leg against the printed `K_g`-leg. -/
  dataM : stepSevenCaccDataM (originCube d n')
      (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
        (Cutoff.translateCutoffSample (offGridCentre n x) omega))
      (fun y => -gsrc (y + offGridCentre n x)) ≤
    CdM * (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ * edFinalDataOscG Khol m)
  /-- `e.oscillation.Holder.bound` at `(n', m-1)`. -/
  osc : (3 : ℝ) ^ (-n') *
      normalizedL2On (truncatedWindow (offGridCentre n x) m n')
        (fun y => uglob.toFun y -
          volumeAverage (truncatedWindow (offGridCentre n x) m n') uglob.toFun) ≤
    Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
        ((3 : ℝ) ^ (-(m - 1)) *
          normalizedL2On (truncatedWindow (offGridCentre n x) m (m - 1))
            (fun y => uglob.toFun y -
              volumeAverage (truncatedWindow (offGridCentre n x) m (m - 1))
                uglob.toFun)) +
      Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
        (edFinalDataG M Cdel (Khol * stepFourGagliardoConst d stepOneS) m + 0)

/-- **The `hosc` join costs nothing.**

The excess-decay lane's `edFinal_oscillationHolderBound_interior` concludes at
the lattice point `Support.triadicLatticePoint n v` on the windows
`stepThreeWindow`; the payload asks for it at `offGridCentre n x` on
`truncatedWindow`s.  At `v :=
offGridLatticeIndex n x` the two statements are the same term — the centre by the
definition of `offGridCentre`, the windows by the definition of
`stepThreeWindow` — so this transfer is the identity. -/
theorem rootClauseBOsc_of_holderBound {M : ABKModel d} {Cosc Cdel Khol alpha : ℝ}
    {n m n' : ℤ} {x : Vec d} {uglob : H1Function (openCubeSet (originCube d m))}
    (h : (3 : ℝ) ^ (-n') *
        normalizedL2On
          (stepThreeWindow (Support.triadicLatticePoint n (offGridLatticeIndex n x)) m n')
          (fun y => uglob.toFun y -
            volumeAverage
              (stepThreeWindow (Support.triadicLatticePoint n (offGridLatticeIndex n x))
                m n') uglob.toFun) ≤
      (Cosc) * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
          ((3 : ℝ) ^ (-(m - 1)) *
            normalizedL2On
              (stepThreeWindow
                (Support.triadicLatticePoint n (offGridLatticeIndex n x)) m (m - 1))
              (fun y => uglob.toFun y -
                volumeAverage
                  (stepThreeWindow
                    (Support.triadicLatticePoint n (offGridLatticeIndex n x)) m (m - 1))
                  uglob.toFun)) +
        (Cosc) * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
          (edFinalDataG M Cdel (Khol * stepFourGagliardoConst d stepOneS) m + 0)) :
    (3 : ℝ) ^ (-n') *
        normalizedL2On (truncatedWindow (offGridCentre n x) m n')
          (fun y => uglob.toFun y -
            volumeAverage (truncatedWindow (offGridCentre n x) m n') uglob.toFun) ≤
      Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
          ((3 : ℝ) ^ (-(m - 1)) *
            normalizedL2On (truncatedWindow (offGridCentre n x) m (m - 1))
              (fun y => uglob.toFun y -
                volumeAverage (truncatedWindow (offGridCentre n x) m (m - 1))
                  uglob.toFun)) +
        Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
          (edFinalDataG M Cdel (Khol * stepFourGagliardoConst d stepOneS) m + 0) := h

/-- The producer's `v`-binder is met by the root's own `x ∈ □_m`. -/
theorem offGridLatticeIndex_mem_of_mem_cube {m : ℤ} (n : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) :
    offGridLatticeIndex n x ∈ Support.latticeCubeSet d n m :=
  offGridLatticeIndex_mem_latticeCubeSet n hx

/-! ## 3. The endpoint: clause (B) of `RootLatticeDisplay` -/

/-- **Clause (B) of `RootAssemblyConditional.RootLatticeDisplay`.**

The S conjunct of the root's lattice-centre display — the interior-guarded,
boundary-leg-free half — produced for every datum satisfying
`RootClauseBPayload`, from the proved §4.4 chain, the frozen Section-3
induction state, and nothing else.

The conclusion is the printed implication verbatim: at `z = offGridCentre n x`
and scale `n+1`,

```text
  z ∈ □_{m-1} →
    √ν ‖ |∇u| ‖_{L̲²((z+□_{n+1}) ∩ □_m)}
      ≤ C_est · 3^{(1-α)(m-n)} ·
          ( √ν ‖ |∇u| ‖_{L̲²(□_m)} + √σ̄_m^{-1}·3^{m/2}·K_g ) .
``` -/
theorem rootClauseB_display_offGrid (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        ∀ (L : ℤ) {alpha : ℝ} {n m n' : ℤ} {x : Vec d}
          (omega : Cutoff.CutoffSample d)
          (uglob hdat : H1Function (openCubeSet (originCube d m)))
          {gsrc : Vec d → Vec d}
          {Khol Kd CB CBc Cdel Cosc CdM C1 delta Cest : ℝ} {B : ℕ},
          m ≤ m0 → n' ≤ m - 1 → n + 1 ≤ n' - 2 → n ≤ m →
          Support.IsDirichletSolutionOn
              (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
              (originCube d m) uglob hdat gsrc →
          MemLp gsrc 2
              (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
          MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
              (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
          0 ≤ Khol → 0 ≤ Kd → 0 ≤ CB → 0 ≤ CBc → 0 ≤ Cdel → 0 ≤ Cosc → 0 ≤ CdM →
          2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 →
          delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
          (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
          RootClauseBPayload M L Khol Kd CB CBc Cdel Cosc CdM alpha n m n' x omega
            uglob gsrc →
          rootClauseBPrefactor d Cch
              (stepSevenCaccConst Cc (originCube d n')
                (Support.fluxCorrectedCoeffFamily M L (n' + 1)
                  (originCube d (n' + 1))
                  (Cutoff.translateCutoffSample (offGridCentre n x) omega)))
              Cosc CBc CB (max (Real.sqrt ((3 : ℝ) ^ d)) Kd)
              (edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS) CdM ≤
            Cest →
          (offGridCentre n x ∈ openCubeSet (originCube d (m - 1)) →
            Real.sqrt M.nu *
                Support.normalizedL2On
                  (truncatedWindow (offGridCentre n x) m (n + 1))
                  (fun y => Real.sqrt (vecNormSq (uglob.grad y)))
              ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                (Real.sqrt M.nu *
                    Support.normalizedL2On (openCubeSet (originCube d m))
                      (fun y => Real.sqrt (vecNormSq (uglob.grad y))) +
                  Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol)) := by
  obtain ⟨Cch, Cc, hCch, hCc, hmain⟩ := rootClauseB_display_interior d
  refine ⟨Cch, Cc, hCch, hCc, ?_⟩
  intro M m0 Ecap hS hgamma L alpha n m n' x omega uglob hdat gsrc Khol Kd CB CBc Cdel
    Cosc CdM C1 delta Cest B hmm0 hn' hcore hnm hsol hgL2 hgW hKhol hKd hCB hCBc hCdel
    hCosc hCdM hC1 halpha0 halpha1 hdelta hgap hbudget hpay hCest hzin
  exact hmain M m0 Ecap hS hgamma L omega uglob hdat hzin hmm0 hn' hcore hnm hsol hgL2
    hgW hKhol hKd hCB hCBc hCdel hCosc hCdM hC1 halpha0 halpha1 hdelta hgap hbudget
    hpay.caps hpay.capsCacc hpay.dataB hpay.dataM hpay.osc hCest

end

end Algsuperdiff.Section4.Provider.Regularity
