/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootAssemblyParameters
import Algsuperdiff.Section4.Provider.Regularity.RootAssemblyChain

/-!
# `t.regularity` root assembly, part three: the lattice-centre display

## What is delivered

`RootLatticeDisplay` — the one named conditional the root assembly is stated
against.  The assembly itself runs on the almost-everywhere form
(`RootInterfaceAe.RootLatticeDisplayAe`, which this predicate implies through
`RootInterfaceAe.RootLatticeDisplayAe_of_forall`) and is discharged at
`RootClauseAEndpoint`.

## What `RootLatticeDisplay` is, and what it is not

It is the §4.4 chain's own endpoint — `e.energy.density.estimate` in the
`z`-form, which the Step-7 modules build and `RootAssemblyChain` transfers off
the grid.  It is stated at the lattice centre and in
the chain's own real carrier precisely so that supplying it is exactly the act
of wiring the proved abstract-real chain to the concrete objects.

It is not implied by the three composition steps of §4.4 on their own: those
leave the `hlambda` shape break across the Step-7 legs, the `hcacc` wiring, the
`hvol` window-to-core step, the `σ̄_{n'} ≤ 2σ̄_m` constant and the `dataOsc`
normalization still to be bridged.  `RootLatticeDisplay` is therefore the
honest single name for the remaining distance: it is implied by those three
steps together with those gaps, and by nothing less.

## References

* ABK26, `t.regularity`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The named conditional -/

/-- **`e.energy.density.estimate` at the lattice centre** (the `z`-form), in the
real carrier of the proved §4.4 chain.

This is the §4.4 chain's endpoint: for every `ω` carrying the Step-1/3/7a payload on
the window `[n,m]`, every truncation index `L ≥ m`, every Dirichlet datum `(u,h,g)`
with Hölder-`1/2` bounds `K_g`, `K_h`, and every `x ∈ □_m`, the energy density on the
lattice window `(z + □_{n+1}) ∩ □_m`, `z = offGridCentre n x`, obeys the printed
three-leg display — and the boundary leg drops when `z ∈ □_{m-1}`.

`RootAssemblyChain` turns this into the frozen root's `ℝ≥0∞` two-clause
conclusion at the arbitrary centre `x`, at the constant `3^d·C_est`. -/
def RootLatticeDisplay (M : ABKModel d) (C1 Cest alpha : ℝ) : Prop :=
  ∀ (n m : ℤ), n ≤ m →
    ∀ omega : Cutoff.CutoffSample d,
      RootWindowPayload M C1 alpha n m omega →
        ∀ L : ℤ, m ≤ L →
          ∀ (u h : H1Function (openCubeSet (originCube d m)))
            (g : Vec d → Vec d) (Kg Kh : ℝ),
            Support.IsDirichletSolutionOn
                (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                (originCube d m) u h g →
            Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                (1 / 2) Kg g →
            Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                (1 / 2) Kh h.grad →
            ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
              (Real.sqrt M.nu *
                  Support.normalizedL2On
                    (truncatedWindow (offGridCentre n x) m (n + 1))
                    (fun y => Real.sqrt (vecNormSq (u.grad y)))
                ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                  (Real.sqrt M.nu *
                      Support.normalizedL2On (openCubeSet (originCube d m))
                        (fun y => Real.sqrt (vecNormSq (u.grad y)))
                    + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                        Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
                    + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                        Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ∧
                (offGridCentre n x ∈ openCubeSet (originCube d (m - 1)) →
                  Real.sqrt M.nu *
                      Support.normalizedL2On
                        (truncatedWindow (offGridCentre n x) m (n + 1))
                        (fun y => Real.sqrt (vecNormSq (u.grad y)))
                    ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                      (Real.sqrt M.nu *
                          Support.normalizedL2On (openCubeSet (originCube d m))
                            (fun y => Real.sqrt (vecNormSq (u.grad y)))
                        + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                            Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg))

end

end Algsuperdiff.Section4.Provider.Regularity
