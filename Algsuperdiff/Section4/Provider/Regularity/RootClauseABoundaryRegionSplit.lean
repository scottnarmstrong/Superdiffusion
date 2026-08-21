/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBBoundaryGateAssembly
import Algsuperdiff.Section4.Provider.Regularity.RootClauseAEndpointC1

/-!
# The boundary clause (A), split into a gated region and a flush shell

## Why the split is stated at `m-2` and not at `k_c`

A clause-level gate/shell dichotomy is not well posed at the coarse scale
`k_c`, because `k_c` is chosen by the payload machinery, not at the clause.  It
*is* well posed at the fixed scale `m-2`: the joint pigeonhole returns
`k_c ≤ m-2`, so `(GATE m-2)` implies `(GATE k_c)` for every admissible `k_c`,
and the sharp criterion `RootInterfaceGate.image_add_subset_openCubeSet_iff`
turns `(GATE m-2)` into the decidable coordinate condition

```text
   ∀ i, |z_i| + ½·3^{m-2} ≤ ½·3^m      i.e.   ∀ i, |z_i| ≤ (4/9)·3^m .
```

So the boundary obligation splits, with no loss and no overlap, into

* `RootDisplayClauseABoundaryC1GateAe` — the boundary centres inside that
  region, produced here unconditionally;
* `RootDisplayClauseABoundaryC1ShellAe` — the `ℓ^∞`-shell
  `(4/9)·3^m < max_i |z_i| < ½·3^m`, still open.

`RootDisplayClauseABoundaryC1Ae_of_gate_shell` is the machine witness that the
two halves compose back to the boundary obligation: a `by_cases` on the gate
and nothing else.

## What this module does not claim

It produces no shell estimate: `RootDisplayClauseABoundaryC1ShellAe` is a named
conditional here.

## References

* ABK26, `t.regularity`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The two halves of the boundary obligation -/

/-- **The boundary clause (A) on the gated region.**

`RootClauseAEndpointC1.RootDisplayClauseABoundaryC1Ae`'s body, character for
character, with the extra region hypothesis `z + □_{m-2} ⊆ □_m`. -/
def RootDisplayClauseABoundaryC1GateAe (M : ABKModel d) (C1 Cest alpha : ℝ) : Prop :=
  ∀ m : ℤ,
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ n : ℤ, n ≤ m →
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
              (∀ y ∈ openCubeSet (originCube d m),
                ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
              Support.HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
              ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                (offGridCentre n x ∉ openCubeSet (originCube d (m - 1)) →
                  (fun y => offGridCentre n x + y) ''
                      openCubeSet (originCube d (m - 2)) ⊆
                    openCubeSet (originCube d m) →
                  Real.sqrt M.nu *
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
                            Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))

/-- **The boundary clause (A) on the flush shell.**

The same body under the negated region hypothesis. -/
def RootDisplayClauseABoundaryC1ShellAe (M : ABKModel d) (C1 Cest alpha : ℝ) : Prop :=
  ∀ m : ℤ,
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ n : ℤ, n ≤ m →
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
              (∀ y ∈ openCubeSet (originCube d m),
                ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
              Support.HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
              ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                (offGridCentre n x ∉ openCubeSet (originCube d (m - 1)) →
                  ¬ ((fun y => offGridCentre n x + y) ''
                        openCubeSet (originCube d (m - 2)) ⊆
                      openCubeSet (originCube d m)) →
                  Real.sqrt M.nu *
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
                            Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))

/-! ## 2. The two halves compose -/

/-- **The region split is exhaustive.**

The boundary obligation from the gated-region half and the shell half, at the
same `C₁`, `C_est` and `α`.  A `by_cases` on the gate. -/
theorem RootDisplayClauseABoundaryC1Ae_of_gate_shell {M : ABKModel d}
    {C1 Cest alpha : ℝ} (hgate : RootDisplayClauseABoundaryC1GateAe M C1 Cest alpha)
    (hshell : RootDisplayClauseABoundaryC1ShellAe M C1 Cest alpha) :
    RootDisplayClauseABoundaryC1Ae M C1 Cest alpha := by
  intro m
  filter_upwards [hgate m, hshell m] with omega hg hs
  intro n hn hpay L hL u h g Kg Kh hdir hKg hKh hsup hgradh x hx hout
  by_cases hin : (fun y => offGridCentre n x + y) '' openCubeSet (originCube d (m - 2)) ⊆
      openCubeSet (originCube d m)
  · exact hg n hn hpay L hL u h g Kg Kh hdir hKg hKh hsup hgradh x hx hout hin
  · exact hs n hn hpay L hL u h g Kg Kh hdir hKg hKh hsup hgradh x hx hout hin

/-- **The boundary obligation implies each half.**

Both halves are `RootClauseAEndpointC1.RootDisplayClauseABoundaryC1Ae` with one
extra hypothesis, so any producer of that obligation produces them.  This is the
machine witness that asking only for `RootDisplayClauseABoundaryC1ShellAe` is a
strict weakening of the boundary obligation — i.e. that the shell-only endpoint
is a strengthening. -/
theorem RootDisplayClauseABoundaryC1ShellAe_of_boundary {M : ABKModel d}
    {C1 Cest alpha : ℝ} (h : RootDisplayClauseABoundaryC1Ae M C1 Cest alpha) :
    RootDisplayClauseABoundaryC1ShellAe M C1 Cest alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout _hshell
  exact h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout

theorem RootDisplayClauseABoundaryC1GateAe_of_boundary {M : ABKModel d}
    {C1 Cest alpha : ℝ} (h : RootDisplayClauseABoundaryC1Ae M C1 Cest alpha) :
    RootDisplayClauseABoundaryC1GateAe M C1 Cest alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout _hgate
  exact h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout

/-! ## 3. `C_est` monotonicity of the two halves -/

/-- The display's printed three-leg bracket is nonnegative: the two Hölder
constants are forced nonnegative by the printed binders themselves
(`RootClauseBFinalAssembly.holderHalf_const_nonneg`). -/
private theorem rootDisplayBracket_nonneg [NeZero d] {M : ABKModel d} {m : ℤ}
    {u : H1Function (openCubeSet (originCube d m))} {g gh : Vec d → Vec d} {Kg Kh : ℝ}
    (hKg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKh : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh gh) :
    (0 : ℝ) ≤ Real.sqrt M.nu *
          Support.normalizedL2On (openCubeSet (originCube d m))
            (fun y => Real.sqrt (vecNormSq (u.grad y)))
        + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
            Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
        + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
            Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
  have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hL2 : (0 : ℝ) ≤ Real.sqrt M.nu *
      Support.normalizedL2On (openCubeSet (originCube d m))
        (fun y => Real.sqrt (vecNormSq (u.grad y))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Support.normalizedL2On_nonneg _ _)
  have hGleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) (holderHalf_const_nonneg hKg)
  have hHleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ) *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) (holderHalf_const_nonneg hKh)
  linarith only [hL2, hGleg, hHleg]

theorem RootDisplayClauseABoundaryC1GateAe.mono_const [NeZero d] {M : ABKModel d}
    {C1 Cest Cest' alpha : ℝ} (hle : Cest ≤ Cest')
    (h : RootDisplayClauseABoundaryC1GateAe M C1 Cest alpha) :
    RootDisplayClauseABoundaryC1GateAe M C1 Cest' alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout hin
  have hbase := h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout hin
  have hB0 : (0 : ℝ) ≤ Real.sqrt M.nu *
        Support.normalizedL2On (openCubeSet (originCube d m))
          (fun y => Real.sqrt (vecNormSq (u.grad y)))
      + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
      + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    rootDisplayBracket_nonneg (M := M) hKg hKh
  have hrpow : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  exact le_trans hbase
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hrpow) hB0)

theorem RootDisplayClauseABoundaryC1ShellAe.mono_const [NeZero d] {M : ABKModel d}
    {C1 Cest Cest' alpha : ℝ} (hle : Cest ≤ Cest')
    (h : RootDisplayClauseABoundaryC1ShellAe M C1 Cest alpha) :
    RootDisplayClauseABoundaryC1ShellAe M C1 Cest' alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout hin
  have hbase := h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout hin
  have hB0 : (0 : ℝ) ≤ Real.sqrt M.nu *
        Support.normalizedL2On (openCubeSet (originCube d m))
          (fun y => Real.sqrt (vecNormSq (u.grad y)))
      + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
      + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    rootDisplayBracket_nonneg (M := M) hKg hKh
  have hrpow : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  exact le_trans hbase
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hrpow) hB0)

/-! ## 4. The gated half -/

/-- **The gated-region boundary clause (A), produced.**

The a.e. display in the obligation's own quantifier order (`m` outside,
`ω`, then `n` and the payload, then `L`), with the boundary guard
`offGridCentre n x ∉ □_{m-1}` introduced and discarded — the produced display
holds at every lattice centre of the gated region, boundary or not.  A pure
binder move. -/
theorem exists_rootDisplayClauseABoundaryC1GateAe (d : ℕ) [NeZero d] (hd : d ≠ 0)
    (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg) :
    ∃ (Cfl Citer : ℝ) (k : ℕ), 1 ≤ Cfl ∧ 11 ≤ k ∧
      ∀ Cedos : ℝ, Cfl ≤ Cedos →
        ∃ Cest gamma0 : ℝ, 0 ≤ Cest ∧ 0 < gamma0 ∧
          ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - Crg * Real.sqrt M.gamma →
              RootDisplayClauseABoundaryC1GateAe M
                (stepOneC1 d Cedos 1 Citer k) Cest alpha := by
  obtain ⟨Cfl, Citer, Cest, k, hCfl, hCest, hk11, hmain⟩ :=
    rootClauseB_display_gate_boundary_final_floor d hd cstar Crg hcstar hCrg
  refine ⟨Cfl, Citer, k, hCfl, hk11, ?_⟩
  intro Cedos hfloor
  obtain ⟨gamma0, hgamma0, hbody⟩ := hmain Cedos hfloor
  refine ⟨Cest, gamma0, hCest, hgamma0, ?_⟩
  intro M hcs hg alpha ha0 ha m
  filter_upwards [hbody M hcs hg alpha ha0 ha m] with omega hom
  intro n hn hpay L hL u h g Kg Kh hdir hKg hKh hsup hgradh x hx _hout hin
  exact hom n L hn hL hpay u h g Kg Kh hdir hKg hKh hsup hgradh x hx hin

end

end Algsuperdiff.Section4.Provider.Regularity
