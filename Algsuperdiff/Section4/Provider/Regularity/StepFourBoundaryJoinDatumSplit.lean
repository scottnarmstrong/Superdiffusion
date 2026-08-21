/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepFourBoundaryJoin
import Algsuperdiff.Section4.Provider.Regularity.StepFourBoundaryBudgetErrorWeighted
import Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeStepFourDatumSplit

/-!
# The boundary Step-4 slot at every centre, with the printed datum leg

## What this module settles

`StepFourBoundaryJoin.excessDecay_stepFour_slot_allCentres` is the Step-4 slot
at every centre, with the interior/met-face disjunction discharged geometrically
— but it is a **conditional interface**, not a boundary `hstep4` producer,
because its carried competitor package forces the join's own competitor to
vanish on the met face (`oddCompetitor_eq_zero_on_metUpperFace`).  That
obstruction is removed here: the package is asked of the Weyl representative `V`
of the manuscript's shifted competitor `v − ℓ_h − v₁`, which is exactly the
object the reflection chain produces from the proved zero-trace supplier, and
whose met-face trace `h − ℓ_h − v₁` genuinely vanishes.

* `excessDecay_stepFour_slot_allCentres_datumSplit` — the Step-4 slot with **no
  geometric hypothesis at all**, at every centre including the boundary lattice
  centres where the cube gate fails, and with the printed datum leg in the
  `δ` slot.  Its only remaining window input is the chain's own competitor
  package `(V, v₁, ℓ_h)` at the datum scale `K_h`.

## The consumption match

The new leg is exactly the `A^h_n` leg of the budget: same `n`-power, same datum
kind, same geometric domination, so it is absorbed by widening that leg's
constant and not by touching the `ε`-free flat slot `F` (which is the anchor's
`K_hinf` leg).  Here that is machine-checked in both budgets:

* `edBridgeDatumLeg_at_budgetIndex` — the slot's leg at budget index `j` is
  `edBridgeDatumLegConst d Cs k · (3^{j/2} · K_h)`, i.e. the `A^h_j` shape
  verbatim;
* `stepFourDeltaOut_add_datumLeg_le_boundaryFourLegs` — the four-leg grouping
  with the `A^h` constant widened from `C_bd` to `C_bd + C_leg`, `F` untouched;
* `stepFourDeltaOutErrorWeighted_add_datumLeg_le_boundaryThreeLegs` — the same
  for the error-weighted three-leg grouping (where `F` is already gone), again only
  `A^h`'s constant moving.

So the budget's geometric sums (`sum_Icc_top_stepFourDeltaOut_le`,
`sum_Icc_top_stepFourDeltaOutErrorWeighted_le`) take the new output with no structural change: `K_h/(1−r₂)`
is the only summand that grows, and it grows by a constant factor.

## References

* ABK26, `l.excess.decay.good.scales`; `t.regularity` Steps 4--5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The Step-4 slot at every centre, geometric half discharged -/

/-- **The Step-4 decay slot at every printed centre, with the printed datum leg.**

`EdBridgeStepFourDatumSplit.excessDecay_stepFour_slot_general_datumSplit` with the join's window
disjunction discharged by `RootInterfaceGate.gate_or_exists_meetsFace`: at every centre and every
scale either the interior gate holds outright, or some coordinate face of `∂□_m` is met and the
carried competitor package supplies the second disjunct.  No interiority, no lattice-centre
condition, no gate.

Unlike `excessDecay_stepFour_slot_allCentres`, the carried package is asked of
the shifted competitor's Weyl representative `V`, so it is not forced to vanish on
the met face and is chain-satisfiable at a general Dirichlet datum; the price
is the printed datum leg `edBridgeDatumLeg` in the `δ` slot. -/
theorem excessDecay_stepFour_slot_allCentres_datumSplit (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Ccap Cb : ℝ, 0 < C ∧ 0 < Ccap ∧ 0 ≤ Cb ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
          M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          ∀ hs : 0 < s,
          ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) 1 →
            delta ≤ 64 * (C ^ (2 : ℕ))⁻¹ * s ^ (6 : ℕ) →
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                  (s / 8 * Real.sqrt delta) →
            edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k * Ccap *
                  Real.rpow s (-(3 : ℝ)) * Real.sqrt delta ≤
                (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) →
            ∀ L m : ℤ, m ≤ L →
              ∀ z : Vec d, z ∈ openCubeSet (originCube d m) →
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  ∀ n : ℤ, n + 1 ≤ m →
                    omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                        (cgEllipLowerConstant d) (n + 1) z ⟨s / 8, by linarith only [hs]⟩
                        (s / 8 * Real.sqrt delta) →
                    ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                      (gflux : Vec d → Vec d),
                      IsDirichletSolutionOn
                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                          (originCube d m) u hdat gflux →
                      MemLp gflux 2
                          (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel s 2 gflux) 2
                          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                      ∀ (v : H1Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                              openCubeSet (originCube d (n - 2))))
                        (w : H10Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                              openCubeSet (originCube d (n - 2)))),
                        IsWeaklyHarmonicOn ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                          openCubeSet (originCube d (n - 2))) v →
                        (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                        (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                        ∀ (V v₁ : Vec d → ℝ) (cl : ℝ) (Al : Vec d) (Kh : ℝ), 0 ≤ Kh →
                        MemLp v.toFun 2 (volume.restrict (truncatedWindow z m n)) →
                        MemLp V 2 (volume.restrict (reflectedWindow z m (n - 2))) →
                        V =ᵐ[volume.restrict (truncatedWindow z m (n - 2))]
                          (fun y => v.toFun y - affineLift z cl Al y - v₁ y) →
                        (∀ᵐ y ∂(volume.restrict (truncatedWindow z m (n - 2))),
                          |v₁ y| ≤ datumResidualBound d n Kh) →
                        (∀ l : Fin d, MeetsUpperFace z m (n - 2) l →
                          ∀ y ∈ reflectedWindow z m (n - 2),
                            V (coordFaceReflection
                              ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) →
                        (∀ l : Fin d, MeetsLowerFace z m (n - 2) l →
                          ∀ y ∈ reflectedWindow z m (n - 2),
                            V (coordFaceReflection
                              (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) →
                        HarmonicOnNhd
                          (V ∘
                            (Schauder.toEuc.symm :
                              EuclideanSpace ℝ (Fin d) → Vec d))
                          ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
                            reflectedWindow z m (n - 2)) →
                        ∀ (c : ℝ) (gmin : Vec d),
                          IsAffineMinimizer (truncatedWindow z m (n + 1)) u.toFun c gmin →
                          affineExcess (truncatedWindow z m (n + 1 - ((k + 1 : ℕ) : ℤ)))
                              u.toFun ≤
                            (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) *
                                affineExcess (truncatedWindow z m (n + 1)) u.toFun +
                              edBridgeEps M
                                    (edBridgeEpsConstGen d
                                      (max (schauderWindowConst d) Cb) C k) L s
                                    ⟨s / 8, by linarith only [hs]⟩ z omega n *
                                  slopeMagnitude gmin +
                              (edBridgeDelta M C
                                  (edBridgeRemWeightGen d
                                    (max (schauderWindowConst d) Cb) k) L m s
                                  ⟨s / 8, by linarith only [hs]⟩ z gflux hdat.grad omega n
                                + edBridgeDatumLeg d
                                    (max (schauderWindowConst d) Cb) k n Kh) := by
  classical
  obtain ⟨C, Ccap, Cb, hC, hCcap, hCb, k₀, hk₀, hslot⟩ :=
    excessDecay_stepFour_slot_general_datumSplit d hd
  refine ⟨C, Ccap, Cb, hC, hCcap, hCb, k₀, hk₀, ?_⟩
  intro k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap hgate L m hmL z hz
  filter_upwards [hslot k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap
    hgate L m hmL z hz] with omega hom
  intro n hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv V v₁ cl Al Kh hKh
    hvn hvR hVae hv₁ hupv hlowv hharmclass c gmin hmin
  refine hom n hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv Kh hKh ?_ c gmin
    hmin
  rcases gate_or_exists_meetsFace z m (n - 2) with hcube | ⟨i, hmet⟩
  · exact Or.inl hcube
  · exact Or.inr ⟨i, V, v₁, cl, Al, hmet, hvn, hvR, hVae, hv₁, hupv, hlowv, hharmclass⟩

/-! ## 2. The datum leg in the budget's `A^h` shape -/

/-- **The slot's datum leg, read at the budget's own index.**

The slot is delivered at `j = n+1`, so as a function of the budget index `j`
the leg is `edBridgeDatumLegConst d Cs k · (3^{j/2} · K_h)` — the `A^h_j` shape
verbatim. -/
theorem edBridgeDatumLeg_at_budgetIndex (d : ℕ) (Cs : ℝ) (k : ℕ) (j : ℤ) (Kh : ℝ) :
    edBridgeDatumLeg d Cs k (j - 1) Kh
      = edBridgeDatumLegConst d Cs k * ((3 : ℝ) ^ ((j : ℝ) / 2) * Kh) := by
  rw [edBridgeDatumLeg_eq, show j - 1 + 1 = j from by ring]

/-! ## 3. The budget composition: only `A^h`'s constant moves -/

/-- **The four-leg grouping with the datum leg absorbed.**

`stepFourDeltaOut_le_boundaryFourLegs` plus the new leg: the `A^h` constant
widens from `C_bd` to `C_bd + C_leg` and **nothing else changes** — in
particular the `ε`-free flat slot `F` (the anchor's `K_hinf` leg, the one
priced at `Θ(γ^{-1/2})`) is untouched. -/
theorem stepFourDeltaOut_add_datumLeg_le_boundaryFourLegs
    {Crem Vd Cst s epsj Khinf SigInvN Kg Kh Cleg : ℝ} {n : ℤ}
    (hCV : 0 ≤ Crem * Vd) (hCst : 0 ≤ Cst) (hs : 0 < s) (heps0 : 0 ≤ epsj)
    (hKhinf : 0 ≤ Khinf) (hSig0 : 0 ≤ SigInvN) (hKg0 : 0 ≤ Kg) (hKh0 : 0 ≤ Kh) :
    stepFourDeltaOut Crem Vd Cst s epsj Khinf SigInvN Kg Kh n +
        Cleg * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) ≤
      stepFourBoundaryDeltaConst Crem Vd Cst s *
          ((3 : ℝ) ^ ((n : ℝ) / 2) * SigInvN * Kg) +
        ((stepFourBoundaryDeltaConst Crem Vd Cst s + Cleg) *
            ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
          (stepFourBoundaryDeltaConst Crem Vd Cst s * epsj) * Khinf +
          stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf) := by
  have h := stepFourDeltaOut_le_boundaryFourLegs (Crem := Crem) (Vd := Vd) (Cst := Cst)
    (s := s) (epsj := epsj) (Khinf := Khinf) (SigInvN := SigInvN) (Kg := Kg) (Kh := Kh)
    (n := n) hCV hCst hs heps0 hKhinf hSig0 hKg0 hKh0
  have hid : (stepFourBoundaryDeltaConst Crem Vd Cst s + Cleg) *
        ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh)
      = stepFourBoundaryDeltaConst Crem Vd Cst s * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh)
        + Cleg * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) := by ring
  linarith only [h, hid]

/-- **The error-weighted three-leg grouping with the datum leg absorbed.**

The error-weighted budget has no `ε`-free flat summand at all; the datum leg is
still absorbed into `A^h`, whose constant widens from `C_bd` to
`C_bd + C_leg`. -/
theorem stepFourDeltaOutErrorWeighted_add_datumLeg_le_boundaryThreeLegs
    {Crem Vd Cst s epsj Khinf SigInvN Kg Kh Cleg : ℝ} {n : ℤ}
    (hCV : 0 ≤ Crem * Vd) (hCst : 0 ≤ Cst) (hs : 0 < s) (heps0 : 0 ≤ epsj)
    (hKhinf : 0 ≤ Khinf) (hSig0 : 0 ≤ SigInvN) (hKg0 : 0 ≤ Kg) (hKh0 : 0 ≤ Kh) :
    stepFourDeltaOutErrorWeighted Crem Vd Cst s epsj Khinf SigInvN Kg Kh n +
        Cleg * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) ≤
      stepFourBoundaryDeltaConst Crem Vd Cst s *
          ((3 : ℝ) ^ ((n : ℝ) / 2) * SigInvN * Kg) +
        ((stepFourBoundaryDeltaConst Crem Vd Cst s + Cleg) *
            ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
          epsj * (2 * stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf)) := by
  have h := stepFourDeltaOutErrorWeighted_le_boundaryThreeLegs (Crem := Crem) (Vd := Vd) (Cst := Cst)
    (s := s) (epsj := epsj) (Khinf := Khinf) (SigInvN := SigInvN) (Kg := Kg) (Kh := Kh)
    (n := n) hCV hCst hs heps0 hKhinf hSig0 hKg0 hKh0
  have hid : (stepFourBoundaryDeltaConst Crem Vd Cst s + Cleg) *
        ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh)
      = stepFourBoundaryDeltaConst Crem Vd Cst s * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh)
        + Cleg * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) := by ring
  linarith only [h, hid]

end

end Algsuperdiff.Section4.Provider.Regularity
