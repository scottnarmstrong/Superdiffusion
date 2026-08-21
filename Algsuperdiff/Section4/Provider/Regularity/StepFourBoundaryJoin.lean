/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootInterfaceGate
import Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeStepFourGeneral

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The met-face hyperplane inside the doubled window -/

/-- **The met upper face really meets the doubled window.**

`z` itself lies in the doubled window, and pushing its `i`-th coordinate onto
the face `{y_i = ½·3^m}` keeps it there: the doubled window's `i`-edge runs
from `windowLo ≤ z_i` up to `3^m − windowLo > ½·3^m`. -/
theorem metUpperFace_point_mem_reflectedWindow {m q : ℤ} {z : Vec d} {i : Fin d}
    (hz : z ∈ openCubeSet (originCube d m)) (hqm : q < m)
    (hup : MeetsUpperFace z m q i) :
    Function.update z i ((1 / 2 : ℝ) * (3 : ℝ) ^ m) ∈ reflectedWindow z m q := by
  have hz0 : z ∈ reflectedWindow z m q :=
    truncatedWindow_subset_reflectedWindow z m q (mem_truncatedWindow_self q hz)
  have hzb := mem_coordBox_iff.mp hz0
  have hlow : ¬ MeetsLowerFace z m q i := not_meetsLowerFace_of_meetsUpperFace hqm hup
  have hzi : z i < (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
    (mem_openCubeSet_originCube_iff.mp hz i).2
  have hwq : (0 : ℝ) < (3 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hwm : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  have hLo : windowLo z m q i < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    rw [windowLo]
    exact max_lt (by linarith only [hzi, hwq]) (by linarith only [hwm])
  refine mem_coordBox_iff.mpr fun j => ?_
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self, reflectedLo_of_not_meetsLowerFace hlow,
      reflectedHi_of_meetsUpperFace hup]
    exact ⟨hLo, by linarith only [hLo]⟩
  · rw [Function.update_of_ne hji]
    exact hzb j

/-- **The join's oddness clause forces the competitor to vanish on the met upper face.**

The reflection fixes the face point of
`metUpperFace_point_mem_reflectedWindow`, so the clause reads `v(p) = −v(p)`. -/
theorem oddCompetitor_eq_zero_on_metUpperFace {m q : ℤ} {z : Vec d} {i : Fin d} {v : Vec d → ℝ}
    (hz : z ∈ openCubeSet (originCube d m)) (hqm : q < m) (hup : MeetsUpperFace z m q i)
    (hodd : ∀ l : Fin d, MeetsUpperFace z m q l → ∀ y ∈ reflectedWindow z m q,
      v (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v y) :
    v (Function.update z i ((1 / 2 : ℝ) * (3 : ℝ) ^ m)) = 0 := by
  have hmem := metUpperFace_point_mem_reflectedWindow hz hqm hup
  have hfix : coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (Function.update z i ((1 / 2 : ℝ) * (3 : ℝ) ^ m))
      = Function.update z i ((1 / 2 : ℝ) * (3 : ℝ) ^ m) :=
    ExcessDecay.coordFaceReflection_eq_self (Function.update_self i _ z)
  have h := hodd i hup _ hmem
  rw [hfix] at h
  linarith only [h]

theorem metLowerFace_point_mem_reflectedWindow {m q : ℤ} {z : Vec d} {i : Fin d}
    (hz : z ∈ openCubeSet (originCube d m)) (hqm : q < m)
    (hlow : MeetsLowerFace z m q i) :
    Function.update z i (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) ∈ reflectedWindow z m q := by
  have hz0 : z ∈ reflectedWindow z m q :=
    truncatedWindow_subset_reflectedWindow z m q (mem_truncatedWindow_self q hz)
  have hzb := mem_coordBox_iff.mp hz0
  have hup : ¬ MeetsUpperFace z m q i := by
    intro hup
    exact not_meetsLowerFace_of_meetsUpperFace hqm hup hlow
  have hzi : -(1 / 2 : ℝ) * (3 : ℝ) ^ m < z i :=
    (mem_openCubeSet_originCube_iff.mp hz i).1
  have hwq : (0 : ℝ) < (3 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hwm : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  have hHi : -(1 / 2 : ℝ) * (3 : ℝ) ^ m < windowHi z m q i := by
    rw [windowHi]
    exact lt_min (by linarith only [hzi, hwq]) (by linarith only [hwm])
  refine mem_coordBox_iff.mpr fun j => ?_
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self, reflectedLo_of_meetsLowerFace hlow,
      reflectedHi_of_not_meetsUpperFace hup]
    exact ⟨by linarith only [hHi], hHi⟩
  · rw [Function.update_of_ne hji]
    exact hzb j

theorem oddCompetitor_eq_zero_on_metLowerFace {m q : ℤ} {z : Vec d} {i : Fin d} {v : Vec d → ℝ}
    (hz : z ∈ openCubeSet (originCube d m)) (hqm : q < m) (hlow : MeetsLowerFace z m q i)
    (hodd : ∀ l : Fin d, MeetsLowerFace z m q l → ∀ y ∈ reflectedWindow z m q,
      v (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v y) :
    v (Function.update z i (-(1 / 2 : ℝ) * (3 : ℝ) ^ m)) = 0 := by
  have hmem := metLowerFace_point_mem_reflectedWindow hz hqm hlow
  have hfix : coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (Function.update z i (-(1 / 2 : ℝ) * (3 : ℝ) ^ m))
      = Function.update z i (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) :=
    ExcessDecay.coordFaceReflection_eq_self (Function.update_self i _ z)
  have h := hodd i hlow _ hmem
  rw [hfix] at h
  linarith only [h]

/-! ## 2. The Step-4 slot at every centre, geometric half discharged -/

/-- **The Step-4 decay slot at every printed centre, boundary included.**

`EdBridgeStepFourGeneral.excessDecay_stepFour_slot_general` with the join's window disjunction
discharged by `RootInterfaceGate.gate_or_exists_meetsFace`: at every centre and every scale
either the interior gate holds outright, or some coordinate face of `∂□_m` is met and the
carried competitor package supplies the second disjunct.  No interiority, no lattice-centre
condition, no gate.  The conclusion is `excessDecay_stepFour_slot_interior`'s, at the join's
constant `max (schauderWindowConst d) C_bdry`.

This is a **conditional interface**, not a boundary `hstep4` producer.  The
competitor package is a carried hypothesis and this module's
`oddCompetitor_eq_zero_on_metUpperFace` / `..._metLowerFace` show it forces the
join's own competitor to vanish on the met face; for a general Dirichlet datum
it is therefore not satisfiable by the anchor's harmonic replacement, and
producing it needs the printed shifted competitor `v − ℓ_h − v₁`.
Interior consumers should keep using
`excessDecay_stepFour_slot_interior`, which asks for no package at all. -/
theorem excessDecay_stepFour_slot_allCentres (d : ℕ) [NeZero d] (hd : d ≠ 0) :
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
                        MemLp v.toFun 2 (volume.restrict (truncatedWindow z m n)) →
                        MemLp v.toFun 2
                          (volume.restrict (reflectedWindow z m (n - 2))) →
                        (∀ l : Fin d, MeetsUpperFace z m (n - 2) l →
                          ∀ y ∈ reflectedWindow z m (n - 2),
                            v.toFun (coordFaceReflection
                              ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v.toFun y) →
                        (∀ l : Fin d, MeetsLowerFace z m (n - 2) l →
                          ∀ y ∈ reflectedWindow z m (n - 2),
                            v.toFun (coordFaceReflection
                              (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v.toFun y) →
                        HarmonicOnNhd
                          (v.toFun ∘
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
                              edBridgeDelta M C
                                (edBridgeRemWeightGen d
                                  (max (schauderWindowConst d) Cb) k) L m s
                                ⟨s / 8, by linarith only [hs]⟩ z gflux hdat.grad omega n := by
  classical
  obtain ⟨C, Ccap, Cb, hC, hCcap, hCb, k₀, hk₀, hslot⟩ :=
    excessDecay_stepFour_slot_general d hd
  refine ⟨C, Ccap, Cb, hC, hCcap, hCb, k₀, hk₀, ?_⟩
  intro k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap hgate L m hmL z hz
  filter_upwards [hslot k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap
    hgate L m hmL z hz] with omega hom
  intro n hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv hvn hvR hupv hlowv
    hharmclass c gmin hmin
  refine hom n hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv ?_ c gmin hmin
  rcases gate_or_exists_meetsFace z m (n - 2) with hcube | ⟨i, hmet⟩
  · exact Or.inl hcube
  · exact Or.inr ⟨i, hmet, hvn, hvR, hupv, hlowv, hharmclass⟩

end

end Algsuperdiff.Section4.Provider.Regularity
