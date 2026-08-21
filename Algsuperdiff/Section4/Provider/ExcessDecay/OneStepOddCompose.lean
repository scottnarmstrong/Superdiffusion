/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddValue
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderComposeBoundary

/-!
# The boundary producer off the variational competitor

`OneStepOddValue` runs the boundary branch's Schauder producer from an
almost-everywhere odd competitor.  This module supplies the two remaining pieces
of plumbing and composes them, so that the producer fires directly off
`OneStepSchauderComposeBoundary.exists_classicalCompetitor_reflectedWindow`,
i.e. off a **variationally** harmonic `H¹` datum on the doubled window.

## The local identification device

's `eqOn_of_ae_eq_of_continuous` needs *global* continuity, which no Weyl
representative has: harmonicity is asserted only on the window.  The local twin
`eqOn_of_ae_eq_of_continuousOn` is the same proof with `ContinuousOn` in place
of `Continuous`: on an open `S` the disagreement set is open, hence null
implies empty.  Continuity on the window comes from harmonicity for free
(`HarmonicAt` carries `ContDiffAt ℝ 2`), which is
`continuousOn_of_harmonicOnNhd`.

This settles the identification of the **two Weyl representatives** the boundary
branch produces: the interior route applies Weyl's lemma on the anchor's moved
replacement cube `R_mov`, the boundary route on the doubled window
`reflectedWindow`, and neither set contains the other — but both contain `U₂`,
both representatives are continuous there and both agree almost everywhere with
the competitor, so they agree *pointwise* on `U₂`
(`eqOn_of_two_harmonic_representatives`).  The two consumers of the
representative then transfer: `gradField` because `fderiv` is local
(`gradField_eq_of_eqOn`), and `affineExcess` because it is an integral over `U₂`
(`affineExcessRaw_congr_eqOn`).

## The composed producer

`exists_classicalCompetitor_gradientHolder_boundary_odd_of_meetsUpperFace` (and
its lower-face twin) takes exactly the data of the proved one-met-face transfer
— a weakly harmonic `v` on the window, the reflected `H¹` datum `w` with its
gradient pinned — plus the value-level pinning of `w` (the residue records: the
gradient pinning determines `w.toFun` only up to an additive constant `c₀`,
which the chain carries for free), and returns the classical competitor on the
doubled window together with the full four-slot Schauder package.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec vecDot openCubeSet originCube coordFaceReflection H1Function)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The local identification device -/

/-- **Two functions continuous *on* an open set and equal almost everywhere there
are equal there.**  The local form's `eqOn_of_ae_eq_of_continuous`: a Weyl
representative is continuous only on its own window. -/
theorem eqOn_of_ae_eq_of_continuousOn {S : Set (Vec d)} (hS : IsOpen S)
    {f g : Vec d → ℝ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hae : ∀ᵐ p ∂(volume : Measure (Vec d)), p ∈ S → f p = g p) : Set.EqOn f g S := by
  intro p hp
  by_contra hne
  have hTopen : IsOpen (S ∩ {q : Vec d | f q ≠ g q}) := by
    refine isOpen_iff_mem_nhds.2 fun q hq => ?_
    have hfq : ContinuousAt f q := hf.continuousAt (hS.mem_nhds hq.1)
    have hgq : ContinuousAt g q := hg.continuousAt (hS.mem_nhds hq.1)
    have hsub : ∀ᶠ r in nhds q, f r - g r ≠ 0 :=
      (hfq.sub hgq).eventually_ne (sub_ne_zero.2 hq.2)
    filter_upwards [hS.mem_nhds hq.1, hsub] with r hr1 hr2
    exact ⟨hr1, sub_ne_zero.1 hr2⟩
  have hTpos : 0 < volume (S ∩ {q : Vec d | f q ≠ g q}) :=
    hTopen.measure_pos volume ⟨p, hp, hne⟩
  have hnull : volume (S ∩ {q : Vec d | f q ≠ g q}) = 0 := by
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.ae_iff.1 hae)
    intro q hq hcon
    exact hq.2 (hcon hq.1)
  rw [hnull] at hTpos
  exact lt_irrefl 0 hTpos

/-- Classical harmonicity on a window gives continuity on that window: `HarmonicAt`
carries `ContDiffAt ℝ 2`. -/
theorem continuousOn_of_harmonicOnNhd {S : Set (Vec d)} {V : Vec d → ℝ}
    (hV : HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' S)) :
    ContinuousOn V S := by
  intro p hp
  have h1 : HarmonicAt (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc p) :=
    hV (toEuc p) ⟨p, hp, rfl⟩
  have h2 : ContinuousAt (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      (toEuc p) := h1.1.continuousAt
  have h3 : ContinuousAt ((V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ∘ (toEuc : Vec d → EuclideanSpace ℝ (Fin d))) p :=
    h2.comp (toEuc : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d)).continuous.continuousAt
  rw [comp_toEuc_symm_toEuc] at h3
  exact h3.continuousWithinAt

/-- **The two Weyl representatives, identified.**  `V₁` is classically harmonic on
`S`, `V₂` on `T`, and neither set need contain the other; on a common open
subwindow `W` on which they agree almost everywhere they agree pointwise. -/
theorem eqOn_of_two_harmonic_representatives {S T W : Set (Vec d)} (hW : IsOpen W)
    (hWm : MeasurableSet W) (hWS : W ⊆ S) (hWT : W ⊆ T) {V₁ V₂ : Vec d → ℝ}
    (h₁ : HarmonicOnNhd (V₁ ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' S))
    (h₂ : HarmonicOnNhd (V₂ ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' T))
    (hae : V₁ =ᵐ[volume.restrict W] V₂) :
    Set.EqOn V₁ V₂ W := by
  refine eqOn_of_ae_eq_of_continuousOn hW
    ((continuousOn_of_harmonicOnNhd h₁).mono hWS)
    ((continuousOn_of_harmonicOnNhd h₂).mono hWT) ?_
  exact (MeasureTheory.ae_restrict_iff' hWm).1 hae

/-! ## 2. Transfer of the two consumers along an `EqOn` -/

/-- `gradField` is local: it transfers along an equality on an open set. -/
theorem gradField_eq_of_eqOn {S : Set (Vec d)} (hS : IsOpen S) {f g : Vec d → ℝ}
    (h : Set.EqOn f g S) {p : Vec d} (hp : p ∈ S) : gradField f p = gradField g p := by
  have hfe : f =ᶠ[nhds p] g := Filter.eventuallyEq_of_mem (hS.mem_nhds hp) h
  funext i
  simp only [gradField, hfe.fderiv_eq]

/-- An `EqOn` on a measurable window is an almost-everywhere equality there. -/
theorem ae_eq_restrict_of_eqOn {W : Set (Vec d)} (hW : MeasurableSet W)
    {f g : Vec d → ℝ} (h : Set.EqOn f g W) : f =ᵐ[volume.restrict W] g :=
  (MeasureTheory.ae_restrict_iff' hW).2 (Filter.Eventually.of_forall fun _ hp => h hp)

/-- The excess minimum is an almost-everywhere invariant: the competitor set is
unchanged. -/
theorem affineExcessRaw_congr_ae {W : Set (Vec d)} {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict W] g) : affineExcessRaw W f = affineExcessRaw W g := by
  have hset : affineDistSet W f = affineDistSet W g := by
    simp only [affineDistSet]
    congr 1
    funext p
    exact affineDistOn_congr_ae h p.1 p.2
  simp only [affineExcessRaw, hset]

/-- The excess is an almost-everywhere invariant. -/
theorem affineExcess_congr_ae {W : Set (Vec d)} {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict W] g) : affineExcess W f = affineExcess W g := by
  simp only [affineExcess, affineExcessRaw_congr_ae h]

/-- The excess transfers along an `EqOn` on a measurable window. -/
theorem affineExcess_congr_eqOn {W : Set (Vec d)} (hW : MeasurableSet W)
    {f g : Vec d → ℝ} (h : Set.EqOn f g W) : affineExcess W f = affineExcess W g :=
  affineExcess_congr_ae (ae_eq_restrict_of_eqOn hW h)

/-! ## 3. The producer off the variational competitor -/

/-- **The boundary producer from a variationally harmonic datum.**  Weyl's lemma
on the doubled window followed by the almost-everywhere odd producer. -/
theorem exists_classicalCompetitor_gradientHolder_boundary_odd [NeZero d] (hd : d ≠ 0)
    {m n : ℤ} {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m)
    {w : H1Function (reflectedWindow x m (n - 2))}
    (hw : IsWeaklyHarmonicOn (reflectedWindow x m (n - 2)) w)
    {O : Vec d → ℝ} {c₀ : ℝ} (hwval : ∀ y, w.toFun y = O y + c₀)
    (hOodd : oddExtend x m (n - 2) O =ᵐ[volume] O)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m (n - 2) (c - c₀) A) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) ∧
      MemLp V 2 (volume : Measure (Vec d)) ∧
      V =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] w.toFun ∧
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ i, IntegrableOn (fun p => gradField V p i)
          (truncatedWindow x m (n - 3)) volume) ∧
        HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
        HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K (gradField V) ∧
        K ≤ boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m (n - 2)) V
            + boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) := by
  obtain ⟨V, hVharm, hVmem, hVae⟩ :=
    exists_classicalCompetitor_reflectedWindow x m (n - 2) hw
  refine ⟨V, hVharm, hVmem, hVae, ?_⟩
  have hVO : V =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] fun y => O y + c₀ := by
    filter_upwards [hVae] with y hy
    rw [hy, hwval y]
  exact exists_gradientHolder_boundary_odd_ae hd hx hmn hVO
    (MeasureTheory.ae_restrict_of_ae hOodd) hodd hVharm (hVmem.restrict _)

/-- **The composed boundary producer, upper met face.**  The data are exactly the
proved one-met-face transfer's — a weakly harmonic `v` on the window and the
reflected `H¹` datum `w` with its gradient pinned — together with the
value-level pinning of `w`, which the gradient pinning determines only up to
the additive constant `c₀`. -/
theorem exists_classicalCompetitor_gradientHolder_boundary_odd_of_meetsUpperFace
    [NeZero d] (hd : d ≠ 0) {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m) {i : Fin d}
    (hup : MeetsUpperFace x m (n - 2) i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j)
    (v : H1Function (truncatedWindow x m (n - 2)))
    (hv : IsWeaklyHarmonicOn (truncatedWindow x m (n - 2)) v)
    (w : H1Function (reflectedWindow x m (n - 2)))
    (hwgrad : ∀ y, w.grad y = oddFaceExtendGrad ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (zeroExtendGrad (truncatedWindow x m (n - 2)) v.grad) y)
    {c₀ : ℝ}
    (hwval : ∀ y, w.toFun y = oddFaceExtend ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (zeroExtend (truncatedWindow x m (n - 2)) v.toFun) y + c₀)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m (n - 2) (c - c₀) A) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) ∧
      MemLp V 2 (volume : Measure (Vec d)) ∧
      V =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] w.toFun ∧
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ i, IntegrableOn (fun p => gradField V p i)
          (truncatedWindow x m (n - 3)) volume) ∧
        HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
        HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K (gradField V) ∧
        K ≤ boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m (n - 2)) V
            + boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) :=
  exists_classicalCompetitor_gradientHolder_boundary_odd hd hx hmn
    (isWeaklyHarmonicOn_reflectedWindow_of_meetsUpperFace hmn hup hother v hv w hwgrad)
    hwval
    (oddExtend_ae_eq_self_of_faceOdd_upper hup hother
      (faceOdd_oddFaceExtend ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
        (zeroExtend (truncatedWindow x m (n - 2)) v.toFun)))
    hodd

/-- **The composed boundary producer, lower met face.** -/
theorem exists_classicalCompetitor_gradientHolder_boundary_odd_of_meetsLowerFace
    [NeZero d] (hd : d ≠ 0) {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m) {i : Fin d}
    (hlow : MeetsLowerFace x m (n - 2) i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j)
    (v : H1Function (truncatedWindow x m (n - 2)))
    (hv : IsWeaklyHarmonicOn (truncatedWindow x m (n - 2)) v)
    (w : H1Function (reflectedWindow x m (n - 2)))
    (hwgrad : ∀ y, w.grad y = oddFaceExtendGrad (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (zeroExtendGrad (truncatedWindow x m (n - 2)) v.grad) y)
    {c₀ : ℝ}
    (hwval : ∀ y, w.toFun y = oddFaceExtend (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (zeroExtend (truncatedWindow x m (n - 2)) v.toFun) y + c₀)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m (n - 2) (c - c₀) A) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) ∧
      MemLp V 2 (volume : Measure (Vec d)) ∧
      V =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] w.toFun ∧
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ i, IntegrableOn (fun p => gradField V p i)
          (truncatedWindow x m (n - 3)) volume) ∧
        HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
        HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K (gradField V) ∧
        K ≤ boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m (n - 2)) V
            + boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) :=
  exists_classicalCompetitor_gradientHolder_boundary_odd hd hx hmn
    (isWeaklyHarmonicOn_reflectedWindow_of_meetsLowerFace hmn hlow hother v hv w hwgrad)
    hwval
    (oddExtend_ae_eq_self_of_faceOdd_lower
      (fun hu => not_meetsLowerFace_of_meetsUpperFace hmn hu hlow) hlow hother
      (faceOdd_oddFaceExtend (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
        (zeroExtend (truncatedWindow x m (n - 2)) v.toFun)))
    hodd

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The one-step excess-decay contraction on the boundary branch, through the
odd class, from an almost-everywhere odd competitor.**

The almost-everywhere twin of
`OneStepBoundaryOdd.excessDecay_oneStep_boundary_odd_of_harmonicApprox`: the
competitor is required to agree almost everywhere on the doubled window with
`O + c₀` for an almost-everywhere odd `O`, which is what a Weyl representative of
the reflected `H¹` datum delivers, and the affine datum is read at the shifted
intercept `c - c₀`.  The binders `hmem`/`hharm` are transcribed verbatim from
`OneStepConditional`. -/
theorem excessDecay_oneStep_boundary_odd_ae_of_harmonicApprox [NeZero d] (hd : d ≠ 0)
    {m n : ℤ} {k : ℕ} (hk : 3 ≤ k) {M : ABKModel d} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {delta : ℝ} (hdelta1 : delta ≤ 1) {x z : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m) (hmn : n - 2 < m)
    {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    (hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
    (hvR : MemLp v 2 (volume.restrict (reflectedWindow x m (n - 2))))
    (huv : MemLp (fun y => u y - v y) 2 (volume.restrict (movedReplacementCube x m n)))
    {O : Vec d → ℝ} {c₀ : ℝ}
    (hvO : v =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] fun y => O y + c₀)
    (hOodd : oddExtend x m (n - 2) O
      =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] O)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m (n - 2) (c - c₀) A)
    (hharmclass : HarmonicOnNhd (v ∘ Schauder.toEuc.symm)
      ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)))
    {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
      (s / 8 * Real.sqrt delta))
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
        (fun _omega' =>
          MeasureTheory.eLpNorm (fun y => u y - v y) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                openCubeSet (originCube d (n - 2)))))
        omega ≤ B) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u
      ≤ taylorContractionConst d * boundaryOddSchauderConst d * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m n) u
        + triangleRemainderConst d (boundaryOddSchauderConst d) k
            * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal))
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
            * (boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n v c A)) := by
  obtain ⟨K, hK, hint, hgrad, hhol, hschauder⟩ :=
    Schauder.exists_gradientHolder_boundary_odd_ae hd hx hmn hvO hOodd hodd hharmclass hvR
  exact excessDecay_oneStep_of_harmonicApprox hd hk hs hs1 hdelta1 hx hnm hu hv huv hmem hB
    hharm hK (Schauder.boundaryOddSchauderConst_nonneg d) hint hgrad hhol hschauder

end

end Algsuperdiff.Section4.Provider.ExcessDecay
