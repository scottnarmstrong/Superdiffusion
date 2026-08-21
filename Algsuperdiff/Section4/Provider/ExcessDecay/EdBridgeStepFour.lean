/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeFolds

/-!
# The anchored one-step delivered in the Step-4 / `IterationDecay` slot

's `excessDecay_oneStep_interior_anchored` is the printed one-step contraction
with the harmonic-approximation anchor's four legs on the right.
`t.regularity` Step 4 and the frozen iteration anchor's own hypothesis
`e.Ej.decay.assumption` (named `IterationDecay` by the Step-5 provider) want
instead

```text
   E(u, U_{j-h}) ≤ θ^h E(u, U_j) + ε_j |∇ℓ_j| + δ_j ,   U_j = (z+□_j) ∩ □_m ,  θ = 3^{-1/4} .
```

This module performs that conversion — residues 1--4 — on the interior
branch.

## Residue 3: the `W' → U_0` window move, measured and closed at zero new analysis

In the proved indices the gap is exactly **one triadic scale**: the one-step at
scale `n` carries all four legs on `(z+□_{n+1}) ∩ □_m` and its supply event at
index `n+1` (the frozen statement's anchor is `z`-centred at its own index `+3`, two
scales above the print's `x`-centred `+1`), while its contraction reads the
excess at `(z+□_n) ∩ □_m`.

The move is therefore **not** an analytic comparison of two incomparable windows: it is a
re-index.  Running the one-step at `x := z` and reading the conclusion at `j := n+1`,

* the anchor's legs sit on `U_{n+1} = U_j` — the recursion's own window, where residue 2 applies
  verbatim, and the supply event sits at index `j`, which is exactly the index of the Step-3 bad
  set `𝓑_z = {j : 𝒢(j,z;·) fails}`;
* the contraction's excess sits on `U_n = U_{j-1}`, one scale below, and is
  moved up by the **proved** excess quasi-monotonicity `E(u,U_n) ≤ κ(d,1)
  E(u,U_{n+1})` (`OneStepWindows.affineExcess_truncatedWindow_le`, a pure
  volume-ratio bound), whose constant is absorbed into the contraction by
  residue 4;
* the left-hand window sits on `U_{n-k} = U_{j-h}` at `h := k+1`.

This module is the general-clause route, kept because it needs no
frontier-empty gate (hence covers the windows that meet `∂□_m`, where the
boundary join lives).

## What is discharged, and what is carried

Discharged inside: the anchor, the good-event cap
(`OneStepGoodScales.ae_errorRepresentative_le_goodEventDeltaSlot`), the
oscillation-to-excess fold, the window move, the contraction absorption, and
the almost-sure quantifier over the whole scale range (`ae_all_iff` over `ℤ`,
so that ONE `ω` serves every scale — what a pathwise bad set needs).

Carried, as source binders: the Dirichlet datum and clause-(iv) `MemLp` data of
the one-step; the harmonic replacement `v, w` on the moved cube at each scale
(the reflection chain plus the Weyl
representative produce them with no analytic input); the affine minimizer at
the scale in question; the interior gate `(z+□_{n-2}) ⊆ □_m`; and one smallness
gate on `δ`.

## The `δ`-gate (disclosed)

Printed Step 4 absorbs the one-step's second `E`-coefficient into `3^{-k/4}` by
the two inequalities (`C s^{-3/2} 3^{-k/4} ≤ 1/2` and `ε_j(z) ≤ ½ s^{3/2}
C^{-1} 3^{-k/4}`).  Here that absorption is a single explicit hypothesis
`hgate`: the capped leg constant times `s^{-3} δ^{1/2}` is at most `½ ·
3^{-(k+1)/4}`.

## References

* ABK26, `l.excess.decay.good.scales`; `t.regularity` Steps 3--5;
  `l.iteration.lemma`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The bridge's constants and legs -/

/-- The one-step remainder's weight `C_r(d, C_sch, k) · √((3²)^d)`, i.e. the
printed `C 3^{(1+d/2)k}` together with the window-transfer factor `3^d`. -/
def edBridgeRemWeight (d : ℕ) [NeZero d] (k : ℕ) : ℝ :=
  triangleRemainderConst d (schauderWindowConst d) k * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d)

theorem edBridgeRemWeight_nonneg (d : ℕ) [NeZero d] (k : ℕ) : 0 ≤ edBridgeRemWeight d k :=
  mul_nonneg (triangleRemainderConst_nonneg d (schauderWindowConst_nonneg d) k)
    (Real.sqrt_nonneg _)

/-- The `ε` constant of the bridge, `3 · C_r √((3²)^d) · C_anchor · C_i(d)`.  The factor `3` is
the single triadic scale of the re-index (`3^{-n} · 3^{n+1} = 3`); `C_i(d)` is the endpoint
constant of the oscillation-to-excess fold. -/
def edBridgeEpsConst (d : ℕ) [NeZero d] (C : ℝ) (k : ℕ) : ℝ :=
  3 * edBridgeRemWeight d k * C * endpointConst d (1 / 9 : ℝ)

/-- **The bridge's `ε_j` at `j = n+1`**: the printed `ε_j` at
the `ε`-re-pin `s^{-4}`, with the error representative left (uncapped),
exactly as `t.regularity` Step 5's own `ε_j(z)` is. -/
def edBridgeEps (M : ABKModel d) (Ceps : ℝ) (L : ℤ) (s : ℝ) (t : {t : ℝ // 0 < t}) (z : Vec d)
    (omega : Cutoff.CutoffSample d) (n : ℤ) : ℝ :=
  Ceps * Real.rpow s (-(4 : ℝ)) *
    fluxCorrectedErrorRepresentative M L (n + 1) t (Cutoff.translateCutoffSample z omega)

/-- The four-leg bracket of the bridge's `δ_j`: the anchor's `∇h` in-bracket companion and its
three data legs, at the re-indexed scales (`n+1` for the window carriers, `n` for the `∇h`
average, `n-2` for `σ̄` and the `3`-powers). -/
def edBridgeDeltaBracket (M : ABKModel d) (C : ℝ) (L m : ℤ) (s : ℝ) (t : {t : ℝ // 0 < t})
    (z : Vec d) (gflux gradh : Vec d → Vec d) (omega : Cutoff.CutoffSample d) (n : ℤ) : ℝ :=
  C * Real.rpow s (-(4 : ℝ)) *
        fluxCorrectedErrorRepresentative M L (n + 1) t (Cutoff.translateCutoffSample z omega) *
        (Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
          ‖volumeAverageVec (truncatedWindow z m n) gradh‖) +
      C * Real.rpow s (-(7 : ℝ)) * (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
          Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
          (normalizedGagliardoESeminormOn (truncatedWindow z m (n + 1)) s gflux).toReal +
      C * Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
          (normalizedGagliardoESeminormOn (truncatedWindow z m (n + 1)) s gradh).toReal +
      C * Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
          (eLpNorm gradh 2
            (normalizedVolumeMeasureOn (truncatedWindow z m (n + 1)))).toReal

/-- **The bridge's `δ_j` at `j = n+1`**: the four-leg bracket at the one-step's own remainder
weight and scale normalizer `3^{-n}`. -/
def edBridgeDelta (M : ABKModel d) (C W : ℝ) (L m : ℤ) (s : ℝ) (t : {t : ℝ // 0 < t})
    (z : Vec d) (gflux gradh : Vec d → Vec d) (omega : Cutoff.CutoffSample d) (n : ℤ) : ℝ :=
  W * ((3 : ℝ) ^ (-n) * edBridgeDeltaBracket M C L m s t z gflux gradh omega n)

/-! ## 2. The scalar recombination -/

/-- `3^{-n} · 3^{n+1} = 3`: the single triadic scale of the re-index. -/
theorem zpow_reindex (n : ℤ) : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n + 1) = 3 := by
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  norm_num

/-- ** residue 3, atom: the one-scale excess move.**  `E(u,U_n) ≤ κ(d,1)
E(u,U_{n+1})` on the Step-3 window family, at the proved volume-ratio constant. -/
theorem affineExcess_reindex_le {m n : ℤ} (z : Vec d)
    (hz : z ∈ openCubeSet (originCube d m)) (hnm : n + 1 - 1 ≤ m) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow z m (n + 1)))) :
    affineExcess (truncatedWindow z m n) u
      ≤ windowRatioConst d 1 * affineExcess (truncatedWindow z m (n + 1)) u := by
  have h := affineExcess_truncatedWindow_le (d := d) (u := u) z hz (by omega : n - 1 ≤ m) hnm
    (by omega : n ≤ n + 1) hu
  rwa [show n + 1 - n = 1 from by ring] at h

/-- ** residue 3, atom (b): the oscillation leg at the one-step's own normalizer.**

The one-step's remainder carries `3^{-n}` while its leg-1 oscillation lives on `U_{n+1}`; the
fold therefore reads

```text
   3^{-n} ‖u − (u)_{U_{n+1}}‖_{L̲²(U_{n+1})} ≤ 3 C_i(d) ( E(u,U_{n+1}) + |∇ℓ(u,U_{n+1})| ) ,
```

with the excess and the slope on `U_{n+1}` — the SAME window as the oscillation.  Read at
`U_n` instead the inequality is **false** (take `u ≡ 0` on `U_n` and a bump on `U_{n+1} ∖ U_n`:
the right side vanishes, the left does not), which is why the slot must be delivered at
`j := n+1` and the contraction's excess moved up by `affineExcess_reindex_le`. -/
theorem oscLeg_normalized_le (hd : d ≠ 0) {m n : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hnm : n + 1 - 1 ≤ m) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow z m (n + 1)))) {c : ℝ} {g : Vec d}
    (hmin : IsAffineMinimizer (truncatedWindow z m (n + 1)) u c g) :
    (3 : ℝ) ^ (-n) *
        (eLpNorm (fun y => u y - volumeAverage (truncatedWindow z m (n + 1)) u) 2
          (normalizedVolumeMeasureOn (truncatedWindow z m (n + 1)))).toReal
      ≤ 3 * endpointConst d (1 / 9 : ℝ) *
        (affineExcess (truncatedWindow z m (n + 1)) u + slopeMagnitude g) := by
  have h := eLpNorm_sub_average_truncatedWindow_le hd hz hnm hu hmin
  calc (3 : ℝ) ^ (-n) *
        (eLpNorm (fun y => u y - volumeAverage (truncatedWindow z m (n + 1)) u) 2
          (normalizedVolumeMeasureOn (truncatedWindow z m (n + 1)))).toReal
      ≤ (3 : ℝ) ^ (-n) * ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
          (affineExcess (truncatedWindow z m (n + 1)) u + slopeMagnitude g))) :=
        mul_le_mul_of_nonneg_left h (zpow_nonneg (by norm_num) _)
    _ = ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n + 1)) * (endpointConst d (1 / 9 : ℝ) *
          (affineExcess (truncatedWindow z m (n + 1)) u + slopeMagnitude g)) := by ring
    _ = 3 * endpointConst d (1 / 9 : ℝ) *
          (affineExcess (truncatedWindow z m (n + 1)) u + slopeMagnitude g) := by
        rw [zpow_reindex]; ring

/-- **The recombination**, over abstract reals.  Given the one-step conclusion `hmain` (with
`Big` its four-leg bracket), the folded bound `hBig` on that bracket (residues 1 and 2), the
absorbed contraction `hcon` (residues 3 and 4), the `δ`-gate `hgate`, and the two bookkeeping
identities `heps`, `hWd`, the conclusion is the Step-4 slot. -/
theorem edBridge_recombine {Elhs Acon Ejm1 Ej pj Big Rhat P Crem Sq B₁ B₂ th₁ th₂ th eps Wd : ℝ}
    (hCrem : 0 ≤ Crem) (hSq : 0 ≤ Sq) (hP : 0 ≤ P) (hEj : 0 ≤ Ej)
    (hmain : Elhs ≤ Acon * Ejm1 + Crem * (P * (Sq * Big)))
    (hBig : Big ≤ B₁ * Ej + B₂ * pj + Rhat)
    (hcon : Acon * Ejm1 ≤ th₁ * Ej)
    (hgate : Crem * (P * (Sq * B₁)) ≤ th₂)
    (heps : Crem * (P * (Sq * B₂)) = eps)
    (hWd : Crem * (P * (Sq * Rhat)) = Wd)
    (hth : th₁ + th₂ ≤ th) :
    Elhs ≤ th * Ej + eps * pj + Wd := by
  have hstep : Crem * (P * (Sq * Big)) ≤ Crem * (P * (Sq * (B₁ * Ej + B₂ * pj + Rhat))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBig hSq) hP) hCrem
  have hexp : Crem * (P * (Sq * (B₁ * Ej + B₂ * pj + Rhat)))
      = Crem * (P * (Sq * B₁)) * Ej + Crem * (P * (Sq * B₂)) * pj
        + Crem * (P * (Sq * Rhat)) := by ring
  rw [heps, hWd] at hexp
  have hgm : Crem * (P * (Sq * B₁)) * Ej ≤ th₂ * Ej := mul_le_mul_of_nonneg_right hgate hEj
  have hthm : (th₁ + th₂) * Ej ≤ th * Ej := mul_le_mul_of_nonneg_right hth hEj
  have hdis : (th₁ + th₂) * Ej = th₁ * Ej + th₂ * Ej := by ring
  linarith only [hmain, hstep, hexp, hcon, hgm, hthm, hdis]

/-! ## 3. The endpoint: the anchored one-step in the Step-4 slot -/

/-- **: the anchored one-step delivered in the `IterationDecay` slot (interior
branch).**

For one `ω` and every scale `n` with `n+1 ≤ m` at which the supply event holds and the window is
interior, the one-step contraction reads

```text
   E(u, U_{n+1-(k+1)}) ≤ 3^{-(k+1)/4} E(u, U_{n+1}) + ε · |∇ℓ(u,U_{n+1})| + δ ,
``` -/
theorem excessDecay_stepFour_slot_interior (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Ccap : ℝ, 0 < C ∧ 0 < Ccap ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
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
            edBridgeEpsConst d C k * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta ≤
                (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) →
            ∀ L m : ℤ, m ≤ L →
              ∀ z : Vec d, z ∈ openCubeSet (originCube d m) →
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  ∀ n : ℤ, n + 1 ≤ m →
                    (fun y => z + y) '' openCubeSet (originCube d (n - 2)) ⊆
                        openCubeSet (originCube d m) →
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
                        ∀ (c : ℝ) (gmin : Vec d),
                          IsAffineMinimizer (truncatedWindow z m (n + 1)) u.toFun c gmin →
                          affineExcess (truncatedWindow z m (n + 1 - ((k + 1 : ℕ) : ℤ)))
                              u.toFun ≤
                            (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) *
                                affineExcess (truncatedWindow z m (n + 1)) u.toFun +
                              edBridgeEps M (edBridgeEpsConst d C k) L s
                                    ⟨s / 8, by linarith only [hs]⟩ z omega n *
                                  slopeMagnitude gmin +
                              edBridgeDelta M C (edBridgeRemWeight d k) L m s
                                ⟨s / 8, by linarith only [hs]⟩ z gflux hdat.grad omega n := by
  classical
  obtain ⟨C, hC, hone⟩ := excessDecay_oneStep_interior_anchored d hd
  obtain ⟨Ccap, hCcap, hcapAe⟩ := ae_errorRepresentative_le_goodEventDeltaSlot d
  obtain ⟨k₀, hk₀, habsorb⟩ := exists_edBridgeStep d
  refine ⟨C, Ccap, hC, hCcap, k₀, hk₀, ?_⟩
  intro k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap hgate L m hmL z hz
  have hk3 : 3 ≤ k := le_trans hk₀ hk
  have hrep : s / 8 * Real.sqrt delta ≤ C⁻¹ * s ^ (4 : ℕ) :=
    excessDecayDelta_repriced hC hs.le hprice
  have hpre : (0 : ℝ) ≤ Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) :=
    mul_nonneg (Real.rpow_nonneg (by linarith only [hs]) _) (sq_nonneg _)
  have hfund : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (C⁻¹ * s ^ (4 : ℕ)) :=
    le_trans hfundcap (mul_le_mul_of_nonneg_left hrep hpre)
  rw [ae_all_iff]
  intro n
  by_cases hnm : n + 1 ≤ m
  · by_cases hcube : (fun y => z + y) '' openCubeSet (originCube d (n - 2)) ⊆
        openCubeSet (originCube d m)
    · have hnm3 : n - 2 + 3 ≤ m := by omega
      have hzmem : z ∈ truncatedWindow z m (n - 3) := mem_truncatedWindow_self (n - 3) hz
      filter_upwards [hone M s hsrange hregime hfund hs delta hdelta.2 hprice L m n hmL hnm3
        z z hzmem hz hcube,
        hcapAe M hregimecap s hsrange hs delta hdelta hfundcap (n + 1) z] with omega hom hcapOm
      intro _hnm _hcube hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv c gmin hmin
      -- the good-event cap at the supply index, and the one-step at `x := z`
      have hEcap := hcapOm hmem L (by omega)
      have hmem' : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
          (cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
          (s / 8 * Real.sqrt delta) := by
        rw [show n - 2 + 3 = n + 1 from by ring]
        exact hmem
      have hmain := hom hmem' u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv k hk3
      simp only [show n - 2 + 3 = n + 1 from by ring, show n - 2 + 2 = n from by ring,
        show (((fun y' : Vec d => z + y') '' openCubeSet (originCube d (n + 1))) ∩
            openCubeSet (originCube d m)) = truncatedWindow z m (n + 1) from rfl,
        show (((fun y' : Vec d => z + y') '' openCubeSet (originCube d n)) ∩
            openCubeSet (originCube d m)) = truncatedWindow z m n from rfl] at hmain
      -- the data of the two windows
      have hu1 : MemLp u.toFun 2 (volume.restrict (truncatedWindow z m (n + 1))) :=
        u.memL2.mono_measure
          (Measure.restrict_mono (truncatedWindow_subset_domain z m (n + 1)) le_rfl)
      have hEj : (0 : ℝ) ≤ affineExcess (truncatedWindow z m (n + 1)) u.toFun :=
        affineExcess_nonneg _ _
      have hCi : (1 : ℝ) ≤ endpointConst d (1 / 9 : ℝ) := one_le_endpointConst (by norm_num)
      have hEcalnn : (0 : ℝ) ≤ fluxCorrectedErrorRepresentative M L (n + 1)
          ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
        fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
      have hCEnn : (0 : ℝ) ≤ C * Real.rpow s (-(4 : ℝ)) *
          fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
            (Cutoff.translateCutoffSample z omega) :=
        mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hs.le _)) hEcalnn
      -- residue 2: the oscillation-to-excess fold on `U_{n+1}`
      have hOSC := eLpNorm_sub_average_truncatedWindow_le hd hz (by omega : n + 1 - 1 ≤ m)
        hu1 hmin
      -- residue 3: the one-scale window move
      have hqm := affineExcess_reindex_le z hz (by omega : n + 1 - 1 ≤ m) hu1
      -- residue 4: the contraction absorption
      have hrate : (0 : ℝ) ≤ ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) :=
        Real.rpow_nonneg (zpow_pos (by norm_num) _).le _
      have hAcon : taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2 *
            ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * affineExcess (truncatedWindow z m n) u.toFun
          ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) *
              affineExcess (truncatedWindow z m (n + 1)) u.toFun := by
        have hpos : (0 : ℝ) ≤ taylorContractionConst d * schauderWindowConst d *
            windowRatioConst d 2 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) :=
          mul_nonneg (mul_nonneg (mul_nonneg (taylorContractionConst_nonneg d)
            (schauderWindowConst_nonneg d)) (windowRatioConst_nonneg d 2)) hrate
        have h1 := mul_le_mul_of_nonneg_left hqm hpos
        have h2 := mul_le_mul_of_nonneg_right (habsorb k hk) hEj
        have hid : taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2 *
              ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
              (windowRatioConst d 1 * affineExcess (truncatedWindow z m (n + 1)) u.toFun)
            = taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2 *
              windowRatioConst d 1 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
              affineExcess (truncatedWindow z m (n + 1)) u.toFun := by ring
        linarith only [h1, h2, hid]
      -- the two bookkeeping identities and the gate, all through the re-index `3^{-n}·3^{n+1}=3`
      have hz3 := zpow_reindex n
      rw [show n + 1 - ((k + 1 : ℕ) : ℤ) = n - (k : ℤ) from by push_cast; ring,
        edBridgeEps, edBridgeEpsConst, edBridgeDelta, edBridgeRemWeight]
      refine edBridge_recombine
        (B₁ := C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
          ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))
        (B₂ := C * Real.rpow s (-(4 : ℝ)) *
          fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
            (Cutoff.translateCutoffSample z omega) *
          ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))
        (Rhat := edBridgeDeltaBracket M C L m s ⟨s / 8, by linarith only [hs]⟩ z gflux
          hdat.grad omega n)
        (th₂ := (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)))
        (triangleRemainderConst_nonneg d (schauderWindowConst_nonneg d) k)
        (Real.sqrt_nonneg _) (zpow_nonneg (by norm_num) (-n)) hEj hmain ?_ hAcon ?_ ?_ ?_ ?_
      · -- residues 1 and 2 folded into the four-leg bracket
        rw [edBridgeDeltaBracket]
        have hXnn : (0 : ℝ) ≤ (3 : ℝ) ^ (n + 1) *
            (endpointConst d (1 / 9 : ℝ) * affineExcess (truncatedWindow z m (n + 1)) u.toFun) :=
          mul_nonneg (zpow_nonneg (by norm_num) _)
            (mul_nonneg (by linarith only [hCi]) hEj)
        have hcapmul := rpow_neg_four_mul_le_of_cap (Cc := C) hs hEcap hXnn hC.le
        have hA0 : C * Real.rpow s (-(4 : ℝ)) *
              fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega) *
              ((eLpNorm (fun y => u.toFun y -
                    volumeAverage (truncatedWindow z m (n + 1)) u.toFun) 2
                  (normalizedVolumeMeasureOn (truncatedWindow z m (n + 1)))).toReal +
                Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                  ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖)
            ≤ C * Real.rpow s (-(4 : ℝ)) *
              fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega) *
              ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
                  (affineExcess (truncatedWindow z m (n + 1)) u.toFun + slopeMagnitude gmin)) +
                Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                  ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖) :=
          mul_le_mul_of_nonneg_left (by linarith only [hOSC]) hCEnn
        have hid1 : C * Real.rpow s (-(4 : ℝ)) *
              fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega) *
              ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
                  (affineExcess (truncatedWindow z m (n + 1)) u.toFun + slopeMagnitude gmin)) +
                Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                  ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖)
            = C * Real.rpow s (-(4 : ℝ)) *
                fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                  (Cutoff.translateCutoffSample z omega) *
                ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
                  affineExcess (truncatedWindow z m (n + 1)) u.toFun))
              + (C * Real.rpow s (-(4 : ℝ)) *
                  fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                    (Cutoff.translateCutoffSample z omega) *
                  ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ))) * slopeMagnitude gmin
              + C * Real.rpow s (-(4 : ℝ)) *
                  fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                    (Cutoff.translateCutoffSample z omega) *
                  (Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                    ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖) := by ring
        have hid2 : C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
              ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
                affineExcess (truncatedWindow z m (n + 1)) u.toFun))
            = (C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
                ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ))) *
              affineExcess (truncatedWindow z m (n + 1)) u.toFun := by ring
        linarith only [hA0, hcapmul, hid1, hid2]
      · -- the `δ`-gate
        have hlin : triangleRemainderConst d (schauderWindowConst d) k *
              ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
                (C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
                  ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))))
            = ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n + 1)) *
              (triangleRemainderConst d (schauderWindowConst d) k *
                Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * C * endpointConst d (1 / 9 : ℝ) * Ccap *
                Real.rpow s (-(3 : ℝ)) * Real.sqrt delta) := by ring
        rw [hlin, hz3]
        rw [edBridgeEpsConst, edBridgeRemWeight] at hgate
        linarith only [hgate]
      · -- the `ε` identity
        have hlin : triangleRemainderConst d (schauderWindowConst d) k *
              ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
                (C * Real.rpow s (-(4 : ℝ)) *
                  fluxCorrectedErrorRepresentative M L (n + 1)
                    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
                  ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))))
            = ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n + 1)) *
              (triangleRemainderConst d (schauderWindowConst d) k *
                Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * C * endpointConst d (1 / 9 : ℝ) *
                Real.rpow s (-(4 : ℝ)) *
                fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                  (Cutoff.translateCutoffSample z omega)) := by ring
        rw [hlin, hz3]
        ring
      · -- the `δ` identity
        ring
      · -- the two halves of `θ^{k+1}`
        exact le_of_eq (by ring)
    · exact Filter.Eventually.of_forall fun _ _ hc => absurd hc hcube
  · exact Filter.Eventually.of_forall fun _ hc => absurd hc hnm

end

end Algsuperdiff.Section4.Provider.ExcessDecay
