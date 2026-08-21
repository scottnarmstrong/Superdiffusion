/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomFinitePTranslate
import Algsuperdiff.Section4.Provider.Homogenization.HomMollifyChain

/-!
# Theorem B, §4.5, Step 3c: the finite-`p` conversion

## THE CONVERSION

The `L^∞` endpoint is taken from the PRINTED finite-`p` proposition rather
than from its `p ↑ ∞` limit.  The mechanism is an
exponent shift, and the conversion is a four-step chain, every step proved:

```text
  (1)  3^{-ms}‖∇u-∇v‖_{B̲^{-s}_{p,p}(□_m)} ≤ A          (hCG', printed carrier)
  (2)  ⟹  |(∇u-∇v)_R| ≤ A·3^{(s+d/p)·depth R}          (HomFinitePGauge: one term
                                                        out of 3^{jd}, constant 1)
  (3)  ⟹  ‖(∇u-∇v)_{x+□_n}‖ ≤ 6dγ·A·3^{(s+d/p)(m-n)}   (HomFinitePTranslate:
                                                        the Whitney tiling, γ = liftGeomFactor)
  (4)  ⟹  3^{-m}|u-v| ≤ 16d·6dγ·A = 96 d² γ A a.e.     (the endpoint)
```

**The `3^{m(s+d/p)}` prefactor cancels exactly.**  Step (2) produces the gauge
constant `A·3^{m s'}` at the shifted order `s' = s + d/p`, and the endpoint
multiplies by `3^{-m s'}` (`linfty_constant_cancels`).  So the finite-`p` route
gives on the SAME display as the `(∞,∞)` route with `L` replaced by the
finite-`p` gauge level, at the dimension-only constant `96 d² γ`
(`≤ 288 d²` at the Step-3 pin, since `γ = liftGeomFactor s' ≤ 3`).

## THE RANGE GUARD, and where it is discharged

The chain requires `0 < s' ≤ 1/2`, i.e. `s + d/p ≤ 1/2`.  At the author's
`p = 4d` this is `d/p = 1/4`, hence exactly `s ≤ 1/4` — which is the Step-3
pin already in force: `s = |log γ|^{-1}` with the `homS_le_quarter` at
`4 ≤ |log γ|`.  The guard is an explicit hypothesis at every statement
(`hguard`), never silent; `fourD_guard` records the `p = 4d` arithmetic.

## Carriers: no harvest, no deviation

`hCG'` is stated at the PRINTED grid-summed carrier (the negative Besov
seminorm definition's pure lattice `3^k ℤ^d ∩ □_m` = `CoarseGraining`'s
`descendantsAtDepth`).  The grid/translate carrier mismatch is
DISCHARGED here by `HomFinitePTranslate.uniformBoxGaugeBound_of_gridGauge`:
the reconstruction is proved.  The only extra
frame item it needs is that the field vanishes off `□_m`, which is the `H¹₀`
zero extension already present in the frame.

## Main results

* `linfty_constant_cancels` — the `3^{m(s+d/p)}` cancellation, displayed;
* `fourD_guard` — the `p = 4d` guard arithmetic;
* `descendantBound_of_negBesovLp` — steps (1)–(2), the extraction in the shape
  `HomFinitePTranslate` consumes;
* `uniformBoxGaugeBound_of_negBesovLp` — steps (1)–(3), the carrier;
* `ae_linfty_of_negBesovLp` — **THE CONVERSION THEOREM**: clause (C3)'s LHS
  shape at `96 d² γ · A`;
* `stepThreeLinfty_of_negBesovLp` — the swap into the Step-3c chain;
* `stepThreeLinfty_of_coarseGraining` — **the whole swap from `hCG'` itself,
  in ONE application**.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch03

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The cancellation and the guard, displayed -/

/-- **THE `3^{m(s+d/p)}` CANCELLATION.**

The extraction inflates the gauge constant by `3^{m s'}` and the endpoint
deflates it by `3^{-m s'}`; the two are inverse.  Nothing about `p` survives
into the `L^∞` display except through the exponent guard. -/
theorem linfty_constant_cancels (m : ℤ) (K A s' : ℝ) :
    K * (A * (3 : ℝ) ^ (s' * (m : ℝ))) * (3 : ℝ) ^ (-(m : ℝ) * s') = K * A := by
  have hone : (3 : ℝ) ^ (s' * (m : ℝ)) * (3 : ℝ) ^ (-(m : ℝ) * s') = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have hzero : s' * (m : ℝ) + -(m : ℝ) * s' = 0 := by ring
    rw [hzero, Real.rpow_zero]
  calc K * (A * (3 : ℝ) ^ (s' * (m : ℝ))) * (3 : ℝ) ^ (-(m : ℝ) * s')
      = (K * A) * ((3 : ℝ) ^ (s' * (m : ℝ)) * (3 : ℝ) ^ (-(m : ℝ) * s')) := by ring
    _ = K * A := by rw [hone, mul_one]

/-- **The `p = 4d` guard arithmetic**: at `p = 4d` the shift is exactly `1/4`,
so the range condition `s' ≤ 1/2` is exactly the Step-3 pin `s ≤ 1/4`. -/
theorem fourD_guard {s : ℝ} (hd : 0 < d) (hs : s ≤ 1 / 4) :
    s + (d : ℝ) / (4 * (d : ℝ)) ≤ 1 / 2 := by
  have hdne : ((d : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have h4d : (4 : ℝ) * (d : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hdne
  have hquarter : (d : ℝ) / (4 * (d : ℝ)) = 1 / 4 := by
    rw [div_eq_div_iff h4d (by norm_num : (4 : ℝ) ≠ 0)]
    ring
  rw [hquarter]
  linarith only [hs]

/-! ## 2. From the printed carrier to the whole grid -/

/-- **Steps (1)–(2): the extraction, in the shape the translate extension
consumes.**

From the printed `(p,p)` grid gauge at level `A` on `□_m`, every triadic
descendant `R` obeys `‖(F)_R‖ ≤ (A·3^{m s'})·3^{-s' · scale R}` with
`s' = s + d/p`.  The constant `A` is unchanged; the `3^{m s'}` is pure
normalization and cancels at the endpoint. -/
theorem descendantBound_of_negBesovLp {m : ℤ} {s p A : ℝ} (hp : 0 < p)
    {F : Vec d → Vec d}
    (hgauge : ∀ N : ℕ, negBesovLpPartialNorm (originCube d m) s p N F ≤ A)
    (j : ℕ) (R : TriadicCube d) (hR : R ∈ descendantsAtDepth (originCube d m) j) :
    ‖cubeAverageVec R F‖ ≤
      A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (m : ℝ)) *
        (3 : ℝ) ^ (-((s + (d : ℝ) / p) * ((R.scale : ℤ) : ℝ))) := by
  have hdepth := negBesovLpDepthSeminorm_le_of_partialBound (originCube d m) hp F hgauge j
  have hcell := sqrt_vecNormSq_cubeAverageVec_le_of_depthBound hp hdepth hR
  have hnorm : ‖cubeAverageVec R F‖ ≤ Real.sqrt (vecNormSq (cubeAverageVec R F)) :=
    norm_le_sqrt_vecNormSq _
  refine (hnorm.trans hcell).trans (le_of_eq ?_)
  have hscale : R.scale = m - (j : ℤ) := by
    have h := scale_eq_sub_of_mem_descendantsAtDepth hR
    simpa using h
  have hexp : (s + (d : ℝ) / p) * (j : ℝ) =
      (s + (d : ℝ) / p) * (m : ℝ) + -((s + (d : ℝ) / p) * (((m - (j : ℤ)) : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [hscale, hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3), ← mul_assoc]

/-! ## 3. The carrier, and the endpoint -/

variable [NeZero d]

/-- **Steps (1)–(3): the translate-uniform carrier from the printed grid
carrier.**

The vanishing hypothesis `hFzero` is the `H¹₀` zero extension. -/
theorem uniformBoxGaugeBound_of_negBesovLp (m : ℤ) {s p A : ℝ} (hp : 0 < p) (hs0 : 0 < s)
    (hguard : s + (d : ℝ) / p ≤ 1 / 2) {F : Vec d → Vec d}
    (hFI : ∀ i, Integrable (fun y => F y i) volume)
    (hFzero : ∀ y, y ∉ cubeSet (originCube d m) → F y = 0)
    (hgauge : ∀ N : ℕ, negBesovLpPartialNorm (originCube d m) s p N F ≤ A) :
    UniformBoxGaugeBound m (s + (d : ℝ) / p)
      (6 * (d : ℝ) * liftGeomFactor (s + (d : ℝ) / p) *
        (A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (m : ℝ)))) F := by
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := div_nonneg (Nat.cast_nonneg d) hp.le
  have hs' : 0 < s + (d : ℝ) / p := by linarith only [hs0, hdp]
  have hs1 : s + (d : ℝ) / p < 1 := by linarith only [hguard]
  have hA : 0 ≤ A := by
    have h0 := negBesovLpDepthSeminorm_le_of_partialBound (originCube d m) hp F hgauge 0
    exact le_trans (negBesovLpDepthSeminorm_nonneg (originCube d m) s p F 0) h0
  have hA' : (0 : ℝ) ≤ A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (m : ℝ)) :=
    mul_nonneg hA (three_rpow_nonneg _)
  refine uniformBoxGaugeBound_of_gridGauge m hs1 hA' hFI ?_
  refine gridGauge_of_descendantBound m hA' hFzero ?_
  intro j R hR
  exact descendantBound_of_negBesovLp hp hgauge j R hR

/-- **THE CONVERSION THEOREM** — the `L^∞` endpoint of Step 3c from the PRINTED
finite-`p` coarse-graining bound.

From the printed `(p,p)` negative Besov gauge of order `-s` on `∇w` at level
`A`, together with the frame (`w` weakly differentiable, integrable, compactly
supported, with a continuous representative vanishing on the faces of `□_m` —
the rendering of `u - v ∈ H¹₀(□_m)`) and the `H¹₀` zero extension of the
gradient, one obtains

```text
  3^{-m}|g x| ≤ 96 d² · liftGeomFactor (s + d/p) · A    for a.e. x ∈ □_m,
```

which is EXACTLY the shape of clause (C3) of the frozen root, with `A` in the
slot the `(∞,∞)` route filled with `3^{-ms}‖∇u-∇v‖_{Ŵ̲^{-s,∞}}`.  The
`3^{m(s+d/p)}` of the extraction has cancelled; the finite-`p` route costs a
dimension-only factor and the exponent guard `s + d/p ≤ 1/2`, nothing else. -/
theorem ae_linfty_of_negBesovLp (m : ℤ) {s p A : ℝ}
    (hp : 0 < p) (hs0 : 0 < s) (hguard : s + (d : ℝ) / p ≤ 1 / 2)
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hGzero : ∀ y, y ∉ cubeSet (originCube d m) → G y = 0)
    (hgauge : ∀ N : ℕ, negBesovLpPartialNorm (originCube d m) s p N G ≤ A)
    {g : Vec d → ℝ} (hgc : Continuous g) (hgw : w =ᵐ[volume] g)
    (hzero : ∀ y ∈ cubeFaceSet (originCube d m), g y = 0) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      (3 : ℝ) ^ (-(m : ℝ)) * |g x| ≤
        96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * A := by
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := div_nonneg (Nat.cast_nonneg d) hp.le
  have hs' : 0 < s + (d : ℝ) / p := by linarith only [hs0, hdp]
  have hbox := uniformBoxGaugeBound_of_negBesovLp m hp hs0 hguard hGI hGzero hgauge
  have hres := ae_linfty_of_uniformBoxGauge_originCube (d := d) m hw hwI hwc hGI hbox hs'
    hguard hgc hgw hzero
  refine hres.mono fun x hx => ?_
  refine hx.trans (le_of_eq ?_)
  have hcanc := linfty_constant_cancels m (16 * (d : ℝ) * (6 * (d : ℝ) *
    liftGeomFactor (s + (d : ℝ) / p))) A (s + (d : ℝ) / p)
  calc 16 * (d : ℝ) *
        (6 * (d : ℝ) * liftGeomFactor (s + (d : ℝ) / p) *
          (A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (m : ℝ)))) *
        (3 : ℝ) ^ (-(m : ℝ) * (s + (d : ℝ) / p))
      = 16 * (d : ℝ) * (6 * (d : ℝ) * liftGeomFactor (s + (d : ℝ) / p)) *
          (A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (m : ℝ))) *
          (3 : ℝ) ^ (-(m : ℝ) * (s + (d : ℝ) / p)) := by ring
    _ = 16 * (d : ℝ) * (6 * (d : ℝ) * liftGeomFactor (s + (d : ℝ) / p)) * A := hcanc
    _ = 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * A := by ring

/-! ## 4. The swap into the Step-3c chain -/

/-- **Step 3c, from the printed finite-`p` proposition** — the
`stepThreeLinftyUpgrade` composed with the conversion, in one application.

The output is the introduction's homogenization estimate with the Step-3
constant `96 d² γ · 2C` DISPLAYED, i.e. the same shape obtained from the
`(∞,∞)` route with `C_lift = 96 d² γ` in place of the `8`.  Nothing in the tree
is edited. -/
theorem stepThreeLinfty_of_negBesovLp (m : ℤ) {s p A C sigma D : ℝ}
    (hp : 0 < p) (hs0 : 0 < s) (hguard : s + (d : ℝ) / p ≤ 1 / 2)
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hGzero : ∀ y, y ∉ cubeSet (originCube d m) → G y = 0)
    (hgauge : ∀ N : ℕ, negBesovLpPartialNorm (originCube d m) s p N G ≤ A)
    {g : Vec d → ℝ} (hgc : Continuous g) (hgw : w =ᵐ[volume] g)
    (hzero : ∀ y ∈ cubeFaceSet (originCube d m), g y = 0)
    (hweak : A ≤ 2 * C * D * (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) +
      (3 : ℝ) ^ ((m : ℝ) / 2))) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      (3 : ℝ) ^ (-(m : ℝ)) * |g x| ≤
        (96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * (2 * C) * D) *
          (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) + (3 : ℝ) ^ ((m : ℝ) / 2)) := by
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := div_nonneg (Nat.cast_nonneg d) hp.le
  have hs1 : s + (d : ℝ) / p < 1 := by linarith only [hguard]
  have hK : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) := by
    have hg0 : (0 : ℝ) ≤ liftGeomFactor (s + (d : ℝ) / p) := liftGeomFactor_nonneg hs1
    have hsq : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) := by
      have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
      linarith only [hd2]
    exact mul_nonneg hsq hg0
  have hbase := ae_linfty_of_negBesovLp m hp hs0 hguard hw hwI hwc hGI hGzero hgauge hgc hgw hzero
  refine hbase.mono fun x hx => ?_
  refine hx.trans ?_
  have hstep := mul_le_mul_of_nonneg_left hweak hK
  refine hstep.trans (le_of_eq ?_)
  ring

/-- **THE SWAP, from `hCG'` itself, in ONE application.**

The transcribed printed proposition `hCG'`, its energy slot supplied by the
Step-2b datum `S`, and the Step-3b comparison `hweak` compose to the
introduction's homogenization estimate.  This is the entry point that replaces
the `(∞,∞)` route: the caller supplies the SAME Step-2b datum and the SAME
Step-3b arithmetic; only the constant changes, from the absolute `8` to the
dimension-only `96 d² · liftGeomFactor (s + d/p)`. -/
theorem stepThreeLinfty_of_coarseGraining (m : ℤ) {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg S C D : ℝ} {Gen : TriadicCube d → ℝ}
    {Fflux : Vec d → Vec d}
    (hp : 0 < p) (hs0 : 0 < s) (hguard : s + (d : ℝ) / p ≤ 1 / 2) (hsigma : 0 < sigma)
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hGzero : ∀ y, y ∉ cubeSet (originCube d m) → G y = 0)
    (hCG : GeneralCoarseGrainingFiniteP (originCube d m) jn Ccg s s1 s2 p sigma E1 E2 Dg
      Gen G Fflux)
    (hS : ∀ N : ℕ,
      coarseGrainingEnergyPartial (originCube d m) p (s - s1) jn N Gen ≤ S)
    {g : Vec d → ℝ} (hgc : Continuous g) (hgw : w =ᵐ[volume] g)
    (hzero : ∀ y ∈ cubeFaceSet (originCube d m), g y = 0)
    (hweak : sigma⁻¹ *
        coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S
          ((originCube d m).scale - (jn : ℤ)) ≤
      2 * C * D * (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) + (3 : ℝ) ^ ((m : ℝ) / 2))) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      (3 : ℝ) ^ (-(m : ℝ)) * |g x| ≤
        (96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * (2 * C) * D) *
          (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) + (3 : ℝ) ^ ((m : ℝ) / 2)) :=
  stepThreeLinfty_of_negBesovLp m hp hs0 hguard hw hwI hwc hGI hGzero
    (fun N => hCG.gradPartial hS hsigma N) hgc hgw hzero hweak

end

end Algsuperdiff.Section4.Provider.Homogenization
