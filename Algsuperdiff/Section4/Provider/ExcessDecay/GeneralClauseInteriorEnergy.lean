/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.ConstantDatumCoreEnergy
import Algsuperdiff.Section4.Provider.ExcessDecay.InteriorClause

/-!
# The interior Caccioppoli energy at the sharpened force envelope

The whole distance sits in one place: the energy estimate that feeds the
`x`-frame coarse-graining composition.  The proved one
(`InteriorClause.ae_interiorCaccioppoliEnergy_anchorWindow`) carries the force
envelope `s^{-11}` (printed) resp.  `s^{-8}` (honest); this module produces the
**same statement at `s^{-6}`**:

```text
  ⨍_{(x-z)+□_n} ∇ũ · ã_{L,n+2} ∇ũ · 1_𝒢
      ≤ Cout ( σ̄_{n+2} 3^{-2(n+2)} ‖u - (u)_W‖²_{L̲²(W)}
               + s^{-6} σ̄_{n+2}^{-1} 3^{2s(n+2)} [g]²_{H̲^s(W)} ) ,
      W = ((z+□_{n+2}) ∩ □_m) .
```

Two `s`-powers better than the honest interior display, four better than the
printed one.  The source of the gain is `ConstantDatumCoreEnergy`: the
Caccioppoli inequality is applied to the difference of `u - c` with the cube's
own zero-trace corrector, so CoarseGraining's `t^{-8}` force leg never appears;
the force enters only through the corrector's own energy and value bounds, at
`t^{-3} λ_{t,2}^{-1}` and `(t^{-3} λ_{t,2}^{-1})²`, and the good event's
two-sided ellipticity caps (`λ_{t,1} ≤ K σ̄`, `λ_{t,2}^{-1} ≤ K σ̄^{-1}`) turn
`λ_{t,1} λ_{t,2}^{-2}` into `K³ σ̄^{-1}` at no `s`-cost.

Downstream, composed with the proved `x`-frame chain's `s^{-4}` flux prefactor,
`√(s^{-6}) = s^{-3}` gives the general clause's own printed force exponent
`s^{-7}` exactly.

## Deviations from the printed statement

* the Caccioppoli parameter pair is `(1/4, s/4)`, the proved interior choice
  (`CaccioppoliInteriorPrefactor`), and the negative-norm value estimate is
  entered at its own parameter `s` (so its negative index is `s/2 = 2·(s/4)`);
* the Besov index of the corrector legs is `s/2`, raised to the anchor's `s` by
  the exponent comparison `[g]_{B̲^{s/2}} ≤ [g]_{B̲^{s}}` (no constant);
* the `σ̄` index is `n+2` throughout, exactly as in the proved interior
  display; `SigmaBarIndex` converts it downstream.
* no `γ`-move is made anywhere.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`; `e.energy.bound.interior`;
  `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The display object, in the cube's own frame -/

/-- **The sharpened interior Caccioppoli right-hand side, squared, in the cube's
own frame.**  The proved `interiorEnergyRHS` at the force envelope `s^{-6}` in
place of `s^{-8}`. -/
def constantDatumEnergyRHS (M : ABKModel d) (n : ℤ) (s : ℝ)
    (u : H1Function (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d)))
    (g : Vec d → Vec d) : ℝ :=
  (Annealed.sigmaBar M (n + 2) : ℝ) *
      Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) *
      normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y -
          volumeAverage (openCubeSet (originCube d (n + 2))) u.toFun) +
    Real.rpow s (-6 : ℝ) * (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ *
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s g ^ (2 : ℕ)

/-! ## 2. The cap arithmetic -/

/-- Squaring a real power of a positive base (local copy of the same step in
`ConstantDatumCorrector`; the original is `private`). -/
private theorem rpow_sq' {x : ℝ} (hx : 0 < x) (a : ℝ) :
    Real.rpow x a ^ (2 : ℕ) = Real.rpow x (2 * a) := by
  have h : Real.rpow x (a + a) = Real.rpow x a * Real.rpow x a := Real.rpow_add hx a a
  have h2 : (2 : ℝ) * a = a + a := by ring
  rw [h2, h, pow_two]

/-- `(s/4)^{-3} = 64 s^{-3}`. -/
private theorem rpow_quarter_neg_three {s : ℝ} (hs : 0 < s) :
    Real.rpow (s / 4) (-3 : ℝ) = 64 * Real.rpow s (-3 : ℝ) := by
  have h4 : Real.rpow (4 : ℝ) (-3 : ℝ) = (64 : ℝ)⁻¹ := by
    rw [Real.rpow_eq_pow, show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  rw [Real.rpow_eq_pow, Real.div_rpow hs.le (by norm_num),
    ← Real.rpow_eq_pow s, ← Real.rpow_eq_pow (4 : ℝ), h4]
  field_simp

/-- The cap composition of the sharpened display, on abstract reals: the
prefactor cap, the two good-event ellipticity caps, the parameter conversion
`(s/4)^{-3} = 64 s^{-3}`, the exponent comparison `s^{-3} ≤ s^{-6}` and the
Besov exponent comparison, folded into one constant.  Every transcendental atom
is opaque here. -/
private theorem constantDatum_cap_arith
    {E P Pb lam1 Kc sig S X t3 linv B Bs s3 s6 KC Cout : ℝ}
    (hmain : E ≤ KC * (P * lam1 * (S * X + (t3 * linv * B) ^ (2 : ℕ)) +
      t3 * linv * B ^ (2 : ℕ)))
    (hP : P ≤ Pb) (hPb0 : 0 ≤ Pb)
    (hlam1 : lam1 ≤ Kc * sig) (hlam10 : 0 ≤ lam1)
    (hlinv : linv ≤ Kc * sig⁻¹) (hlinv0 : 0 ≤ linv)
    (ht3 : t3 = 64 * s3) (hs3s6 : s3 ≤ s6) (hs30 : 0 ≤ s3) (hs32 : s3 ^ (2 : ℕ) = s6)
    (hB : B ≤ Bs) (hB0 : 0 ≤ B)
    (hS0 : 0 ≤ S) (hX0 : 0 ≤ X) (hsig : 0 < sig) (hKc0 : 0 ≤ Kc) (hKC0 : 0 ≤ KC)
    (hCout : KC * (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) ≤ Cout) :
    E ≤ Cout * (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by
  have hsiginv0 : (0 : ℝ) ≤ sig⁻¹ := inv_nonneg.mpr hsig.le
  have hs60 : (0 : ℝ) ≤ s6 := le_trans hs30 hs3s6
  have hBs0 : (0 : ℝ) ≤ Bs := le_trans hB0 hB
  have hA1 : (0 : ℝ) ≤ sig * S * X := mul_nonneg (mul_nonneg hsig.le hS0) hX0
  have hA2 : (0 : ℝ) ≤ s6 * sig⁻¹ * Bs ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg hs60 hsiginv0) (pow_nonneg hBs0 2)
  -- the first leg
  have hT1 : P * lam1 * (S * X) ≤ Pb * Kc * (sig * S * X) := by
    have h1 : P * lam1 ≤ Pb * (Kc * sig) := mul_le_mul hP hlam1 hlam10 hPb0
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hS0 hX0)
    calc P * lam1 * (S * X) ≤ Pb * (Kc * sig) * (S * X) := h2
      _ = Pb * Kc * (sig * S * X) := by ring
  -- the corrector value leg
  have hprod : t3 * linv * B ≤ 64 * s3 * (Kc * sig⁻¹) * Bs := by
    have hfac : (0 : ℝ) ≤ 64 * s3 := by linarith only [hs30]
    have h1 : 64 * s3 * linv ≤ 64 * s3 * (Kc * sig⁻¹) :=
      mul_le_mul_of_nonneg_left hlinv hfac
    have h2 : (0 : ℝ) ≤ 64 * s3 * (Kc * sig⁻¹) :=
      mul_nonneg hfac (mul_nonneg hKc0 hsiginv0)
    rw [ht3]
    exact mul_le_mul h1 hB hB0 h2
  have hprod0 : (0 : ℝ) ≤ t3 * linv * B := by
    rw [ht3]
    exact mul_nonneg (mul_nonneg (by linarith only [hs30]) hlinv0) hB0
  have hsq : (t3 * linv * B) ^ (2 : ℕ) ≤
      4096 * s6 * (Kc ^ (2 : ℕ) * (sig⁻¹) ^ (2 : ℕ)) * Bs ^ (2 : ℕ) := by
    refine le_trans (pow_le_pow_left₀ hprod0 hprod 2) (le_of_eq ?_)
    rw [← hs32]
    ring
  have hsigsq : sig * (sig⁻¹) ^ (2 : ℕ) = sig⁻¹ := by
    field_simp
  have hT2 : P * lam1 * (t3 * linv * B) ^ (2 : ℕ) ≤
      4096 * (Pb * Kc ^ (3 : ℕ)) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by
    have h1 : P * lam1 ≤ Pb * (Kc * sig) := mul_le_mul hP hlam1 hlam10 hPb0
    have hstep := mul_le_mul h1 hsq (pow_nonneg hprod0 2)
      (mul_nonneg hPb0 (mul_nonneg hKc0 hsig.le))
    refine le_trans hstep (le_of_eq ?_)
    calc Pb * (Kc * sig) * (4096 * s6 * (Kc ^ (2 : ℕ) * (sig⁻¹) ^ (2 : ℕ)) * Bs ^ (2 : ℕ))
        = 4096 * (Pb * Kc ^ (3 : ℕ)) * (s6 * (sig * (sig⁻¹) ^ (2 : ℕ)) * Bs ^ (2 : ℕ)) := by
          ring
      _ = 4096 * (Pb * Kc ^ (3 : ℕ)) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by rw [hsigsq]
  -- the corrector energy leg
  have hT3 : t3 * linv * B ^ (2 : ℕ) ≤ 64 * Kc * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by
    have hBsq : B ^ (2 : ℕ) ≤ Bs ^ (2 : ℕ) := pow_le_pow_left₀ hB0 hB 2
    have h1 : t3 * linv ≤ 64 * s6 * (Kc * sig⁻¹) := by
      have ha : t3 ≤ 64 * s6 := by
        rw [ht3]
        linarith only [hs3s6]
      have hb : (0 : ℝ) ≤ 64 * s6 := by linarith only [hs60]
      exact mul_le_mul ha hlinv hlinv0 hb
    have h2 : (0 : ℝ) ≤ 64 * s6 * (Kc * sig⁻¹) :=
      mul_nonneg (by linarith only [hs60]) (mul_nonneg hKc0 hsiginv0)
    refine le_trans (mul_le_mul h1 hBsq (pow_nonneg hB0 2) h2) (le_of_eq ?_)
    ring
  -- the assembly
  have hsum : P * lam1 * (S * X + (t3 * linv * B) ^ (2 : ℕ)) + t3 * linv * B ^ (2 : ℕ) ≤
      (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) *
        (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by
    have hexp : P * lam1 * (S * X + (t3 * linv * B) ^ (2 : ℕ)) =
        P * lam1 * (S * X) + P * lam1 * (t3 * linv * B) ^ (2 : ℕ) := by ring
    have hc1 : Pb * Kc * (sig * S * X) ≤
        (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) * (sig * S * X) := by
      have hrest : (0 : ℝ) ≤ 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc := by
        have h1 : (0 : ℝ) ≤ Pb * Kc ^ (3 : ℕ) := mul_nonneg hPb0 (pow_nonneg hKc0 3)
        linarith only [h1, hKc0]
      have := mul_le_mul_of_nonneg_right hrest hA1
      linarith only [this]
    have hc2 : (4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) ≤
        (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by
      have hrest : (0 : ℝ) ≤ Pb * Kc := mul_nonneg hPb0 hKc0
      have := mul_le_mul_of_nonneg_right hrest hA2
      linarith only [this]
    have hd : 4096 * (Pb * Kc ^ (3 : ℕ)) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) +
        64 * Kc * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) =
        (4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by ring
    have hexpand : (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) *
        (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ)) =
        (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) * (sig * S * X) +
          (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) *
            (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by ring
    rw [hexp, hexpand]
    linarith only [hT1, hT2, hT3, hc1, hc2, hd]
  have hbig : (0 : ℝ) ≤ sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ) := by
    linarith only [hA1, hA2]
  calc E ≤ KC * (P * lam1 * (S * X + (t3 * linv * B) ^ (2 : ℕ)) + t3 * linv * B ^ (2 : ℕ)) :=
        hmain
    _ ≤ KC * ((Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) *
          (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ))) := mul_le_mul_of_nonneg_left hsum hKC0
    _ = KC * (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) *
          (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by ring
    _ ≤ Cout * (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hCout hbig

/-! ## 3. The energy estimate on the good event, in the cube's own frame -/

/-- **The sharpened `e.energy.bound.interior` at the parent slot.**

Almost surely on the harmonic anchor's good event `𝒢(n+2, z; s/8, 1/2)`, for
every `L ≥ n+2`, every window centre `w` whose Dirichlet patch `w + □_{n+1}`
sits inside `□_{n+2}` (the interior regime), and every `H¹(□_{n+2})` solution of
`-∇·ã_{L,n+2}∇u = ∇·g` with `g ∈ H^s(□_{n+2})`,

```text
  ⨍_{□_{n+2} ∩ (w+□_n)} ∇u · ã_{L,n+2} ∇u ≤ Cout · constantDatumEnergyRHS M n s u g ,
```

i.e. the proved interior display at the force envelope `s^{-6}` in place of
`s^{-8}`.  The Caccioppoli parameter pair is the proved `(1/4, s/4)`; the two
ellipticity caps are the proved good-event ones, read at the `q = 2` indices
`1/8`, `s/8` and `s/4`. -/
theorem ae_constantDatumEnergy_harmonicSlot (d : ℕ) [NeZero d] :
    ∃ C Cout : ℝ, 0 < C ∧ 0 < Cout ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ (n : ℤ) (z : Vec d),
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 2) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ L : ℤ, n + 2 ≤ L → ∀ (w : Vec d) (g : Vec d → Vec d)
                (u : H1Function
                  (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d))),
                openCubeAtScale w (n + 1) ⊆ openCubeSet (originCube d (n + 2)) →
                ForceBesovRegularity (originCube d (n + 2)) s g →
                IsForcedEquation (originCube d (n + 2))
                    (Support.fluxCorrectedCoeffFamily M L (n + 2)
                      (originCube d (n + 2))
                      (Cutoff.translateCutoffSample z omega)) u g →
                  localizedCoeffEnergyValue
                      (caccioppoliCoreSet (originCube d (n + 2)) w)
                      ((Support.fluxCorrectedCoeffFamily M L (n + 2)
                        (originCube d (n + 2))
                        (Cutoff.translateCutoffSample z omega)).coeffOn
                        (originCube d (n + 2))) u ≤
                    Cout * constantDatumEnergyRHS M n s u g := by
  obtain ⟨C₁, KC, hC₁, hKC, hcore⟩ := exists_constantDatumCoreEnergy d
  obtain ⟨C, hCpos, hcaps⟩ := ae_boundLambdasByEs_parent_index_le_harmonicSlot d
  have hd : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set Kc : ℝ := 2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1) with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    have h1 : (0 : ℝ) < (C * (1 / 2)) ^ 2 + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (d : ℝ) := by linarith only [hd]
    exact mul_pos h2 h1
  set Pb : ℝ := (2 * max 1 C₁) ^ (4 : ℕ) * 4 * (Kc ^ (2 : ℕ)) ^ (2 : ℕ) with hPbdef
  have hPbpos : 0 < Pb := by
    have hCm : (0 : ℝ) < 2 * max 1 C₁ := by
      have : (1 : ℝ) ≤ max 1 C₁ := le_max_left _ _
      linarith only [this]
    rw [hPbdef]
    positivity
  refine ⟨C, KC * (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc), hCpos, ?_, ?_⟩
  · have h1 : 0 < Pb * Kc := mul_pos hPbpos hKcpos
    have h2 : 0 < 4096 * (Pb * Kc ^ (3 : ℕ)) := by positivity
    have h3 : 0 < 64 * Kc := by linarith only [hKcpos]
    exact mul_pos hKC (by linarith only [h1, h2, h3])
  intro M s hsrange hregime hsmall hs n z
  filter_upwards [hcaps M s hsrange hregime hsmall hs n z] with omega hcap
  intro hmem L hL w g u hpatch hgreg hu
  have hs1 : s ≤ 1 := hsrange.2
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 2) : ℝ) := (Annealed.sigmaBar M (n + 2)).2
  set aFam : CoeffFamily d := Support.fluxCorrectedCoeffFamily M L (n + 2)
    (originCube d (n + 2)) (Cutoff.translateCutoffSample z omega) with haFam
  -- the deterministic core bound at the proved parameter pair
  have hgreg' : ForceBesovRegularity (originCube d (n + 2)) (2 * (s / 4)) g :=
    CubeVectorBesovHRegularity.of_exponent_le hgreg (by linarith only [hs])
  have hscale : (originCube d (n + 2)).scale - 1 = n + 1 := by
    show n + 2 - 1 = n + 1
    ring
  have hpatch' : openCubeAtScale w ((originCube d (n + 2)).scale - 1) ⊆
      openCubeSet (originCube d (n + 2)) := by
    rw [hscale]
    exact hpatch
  have hmain := hcore (t := s / 4)
    (c := volumeAverage (openCubeSet (originCube d (n + 2))) u.toFun) u hu
    (by linarith only [hs]) (by linarith only [hs1]) hpatch' hgreg'
  -- the two `q = 2` caps, read off the proved ratio maximum
  have hcapU : (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ *
      Ch02.LambdaSq (originCube d (n + 2)) (1 / 4 / 2) (.finite 2) aFam ≤ Kc := by
    have h := hcap hmem L hL (1 / 4 / 2) (by linarith only [hs1])
    rw [fluxCorrectedEllipticityRatioMax_def] at h
    exact le_trans (le_max_left _ _) h
  have hcapL : (Annealed.sigmaBar M (n + 2) : ℝ) *
      (Ch02.lambdaSq (originCube d (n + 2)) (s / 4 / 2) (.finite 2) aFam)⁻¹ ≤ Kc := by
    have h := hcap hmem L hL (s / 4 / 2) (by linarith only [])
    rw [fluxCorrectedEllipticityRatioMax_def] at h
    exact le_trans (le_max_right _ _) h
  have hcapL2 : (Annealed.sigmaBar M (n + 2) : ℝ) *
      (Ch02.lambdaSq (originCube d (n + 2)) (s / 4) (.finite 2) aFam)⁻¹ ≤ Kc := by
    have h := hcap hmem L hL (s / 4) (by linarith only [hs])
    rw [fluxCorrectedEllipticityRatioMax_def] at h
    exact le_trans (le_max_right _ _) h
  -- the `q = 1` ingredients and the prefactor
  have hLam := LambdaS_le_of_ratio_cap (originCube d (n + 2)) aFam (u := 1 / 4)
    (by norm_num) hsig hcapU
  have hlamInv := lambdaS_inv_le_of_ratio_cap (originCube d (n + 2)) aFam (u := s / 4)
    (by linarith only [hs]) hsig hcapL
  have hlam1 : Ch02.lambdaS (originCube d (n + 2)) (s / 4) aFam ≤ Kc *
      (Annealed.sigmaBar M (n + 2) : ℝ) :=
    le_trans (lambdaS_le_LambdaS (originCube d (n + 2)) _ (by norm_num)
      (by linarith only [hs])) hLam
  have hTheta : Ch02.ThetaRatio (originCube d (n + 2)) (1 / 4) (s / 4) aFam ≤
      (Kc ^ (2 : ℕ)) := by
    have h := thetaRatio_le_of_caps (originCube d (n + 2)) aFam
      (by norm_num : (0 : ℝ) < 1 / 4) (by linarith only [hs] : (0 : ℝ) < s / 4)
      hLam hlamInv
    have heq : Kc * (Annealed.sigmaBar M (n + 2) : ℝ) *
        (Kc * (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹) = Kc ^ (2 : ℕ) := by
      field_simp
    rw [heq] at h
    exact h
  have hP := caccioppoliWithRHSPrefactor_quarter_le (Q := originCube d (n + 2))
    (a := aFam) (C := C₁) (s := s) hC₁ hs hs1 hTheta
  -- the `q = 2` inverse, in the `rpow` form the corrector bounds produce
  have hlinv : Real.rpow (Ch02.lambdaSq (originCube d (n + 2)) (s / 4) (.finite 2) aFam)
      (-1 : ℝ) ≤ Kc * (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ := by
    rw [Real.rpow_eq_pow, Real.rpow_neg_one]
    have h2 := mul_le_mul_of_nonneg_left hcapL2 (inv_nonneg.mpr hsig.le)
    rw [inv_mul_cancel_left₀ hsig.ne'] at h2
    calc (Ch02.lambdaSq (originCube d (n + 2)) (s / 4) (.finite 2) aFam)⁻¹
        ≤ (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ * Kc := h2
      _ = Kc * (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ := by ring
  -- the remaining data
  have hlam10 : 0 ≤ Ch02.lambdaS (originCube d (n + 2)) (s / 4) aFam := by
    rw [Ch02.lambdaS]
    exact Ch02.lambdaSq_finite_nonneg _ _ (by linarith only [hs]) (by norm_num)
  have hlinv0 : (0 : ℝ) ≤ Real.rpow
      (Ch02.lambdaSq (originCube d (n + 2)) (s / 4) (.finite 2) aFam) (-1 : ℝ) :=
    Real.rpow_nonneg
      (Ch02.lambdaSq_finite_nonneg _ _ (by linarith only [hs]) (by norm_num)) _
  have hBnn : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d (n + 2)) (2 * (s / 4)) g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove _ _ g
      hgreg'.partialSeminorms_bddAbove
  have hB : scaleNormalizedPositiveBesovVectorSeminormTwo
        (originCube d (n + 2)) (2 * (s / 4)) g ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s g :=
    cubeBesovPositiveVectorSeminormTwo_le_of_exponent_le_of_bddAbove
      (originCube d (n + 2)) g (by linarith only [hs])
      hgreg.partialSeminorms_bddAbove
  have hS0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hX0 : 0 ≤ normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
      (fun y => u.toFun y -
        volumeAverage (openCubeSet (originCube d (n + 2))) u.toFun) :=
    normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet _)
  have ht3 : Real.rpow (s / 4) (-3 : ℝ) = 64 * Real.rpow s (-3 : ℝ) :=
    rpow_quarter_neg_three hs
  have hs3s6 : Real.rpow s (-3 : ℝ) ≤ Real.rpow s (-6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
  have hs30 : (0 : ℝ) ≤ Real.rpow s (-3 : ℝ) := Real.rpow_nonneg hs.le _
  have hs32 : Real.rpow s (-3 : ℝ) ^ (2 : ℕ) = Real.rpow s (-6 : ℝ) := by
    rw [rpow_sq' hs]
    congr 1
    norm_num
  have hscaleeq : (((originCube d (n + 2)).scale : ℤ) : ℝ) = (((n + 2 : ℤ)) : ℝ) := by
    rw [scale_originCube]
  rw [hscaleeq] at hmain
  rw [constantDatumEnergyRHS]
  exact constantDatum_cap_arith hmain hP hPbpos.le hlam1 hlam10 hlinv hlinv0 ht3
    hs3s6 hs30 hs32 hB hBnn hS0 hX0 hsig hKcpos.le hKC.le (le_refl _)

/-! ## 4. The display in the frozen theorem's own carriers -/

/-- **The sharpened right-hand side, in the frozen theorem's own carriers.** The
proved `interiorAnchorEnergyRHSOn` at `s^{-6}` in place of `s^{-11}`. -/
def constantDatumAnchorEnergyRHSOn (M : ABKModel d) (n : ℤ) (s : ℝ) (W : Set (Vec d))
    (f : Vec d → ℝ) (g : Vec d → Vec d) : ℝ :=
  (Annealed.sigmaBar M (n + 2) : ℝ) *
      Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) *
      (eLpNorm (fun y => f y - volumeAverage W f) 2
        (Support.normalizedVolumeMeasureOn W)).toReal ^ (2 : ℕ) +
    Real.rpow s (-6 : ℝ) * (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ *
      Real.rpow (3 : ℝ) (2 * s * (((n + 2 : ℤ)) : ℝ)) *
      (Support.normalizedGagliardoESeminormOn W s g).toReal ^ (2 : ℕ)

/-- The arithmetic of the carrier conversion: the `L²` leg is an identity, the
force leg costs the square of the Besov-versus-Gagliardo constant. -/
private theorem anchor_stitch' {A L2 B Bes K W G : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL2 : 0 ≤ L2) (hBes : 0 ≤ Bes) (hK : 0 ≤ K) (hW : 0 ≤ W) (hG : 0 ≤ G)
    (hbes : Bes ≤ K * W * G) :
    A * L2 + B * Bes ^ (2 : ℕ) ≤
      (K ^ (2 : ℕ) + 1) * (A * L2 + B * W ^ (2 : ℕ) * G ^ (2 : ℕ)) := by
  have hsq : Bes ^ (2 : ℕ) ≤ K ^ (2 : ℕ) * (W ^ (2 : ℕ) * G ^ (2 : ℕ)) := by
    calc Bes ^ (2 : ℕ) ≤ (K * W * G) ^ (2 : ℕ) := pow_le_pow_left₀ hBes hbes 2
      _ = K ^ (2 : ℕ) * (W ^ (2 : ℕ) * G ^ (2 : ℕ)) := by ring
  have hAL2 : 0 ≤ A * L2 := mul_nonneg hA hL2
  have hWG : (0 : ℝ) ≤ W ^ (2 : ℕ) * G ^ (2 : ℕ) :=
    mul_nonneg (pow_nonneg hW 2) (pow_nonneg hG 2)
  have hK2 : (0 : ℝ) ≤ K ^ (2 : ℕ) := pow_nonneg hK 2
  have hBWG : 0 ≤ B * (W ^ (2 : ℕ) * G ^ (2 : ℕ)) := mul_nonneg hB hWG
  have hterm : B * Bes ^ (2 : ℕ) ≤ K ^ (2 : ℕ) * (B * (W ^ (2 : ℕ) * G ^ (2 : ℕ))) := by
    calc B * Bes ^ (2 : ℕ) ≤ B * (K ^ (2 : ℕ) * (W ^ (2 : ℕ) * G ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left hsq hB
      _ = K ^ (2 : ℕ) * (B * (W ^ (2 : ℕ) * G ^ (2 : ℕ))) := by ring
  have hexp : (K ^ (2 : ℕ) + 1) * (A * L2 + B * W ^ (2 : ℕ) * G ^ (2 : ℕ)) =
      K ^ (2 : ℕ) * (A * L2) + K ^ (2 : ℕ) * (B * (W ^ (2 : ℕ) * G ^ (2 : ℕ))) +
        (A * L2 + B * (W ^ (2 : ℕ) * G ^ (2 : ℕ))) := by ring
  have hpos1 : 0 ≤ K ^ (2 : ℕ) * (A * L2) := mul_nonneg hK2 hAL2
  rw [hexp]
  linarith only [hterm, hpos1, hBWG]

/-- **The carrier conversion of the sharpened display.**  Verbatim the proved
`interiorEnergyRHSPrinted_le_anchorRHS`, at the force envelope `s^{-6}`. -/
theorem constantDatumEnergyRHS_le_anchorRHS [NeZero d] (M : ABKModel d) (n : ℤ)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {z : Vec d} {f : Vec d → ℝ}
    (v : H1Function (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d)))
    (hv : v.toFun = fun y => f (y + z))
    (hmem : MemLp (fun y => f (y + z)) 2 (normalizedCubeMeasure (originCube d (n + 2))))
    (g : Vec d → Vec d)
    (hgL2 : MemLp g 2 (Support.normalizedVolumeMeasureOn
      ((fun y' => z + y') '' openCubeSet (originCube d (n + 2)))))
    (hgW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))))) :
    constantDatumEnergyRHS M n s v (fun y => -g (y + z)) ≤
      (besovGagliardoConstant d ^ (2 : ℕ) + 1) *
        constantDatumAnchorEnergyRHSOn M n s
          ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) f g := by
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 2) : ℝ) :=
    (Annealed.sigmaBar M (n + 2)).2
  have hgreg : ForceBesovRegularity (originCube d (n + 2)) s (fun y => -g (y + z)) :=
    forceBesovRegularity_translated_neg (originCube d (n + 2)) hs hs1 hgL2 hgW
  have hbes := besovVectorSeminormTwo_translated_neg_le_gagliardo_window
    (originCube d (n + 2)) hs hs1 hgL2 hgW
  have hBesnn : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d (n + 2)) s (fun y => -g (y + z)) :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove _ s _
      hgreg.partialSeminorms_bddAbove
  rw [constantDatumEnergyRHS, constantDatumAnchorEnergyRHSOn]
  simp only [hv]
  rw [normalizedL2SqOnSet_translate_sub_average_eq_eLpNorm_sq_image_add
      (originCube d (n + 2)) f hmem,
    ← cubeBesovScaleWeight_neg_originCube_sq (d := d) (n + 2) s]
  exact anchor_stitch'
    (mul_nonneg hsig.le (Real.rpow_nonneg (by norm_num) _))
    (mul_nonneg (Real.rpow_nonneg hs.le _) (inv_nonneg.mpr hsig.le))
    (pow_nonneg ENNReal.toReal_nonneg 2) hBesnn (besovGagliardoConstant_nonneg d)
    (cubeBesovScaleWeight_nonneg (-s) _) ENNReal.toReal_nonneg hbes

/-! ## 5. The sharpened energy estimate at the anchor's own geometry -/

/-- **The sharpened interior energy estimate, at the frozen theorem's binders.**

Verbatim `InteriorClause.ae_interiorCaccioppoliEnergy_anchorWindow` — same
hypotheses, same left-hand side, same window — with the right-hand side at the
force envelope `s^{-6}` in place of `s^{-11}`. -/
theorem ae_constantDatumEnergy_anchorWindow (d : ℕ) [NeZero d] :
    ∃ C Cout : ℝ, 0 < C ∧ 0 < Cout ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 2 ≤ m → ∀ x z : Vec d,
          ∀ hz : z ∈ openCubeSet (originCube d m),
            (fun y => x + y) '' openCubeSet (originCube d n) ⊆
              ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                openCubeSet (originCube d m) →
            ∀ hfr : ((fun y => z + y) '' openCubeSet (originCube d (n + 2))) ∩
                frontier (openCubeSet (originCube d m)) = ∅,
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                    (Support.cgEllipLowerConstant d) (n + 2) z
                    ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                  ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                    Support.IsDirichletSolutionOn
                        (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                        (originCube d m) u hdat g →
                    MemLp g 2
                      (Support.normalizedVolumeMeasureOn
                        (((fun y' => z + y') ''
                            openCubeSet (originCube d (n + 2))) ∩
                          openCubeSet (originCube d m))) →
                    MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                      (Support.normalizedGagliardoMeasureOn
                        (((fun y' => z + y') ''
                            openCubeSet (originCube d (n + 2))) ∩
                          openCubeSet (originCube d m))) →
                      localizedCoeffEnergyValue
                          ((fun y => (x - z) + y) '' openCubeSet (originCube d n))
                          ((Support.fluxCorrectedCoeffFamily M L (n + 2)
                            (originCube d (n + 2))
                            (Cutoff.translateCutoffSample z omega)).coeffOn
                            (originCube d (n + 2)))
                          (H1Function.untranslate z
                            (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
                              (translateSet_openCubeSet_subset_of_frontier_inter_empty
                                hz hfr))) ≤
                        Cout * constantDatumAnchorEnergyRHSOn M n s
                          (((fun y' => z + y') ''
                              openCubeSet (originCube d (n + 2))) ∩
                            openCubeSet (originCube d m)) u.toFun g := by
  obtain ⟨C, Cout, hCpos, hCoutpos, hmain⟩ := ae_constantDatumEnergy_harmonicSlot d
  refine ⟨C, Cout * (besovGagliardoConstant d ^ (2 : ℕ) + 1), hCpos, ?_, ?_⟩
  · have hK : (0 : ℝ) ≤ besovGagliardoConstant d := besovGagliardoConstant_nonneg d
    positivity
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hz hsub hfr
  filter_upwards [hmain M s hsrange hregime hsmall hs n z] with omega hbound
  intro hmem u hdat g hsol hgL2 hgW
  have hs1 : s ≤ 1 := hsrange.2
  have hwin : (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      openCubeSet (originCube d m)) =
      (fun y' => z + y') '' openCubeSet (originCube d (n + 2)) :=
    inter_eq_of_frontier_inter_empty hz hfr
  rw [hwin] at hgL2 hgW
  rw [hwin]
  have heq := isForcedEquation_fluxCorrectedCoeffFamily_of_isDirichletSolutionOn
    (n := n) M L z omega hz hfr hsol
  have hgreg : ForceBesovRegularity (originCube d (n + 2)) s (fun y => -g (y + z)) :=
    forceBesovRegularity_translated_neg (originCube d (n + 2)) hs hs1 hgL2 hgW
  have hpatch : openCubeAtScale (x - z) (n + 1) ⊆
      openCubeSet (originCube d (n + 2)) :=
    openCubeAtScale_patch_subset_of_anchorGeometry hsub
  have hstep := hbound hmem L (le_trans hnm hmL) (x - z) (fun y => -g (y + z)) _
    hpatch hgreg heq
  rw [← caccioppoliCoreSet_eq_image_add_of_anchorGeometry hsub]
  have hmemL2 : MemLp (fun y => u.toFun (y + z)) 2
      (normalizedCubeMeasure (originCube d (n + 2))) :=
    memLp_two_normalizedCubeMeasure_of_h1 (originCube d (n + 2))
      (H1Function.untranslate z
        (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
          (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
  have hRHS := constantDatumEnergyRHS_le_anchorRHS M n hs hs1 (f := u.toFun)
    (H1Function.untranslate z
      (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
        (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
    rfl hmemL2 g hgL2 hgW
  refine le_trans hstep ?_
  calc Cout * constantDatumEnergyRHS M n s
        (H1Function.untranslate z
          (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
            (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
        (fun y => -g (y + z))
      ≤ Cout * ((besovGagliardoConstant d ^ (2 : ℕ) + 1) *
          constantDatumAnchorEnergyRHSOn M n s
            ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) u.toFun g) :=
        mul_le_mul_of_nonneg_left hRHS hCoutpos.le
    _ = Cout * (besovGagliardoConstant d ^ (2 : ℕ) + 1) *
          constantDatumAnchorEnergyRHSOn M n s
            ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) u.toFun g := by
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
