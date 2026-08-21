/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Frozen.Section24.LambdaSensitivityUnconditional
import Algsuperdiff.Section3.Provider.BadEvents.ResponseCongruence
import Algsuperdiff.Section3.Provider.BadEvents.ObservableSwapPayoff
import Algsuperdiff.Section3.Provider.Multiscale.Step1Assembly
import Algsuperdiff.Section4.Support.Events

/-!
# The field switch `a_{n−2} ⟶ a_{j−2}` at a triadic cube

ABK26, §4.1, the first inequality of the
sensitivity switch of `l.localize.lambdas.for.regularity`:

```
λ_{γ,2}^{-1}(z+□_{j−2}; a_{n−2})
  ≤ 6 ( 1 + C 3^{2j} ‖∇(k_{n−2} − k_{j−2})‖_{W̲^{1,∞}(z+□_{j−2})}
              λ_{γ,2}^{-1}(z+□_{j−2}; a_{j−2}) )^{2γ/(1−2γ)}
      λ_{γ,2}^{-1}(z+□_{j−2}; a_{j−2}) .
```

The manuscript reads this off `l.J.sensitivity.no.conditions`'s display
`e.lambda.sensitivity.no.conditions` at `a := a_{j−2}`, `h := k_{n−2} − k_{j−2}`,
`s = t = γ`, `q = 2` — hence the literal factor `6` and the exponent
`2γ/(1−2γ)`.

This module performs the transport to an arbitrary triadic cube `Q = z + □_l`
at the actual cutoff fields, using only proved, pointwise, unconditional
Section 3 machinery:

* `BadEvents.unitRescaledCutoffCoeff` / `unitCubeLambda_unitRescaledCutoffCoeff`
  — the `λ`-gauge of `a_r` on `Q` **is** the frozen unit-cube gauge of the
  rescaled coefficient object (an equality, no side condition);
* `BadEvents.perturbCoeffOn_unitRescaledCutoffCoeff_aeEq` /
  `unitCubeLambda_perturbCoeffOn_unitRescaledCutoffCoeff` — the frozen
  perturbation of the rescaled `a_j` by the rescaled increment `k_n − k_j`
  **is** the rescaled `a_n` (for `j ≤ n`);
* `BadEvents.gradientW1Infinity_incrementUnitCube₂_le` — the anchor's unit-cube
  gauge is below `incrementOscGauge₂ Q j n`, which is the manuscript's
  `3^{2l} ‖∇(k_n − k_j)‖_{W̲^{1,∞}(z+□_l)}`.

Nothing here is a.e. in the sample and nothing is conditional on a good local
event: unlike the Section 3 consumers of the *conditional* anchor
`Frozen.Section24.lambda_sensitivity`, the unconditional anchor needs no gate,
which is exactly why §4.1 can cite it as `l.J.sensitivity.no.conditions`.

## The carrier identification

`Section4/Support/Events.lean` writes the `𝒢₀` atom as the centered literal of
`Observable/CutoffMultiscaleEllipticity.lean` read at the translated sample.
`lambdaAnnulusAtom_eq_inv_lambdaSq` identifies it with `λ_{γ,2}^{-1}` of the
Chapter 2 carrier on the honest triadic cube `z + □_{k−2}`, which is what the
sensitivity statement above is phrased at.  It is the composition of two proved
Section 3 identities and carries no hypothesis.

## What is *not* here

The `𝒢₁`-derived budget `3^{2j}‖∇(k_{n−2}−k_{j−2})‖_{W̲^{1,∞}(z+□_{j−2})}
≤^{(1+γ)(m−j)/4}` — the second inequality of the step — is **not** proved here.

## References

* ABK26, `l.localize.lambdas.for.regularity`, the sensitivity switch.
* `l.J.sensitivity.no.conditions` / `e.lambda.sensitivity.no.conditions`, the
  anchor `Frozen.Section24.lambda_sensitivity_unconditional`.
* `d.good.event.for.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Localize

open Algsuperdiff.Section3
open Homogenization Homogenization.Book MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The triadic cube of a lattice point -/

/-- The triadic cube `z + □_j` at the lattice point `z = 3^j v` of `3^j ℤ^d`,
i.e. the cube of scale `j` and integer index `v`. -/
def latticeCube (j : ℤ) (v : Fin d → ℤ) : TriadicCube d := ⟨j, v⟩

@[simp] theorem latticeCube_scale (j : ℤ) (v : Fin d → ℤ) :
    (latticeCube j v).scale = j := rfl

/-- The base point of `latticeCube j v` is the Section 4 lattice point
`Support.triadicLatticePoint j v`. -/
theorem triadicCubeShift_latticeCube (j : ℤ) (v : Fin d → ℤ) :
    triadicCubeShift (latticeCube j v) = Support.triadicLatticePoint j v := by
  funext i
  simp only [triadicCubeShift, latticeCube, Support.triadicLatticePoint,
    cubeScaleFactor]
  exact mul_comm _ _

/-! ## 2. The `𝒢₀` atom is `λ_{γ,2}^{-1}` at the Chapter 2 carrier -/

/-- **The carrier identification.**  The Section 4 support layer's `𝒢₀` atom at
the lattice point `3^{k−2} v` is `λ_{γ,2}^{-1}(z + □_{k−2}; a_{k−2})` of the
Chapter 2 coefficient family of the actual cutoff, on the honest triadic cube.

This is the composition of the proved off-centre identification
`BadEvents.cubeLowerEllipticityInvLiteral_translateCutoffSample` with the
proved `Multiscale.cubeLowerEllipticityInvLiteral_eq_lambdaSq_inv`; it holds at
every sample point and carries no hypothesis. -/
theorem lambdaAnnulusAtom_eq_inv_lambdaSq (M : ABKModel d) (k : ℤ)
    (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d) :
    Support.lambdaAnnulusAtom M k (Support.triadicLatticePoint (k - 2) v) omega =
      (Ch02.lambdaSq (latticeCube (k - 2) v) M.gamma
        Support.coarseEllipticityExponentTwo.1
        (Cutoff.coefficientCutoffTriadicCoeffFamily M (k - 2) omega))⁻¹ := by
  have hshift := triadicCubeShift_latticeCube (d := d) (k - 2) v
  have hswap :=
    Algsuperdiff.Section3.Provider.BadEvents.cubeLowerEllipticityInvLiteral_translateCutoffSample
      M (latticeCube (k - 2) v) (k - 2) M.gamma
      Support.coarseEllipticityExponentTwo omega
  rw [hshift, latticeCube_scale] at hswap
  rw [Support.lambdaAnnulusAtom, ← hswap,
    Algsuperdiff.Section3.Provider.Multiscale.cubeLowerEllipticityInvLiteral_eq_lambdaSq_inv]

/-! ## 3. The unconditional `λ`-sensitivity, transported to a cube -/

private theorem gradientW1Infinity_nonneg
    (h : Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity d) :
    0 ≤ h.gradientW1Infinity :=
  le_max_of_le_left ENNReal.toReal_nonneg

/-- **`e.lambda.sensitivity.no.conditions` at an arbitrary triadic cube** (the
first inequality).

For two cutoff levels `j ≤ n` and every triadic cube `Q = z + □_l`,

```
λ_{t,q}^{-1}(Q; a_n)
  ≤ 6 ( 1 + C · 3^{2l}‖∇(k_n − k_j)‖_{W̲^{1,∞}(Q)} · λ_{s,2}^{-1}(Q; a_j) )^{2t/(1−2s)}
      λ_{t,q}^{-1}(Q; a_j) ,
```

with the literal factor `6` and the exponent `2t/(1−2s)` of the anchor.  The
manuscript's instance is `s = t = γ` and `q = 2`, admissible as soon as `γ ≤
1/4` — in particular under the enclosing lemma's `γ ≤ 1/8`.

Pointwise in the sample; no good event, no induction state, no scale gate. -/
theorem exists_inv_lambdaSq_sensitivity (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (Q : TriadicCube d) (j n : ℤ), j ≤ n →
        ∀ s t : ℝ, 0 < s → s ≤ 1 / 4 → 0 < t → t ≤ 1 / 4 →
          ∀ q : Ch02.MultiscaleExponent, q.IsAdmissible →
            ∀ omega : Cutoff.CutoffSample d,
              (Ch02.lambdaSq Q t q
                  (Cutoff.coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ ≤
                6 *
                    Real.rpow
                      (1 +
                        C *
                            Algsuperdiff.Section3.Provider.BadEvents.incrementOscGauge₂
                              Q j n omega *
                          (Ch02.lambdaSq Q s (.finite 2)
                            (Cutoff.coefficientCutoffTriadicCoeffFamily M j
                              omega))⁻¹)
                      (2 * t / (1 - 2 * s)) *
                  (Ch02.lambdaSq Q t q
                    (Cutoff.coefficientCutoffTriadicCoeffFamily M j omega))⁻¹ := by
  obtain ⟨C, hC, hsens⟩ :=
    Algsuperdiff.Frozen.Section24.lambda_sensitivity_unconditional (d := d) hd
  refine ⟨C, hC, ?_⟩
  intro M Q j n hjn s t hs hs4 ht ht4 q hq omega
  haveI : NeZero d := ⟨by omega⟩
  -- the anchor at the rescaled objects
  have hbase :=
    hsens
      (Algsuperdiff.Section3.Provider.BadEvents.unitRescaledCutoffCoeff M Q j omega)
      (Algsuperdiff.Section3.Provider.BadEvents.incrementUnitCube₂ Q j n omega)
      s t q hs hs4 ht ht4 hq
  rw [Algsuperdiff.Section3.Provider.BadEvents.unitCubeLambda_perturbCoeffOn_unitRescaledCutoffCoeff
      M Q hjn omega t q] at hbase
  simp only
    [Algsuperdiff.Section3.Provider.BadEvents.unitCubeLambda_unitRescaledCutoffCoeff]
    at hbase
  refine hbase.trans ?_
  -- upgrade the unit-cube gauge to the manuscript's `3^{2l} ‖∇(k_n − k_j)‖`
  set g : ℝ :=
    (Algsuperdiff.Section3.Provider.BadEvents.incrementUnitCube₂ Q j n
      omega).gradientW1Infinity with hg
  set G : ℝ :=
    Algsuperdiff.Section3.Provider.BadEvents.incrementOscGauge₂ Q j n omega with hG
  set L : ℝ :=
    (Ch02.lambdaSq Q s (.finite 2)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M j omega))⁻¹ with hL
  set T : ℝ :=
    (Ch02.lambdaSq Q t q
      (Cutoff.coefficientCutoffTriadicCoeffFamily M j omega))⁻¹ with hT
  have hgnn : 0 ≤ g := gradientW1Infinity_nonneg _
  have hgG : g ≤ G :=
    Algsuperdiff.Section3.Provider.BadEvents.gradientW1Infinity_incrementUnitCube₂_le
      Q j n omega
  have hLnn : 0 ≤ L :=
    inv_nonneg.mpr (Ch02.lambdaSq_nonneg Q _ hs (by norm_num))
  have hTnn : 0 ≤ T := inv_nonneg.mpr (Ch02.lambdaSq_nonneg Q _ ht hq)
  have hexp : (0 : ℝ) ≤ 2 * t / (1 - 2 * s) := by
    have hden : (0 : ℝ) < 1 - 2 * s := by linarith only [hs4]
    have hnum : (0 : ℝ) ≤ 2 * t := by linarith only [ht]
    exact div_nonneg hnum hden.le
  have hb0 : (0 : ℝ) ≤ 1 + C * g * L := by
    have : (0 : ℝ) ≤ C * g * L := mul_nonneg (mul_nonneg hC.le hgnn) hLnn
    linarith only [this]
  have hbLe : 1 + C * g * L ≤ 1 + C * G * L := by
    have : C * g * L ≤ C * G * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgG hC.le) hLnn
    linarith only [this]
  have hstep :
      Real.rpow (1 + C * g * L) (2 * t / (1 - 2 * s)) ≤
        Real.rpow (1 + C * G * L) (2 * t / (1 - 2 * s)) :=
    Real.rpow_le_rpow hb0 hbLe hexp
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 6)) hTnn

end

end Algsuperdiff.Section4.Provider.Localize
