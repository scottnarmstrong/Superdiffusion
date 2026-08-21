/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Schauder.CubeSchauderResidue
import Algsuperdiff.Section4.Provider.Schauder.CubeSchauderBoundaryZeroTrace
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepPartialReflection
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderComposeBoundary

/-!
# Cube Schauder: the harmonic competitor on the **reflected** window

`CubeSchauderResidue.exists_harmonicCompetitor_residue` produces the harmonic
competitor of the forced equation on the *truncated* window `(x+□_n) ∩ □_m`.
The boundary branch's Lipschitz atom
(`CubeSchauderBoundaryTwin.exists_gradientLipschitz_boundary`) instead asks for a
competitor that is classically harmonic on the **partially reflected** window
`reflectedWindow x m (n-2)` — the odd double of the truncated window across
every met face of `∂□_m`.  This module produces it, for the **zero-datum** cube
problem, and prices its residue.

The chain, on the window `W = (x + □_{n-2}) ∩ □_m`:

1. *freezing at the window's own scale*
   (`CubeSchauderResidue.exists_frozenHarmonicReplacement_truncatedWindow`, at
   the base point `x` and the constant `c = G(x)`): a corrector `w ∈ H¹₀(W)`
   with `u - w` weakly harmonic on `W` and
   `Σᵢ ‖∂ᵢw‖_{L²(W)} ≤ d KG √(3^{n-2}|W|)`;
2. *the zero-trace slot* (`CubeSchauderBoundaryZeroTrace`): `u ∈ H¹₀(□_m)` and
   `w ∈ H¹₀(W)` give the face-only localized zero trace of `u - w` on `W`
   against `reflectedWindow x m (n-2)` — no extra hypothesis;
3. *the odd reflection*
   (`ExcessDecay.exists_h1_oddReflection_reflectedWindow`, any met
   configuration — interior, face, edge or corner): a weakly harmonic
   `H¹(reflectedWindow x m (n-2))` extension pinned to `u - w` on `W`;
4. *Weyl on the doubled window*
   (`ExcessDecay.Schauder.exists_classicalCompetitor_reflectedWindow`): a
   classically harmonic representative `V`, so that `u - V = w` almost
   everywhere on `W`;
5. *the Dirichlet Poincaré* (`CubeSchauderPoincare`, at the inscribing cube
   `x + □_{n-2}`), exactly as in the interior chain.

Because the freezing runs at the *replacement* scale `n-2` rather than at `n`,
the interior chain's window transfer `U_0 → U_2` is not needed and the residue
constant loses the `√((3⁴)^d)` volume-ratio factor: the boundary residue is
**smaller** than the interior one, at
`boundaryResidueConst d = C_Poincaré(d) · d` (the honest value carries a further
factor `1/27`, discarded here).

## What this module does *not* do

It supplies the **competitor** of the boundary one step, not the one step.  The
step that remains open is the fold of the competitor's excess on the doubled
window, `E(V, reflectedWindow x m (n-2))`, back into `E(u, (x+□_n) ∩ □_m)`: on
the interior branch that is one triangle inequality
(`affineExcess_sub_le_truncatedWindow`), but on the doubled window `u` is not
defined on the far side, and the affine competitor must be replaced by its odd
part before the far-side leg can be folded back.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`), the
  harmonic-approximation display `e.harmapprox.Sch.onealpha`.
* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory InnerProductSpace
open Homogenization
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The constant -/

/-- The residue constant of the boundary branch: `C_Poincaré(d) · d`.  No
volume-ratio factor, because the freezing runs at the replacement scale. -/
def boundaryResidueConst (d : ℕ) : ℝ := schauderDirichletPoincareConst d * (d : ℝ)

theorem boundaryResidueConst_nonneg (d : ℕ) : 0 ≤ boundaryResidueConst d :=
  mul_nonneg (schauderDirichletPoincareConst_nonneg d) (Nat.cast_nonneg d)

/-! ## 2. The competitor and its residue -/

/-- **The harmonic competitor on the doubled window, with its residue priced.**

For the zero-datum solution `u ∈ H¹₀(□_m)` of `-Δu = ∇·G` with
`[G]_{C^{0,1/2}(□_m)} ≤ KG`, and for every base point `x ∈ □_m` and scale `n`
with `n - 2 < m`, there is a function `V` which is

* classically harmonic on the **partially reflected** window
  `reflectedWindow x m (n-2)` (any met configuration: interior, face, edge or
  corner), and
* globally square integrable,

with the one-step remainder slot bounded by the freezing gain:

```text
  3^{-n} · ‖u - V‖_{L̲²((x+□_{n-2}) ∩ □_m)} ≤ boundaryResidueConst d · KG · √(3ⁿ) .
```

This is the boundary twin of
`CubeSchauderResidue.exists_harmonicCompetitor_residue`; the only new inputs
are the zero-trace slot (free for the zero datum) and the proved odd-reflection
packaging. -/
theorem exists_harmonicCompetitor_residue_reflected [NeZero d] {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 2 < m)
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
          ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) ∧
        MemLp V 2 (volume : Measure (Vec d)) ∧
        (3 : ℝ) ^ (-n) *
            normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u.toFun y - V y)
          ≤ boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ n) := by
  have hWopen : IsOpen (truncatedWindow x m (n - 2)) := isOpen_truncatedWindow x m (n - 2)
  have hWsub : truncatedWindow x m (n - 2) ⊆ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain x m (n - 2)
  have hWmeas : MeasurableSet (truncatedWindow x m (n - 2)) :=
    measurableSet_truncatedWindow x m (n - 2)
  have hWpos : 0 < (volume (truncatedWindow x m (n - 2))).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  -- (1) the freezing step at the replacement scale
  obtain ⟨w, hharm, hgrad⟩ :=
    exists_frozenHarmonicReplacement_truncatedWindow (n := n - 2) hx u.toH1Function hKG
      hGL2 hG hu
  -- (2) the zero-trace slot
  have hzt : LocalizedZeroTraceFunctionOn (truncatedWindow x m (n - 2))
      (reflectedWindow x m (n - 2))
      (u.toH1Function.restrict hWopen hWsub - w.toH1Function).toFun :=
    localizedZeroTraceFunctionOn_h1Function_sub x ⟨u, rfl⟩ w (fun _ => rfl)
  -- (3) the odd reflection and (4) Weyl on the doubled window
  obtain ⟨W₁, hW₁harm, hW₁pin, -⟩ :=
    exists_h1_oddReflection_reflectedWindow (by omega : n - 2 < m) _ hharm hzt
  obtain ⟨V, hVharm, hVmem, hVae⟩ :=
    exists_classicalCompetitor_reflectedWindow x m (n - 2) hW₁harm
  refine ⟨V, hVharm, hVmem, ?_⟩
  -- `u - V = w` almost everywhere on the window
  have hVaeW : V =ᵐ[volume.restrict (truncatedWindow x m (n - 2))] W₁.toFun :=
    ae_restrict_of_ae_restrict_of_subset
      (truncatedWindow_subset_reflectedWindow x m (n - 2)) hVae
  have hae : ∀ᵐ y ∂(volume.restrict (truncatedWindow x m (n - 2))),
      u.toFun y - V y = w.toH1Function.toFun y := by
    filter_upwards [hVaeW, MeasureTheory.self_mem_ae_restrict hWmeas] with y hy hyW
    have hsub : (u.toH1Function.restrict hWopen hWsub - w.toH1Function).toFun y
        = u.toFun y - w.toH1Function.toFun y := by
      simp only [H1Function.sub_toFun]
      rfl
    rw [hy, hW₁pin y hyW, hsub]
    ring
  have hcongr : normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u.toFun y - V y)
      = normalizedL2On (truncatedWindow x m (n - 2)) w.toH1Function.toFun :=
    normalizedL2On_congr_ae hae
  -- (5) the Dirichlet Poincaré at the inscribing cube
  have hwW : MemLp w.toH1Function.toFun 2
      (volume.restrict (truncatedWindow x m (n - 2))) := by
    have h := w.toH1Function.memL2
    simpa only [volumeMeasureOn] using h
  have hinscribe : ∀ y ∈ truncatedWindow x m (n - 2), ∀ j : Fin d,
      x j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 2) < y j ∧
        y j < x j + (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 2) := by
    intro y hy j
    have h := mem_image_add_openCubeSet_iff.1
      (truncatedWindow_subset_translate x m (n - 2) hy) j
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  have hpoin := eLpNorm_le_schauderDirichletPoincare hWmeas x (n - 2) hinscribe w
  have hpoin' : (eLpNorm w.toH1Function.toFun 2
        (volume.restrict (truncatedWindow x m (n - 2)))).toReal
      ≤ schauderDirichletPoincareConst d * (3 : ℝ) ^ (n - 2) *
        ((d : ℝ) * KG *
          Real.sqrt ((3 : ℝ) ^ (n - 2) *
            (volume (truncatedWindow x m (n - 2))).toReal)) := by
    refine hpoin.trans (mul_le_mul_of_nonneg_left hgrad ?_)
    exact mul_nonneg (schauderDirichletPoincareConst_nonneg d)
      (zpow_pos (by norm_num) (n - 2)).le
  have hsqrtV : Real.sqrt ((3 : ℝ) ^ (n - 2)
        * (volume (truncatedWindow x m (n - 2))).toReal)
      = Real.sqrt ((3 : ℝ) ^ (n - 2))
        * Real.sqrt ((volume (truncatedWindow x m (n - 2))).toReal) :=
    Real.sqrt_mul (zpow_pos (by norm_num) (n - 2)).le _
  have hnormW : normalizedL2On (truncatedWindow x m (n - 2)) w.toH1Function.toFun
      ≤ schauderDirichletPoincareConst d * (d : ℝ) * KG *
        ((3 : ℝ) ^ (n - 2) * Real.sqrt ((3 : ℝ) ^ (n - 2))) := by
    rw [normalizedL2On_eq_toReal_eLpNorm_div hwW, div_le_iff₀ (Real.sqrt_pos.2 hWpos)]
    refine hpoin'.trans (le_of_eq ?_)
    rw [hsqrtV]
    ring
  -- the scale bookkeeping
  rw [hcongr]
  have h3n : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_left hnormW h3n.le
  refine hmul.trans ?_
  have hc : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n - 2) = 1 / 9 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), show -n + (n - 2) = (-2 : ℤ) by ring]
    norm_num
  have hAnn : (0 : ℝ) ≤ schauderDirichletPoincareConst d * (d : ℝ) * KG :=
    mul_nonneg (mul_nonneg (schauderDirichletPoincareConst_nonneg d) (Nat.cast_nonneg d)) hKG
  have hsq : Real.sqrt ((3 : ℝ) ^ (n - 2)) ≤ Real.sqrt ((3 : ℝ) ^ n) :=
    Real.sqrt_le_sqrt (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have hstep : schauderDirichletPoincareConst d * (d : ℝ) * KG
        * Real.sqrt ((3 : ℝ) ^ (n - 2)) * (1 / 9)
      ≤ boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ n) := by
    have h1 : schauderDirichletPoincareConst d * (d : ℝ) * KG
          * Real.sqrt ((3 : ℝ) ^ (n - 2))
        ≤ schauderDirichletPoincareConst d * (d : ℝ) * KG * Real.sqrt ((3 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hsq hAnn
    have h2 : (0 : ℝ) ≤ schauderDirichletPoincareConst d * (d : ℝ) * KG
        * Real.sqrt ((3 : ℝ) ^ (n - 2)) := mul_nonneg hAnn (Real.sqrt_nonneg _)
    have hid : boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ n)
        = schauderDirichletPoincareConst d * (d : ℝ) * KG * Real.sqrt ((3 : ℝ) ^ n) := by
      rw [boundaryResidueConst]
    rw [hid]
    linarith only [h1, h2]
  refine le_trans (le_of_eq ?_) hstep
  calc (3 : ℝ) ^ (-n) * (schauderDirichletPoincareConst d * (d : ℝ) * KG
        * ((3 : ℝ) ^ (n - 2) * Real.sqrt ((3 : ℝ) ^ (n - 2))))
      = (schauderDirichletPoincareConst d * (d : ℝ) * KG
          * Real.sqrt ((3 : ℝ) ^ (n - 2)))
        * ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n - 2)) := by ring
    _ = schauderDirichletPoincareConst d * (d : ℝ) * KG
          * Real.sqrt ((3 : ℝ) ^ (n - 2)) * (1 / 9) := by rw [hc]

end

end Algsuperdiff.Section4.Provider.Schauder
