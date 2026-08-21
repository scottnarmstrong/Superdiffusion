import Algsuperdiff.Section3.Provider.Stream.LayerDiagonalAllGap
import Algsuperdiff.Section3.Provider.Stream.LayerPairAllGap

/-!
# Deterministic algebra for the finite-shell Frobenius mass

This internal module expands the literal cube Frobenius mass of a finite shell
increment into its diagonal one-shell masses and its ordered off-diagonal
pairings.  It also records measurability of the two literal observables through
the measurable representatives already used by the concentration arguments.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Ordered distinct shell pairs in `(n,m]`, with the coarser shell first. -/
def layerOrderedPairs (n m : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Ioc n m).product (Finset.Ioc n m)).filter (fun p => p.2 < p.1)

@[simp]
theorem mem_layerOrderedPairs {n m k k' : ℤ} :
    (k, k') ∈ layerOrderedPairs n m ↔
      k ∈ Finset.Ioc n m ∧ k' ∈ Finset.Ioc n m ∧ k' < k := by
  simp [layerOrderedPairs, and_assoc, and_left_comm, and_comm]

/-- Scalar square expansion over an integer interval. -/
theorem sq_sum_Ioc_eq_diag_add_two_cross (n : ℤ) (a : ℤ → ℝ) :
    ∀ m : ℤ,
      (∑ k ∈ Finset.Ioc n m, a k) ^ 2 =
        (∑ k ∈ Finset.Ioc n m, (a k) ^ 2) +
          2 * ∑ k ∈ Finset.Ioc n m,
            (∑ k' ∈ Finset.Ioc n (k - 1), a k') * a k := by
  intro m
  rcases le_or_gt m n with hle | hlt
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp
  · have hbase : n + 1 ≤ m := hlt
    clear hlt
    induction m, hbase using Int.le_induction with
    | base =>
        have h1 : Finset.Ioc n (n + 1) = {n + 1} := by
          ext q
          rw [Finset.mem_Ioc, Finset.mem_singleton]
          omega
        rw [h1]
        simp only [Finset.sum_singleton, add_sub_cancel_right]
        have h2 : Finset.Ioc n n = (∅ : Finset ℤ) :=
          Finset.Ioc_eq_empty (by omega)
        rw [h2, Finset.sum_empty]
        ring
    | succ q hq ih =>
        have hsplit : Finset.Ioc n (q + 1) = insert (q + 1) (Finset.Ioc n q) := by
          ext r
          simp only [Finset.mem_Ioc, Finset.mem_insert]
          constructor
          · intro hr
            by_cases hrq : r = q + 1
            · exact Or.inl hrq
            · exact Or.inr ⟨hr.1, by omega⟩
          · rintro (rfl | hr)
            · omega
            · exact ⟨hr.1, hr.2.trans (by omega)⟩
        have hnotmem : q + 1 ∉ Finset.Ioc n q := by
          simp only [Finset.mem_Ioc, not_and_or]
          exact Or.inr (by omega)
        rw [hsplit]
        simp only [Finset.sum_insert hnotmem]
        have hpartial : Finset.Ioc n ((q + 1) - 1) = Finset.Ioc n q := by
          congr 2
          omega
        rw [hpartial]
        calc
          (a (q + 1) + ∑ k ∈ Finset.Ioc n q, a k) ^ 2 =
              a (q + 1) ^ 2 + (∑ k ∈ Finset.Ioc n q, a k) ^ 2 +
                2 * (∑ k ∈ Finset.Ioc n q, a k) * a (q + 1) := by ring
          _ = _ := by rw [ih]; ring

/-- The nested ordered-pair sum is the sum over `layerOrderedPairs`. -/
theorem sum_layerOrderedPairs_eq_nested (n m : ℤ) (f : ℤ → ℤ → ℝ) :
    ∑ p ∈ layerOrderedPairs n m, f p.1 p.2 =
      ∑ k ∈ Finset.Ioc n m, ∑ k' ∈ Finset.Ioc n (k - 1), f k k' := by
  classical
  rw [layerOrderedPairs, Finset.sum_filter]
  change (∑ p ∈ (Finset.Ioc n m) ×ˢ (Finset.Ioc n m),
      if p.2 < p.1 then f p.1 p.2 else 0) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  have hset : Finset.Ioc n (k - 1) =
      (Finset.Ioc n m).filter (fun k' => k' < k) := by
    ext k'
    simp only [Finset.mem_Ioc, Finset.mem_filter]
    rw [Finset.mem_Ioc] at hk
    constructor <;> omega
  rw [hset, Finset.sum_filter]

/-- The literal finite-shell Frobenius mass is measurable. -/
theorem measurable_cubeFrobeniusMassFiniteShellIncrement (l n m : ℤ) :
    Measurable (cubeFrobeniusMassFiniteShellIncrement (d := d) l n m) := by
  have hrep := (measurable_regFieldFrobeniusMassRep
    (d := d) (cubeSet (originCube d l))).comp
      (measurable_finiteShellIncrement (d := d) n m)
  have heq : (fun omega : ShellSeq d =>
      regFieldFrobeniusMassRep (cubeSet (originCube d l))
        (finiteShellIncrement omega n m)) =
      cubeFrobeniusMassFiniteShellIncrement l n m := by
    funext omega
    rw [regFieldFrobeniusMassRep_cubeSet_eq]
    · rfl
    · exact fun i j => continuous_finiteShellIncrement_entry omega n m i j
  rw [← heq]
  exact hrep

/-- A literal pairing of two finite shell increments is measurable. -/
theorem measurable_cubeFrobeniusPairingReg_finiteShellIncrements
    (l n₁ m₁ n₂ m₂ : ℤ) :
    Measurable (fun omega : ShellSeq d =>
      cubeFrobeniusPairingReg (originCube d l)
        (finiteShellIncrement omega n₁ m₁)
        (finiteShellIncrement omega n₂ m₂)) := by
  have hrep := measurable_regFieldFrobeniusPairingRep_comp
    (d := d) (cubeSet (originCube d l))
    (measurable_finiteShellIncrement (d := d) n₁ m₁)
    (measurable_finiteShellIncrement (d := d) n₂ m₂)
  have heq : (fun omega : ShellSeq d =>
      regFieldFrobeniusPairingRep (cubeSet (originCube d l))
        (finiteShellIncrement omega n₁ m₁)
        (finiteShellIncrement omega n₂ m₂)) =
      fun omega => cubeFrobeniusPairingReg (originCube d l)
        (finiteShellIncrement omega n₁ m₁)
        (finiteShellIncrement omega n₂ m₂) := by
    funext omega
    rw [regFieldFrobeniusPairingRep_cubeSet_eq]
    · exact fun i j => continuous_finiteShellIncrement_entry omega n₁ m₁ i j
    · exact fun i j => continuous_finiteShellIncrement_entry omega n₂ m₂ i j
  rw [← heq]
  exact hrep

/-- Exact diagonal-plus-ordered-pair expansion of the literal cube mass. -/
theorem cubeFrobeniusMassFiniteShellIncrement_eq_diagonal_add_pairs
    (l n m : ℤ) (omega : ShellSeq d) :
    cubeFrobeniusMassFiniteShellIncrement l n m omega =
      (∑ k ∈ Finset.Ioc n m,
        cubeFrobeniusMassFiniteShellIncrement l (k - 1) k omega) +
      2 * ∑ p ∈ layerOrderedPairs n m,
        cubeFrobeniusPairingReg (originCube d l)
          (finiteShellIncrement omega (p.1 - 1) p.1)
          (finiteShellIncrement omega (p.2 - 1) p.2) := by
  classical
  let S : Finset ℤ := Finset.Ioc n m
  have hsingle : ∀ (k : ℤ) (x : Vec d) (i j : Fin d),
      finiteShellIncrement omega (k - 1) k x i j = omega k x i j := by
    intro k x i j
    simp only [finiteShellIncrement_apply_entry]
    have hs : Finset.Ioc (k - 1) k = {k} := by
      ext q
      rw [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    rw [hs, Finset.sum_singleton]
  have hentry : ∀ (x : Vec d) (i j : Fin d),
      finiteShellIncrement omega n m x i j = ∑ k ∈ S, omega k x i j := by
    intro x i j
    simp only [finiteShellIncrement_apply_entry, S]
  have hswap : ∀ (g : ℤ → Fin d → Fin d → ℝ),
      (∑ i, ∑ j, ∑ k ∈ S, g k i j) = ∑ k ∈ S, ∑ i, ∑ j, g k i j := by
    intro g
    calc
      (∑ i, ∑ j, ∑ k ∈ S, g k i j) =
          ∑ i, ∑ k ∈ S, ∑ j, g k i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hswapPairs : ∀ (g : (ℤ × ℤ) → Fin d → Fin d → ℝ),
      (∑ i, ∑ j, ∑ p ∈ layerOrderedPairs n m, g p i j) =
        ∑ p ∈ layerOrderedPairs n m, ∑ i, ∑ j, g p i j := by
    intro g
    calc
      (∑ i, ∑ j, ∑ p ∈ layerOrderedPairs n m, g p i j) =
          ∑ i, ∑ p ∈ layerOrderedPairs n m, ∑ j, g p i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hpoint : (fun x : Vec d =>
      matrixFrobeniusNormSq (finiteShellIncrement omega n m x)) =
      fun x =>
        (∑ k ∈ S,
          matrixFrobeniusNormSq (finiteShellIncrement omega (k - 1) k x)) +
        2 * ∑ p ∈ layerOrderedPairs n m,
          ∑ i, ∑ j,
            finiteShellIncrement omega (p.1 - 1) p.1 x i j *
              finiteShellIncrement omega (p.2 - 1) p.2 x i j := by
    funext x
    have hij : ∀ i j,
        (finiteShellIncrement omega n m x i j) ^ 2 =
          (∑ k ∈ S,
            (finiteShellIncrement omega (k - 1) k x i j) ^ 2) +
          2 * ∑ p ∈ layerOrderedPairs n m,
            finiteShellIncrement omega (p.1 - 1) p.1 x i j *
              finiteShellIncrement omega (p.2 - 1) p.2 x i j := by
      intro i j
      rw [hentry x i j, sq_sum_Ioc_eq_diag_add_two_cross n
        (fun k => omega k x i j) m]
      simp_rw [hsingle]
      simp_rw [Finset.sum_mul]
      rw [← sum_layerOrderedPairs_eq_nested]
      simp only [S, mul_comm]
    unfold matrixFrobeniusNormSq
    calc
      (∑ i, ∑ j, (finiteShellIncrement omega n m x i j) ^ 2) =
          ∑ i, ∑ j,
            ((∑ k ∈ S,
                (finiteShellIncrement omega (k - 1) k x i j) ^ 2) +
              2 * ∑ p ∈ layerOrderedPairs n m,
                finiteShellIncrement omega (p.1 - 1) p.1 x i j *
                  finiteShellIncrement omega (p.2 - 1) p.2 x i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hij i j
      _ = (∑ k ∈ S,
            ∑ i, ∑ j,
              (finiteShellIncrement omega (k - 1) k x i j) ^ 2) +
          2 * ∑ p ∈ layerOrderedPairs n m,
            ∑ i, ∑ j,
              finiteShellIncrement omega (p.1 - 1) p.1 x i j *
                finiteShellIncrement omega (p.2 - 1) p.2 x i j := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        · exact hswap fun k i j =>
            (finiteShellIncrement omega (k - 1) k x i j) ^ 2
        · calc
            (∑ i, ∑ j, 2 * ∑ p ∈ layerOrderedPairs n m,
                finiteShellIncrement omega (p.1 - 1) p.1 x i j *
                  finiteShellIncrement omega (p.2 - 1) p.2 x i j) =
                2 * ∑ i, ∑ j, ∑ p ∈ layerOrderedPairs n m,
                  finiteShellIncrement omega (p.1 - 1) p.1 x i j *
                    finiteShellIncrement omega (p.2 - 1) p.2 x i j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
            _ = _ := by
              rw [hswapPairs fun p i j =>
                finiteShellIncrement omega (p.1 - 1) p.1 x i j *
                  finiteShellIncrement omega (p.2 - 1) p.2 x i j]
      _ = _ := rfl
  have hdiagInt : ∀ k ∈ S, IntegrableOn
      (fun x : Vec d => matrixFrobeniusNormSq
        (finiteShellIncrement omega (k - 1) k x))
      (cubeSet (originCube d l)) volume := by
    intro k _
    exact (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_finiteShellIncrement_entry omega (k - 1) k i j).pow 2
      ).continuousOn.integrableOn_compact
        (isCompact_closedBall (cubeCenter (originCube d l))
          (cubeRadius (originCube d l))) |>.mono_set
            (cubeSet_subset_closedBall (originCube d l))
  have hpairInt : ∀ p ∈ layerOrderedPairs n m, IntegrableOn
      (fun x : Vec d => ∑ i, ∑ j,
        finiteShellIncrement omega (p.1 - 1) p.1 x i j *
          finiteShellIncrement omega (p.2 - 1) p.2 x i j)
      (cubeSet (originCube d l)) volume := by
    intro p _
    exact (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_finiteShellIncrement_entry omega (p.1 - 1) p.1 i j).mul
        (continuous_finiteShellIncrement_entry omega (p.2 - 1) p.2 i j)
      ).continuousOn.integrableOn_compact
        (isCompact_closedBall (cubeCenter (originCube d l))
          (cubeRadius (originCube d l))) |>.mono_set
            (cubeSet_subset_closedBall (originCube d l))
  unfold cubeFrobeniusMassFiniteShellIncrement cubeFrobeniusPairingReg cubeAverage
  rw [hpoint, integral_add
    (integrable_finset_sum _ hdiagInt)
    ((integrable_finset_sum _ hpairInt).const_mul 2),
    integral_finset_sum _ hdiagInt, integral_const_mul,
    integral_finset_sum _ hpairInt]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  dsimp only [S]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

end

end Algsuperdiff.Section3.Provider.Stream
