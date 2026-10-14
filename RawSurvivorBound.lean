import ReplicaSurvivorEntries
import UniformRawPrefixes

/-! Quantitative survivor and residual-supply bounds for raw prefixes. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.RawSurvivorBound
open UniformProduct CouponLowerBound ReplicaPS ReplicaChoiceMachine ReplicaRawProcess

variable {m q : ℕ} [Nonempty (Fin (m * q))]

theorem total_residual_le_active_quota (s : State m q) :
    (∑ g : Fin m, residual s.reference s.clock g) ≤ q * (s.active.card : ℝ) := by
  by_cases hd : s.depth / (m * q) ≤ m * q
  · have hzero (g : Fin m) (hg : g ∉ s.active) : residual s.reference s.clock g = 0 := by
      apply le_antisymm _ (residual_nonneg _ _ _)
      by_contra hn
      have hpos : 0 < residual s.reference s.clock g := lt_of_not_ge hn
      have h := residual_pos_implies_active s.reference s.clock g hpos
        (s.depth / (m * q)) hd s.clock_eq_roundTime.ge
      rw [← s.active_on_fiber s.reference s.reference_mem_fiber] at h
      exact hg h
    have heq : (∑ g : Fin m, residual s.reference s.clock g) =
        ∑ g ∈ s.active, residual s.reference s.clock g := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun g _ hg => hzero g hg)
    rw [heq]
    calc
      _ ≤ ∑ _g ∈ s.active, (q : ℝ) := Finset.sum_le_sum (fun g _ => residual_le_quota _ _ _)
      _ = _ := by simp [mul_comm]
  · have ht : s.clock = 1 := by
      have h := roundTime_mono s.reference (le_of_not_ge hd)
      rw [roundTime_terminal, ← s.clock_eq_roundTime] at h
      exact le_antisymm s.clock_le_one h
    rw [sum_residual _ _ s.clock_nonneg s.clock_le_one, ht]
    simp only [sub_self, mul_zero]
    positivity

def survivorFamily (m s : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun S => s ≤ S.card)

theorem survivor_card_tail (hm : 0 < m) (reference : ReplicaPS.Profile m q)
    (k s : ℕ) {α : ℝ} (hα : 1 < α)
    (hmean : α * (m * q : ℕ) ≤ k * ((s : ℝ) / m)) :
    probability (labelSample m k)
      (fun w => s ≤ ((initialState reference).evolve k w).active.card) ≤
      ((survivorFamily m s).card : ℝ) *
        Real.exp (-(α - 1 - Real.log α) * (m * q : ℕ)) := by
  calc
    _ ≤ probability (labelSample m k)
        (fun w => ∃ S ∈ survivorFamily m s, RawSubsetCounts.count S w ≤ (m * q : ℕ)) := by
      apply probability_mono
      intro w hw hsize
      refine ⟨((initialState reference).evolve k w).active, ?_, ?_⟩
      · simpa [survivorFamily] using hsize
      · exact ReplicaSurvivorEntries.raw_count_survivor_le_agents reference k w _ (by rfl)
    _ ≤ ∑ S ∈ survivorFamily m s, probability (labelSample m k)
        (fun w => RawSubsetCounts.count S w ≤ (m * q : ℕ)) := union_bound _ _ _
    _ ≤ ∑ _S ∈ survivorFamily m s,
        Real.exp (-(α - 1 - Real.log α) * (m * q : ℕ)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply RawSubsetCounts.count_lower_tail_of_mean_ge hm S k hα
      apply hmean.trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (Finset.mem_filter.mp hS).2
    _ = _ := by simp

theorem expected_residual_le (hm : 0 < m) (reference : ReplicaPS.Profile m q)
    (k s : ℕ) {α : ℝ} (hα : 1 < α)
    (hmean : α * (m * q : ℕ) ≤ k * ((s : ℝ) / m)) :
    (𝔼 w ∈ labelSample m k, ∑ g : Fin m,
      residual ((initialState reference).evolve k w).reference
        ((initialState reference).evolve k w).clock g) ≤
      q * (s : ℝ) + (q * (m : ℝ)) * ((survivorFamily m s).card : ℝ) *
        Real.exp (-(α - 1 - Real.log α) * (m * q : ℕ)) := by
  have hsamp : (labelSample m k).Nonempty :=
    productSample_nonempty ⟨⟨0, hm⟩, Finset.mem_univ _⟩ k
  have h := Finset.expect_le_expect (s := labelSample m k)
    (f := fun w => ∑ g : Fin m,
      residual ((initialState reference).evolve k w).reference
        ((initialState reference).evolve k w).clock g)
    (g := fun w => (q : ℝ) * s + (q * (m : ℝ)) *
      if s ≤ ((initialState reference).evolve k w).active.card then 1 else 0) (by
        intro w hw
        let t := (initialState reference).evolve k w
        have ht := total_residual_le_active_quota t
        have hc : (t.active.card : ℝ) ≤ m := by
          exact_mod_cast (show t.active.card ≤ m by simpa using t.active.card_le_univ)
        change (∑ g : Fin m, residual t.reference t.clock g) ≤
          (q : ℝ) * s + (q * (m : ℝ)) * if s ≤ t.active.card then 1 else 0
        by_cases hsize : s ≤ t.active.card
        · simp only [hsize, if_true, mul_one]
          have hm := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg q)
          have hs : 0 ≤ (q : ℝ) * s := by positivity
          linarith
        · simp only [hsize, if_false, mul_zero, add_zero]
          apply ht.trans
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
          exact_mod_cast (le_of_not_ge hsize))
  rw [Finset.expect_add_distrib, Finset.expect_const hsamp, ← Finset.mul_expect] at h
  change _ ≤ (q : ℝ) * s + (q * (m : ℝ)) *
    probability (labelSample m k)
      (fun w => s ≤ ((initialState reference).evolve k w).active.card) at h
  apply h.trans
  have he := mul_le_mul_of_nonneg_left (survivor_card_tail hm reference k s hα hmean)
    (show 0 ≤ (q : ℝ) * m by positivity)
  nlinarith

end ProbabilisticSerial.RawSurvivorBound
