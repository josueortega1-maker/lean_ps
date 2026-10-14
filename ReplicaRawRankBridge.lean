import ReplicaBandLower
import ReplicaLowerRank
import ReplicaRankAllocation

/-! The raw draw cost is an integral of prefix counts along the actual PS clock. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaRawRankBridge
open ReplicaPS ReplicaChoiceMachine ReplicaRawStep ReplicaRawProcess

variable {m q : ℕ} [Nonempty (Fin (m * q))]

lemma roundDuration_tail (p : ReplicaPS.Profile m q) (j : ℕ) :
    1 - roundTime p j = ∑ r ∈ Finset.range (m * q),
      roundDuration p r * (if j ≤ r then (1 : ℝ) else 0) := by
  have hsum (k : ℕ) : (∑ r ∈ Finset.range k, roundDuration p r) = roundTime p k :=
    PSChoiceMachine.sum_roundDuration (liftedProfile p) k
  by_cases hj : j ≤ m * q
  · have hfilter : (Finset.range (m * q)).filter (fun r => j ≤ r) = Finset.Ico j (m * q) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    rw [hfilter, Finset.sum_Ico_eq_sub _ hj, hsum, hsum, roundTime_terminal]
  · have ht : roundTime p j = 1 :=
      le_antisymm (roundTime_le_one _ _) (by
        have h := roundTime_mono p (le_of_not_ge hj)
        rwa [roundTime_terminal] at h)
    rw [ht, sub_self]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    have hjr : ¬ j ≤ r := by have := Finset.mem_range.mp hr; omega
    simp [hjr]

def rawRoundCount (s : State m q) (r : ℕ) :
    (n : ℕ) → (Fin n → Fin m) → ℕ
  | 0, _ => 0
  | n + 1, w => rawRoundCount s r n (Fin.tail w) +
      if (s.evolve n (Fin.tail w)).normalize.depth / (m * q) ≤ r then 1 else 0

lemma rawRoundCount_le_length (s : State m q) (r n : ℕ) (w : Fin n → Fin m) :
    rawRoundCount s r n w ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [rawRoundCount]
      have h := ih (Fin.tail w)
      split_ifs <;> omega

theorem weightedRawSum_eq_round_counts (s : State m q) (n : ℕ)
    (w : Fin n → Fin m) (p : ReplicaPS.Profile m q)
    (hp : p ∈ fiber (s.evolve n w).reference (s.evolve n w).depth) :
    weightedRawSum s remainingWeight n w =
      ∑ r ∈ Finset.range (m * q), roundDuration p r * (rawRoundCount s r n w : ℝ) := by
  induction n with
  | zero => simp [weightedRawSum, rawRoundCount]
  | succ n ih =>
      have hp' : p ∈ fiber (s.evolve n (Fin.tail w)).reference
          (s.evolve n (Fin.tail w)).depth :=
        (s.evolve n (Fin.tail w)).step_fiber_subset (w 0) hp
      have hpn : p ∈ fiber (s.evolve n (Fin.tail w)).normalize.reference
          (s.evolve n (Fin.tail w)).normalize.depth := by
        rwa [State.normalize_fiber]
      have ht := (s.evolve n (Fin.tail w)).normalize.clock_on_fiber p hpn
      have hweight : remainingWeight (s.evolve n (Fin.tail w)) =
          ∑ r ∈ Finset.range (m * q), roundDuration p r *
            (if (s.evolve n (Fin.tail w)).normalize.depth / (m * q) ≤ r then (1 : ℝ) else 0) := by
        unfold remainingWeight
        rw [ht]
        exact roundDuration_tail p _
      rw [weightedRawSum, ih (Fin.tail w) hp', hweight]
      simp only [rawRoundCount, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        mul_add, Finset.sum_add_distrib]

theorem rawBandCost_eq_round_counts (s : State m q) (n : ℕ)
    (w : Fin n → Fin m) (p : ReplicaPS.Profile m q)
    (hp : p ∈ fiber (s.evolve n w).reference (s.evolve n w).depth) :
    rawBandCost s n w = ∑ r ∈ Finset.range (m * q),
      roundDuration p r * ((rawRoundCount s r n w : ℝ) / m) := by
  rw [rawBandCost, weightedRawSum_eq_round_counts s n w p hp, Finset.sum_div]
  simp only [mul_div_assoc]

lemma normalize_depth_le_step (s : State m q) (g : Fin m) :
    s.normalize.depth ≤ (s.step g).depth := by
  unfold State.step
  dsimp only
  split_ifs with ht hs hg
  · rfl
  · exact (Nat.le_succ _).trans (s.normalize.child hs g hg).le_normalize_depth
  · rfl
  · rfl

theorem rawRoundCount_eq_length_of_depth (s : State m q) (r n : ℕ)
    (w : Fin n → Fin m) (hdepth : (s.evolve n w).depth / (m * q) ≤ r) :
    rawRoundCount s r n w = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnorm : (s.evolve n (Fin.tail w)).normalize.depth / (m * q) ≤ r :=
        (Nat.div_le_div_right (normalize_depth_le_step (s.evolve n (Fin.tail w)) (w 0))).trans hdepth
      have hprev : (s.evolve n (Fin.tail w)).depth / (m * q) ≤ r :=
        (Nat.div_le_div_right (s.evolve n (Fin.tail w)).le_normalize_depth).trans hnorm
      rw [rawRoundCount, if_pos hnorm, ih (Fin.tail w) hprev]

end ProbabilisticSerial.ReplicaRawRankBridge
