import PSRankHistory
import PSWeightedExposure

/-! Exact allocation-rank summation by parts on the concrete PS schedule. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PSChoiceMachine
open UniformPermutation PSProcess SequentialRevelation StoppedChoices
variable {n : ℕ} [Nonempty (Fin n)]

def roundTerm (profile : Profile n) (W : Phase n profile → ℝ) (r : ℕ) : ℝ :=
  if hA : (activeGoods (profileSupply profile r)).Nonempty then
    W (roundPhase profile r hA) else 0

lemma sum_range_shift (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), f k) = f 0 + ∑ k ∈ Finset.range N, f (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

lemma runFrom_round_sum (profile : Profile n) (W : Phase n profile → ℝ) (N r : ℕ)
    (hcard : (activeGoods (profileSupply profile r)).card ≤ N) :
    ((runFrom profile (profileSupply profile r) (profileSupply_valid profile r)).phases.map W).sum =
      ∑ k ∈ Finset.range N, roundTerm profile W (r + k) := by
  classical
  induction N generalizing r with
  | zero =>
      have hA : ¬ (activeGoods (profileSupply profile r)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        exact not_not_intro (Finset.card_eq_zero.mp (by omega))
      rw [runFrom, dif_neg hA]
      simp
  | succ N ih =>
      by_cases hA : (activeGoods (profileSupply profile r)).Nonempty
      · have hnext : (activeGoods (profileSupply profile (r + 1))).card ≤ N := by
          rw [profileSupply, dif_pos hA]
          have hlt := activeGoods_step_card_lt profile (profileSupply profile r) hA
          omega
        have htail := ih (r + 1) hnext
        have hq : profileSupply profile (r + 1) =
            stepState profile (profileSupply profile r) hA := by
          rw [profileSupply, dif_pos hA]
        simp only [hq] at htail
        rw [runFrom, dif_pos hA]
        change W (roundPhase profile r hA) +
          ((runFrom profile (stepState profile (profileSupply profile r) hA)
            (stepState_valid profile _ (profileSupply_valid profile r) hA)).phases.map W).sum = _
        rw [htail, sum_range_shift]
        simp only [Nat.add_zero]
        rw [show roundTerm profile W r = W (roundPhase profile r hA) by
          simp only [roundTerm, dif_pos hA]]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [show r + 1 + k = r + (k + 1) by omega]
      · rw [runFrom, dif_neg hA]
        simp only [List.map_nil, List.sum_nil]
        symm
        apply Finset.sum_eq_zero
        intro k hk
        have hnot : ¬ (activeGoods (profileSupply profile (r + k))).Nonempty := by
          intro h
          exact hA ⟨h.choose, profileSupply_active_subset_of_le profile (Nat.le_add_right _ _) h.choose_spec⟩
        simp [roundTerm, hnot]

def roundRank (profile : Profile n) (i : Fin n) (r : ℕ) : ℝ :=
  rankOf (profile i) (roundChoice profile r i)

lemma averageRank_eq_round_sum (profile : Profile n) :
    averageRank (run profile) = (1 / (n : ℝ)) *
      ∑ r ∈ Finset.range n, roundDuration profile r * ∑ i : Fin n, roundRank profile i r := by
  rw [averageRank_eq_dynamicRank]
  unfold dynamicRank
  have h := runFrom_round_sum profile
    (fun p => p.duration * ∑ i : Fin n, (activeRank p.active (profile i) : ℝ)) n 0
    (by simp [profileSupply, activeGoods_initial])
  change (1 / (n : ℝ)) *
    (((runFrom profile (profileSupply profile 0) (profileSupply_valid profile 0)).phases.map _).sum) = _
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Nat.zero_add, roundTerm]
  split
  next hA =>
    unfold roundDuration
    rw [dif_pos hA]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [roundRank, roundChoice_eq profile r i hA]
    exact_mod_cast (rankOf_favorite_eq_activeRank (profile i)
      (activeGoods (profileSupply profile r)) hA).symm
  next hA => simp [roundDuration, hA]

lemma roundRank_initial (profile : Profile n) (i : Fin n) : roundRank profile i 0 = 1 := by
  have hA : (activeGoods (profileSupply profile 0)).Nonempty := by
    simp [profileSupply, activeGoods_initial]
  rw [roundRank, roundChoice_eq profile 0 i hA]
  have hmem : profile i ⟨0, market_pos⟩ ∈ activeGoods (profileSupply profile 0) := by
    simp [profileSupply, activeGoods_initial]
  have hle := ReplicaPS.favorite_rank_le (profile i)
    (activeGoods (profileSupply profile 0)) hA (profile i ⟨0, market_pos⟩) hmem
  have heq : rankOf (profile i) (favorite (profile i)
      (activeGoods (profileSupply profile 0)) hA) = 1 := by
    simp only [rankOf, Equiv.symm_apply_apply, Fin.val_zero, zero_add] at hle ⊢
    omega
  exact_mod_cast heq

def weightedRankJump (profile : Profile n) (i : Fin n) : ℕ → ℝ
  | 0 => max (1 - roundTime profile 0) 0 * roundRank profile i 0
  | r + 1 => max (1 - roundTime profile (r + 1)) 0 *
      (roundRank profile i (r + 1) - roundRank profile i r)

lemma averageRank_eq_weighted_jumps (profile : Profile n) :
    averageRank (run profile) = (1 / (n : ℝ)) *
      ∑ r ∈ Finset.range n, ∑ i : Fin n, weightedRankJump profile i r := by
  rw [averageRank_eq_round_sum]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range n)]
  apply Finset.sum_congr rfl
  intro i hi
  symm
  have h := sum_shifted_entries
    (fun r => max (1 - roundTime profile r) 0) (roundRank profile i)
    (weightedRankJump profile i) n rfl (fun _ => rfl)
    (by change max (1 - roundTime profile n) 0 = 0; simp [roundTime_terminal])
  rw [h]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← partialDuration_eq_ramp, partialDuration_eq_full profile r (roundTime_le_one _ _)]

lemma weightedRankJump_initial (profile : Profile n) (i : Fin n) :
    weightedRankJump profile i 0 = 1 := by
  simp [weightedRankJump, roundTime_zero, roundRank_initial]

lemma arrivalWeight_initial (profile : Profile n) (i : Fin n) :
    arrivalWeight (profileHistory profile (0 * n + i.val)) = 1 / (n : ℝ) := by
  have hactive : queryActive (profileHistory profile i.val) = Finset.univ := by
    simpa [profileSupply, activeGoods_initial] using queryActive_at_slot profile 0 i
  have hA : (queryActive (profileHistory profile i.val)).Nonempty := by simp [hactive]
  simp [arrivalWeight, stochasticRecording, FreshQuery, previousChoice_at_slot_zero,
    hactive, hA]

lemma rank_jump_zero_of_not_stochastic (profile : Profile n) (r : ℕ) (i : Fin n)
    (hA : (activeGoods (profileSupply profile (r + 1))).Nonempty)
    (hs : stochasticRecording (profileHistory profile ((r + 1) * n + i.val)) = false) :
    roundRank profile i (r + 1) - roundRank profile i r = 0 := by
  classical
  let hprev : (activeGoods (profileSupply profile r)).Nonempty :=
    ⟨hA.choose, profileSupply_active_subset profile r hA.choose_spec⟩
  have hmem : favorite (profile i) (activeGoods (profileSupply profile r)) hprev ∈
      activeGoods (profileSupply profile (r + 1)) := by
    by_contra hm
    have hs1 : stochasticRecording (profileHistory profile ((r + 1) * n + i.val)) = true := by
      simp [stochasticRecording, FreshQuery, queryActive_at_slot,
        previousChoice_at_slot_succ profile r i hA, hA, hm]
    simp [hs] at hs1
  have heq := favorite_of_mem_of_subset (profile i) hprev hA
    (profileSupply_active_subset profile r) hmem
  simp only [roundRank, roundChoice_eq profile (r + 1) i hA,
    roundChoice_eq profile r i hprev, heq, sub_self]

end ProbabilisticSerial.PSChoiceMachine
