import ReplicaWeightedExposure

/-! The actual replica allocation rank as a sum of time-weighted type rank increments. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators
namespace ProbabilisticSerial.ReplicaChoiceMachine
open UniformPermutation PSProcess ReplicaPS PSChoiceMachine
variable {m q : ℕ} [Nonempty (Fin (m * q))]

def roundRank (p : ReplicaPS.Profile m q) (i : Fin (m * q)) (r : ℕ) : ℝ :=
  rankOf (p i) (roundChoice p r i)

lemma averageRank_eq_round_sum (p : ReplicaPS.Profile m q) :
    ReplicaPS.averageRank p = (1 / ((m * q : ℕ) : ℝ)) *
      ∑ r ∈ Finset.range (m * q), roundDuration p r * ∑ i : Fin (m * q), roundRank p i r := by
  rw [ReplicaRank.averageRank_eq_phase_sum]
  have h := runFrom_round_sum (liftedProfile p)
    (fun phase => phase.duration * ReplicaRank.phaseRank phase) (m * q) 0
    (by simp [profileSupply, activeGoods_initial])
  change (((runFrom (liftedProfile p) (profileSupply (liftedProfile p) 0)
    (profileSupply_valid (liftedProfile p) 0)).phases.map _).sum) = _
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Nat.zero_add, roundTerm]
  split
  next hA =>
    have hT : (roundTypes p r).Nonempty := hA.image typeOf
    have hsum : (∑ i : Fin (m * q), (activeRank (roundTypes p r) (p i) : ℝ)) =
        ∑ i : Fin (m * q), roundRank p i r := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [roundRank, roundChoice_eq p r i hT]
      exact_mod_cast (rankOf_favorite_eq_activeRank (p i) _ hT).symm
    change _ * (𝔼 i : Fin (m * q), (activeRank (roundTypes p r) (p i) : ℝ)) = _
    rw [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_fin, hsum]
    unfold roundDuration PSChoiceMachine.roundDuration
    rw [dif_pos hA]
    change nextDelay (liftedProfile p) (profileSupply (liftedProfile p) r) hA *
      ((∑ i : Fin (m * q), roundRank p i r) / (m * q : ℕ)) = _
    ring
  next hA => simp [roundDuration, PSChoiceMachine.roundDuration, hA]

lemma roundRank_initial (p : ReplicaPS.Profile m q) (i : Fin (m * q)) : roundRank p i 0 = 1 := by
  have hA : (roundTypes p 0).Nonempty := by
    rw [roundTypes_initial]
    exact ⟨⟨0, type_count_pos (m := m) (q := q)⟩, Finset.mem_univ _⟩
  rw [roundRank, roundChoice_eq p 0 i hA]
  have hmem : p i ⟨0, type_count_pos (m := m) (q := q)⟩ ∈ roundTypes p 0 := by rw [roundTypes_initial]; simp
  have hle := favorite_rank_le (p i) (roundTypes p 0) hA
    (p i ⟨0, type_count_pos (m := m) (q := q)⟩) hmem
  have heq : rankOf (p i) (favorite (p i) (roundTypes p 0) hA) = 1 := by
    simp only [rankOf, Equiv.symm_apply_apply, Fin.val_zero, zero_add] at hle ⊢
    omega
  exact_mod_cast heq

def weightedRankJump (p : ReplicaPS.Profile m q) (i : Fin (m * q)) : ℕ → ℝ
  | 0 => max (1 - roundTime p 0) 0 * roundRank p i 0
  | r + 1 => max (1 - roundTime p (r + 1)) 0 * (roundRank p i (r + 1) - roundRank p i r)

lemma averageRank_eq_weighted_jumps (p : ReplicaPS.Profile m q) :
    ReplicaPS.averageRank p = (1 / ((m * q : ℕ) : ℝ)) *
      ∑ r ∈ Finset.range (m * q), ∑ i : Fin (m * q), weightedRankJump p i r := by
  rw [averageRank_eq_round_sum]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range (m * q))]
  apply Finset.sum_congr rfl
  intro i hi
  symm
  have h := sum_shifted_entries (fun r => max (1 - roundTime p r) 0) (roundRank p i)
    (weightedRankJump p i) (m * q) rfl (fun _ => rfl)
    (by change max (1 - roundTime p (m * q)) 0 = 0; simp [roundTime_terminal])
  rw [h]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← partialDuration_eq_ramp]
  exact congrArg (fun x => x * roundRank p i r)
    (PSChoiceMachine.partialDuration_eq_full (liftedProfile p) r (roundTime_le_one _ _))

lemma weightedRankJump_initial (p : ReplicaPS.Profile m q) (i : Fin (m * q)) :
    weightedRankJump p i 0 = 1 := by simp [weightedRankJump, roundTime_zero, roundRank_initial]

lemma arrivalWeight_initial (p : ReplicaPS.Profile m q) (i : Fin (m * q)) :
    arrivalWeight (history p (0 * (m * q) + i.val)) = 1 / (m : ℝ) := by
  have hactive : queryTypes (history p i.val) = Finset.univ := by
    simpa only [Nat.zero_mul, Nat.zero_add, roundTypes_initial] using queryTypes_at_slot p 0 i
  have hA : (queryTypes (history p i.val)).Nonempty := by
    rw [hactive]; exact ⟨⟨0, type_count_pos (m := m) (q := q)⟩, Finset.mem_univ _⟩
  have hu : (Finset.univ : Finset (Fin m)).Nonempty := by rwa [hactive] at hA
  simp [arrivalWeight, stochasticRecording, FreshQuery, previousType_at_slot_zero, hactive, hu]

lemma rank_jump_zero_of_not_stochastic (p : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q))
    (hA : (roundTypes p (r + 1)).Nonempty)
    (hs : stochasticRecording (history p ((r + 1) * (m * q) + i.val)) = false) :
    roundRank p i (r + 1) - roundRank p i r = 0 := by
  have h := answer_type_of_nonfresh p ((r + 1) * (m * q) + i.val)
    (by simpa only [queryTypes_at_slot] using hA) hs
  rw [previousType_at_slot_succ p r i hA, answer_type_at_slot p (r + 1) i hA] at h
  simp only [Option.some.injEq] at h
  simp only [roundRank, roundChoice_eq p (r + 1) i hA,
    roundChoice_eq p r i (hA.mono (roundTypes_subset p (Nat.le_succ r))), h, sub_self]

end ProbabilisticSerial.ReplicaChoiceMachine
