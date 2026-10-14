import PSRankIncrement
import PSChoiceMachine

/-! Exact preference fibers and the conditional rank bound on actual PS paths. -/

noncomputable section
set_option maxHeartbeats 4000000

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PSChoiceMachine

open UniformPermutation PSProcess SequentialRevelation AdaptiveCategorical StoppedChoices

variable {n : ℕ} [Nonempty (Fin n)]

lemma profileRevealHistory_mono (profile : Profile n) {a b : ℕ} (hab : a ≤ b) :
    ∀ r ∈ profileRevealHistory profile a, r ∈ profileRevealHistory profile b := by
  intro r hr
  obtain ⟨k, hk, hs, ha, hA, hc⟩ := (mem_profileRevealHistory profile a r).mp hr
  exact (mem_profileRevealHistory profile b r).mpr ⟨k, lt_of_lt_of_le hk hab, hs, ha, hA, hc⟩

theorem profileHistory_eq_of_compatible (reference other : Profile n) (depth : ℕ)
    (hc : Compatible other (profileRevealHistory reference depth)) :
    profileHistory reference depth = profileHistory other depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      have hprefix : Compatible other (profileRevealHistory reference depth) := by
        intro r hr
        exact hc r (profileRevealHistory_mono reference (Nat.le_succ depth) r hr)
      have heq := ih hprefix
      rw [profileHistory_succ, profileHistory_succ, ← heq]
      congr 1
      by_cases hs : stochasticRecording (profileHistory reference depth) = true
      · have hstep := hc ⟨queryAgent (profileHistory reference depth),
            queryActive (profileHistory reference depth),
            profileAnswer reference (profileHistory reference depth), by
              rw [← queryAvailable_eq_active_of_stochastic _ hs]
              exact profileAnswer_mem reference _⟩ (by
            rw [profileRevealHistory_succ, profileRevealStep_eq_some reference depth hs]
            simp)
        change favorite (other (queryAgent (profileHistory reference depth)))
          (queryActive (profileHistory reference depth)) _ =
          profileAnswer reference (profileHistory reference depth) at hstep
        exact hstep.symm.trans (favorite_congr_set _ _ _ _ _
          (queryAvailable_eq_active_of_stochastic _ hs).symm)
      · have hcard := queryAvailable_card_eq_one_of_not_stochastic
          (profileHistory reference depth) (Bool.eq_false_of_not_eq_true hs)
        exact Finset.card_le_one.mp hcard.le _ (profileAnswer_mem reference _)
          _ (profileAnswer_mem other _)

theorem pathFiber_eq_compatibleProfiles (reference : Profile n) (depth : ℕ) :
    pathFiber depth (profileHistory reference depth) =
      compatibleProfiles (profileRevealHistory reference depth) := by
  ext other
  simp only [pathFiber, Finset.mem_filter, mem_compatibleProfiles_iff]
  constructor
  · rintro ⟨_, heq⟩
    exact compatible_of_profileHistory_eq reference other depth heq.symm
  · intro hc
    exact ⟨by simp [preferenceProfileSample, UniformProduct.productSample,
      preferenceSample, permutationSample],
      (profileHistory_eq_of_compatible reference other depth hc).symm⟩

lemma fresh_answer_recorded (profile : Profile n) (depth : ℕ)
    (hs : stochasticRecording (profileHistory profile depth) = true) :
    ∃ r ∈ profileRevealHistory profile (depth + 1),
      r.agent = queryAgent (profileHistory profile depth) ∧
      r.chosen = profileAnswer profile (profileHistory profile depth) := by
  refine ⟨⟨queryAgent (profileHistory profile depth),
    queryActive (profileHistory profile depth),
    profileAnswer profile (profileHistory profile depth), ?_⟩, ?_, rfl, rfl⟩
  · rw [← queryAvailable_eq_active_of_stochastic _ hs]
    exact profileAnswer_mem profile _
  · rw [profileRevealHistory_succ, profileRevealStep_eq_some profile depth hs]
    simp

lemma round_favorite_recorded (profile : Profile n) (round : ℕ) (i : Fin n)
    (hA : (activeGoods (profileSupply profile round)).Nonempty) :
    ∃ r ∈ profileRevealHistory profile (round * n + i.val + 1),
      r.agent = i ∧ r.chosen = favorite (profile i)
        (activeGoods (profileSupply profile round)) hA := by
  classical
  induction round with
  | zero =>
      have hs : stochasticRecording (profileHistory profile i.val) = true := by
        have ha := queryActive_at_slot profile 0 i
        simp only [Nat.zero_mul, Nat.zero_add] at ha
        simp [stochasticRecording, FreshQuery, previousChoice_at_slot_zero, ha, hA]
      simpa only [queryAgent_at_slot, profileAnswer_at_slot profile 0 i hA] using
        fresh_answer_recorded profile (0 * n + i.val) (by simpa using hs)
  | succ round ih =>
      let hprev : (activeGoods (profileSupply profile round)).Nonempty :=
        ⟨hA.choose, profileSupply_active_subset profile round hA.choose_spec⟩
      by_cases hs : stochasticRecording
          (profileHistory profile ((round + 1) * n + i.val)) = true
      · simpa [queryAgent_at_slot, profileAnswer_at_slot, hA] using
          fresh_answer_recorded profile ((round + 1) * n + i.val) hs
      · have hmem : favorite (profile i) (activeGoods (profileSupply profile round)) hprev ∈
            activeGoods (profileSupply profile (round + 1)) := by
          by_contra hnot
          apply hs
          simp [stochasticRecording, FreshQuery, queryActive_at_slot,
            previousChoice_at_slot_succ profile round i hA, hA, hnot]
        obtain ⟨r, hr, hra, hrc⟩ := ih hprev
        refine ⟨r, profileRevealHistory_mono profile ?_ r hr, hra, ?_⟩
        · have hn : 0 < n := i.pos
          simp only [Nat.add_mul, Nat.one_mul]
          omega
        · rw [hrc]
          exact (favorite_of_mem_of_subset (profile i) hprev hA
            (profileSupply_active_subset profile round) hmem).symm

lemma previous_favorite_mem_reveals (profile : Profile n) (round : ℕ) (i : Fin n)
    (hA : (activeGoods (profileSupply profile round)).Nonempty) :
    ∀ r ∈ profileRevealHistory profile ((round + 1) * n + i.val), r.agent = i →
      favorite (profile i) (activeGoods (profileSupply profile round)) hA ∈ r.available := by
  intro r hr hra
  obtain ⟨k, hk, hs, ha, hav, hc⟩ := (mem_profileRevealHistory _ _ r).mp hr
  have hm : k % n = i.val := by
    have hv := congrArg Fin.val (ha.symm.trans hra)
    simpa [queryAgent, roundOffset, profileHistory_length] using hv
  have hkr : k / n ≤ round := by
    have hd := Nat.mod_add_div k n
    have hn : 0 < n := i.pos
    rw [hm] at hd
    nlinarith
  rw [hav]
  unfold queryActive
  rw [(profile_machine_correspondence profile k).1]
  exact profileSupply_active_subset_of_le profile hkr (favorite_mem _ _ hA)

/-- The finite conditional estimate now applies to the exact path fiber of
the concrete PS machine at every fresh query after the initial round. -/
theorem expected_rank_jump_at_slot_le (profile : Profile n) (round : ℕ) (i : Fin n)
    (hA : (activeGoods (profileSupply profile (round + 1))).Nonempty)
    (hs : stochasticRecording (profileHistory profile ((round + 1) * n + i.val)) = true) :
    let previous := favorite (profile i) (activeGoods (profileSupply profile round))
      (by exact ⟨hA.choose, profileSupply_active_subset profile round hA.choose_spec⟩)
    (𝔼 other ∈ pathFiber ((round + 1) * n + i.val)
        (profileHistory profile ((round + 1) * n + i.val)),
      ((rankOf (other i) (favorite (other i)
          (activeGoods (profileSupply profile (round + 1))) hA) : ℝ) -
        rankOf (other i) previous)) ≤
      (n : ℝ) / ((activeGoods (profileSupply profile (round + 1))).card + 1) := by
  dsimp only
  rw [pathFiber_eq_compatibleProfiles]
  apply PSRankIncrement.expected_rank_jump_le
  · exact ⟨profile, mem_compatibleProfiles_iff.mpr (profileRevealHistory_compatible _ _)⟩
  · simpa [queryAgent_at_slot, queryActive_at_slot] using
      profile_fresh_query_admissible profile ((round + 1) * n + i.val) hs
  · exact previous_favorite_mem_reveals profile round i _
  · obtain ⟨r, hr, ha, hc⟩ := round_favorite_recorded profile round i
      (show (activeGoods (profileSupply profile round)).Nonempty from
        ⟨hA.choose, profileSupply_active_subset profile round hA.choose_spec⟩)
    refine ⟨r, profileRevealHistory_mono profile ?_ r hr, ha, hc⟩
    have hn : 0 < n := i.pos
    simp only [Nat.add_mul, Nat.one_mul]
    omega

end ProbabilisticSerial.PSChoiceMachine
