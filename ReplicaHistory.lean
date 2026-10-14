import ReplicaChoiceMachine
import ReplicaRankIncrement

/-! Admissible fresh type queries and conditional ranks on concrete replica paths. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaChoiceMachine
open UniformPermutation PSProcess ReplicaPS ReplicaRevelation PSChoiceMachine
variable {m q : ℕ} [Nonempty (Fin (m * q))]

theorem fresh_query_admissible (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history profile depth) = true) :
    AdmissibleQuery (revealHistory profile depth)
      (queryAgent (history profile depth)) (queryTypes (history profile depth)) := by
  classical
  have hsProp : (queryTypes (history profile depth)).Nonempty ∧
      FreshQuery (history profile depth) := of_decide_eq_true hs
  intro r hr hra g hg
  obtain ⟨k, hk, hks, hka, hkA, hkc⟩ := (mem_revealHistory profile depth r).mp hr
  have hmod : k % (m * q) = depth % (m * q) := by
    have hv := congrArg Fin.val (hka.symm.trans hra)
    simpa only [queryAgent, roundOffset, history, profileHistory_length] using hv
  have hlt : k / (m * q) < depth / (m * q) := by
    have hle : k / (m * q) ≤ depth / (m * q) := Nat.div_le_div_right hk.le
    have he : k / (m * q) ≠ depth / (m * q) := by
      intro he
      have h1 := Nat.mod_add_div k (m * q)
      have h2 := Nat.mod_add_div depth (m * q)
      rw [hmod, he] at h1
      omega
    omega
  have hsub : queryTypes (history profile depth) ⊆ r.available := by
    rw [hkA, queryTypes_at_depth, queryTypes_at_depth]
    exact roundTypes_subset profile hlt.le
  apply Finset.mem_erase.mpr
  refine ⟨?_, hsub hg⟩
  intro heq
  have hchosen : r.chosen ∈ queryTypes (history profile depth) := heq ▸ hg
  let i := queryAgent (history profile depth)
  let prev := depth / (m * q) - 1
  have hpos : 0 < depth / (m * q) := lt_of_le_of_lt (Nat.zero_le _) hlt
  have hprev : prev + 1 = depth / (m * q) := by dsimp [prev]; omega
  have hkprev : k / (m * q) ≤ prev := by dsimp [prev]; omega
  have hA : (roundTypes profile (prev + 1)).Nonempty := by
    rw [hprev, ← queryTypes_at_depth]
    exact hsProp.1
  have hprevA : (roundTypes profile prev).Nonempty :=
    hA.mono (roundTypes_subset profile (Nat.le_succ prev))
  have hkA' : (queryTypes (history profile k)).Nonempty := stochastic_nonempty _ hks
  have hchosenEq : r.chosen = favorite (profile i)
      (roundTypes profile (k / (m * q))) (by rwa [← queryTypes_at_depth]) := by
    rw [hkc, answer_type profile k hkA']
    have hai : queryAgent (history profile k) = i := hka.symm.trans hra
    simp only [hai, queryTypes_at_depth]
  have hkeep : r.chosen ∈ roundTypes profile prev := by
    apply roundTypes_subset profile (by omega : prev ≤ depth / (m * q))
    simpa only [queryTypes_at_depth] using hchosen
  have hf : favorite (profile i) (roundTypes profile prev) hprevA = r.chosen := by
    rw [hchosenEq]
    apply ReplicaTrace.favorite_persists _ _ _ (roundTypes_subset profile hkprev)
    simpa only [hchosenEq] using hkeep
  have hd : depth = (prev + 1) * (m * q) + i.val := by
    rw [hprev]
    exact depth_decomposition profile depth
  have hp := previousType_at_slot_succ profile prev i hA
  rw [← hd, hf] at hp
  have habsent : r.chosen ∉ queryTypes (history profile depth) := by
    simpa only [FreshQuery, hp] using hsProp.2
  exact habsent hchosen

lemma fresh_answer_recorded (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history profile depth) = true) :
    ∃ r ∈ revealHistory profile (depth + 1),
      r.agent = queryAgent (history profile depth) ∧
      r.chosen = typeOf (answer profile (history profile depth)) := by
  refine ⟨⟨queryAgent (history profile depth), queryTypes (history profile depth),
    typeOf (answer profile (history profile depth)), ?_⟩, ?_, rfl, rfl⟩
  · rw [answer_type profile depth (stochastic_nonempty _ hs)]
    exact favorite_mem _ _ _
  · rw [revealHistory_succ, revealStep_eq_some profile depth hs]
    simp

lemma round_favorite_recorded (profile : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q))
    (hA : (roundTypes profile r).Nonempty) :
    ∃ d ∈ revealHistory profile (r * (m * q) + i.val + 1),
      d.agent = i ∧ d.chosen = favorite (profile i) (roundTypes profile r) hA := by
  induction r with
  | zero =>
      have hs : stochasticRecording (history profile i.val) = true := by
        have ha := queryTypes_at_slot profile 0 i
        simp only [Nat.zero_mul, Nat.zero_add] at ha
        simp [stochasticRecording, FreshQuery, previousType_at_slot_zero, ha, hA]
      have h := fresh_answer_recorded profile (0 * (m * q) + i.val) (by simpa using hs)
      simpa only [history, queryAgent_at_slot, answer_type_at_slot profile 0 i hA] using h
  | succ r ih =>
      have hprev := hA.mono (roundTypes_subset profile (Nat.le_succ r))
      by_cases hs : stochasticRecording (history profile ((r + 1) * (m * q) + i.val)) = true
      · have h := fresh_answer_recorded profile ((r + 1) * (m * q) + i.val) hs
        simpa only [history, queryAgent_at_slot, answer_type_at_slot profile (r + 1) i hA] using h
      · have hk : favorite (profile i) (roundTypes profile r) hprev ∈ roundTypes profile (r + 1) := by
          by_contra hn
          apply hs
          simp [stochasticRecording, FreshQuery, previousType_at_slot_succ profile r i hA,
            queryTypes_at_slot, hA, hn]
        obtain ⟨d, hd, hda, hdc⟩ := ih hprev
        refine ⟨d, revealHistory_mono profile ?_ d hd, hda, ?_⟩
        · have hn := i.pos
          simp only [Nat.add_mul, Nat.one_mul]
          omega
        · rw [hdc]
          exact (ReplicaTrace.favorite_persists _ _ _ (roundTypes_subset profile (Nat.le_succ r)) hk).symm

lemma previous_favorite_mem_reveals (profile : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q))
    (hA : (roundTypes profile r).Nonempty) :
    ∀ d ∈ revealHistory profile ((r + 1) * (m * q) + i.val), d.agent = i →
      favorite (profile i) (roundTypes profile r) hA ∈ d.available := by
  intro d hd hdi
  obtain ⟨k, hk, hs, ha, hAv, hc⟩ := (mem_revealHistory _ _ d).mp hd
  have hm : k % (m * q) = i.val := by
    have hv := congrArg Fin.val (ha.symm.trans hdi)
    simpa only [queryAgent, roundOffset, history, profileHistory_length] using hv
  have hkr : k / (m * q) ≤ r := by
    have hd := Nat.mod_add_div k (m * q)
    have hn := i.pos
    rw [hm] at hd
    nlinarith
  rw [hAv, queryTypes_at_depth]
  exact roundTypes_subset profile hkr (favorite_mem _ _ hA)

theorem expected_rank_jump_at_slot_le (profile : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q))
    (hA : (roundTypes profile (r + 1)).Nonempty)
    (hs : stochasticRecording (history profile ((r + 1) * (m * q) + i.val)) = true) :
    let previous := favorite (profile i) (roundTypes profile r)
      (hA.mono (roundTypes_subset profile (Nat.le_succ r)))
    (𝔼 other ∈ pathFiber ((r + 1) * (m * q) + i.val)
      (history profile ((r + 1) * (m * q) + i.val)),
      ((rankOf (other i) (favorite (other i) (roundTypes profile (r + 1)) hA) : ℝ) -
        rankOf (other i) previous)) ≤ (m : ℝ) / ((roundTypes profile (r + 1)).card + 1) := by
  dsimp only
  rw [pathFiber_eq_compatibleProfiles]
  apply ReplicaRankIncrement.expected_rank_jump_le
  · exact ⟨profile, mem_compatibleProfiles_iff.mpr (revealHistory_compatible _ _)⟩
  · simpa only [history, queryAgent_at_slot, queryTypes_at_slot] using
      fresh_query_admissible profile ((r + 1) * (m * q) + i.val) hs
  · exact previous_favorite_mem_reveals profile r i _
  · obtain ⟨d, hd, ha, hc⟩ := round_favorite_recorded profile r i
      (hA.mono (roundTypes_subset profile (Nat.le_succ r)))
    refine ⟨d, revealHistory_mono profile ?_ d hd, ha, hc⟩
    have hn := i.pos
    simp only [Nat.add_mul, Nat.one_mul]
    omega

end ProbabilisticSerial.ReplicaChoiceMachine
