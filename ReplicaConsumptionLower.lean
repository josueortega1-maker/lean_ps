import ReplicaWeightedExposure
import ReplicaUntouched
import ReplicaRawBands

/-! Consumption is bounded by the remaining-time weights of fresh entries. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaConsumptionLower
open ReplicaPS ReplicaChoiceMachine ReplicaRawStep ReplicaRawProcess
  ReplicaSurvivorEntries AdaptiveCategorical

variable {m q : ℕ} [Nonempty (Fin (m * q))]

lemma entry_successor_weighted_ge (p : ReplicaPS.Profile m q) (t : ℝ) (ht : t ≤ 1)
    (r : ℕ) (i : Fin (m * q)) (g : Fin m) :
    max (t - roundTime p (r + 1)) 0 *
        (choiceIndicator p i g (r + 1) - choiceIndicator p i g r) ≤
      PSChoiceMachine.timeWeight t (history p ((r + 1) * (m * q) + i.val)) *
        (if entry g (history p ((r + 1) * (m * q) + i.val))
          (answer p (history p ((r + 1) * (m * q) + i.val))) then 1 else 0) := by
  by_cases htime : roundTime p (r + 1) < t
  · by_cases hg : g ∈ roundTypes p (r + 1)
    · exact (entry_successor_weighted p t r i g (fun _ => hg)).ge
    · have hA : (roundTypes p (r + 1)).Nonempty :=
        (roundTime_lt_one_iff _ _).1 (htime.trans_le ht)
      have hchoice : roundChoice p (r + 1) i ≠ g := by
        rw [roundChoice_eq _ _ _ hA]
        intro heq
        exact hg (heq ▸ PSProcess.favorite_mem (p i) _ hA)
      have hzero : choiceIndicator p i g (r + 1) = 0 := by
        simp [choiceIndicator, hchoice]
      have hprev : 0 ≤ choiceIndicator p i g r := by unfold choiceIndicator; positivity
      have hrhs : 0 ≤ PSChoiceMachine.timeWeight t
          (history p ((r + 1) * (m * q) + i.val)) *
          (if entry g (history p ((r + 1) * (m * q) + i.val))
            (answer p (history p ((r + 1) * (m * q) + i.val))) then 1 else 0) := by
        unfold PSChoiceMachine.timeWeight
        positivity
      rw [hzero]
      exact (mul_nonpos_of_nonneg_of_nonpos (le_max_right _ _) (by linarith)).trans hrhs
  · simp [PSChoiceMachine.timeWeight, queryTime_at_slot,
      max_eq_right (sub_nonpos.mpr (le_of_not_gt htime))]

theorem consumption_le_full_weighted_entries (p : ReplicaPS.Profile m q)
    (t : ℝ) (ht : t ≤ 1) (g : Fin m) :
    partialConsumption p t g ≤
      weightedSuccesses (entry g) (PSChoiceMachine.timeWeight t)
        (history p ((m * q) * (m * q))) := by
  let e (i : Fin (m * q)) : ℕ → ℝ
    | 0 => max (t - roundTime p 0) 0 * choiceIndicator p i g 0
    | r + 1 => max (t - roundTime p (r + 1)) 0 *
        (choiceIndicator p i g (r + 1) - choiceIndicator p i g r)
  have heach (i : Fin (m * q)) :
      (∑ r ∈ Finset.range (m * q), partialDuration p t r * choiceIndicator p i g r) =
        ∑ r ∈ Finset.range (m * q), e i r := by
    have h := PSChoiceMachine.sum_shifted_entries
      (fun r => max (t - roundTime p r) 0) (choiceIndicator p i g) (e i) (m * q)
      rfl (fun _ => rfl) (by
        change max (t - roundTime p (m * q)) 0 = 0
        rw [roundTime_terminal, max_eq_right (sub_nonpos.mpr ht)])
    simpa only [← partialDuration_eq_ramp] using h.symm
  rw [partialConsumption_eq, PSChoiceMachine.weightedSuccesses_profileHistory,
    PSChoiceMachine.sum_slots (n := m * q) _ (m * q)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range (m * q))]
  apply Finset.sum_le_sum
  intro i hi
  rw [heach]
  apply Finset.sum_le_sum
  intro r hr
  cases r with
  | zero => simpa only [e, Nat.zero_mul, Nat.zero_add] using (entry_initial_weighted p t i g).ge
  | succ r => exact entry_successor_weighted_ge p t ht r i g

def weightedEntries (s : State m q) (g : Fin m) : ℝ :=
  weightedSuccesses (entry g) (PSChoiceMachine.timeWeight 1) (history s.reference s.depth)

lemma weightedEntries_nonneg (s : State m q) (g : Fin m) : 0 ≤ weightedEntries s g := by
  unfold weightedEntries
  rw [PSChoiceMachine.weightedSuccesses_profileHistory]
  apply Finset.sum_nonneg
  intro k hk
  unfold PSChoiceMachine.timeWeight
  positivity

theorem consumption_at_clock_le_entries (s : State m q) (g : Fin m) :
    partialConsumption s.reference s.clock g ≤ weightedEntries s g := by
  apply (consumption_le_full_weighted_entries s.reference s.clock s.clock_le_one g).trans
  unfold weightedEntries
  simp only [PSChoiceMachine.weightedSuccesses_profileHistory]
  let f (t : ℝ) (k : ℕ) : ℝ :=
    PSChoiceMachine.timeWeight t (history s.reference k) *
      (if entry g (history s.reference k) (answer s.reference (history s.reference k))
        then 1 else 0)
  change (∑ k ∈ Finset.range ((m * q) * (m * q)), f s.clock k) ≤
    ∑ k ∈ Finset.range s.depth, f 1 k
  have hf (t : ℝ) (k : ℕ) : 0 ≤ f t k := by
    unfold f PSChoiceMachine.timeWeight
    positivity
  have hmono (k : ℕ) : f s.clock k ≤ f 1 k := by
    apply mul_le_mul_of_nonneg_right _ (by split_ifs <;> norm_num)
    exact max_le_max (sub_le_sub_right s.clock_le_one _) le_rfl
  have hzero (k : ℕ) (hk : s.depth ≤ k) : f s.clock k = 0 := by
    have htime : s.clock ≤ PSChoiceMachine.queryTime (history s.reference k) := by
      rw [queryTime_at_depth, s.clock_eq_roundTime]
      exact roundTime_mono _ (Nat.div_le_div_right hk)
    simp [f, PSChoiceMachine.timeWeight, max_eq_right (sub_nonpos.mpr htime)]
  by_cases hd : s.depth ≤ (m * q) * (m * q)
  · have heq : (∑ k ∈ Finset.range ((m * q) * (m * q)), f s.clock k) =
        ∑ k ∈ Finset.range s.depth, f s.clock k := by
      symm
      apply Finset.sum_subset (Finset.range_mono hd)
      intro k hk hnot
      exact hzero k (by simpa using hnot)
    rw [heq]
    exact Finset.sum_le_sum (fun k _ => hmono k)
  · apply (Finset.sum_le_sum (fun k _ => hmono k)).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_of_not_ge hd))
      (fun k _ _ => hf 1 k)

lemma nextQueryDepth_weightedEntries (p : ReplicaPS.Profile m q) (fuel depth : ℕ)
    (g : Fin m) :
    weightedSuccesses (entry g) (PSChoiceMachine.timeWeight 1)
      (history p (nextQueryDepth p fuel depth)) =
      weightedSuccesses (entry g) (PSChoiceMachine.timeWeight 1) (history p depth) := by
  induction fuel generalizing depth with
  | zero => rfl
  | succ fuel ih =>
      unfold nextQueryDepth
      split_ifs with h
      · rfl
      · have hs : stochasticRecording (history p depth) = false :=
          Bool.eq_false_of_not_eq_true (fun ht => h (Or.inr ht))
        rw [ih]
        change weightedSuccesses (entry g) (PSChoiceMachine.timeWeight 1)
          (answer p (history p depth) :: history p depth) = _
        simp [weightedSuccesses, entry, hs]

@[simp] lemma weightedEntries_normalize (s : State m q) (g : Fin m) :
    weightedEntries s.normalize g = weightedEntries s g :=
  nextQueryDepth_weightedEntries _ _ _ _

lemma weightedEntries_child (s : State m q)
    (hs : stochasticRecording (history s.reference s.depth) = true)
    (a : Fin m) (ha : a ∈ available s.reference s.depth) (g : Fin m) :
    weightedEntries (s.child hs a ha) g =
      weightedEntries s g + (1 - s.clock) * RawSubsetCounts.hit {g} a := by
  let other := (s.child hs a ha).reference
  have hp : other ∈ acceptedFiber s.reference s.depth a :=
    (acceptedFiber_nonempty s.reference s.depth hs a ha).choose_spec
  obtain ⟨hp, ht⟩ := Finset.mem_filter.mp hp
  have hh : history other s.depth = history s.reference s.depth := (Finset.mem_filter.mp hp).2
  have ht' : typeOf (answer other (history other s.depth)) = a := by
    change typeOf (answer other (history s.reference s.depth)) = a at ht
    rwa [hh]
  have htref : typeOf (answer other (history s.reference s.depth)) = a := ht
  change weightedSuccesses (entry g) (PSChoiceMachine.timeWeight 1)
    (answer other (history other s.depth) :: history other s.depth) = _
  rw [weightedSuccesses]
  simp only [entry, hh, hs, htref, Bool.true_and]
  have hz : PSChoiceMachine.timeWeight 1 (history s.reference s.depth) = 1 - s.clock :=
    max_eq_left (sub_nonneg.mpr s.clock_le_one)
  rw [hz]
  by_cases hag : a = g
  · have hg : g ∈ queryTypes (history s.reference s.depth) := hag ▸ ha
    simp [RawSubsetCounts.hit, weightedEntries, hag, hg]
  · simp [RawSubsetCounts.hit, weightedEntries, hag]

theorem weightedEntries_step_le (s : State m q) (a g : Fin m) :
    weightedEntries (s.step a) g ≤ weightedEntries s g +
      remainingWeight s * RawSubsetCounts.hit {g} a := by
  have hnonneg : 0 ≤ remainingWeight s * RawSubsetCounts.hit {g} a := by
    apply mul_nonneg (remainingWeight_bounds s).1
    unfold RawSubsetCounts.hit
    positivity
  by_cases ht : (m * q) * (m * q) ≤ s.normalize.depth
  · have heq : s.step a = s.normalize := by simp [State.step, ht]
    rw [heq, weightedEntries_normalize]
    linarith
  · have hs := s.normalize_ready.resolve_left ht
    by_cases ha : a ∈ available s.normalize.reference s.normalize.depth
    · have heq : s.step a = (s.normalize.child hs a ha).normalize := by
        simp [State.step, ht, hs, ha]
      rw [heq, weightedEntries_normalize, weightedEntries_child, weightedEntries_normalize]
      rfl
    · have heq : s.step a = s.normalize := by simp [State.step, ht, hs, ha]
      rw [heq, weightedEntries_normalize]
      linarith

theorem weightedEntries_evolve_le (s : State m q) (g : Fin m)
    (n : ℕ) (w : Fin n → Fin m) :
    weightedEntries (s.evolve n w) g ≤ weightedEntries s g +
      weightedRawHits s remainingWeight {g} n w := by
  induction n with
  | zero => simp [State.evolve, weightedRawHits]
  | succ n ih =>
      have hstep := weightedEntries_step_le (s.evolve n (Fin.tail w)) (w 0) g
      change weightedEntries ((s.evolve n (Fin.tail w)).step (w 0)) g ≤ _
      rw [weightedRawHits]
      linarith [ih (Fin.tail w)]

theorem weightedEntries_le_entryCount (s : State m q) (g : Fin m) :
    weightedEntries s g ≤ entryCount s {g} := by
  rcases s with ⟨p, d⟩
  induction d with
  | zero => simp [weightedEntries, entryCount, survivorAgents, history,
      PSChoiceMachine.profileHistory_zero, weightedSuccesses]
  | succ d ih =>
      have hclock : 0 ≤ (State.mk p d).clock := (State.mk p d).clock_nonneg
      have hz : PSChoiceMachine.timeWeight 1 (history p d) ≤ 1 := by
        change max (1 - (State.mk p d).clock) 0 ≤ 1
        exact max_le (by linarith) (by norm_num)
      have hz0 : 0 ≤ PSChoiceMachine.timeWeight 1 (history p d) := le_max_right _ _
      have hrec : weightedEntries (State.mk p (d + 1)) g =
          weightedEntries (State.mk p d) g +
          PSChoiceMachine.timeWeight 1 (history p d) *
            (if entry g (history p d) (answer p (history p d)) then 1 else 0) := rfl
      rw [hrec]
      change _ ≤ ((survivorAgents p (d + 1) {g}).length : ℝ)
      rw [survivorAgents_succ]
      have hih : weightedEntries (State.mk p d) g ≤
          ((survivorAgents p d {g}).length : ℝ) := ih
      by_cases hs : stochasticRecording (history p d) = true
      · rw [if_pos hs]
        by_cases hg : typeOf (answer p (history p d)) ∈ ({g} : Finset (Fin m))
        · rw [if_pos hg]
          simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
          have ht : typeOf (answer p (history p d)) = g := by simpa using hg
          simp only [entry, hs, Bool.true_and, ht, and_true, decide_eq_true_eq]
          split_ifs <;> nlinarith
        · rw [if_neg hg]
          have ht : typeOf (answer p (history p d)) ≠ g := by simpa using hg
          simpa [entry, hs, ht] using hih
      · have hs0 := Bool.eq_false_of_not_eq_true hs
        rw [if_neg hs]
        simpa [entry, hs0] using hih

theorem weightedEntries_zero_of_no_entry (s : State m q) (g : Fin m)
    (hg : entryCount s {g} = 0) : weightedEntries s g = 0 := by
  have h := weightedEntries_le_entryCount s g
  rw [hg, Nat.cast_zero] at h
  exact le_antisymm h (weightedEntries_nonneg s g)

lemma sum_weightedRawHits_singletons (s : State m q) (W : State m q → ℝ)
    (S : Finset (Fin m)) (n : ℕ) (w : Fin n → Fin m) :
    (∑ g ∈ S, weightedRawHits s W {g} n w) = weightedRawHits s W S n w := by
  induction n with
  | zero => simp [weightedRawHits]
  | succ n ih =>
      simp only [weightedRawHits, Finset.sum_add_distrib]
      rw [ih, ← Finset.mul_sum]
      congr 1
      simp [RawSubsetCounts.hit, Finset.mem_singleton, eq_comm]

theorem consumed_set_le_raw_hits (s : State m q) (S : Finset (Fin m))
    (hS : ∀ g ∈ S, entryCount s {g} = 0) (n : ℕ) (w : Fin n → Fin m) :
    (∑ g ∈ S, partialConsumption (s.evolve n w).reference (s.evolve n w).clock g) ≤
      weightedRawHits s remainingWeight S n w := by
  calc
    _ ≤ ∑ g ∈ S, weightedEntries (s.evolve n w) g :=
      Finset.sum_le_sum (fun g _ => consumption_at_clock_le_entries _ g)
    _ ≤ ∑ g ∈ S, weightedRawHits s remainingWeight {g} n w := by
      apply Finset.sum_le_sum
      intro g hg
      have h := weightedEntries_evolve_le s g n w
      rwa [weightedEntries_zero_of_no_entry s g (hS g hg), zero_add] at h
    _ = _ := sum_weightedRawHits_singletons s remainingWeight S n w

theorem band_quota_le_hits_and_residual (s : State m q) (S : Finset (Fin m))
    (hS : ∀ g ∈ S, entryCount s {g} = 0) (n : ℕ) (w : Fin n → Fin m) :
    (q : ℝ) * S.card - (∑ g : Fin m,
      residual (s.evolve n w).reference (s.evolve n w).clock g) ≤
        weightedRawHits s remainingWeight S n w := by
  have h := consumed_set_le_raw_hits s S hS n w
  have heq : (∑ g ∈ S, partialConsumption (s.evolve n w).reference (s.evolve n w).clock g) =
      (q : ℝ) * S.card - ∑ g ∈ S, residual (s.evolve n w).reference (s.evolve n w).clock g := by
    simp only [residual_eq, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [heq] at h
  have hres : (∑ g ∈ S, residual (s.evolve n w).reference (s.evolve n w).clock g) ≤
      ∑ g : Fin m, residual (s.evolve n w).reference (s.evolve n w).clock g :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun g _ _ => residual_nonneg _ _ _)
  linarith

theorem expected_bandCost_lower (hm : 0 < m) (s : State m q) (S : Finset (Fin m))
    (hne : S.Nonempty) (hS : ∀ g ∈ S, entryCount s {g} = 0) (n : ℕ) :
    (q : ℝ) - (𝔼 w : Fin n → Fin m, ∑ g : Fin m,
      residual (s.evolve n w).reference (s.evolve n w).clock g) / S.card ≤
        𝔼 w : Fin n → Fin m, rawBandCost s n w := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hsamp : (Finset.univ : Finset (Fin n → Fin m)).Nonempty := by
    exact ⟨fun _ => ⟨0, hm⟩, Finset.mem_univ _⟩
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun w (_ : w ∈ (Finset.univ : Finset (Fin n → Fin m))) =>
      div_le_div_of_nonneg_right (band_quota_le_hits_and_residual s S hS n w) hcard.le)
  simp only [sub_div, mul_div_cancel_right₀ _ hcard.ne'] at h
  rw [Finset.expect_sub_distrib, Finset.expect_const hsamp, ← Finset.expect_div,
    expected_hits_per_type hm s S hne n] at h
  exact h

end ProbabilisticSerial.ReplicaConsumptionLower
