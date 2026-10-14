import ReplicaSurvivorEntries

/-! A type absent from the raw labels retains its whole actual PS quota. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaUntouched
open ReplicaPS ReplicaChoiceMachine ReplicaRawStep ReplicaRawProcess ReplicaSurvivorEntries

variable {m q : ℕ} [Nonempty (Fin (m * q))]

lemma entryCount_step_le_raw (s : State m q) (g : Fin m) (S : Finset (Fin m)) :
    entryCount (s.step g) S ≤ entryCount s S + if g ∈ S then 1 else 0 := by
  by_cases ht : (m * q) * (m * q) ≤ s.normalize.depth
  · have heq : s.step g = s.normalize := by simp [State.step, ht]
    rw [heq, entryCount_normalize]
    omega
  · have hs := s.normalize_ready.resolve_left ht
    by_cases hg : g ∈ available s.normalize.reference s.normalize.depth
    · have heq : s.step g = (s.normalize.child hs g hg).normalize := by
        simp [State.step, ht, hs, hg]
      rw [heq, entryCount_normalize, entryCount_child, entryCount_normalize]
    · have heq : s.step g = s.normalize := by simp [State.step, ht, hs, hg]
      rw [heq, entryCount_normalize]
      omega

theorem entryCount_evolve_le_raw (s : State m q) (n : ℕ) (w : Fin n → Fin m)
    (S : Finset (Fin m)) :
    entryCount (s.evolve n w) S ≤ entryCount s S +
      ∑ i : Fin n, if w i ∈ S then (1 : ℕ) else 0 := by
  induction n with
  | zero => simp [State.evolve]
  | succ n ih =>
      have hstep := entryCount_step_le_raw (s.evolve n (Fin.tail w)) (w 0) S
      have hprev := ih (Fin.tail w)
      change entryCount ((s.evolve n (Fin.tail w)).step (w 0)) S ≤ _
      simp only [Fin.sum_univ_succ, Fin.tail] at hprev ⊢
      omega

theorem untouched_entryCount_zero (reference : ReplicaPS.Profile m q)
    (n : ℕ) (w : Fin n → Fin m) (g : Fin m) (hg : ∀ i, w i ≠ g) :
    entryCount ((initialState reference).evolve n w) {g} = 0 := by
  have h := entryCount_evolve_le_raw (initialState reference) n w {g}
  have hzero : (∑ i : Fin n, if w i ∈ ({g} : Finset (Fin m)) then (1 : ℕ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hg i]
  rw [hzero] at h
  simp only [entryCount, initialState, survivorAgents, revealHistory_zero,
    List.filter_nil, List.map_nil, List.length_nil, zero_add, add_zero] at h
  exact Nat.eq_zero_of_le_zero h

lemma slot_succ_le_depth {n depth r : ℕ} (hr : r < depth / n) (i : Fin n) :
    r * n + i.val + 1 ≤ depth := by
  have hd := Nat.div_mul_le_self depth n
  have hm := Nat.mul_le_mul_right n (show r + 1 ≤ depth / n by omega)
  have hi := i.isLt
  nlinarith

lemma no_entry_no_previous_choice (s : State m q) (g : Fin m)
    (hzero : entryCount s {g} = 0) (r : ℕ) (ht : roundTime s.reference r < s.clock)
    (i : Fin (m * q)) : choiceIndicator s.reference i g r = 0 := by
  have hA : (roundTypes s.reference r).Nonempty :=
    (roundTime_lt_one_iff _ _).1 (ht.trans_le s.clock_le_one)
  have hr : r < s.depth / (m * q) := by
    by_contra hn
    have h := roundTime_mono s.reference (le_of_not_gt hn)
    rw [← s.clock_eq_roundTime] at h
    linarith
  unfold choiceIndicator
  apply if_neg
  intro hchoice
  obtain ⟨record, hrecord, ha, hc⟩ := round_favorite_recorded s.reference r i hA
  have hmem := revealHistory_mono s.reference (slot_succ_le_depth hr i) record hrecord
  have hchosen : record.chosen = g := by
    rw [hc]
    rwa [roundChoice_eq s.reference r i hA] at hchoice
  have hag : record.agent ∈ survivorAgents s.reference s.depth {g} := by
    apply List.mem_map.mpr
    refine ⟨record, List.mem_filter.mpr ⟨hmem, ?_⟩, rfl⟩
    simp [hchosen]
  have hpositive := List.length_pos_of_mem hag
  change 0 < entryCount s {g} at hpositive
  omega

theorem no_entry_consumption_zero (s : State m q) (g : Fin m)
    (hzero : entryCount s {g} = 0) :
    partialConsumption s.reference s.clock g = 0 := by
  rw [partialConsumption_eq]
  apply Finset.sum_eq_zero
  intro r hr
  by_cases ht : roundTime s.reference r < s.clock
  · have hsum : (∑ i : Fin (m * q), choiceIndicator s.reference i g r) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact no_entry_no_previous_choice s g hzero r ht i
    rw [hsum, mul_zero]
  · have hz : partialDuration s.reference s.clock r = 0 :=
      PSChoiceMachine.partialDuration_eq_zero (liftedProfile s.reference) r (le_of_not_gt ht)
    rw [hz, zero_mul]

theorem untouched_residual_eq_quota (reference : ReplicaPS.Profile m q)
    (n : ℕ) (w : Fin n → Fin m) (g : Fin m) (hg : ∀ i, w i ≠ g) :
    residual ((initialState reference).evolve n w).reference
      ((initialState reference).evolve n w).clock g = q := by
  rw [residual_eq, no_entry_consumption_zero _ g (untouched_entryCount_zero reference n w g hg),
    sub_zero]

end ProbabilisticSerial.ReplicaUntouched
