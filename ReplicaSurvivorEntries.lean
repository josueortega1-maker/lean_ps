import ReplicaRawClock
import RawSubsetCounts

/-! Surviving type entries have distinct agents on the actual PS history. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaSurvivorEntries
open ReplicaPS ReplicaRevelation ReplicaChoiceMachine ReplicaRawStep ReplicaRawProcess

variable {m q : ℕ} [Nonempty (Fin (m * q))]

def survivorAgents (profile : ReplicaPS.Profile m q) (depth : ℕ) (S : Finset (Fin m)) :
    List (Fin (m * q)) :=
  ((revealHistory profile depth).filter (fun r => decide (r.chosen ∈ S))).map Reveal.agent

lemma survivorAgents_succ (profile : ReplicaPS.Profile m q) (depth : ℕ) (S : Finset (Fin m)) :
    survivorAgents profile (depth + 1) S =
      if stochasticRecording (history profile depth) = true then
        if typeOf (answer profile (history profile depth)) ∈ S then
          survivorAgents profile depth S ++ [PSChoiceMachine.queryAgent (history profile depth)]
        else survivorAgents profile depth S
      else survivorAgents profile depth S := by
  by_cases hs : stochasticRecording (history profile depth) = true
  · by_cases hg : typeOf (answer profile (history profile depth)) ∈ S
    all_goals simp [survivorAgents, revealHistory_succ, revealStep, hs, hg, List.filter_append]
  · simp [survivorAgents, revealHistory_succ, revealStep, hs, List.filter_append]

lemma fresh_agent_not_mem (profile : ReplicaPS.Profile m q) (depth : ℕ) (S : Finset (Fin m))
    (hs : stochasticRecording (history profile depth) = true)
    (hS : S ⊆ queryTypes (history profile depth)) :
    PSChoiceMachine.queryAgent (history profile depth) ∉ survivorAgents profile depth S := by
  intro hi
  obtain ⟨r, hr, ha⟩ := List.mem_map.mp hi
  obtain ⟨hr, hg⟩ := List.mem_filter.mp hr
  have hgS : r.chosen ∈ S := of_decide_eq_true hg
  have h := fresh_query_admissible profile depth hs r hr ha (hS hgS)
  exact Finset.not_mem_erase r.chosen r.available h

theorem survivorAgents_nodup (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (S : Finset (Fin m)) (hS : S ⊆ queryTypes (history profile depth)) :
    (survivorAgents profile depth S).Nodup := by
  induction depth generalizing S with
  | zero => simp [survivorAgents]
  | succ depth ih =>
      have hnest : queryTypes (history profile (depth + 1)) ⊆ queryTypes (history profile depth) := by
        rw [queryTypes_at_depth, queryTypes_at_depth]
        exact roundTypes_subset _ (Nat.div_le_div_right (Nat.le_succ depth))
      have hS' := hS.trans hnest
      have hold := ih S hS'
      rw [survivorAgents_succ]
      by_cases hs : stochasticRecording (history profile depth) = true
      · rw [if_pos hs]
        by_cases hg : typeOf (answer profile (history profile depth)) ∈ S
        · rw [if_pos hg, List.nodup_append_comm]
          simp only [List.singleton_append, List.nodup_cons]
          exact ⟨fresh_agent_not_mem profile depth S hs hS', hold⟩
        · simpa only [if_neg hg] using hold
      · simpa only [if_neg hs] using hold

theorem survivorAgents_length_le (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (S : Finset (Fin m)) (hS : S ⊆ queryTypes (history profile depth)) :
    (survivorAgents profile depth S).length ≤ m * q := by
  have h := (survivorAgents profile depth S).toFinset.card_le_univ
  rw [List.toFinset_card_of_nodup (survivorAgents_nodup profile depth S hS)] at h
  simpa using h

theorem revealHistory_eq_of_history_eq (reference other : ReplicaPS.Profile m q) (depth : ℕ) :
    history reference depth = history other depth →
      revealHistory reference depth = revealHistory other depth := by
  induction depth with
  | zero => intro h; rfl
  | succ depth ih =>
      intro h
      change answer reference (history reference depth) :: history reference depth =
        answer other (history other depth) :: history other depth at h
      obtain ⟨hans, hprev⟩ := List.cons.inj h
      have ha : answer reference (history other depth) = answer other (history other depth) := by
        simpa only [hprev] using hans
      rw [revealHistory_succ, revealHistory_succ, ih hprev]
      simp only [revealStep, hprev, ha]

theorem nextQueryDepth_reveals (reference : ReplicaPS.Profile m q) (fuel depth : ℕ) :
    revealHistory reference (nextQueryDepth reference fuel depth) = revealHistory reference depth := by
  induction fuel generalizing depth with
  | zero => rfl
  | succ fuel ih =>
      unfold nextQueryDepth
      split_ifs with h
      · rfl
      · have hs : stochasticRecording (history reference depth) = false :=
          Bool.eq_false_of_not_eq_true (fun ht => h (Or.inr ht))
        rw [ih, revealHistory_succ, revealStep_eq_none reference depth hs]
        simp

def entryCount (s : State m q) (S : Finset (Fin m)) : ℕ :=
  (survivorAgents s.reference s.depth S).length

@[simp] theorem entryCount_normalize (s : State m q) (S : Finset (Fin m)) :
    entryCount s.normalize S = entryCount s S := by
  unfold entryCount survivorAgents State.normalize
  rw [nextQueryDepth_reveals]

theorem entryCount_le_agents (s : State m q) (S : Finset (Fin m))
    (hS : S ⊆ s.active) : entryCount s S ≤ m * q :=
  survivorAgents_length_le s.reference s.depth S hS

theorem entryCount_child (s : State m q)
    (hs : stochasticRecording (history s.reference s.depth) = true)
    (g : Fin m) (hg : g ∈ available s.reference s.depth) (S : Finset (Fin m)) :
    entryCount (s.child hs g hg) S = entryCount s S + if g ∈ S then 1 else 0 := by
  let other := (s.child hs g hg).reference
  have hp : other ∈ acceptedFiber s.reference s.depth g :=
    (acceptedFiber_nonempty s.reference s.depth hs g hg).choose_spec
  obtain ⟨hp, htype⟩ := Finset.mem_filter.mp hp
  have hh : history other s.depth = history s.reference s.depth := (Finset.mem_filter.mp hp).2
  have hs' : stochasticRecording (history other s.depth) = true := by rw [hh]; exact hs
  have ht : typeOf (answer other (history other s.depth)) = g := by
    change typeOf (answer other (history s.reference s.depth)) = g at htype
    rwa [hh]
  have hold : survivorAgents other s.depth S = survivorAgents s.reference s.depth S := by
    unfold survivorAgents
    rw [revealHistory_eq_of_history_eq other s.reference s.depth hh]
  change (survivorAgents other (s.depth + 1) S).length = _
  rw [survivorAgents_succ, if_pos hs', ht, hold]
  by_cases hgS : g ∈ S <;> simp [hgS, entryCount]

lemma terminal_active_empty (s : State m q) (ht : (m * q) * (m * q) ≤ s.depth) :
    s.active = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hA
  have hactive := s.active_on_fiber s.reference s.reference_mem_fiber
  rw [hactive] at hA
  have htime := (roundTime_lt_one_iff s.reference (s.depth / (m * q))).2 hA
  rw [← s.clock_eq_roundTime, s.terminal_clock ht] at htime
  exact lt_irrefl _ htime

/-- The count increases by one exactly when the next raw label is in the
survivor set. Rejected labels cannot belong to a later active set. -/
theorem entryCount_step_survivor (s : State m q) (g : Fin m) (S : Finset (Fin m))
    (hS : S ⊆ (s.step g).active) :
    entryCount (s.step g) S = entryCount s S + if g ∈ S then 1 else 0 := by
  by_cases ht : (m * q) * (m * q) ≤ s.normalize.depth
  · have heq : s.step g = s.normalize := by simp [State.step, ht]
    have hempty := terminal_active_empty s.normalize ht
    have hgS : g ∉ S := by
      intro hg
      have h := hS hg
      rw [heq, hempty] at h
      exact Finset.not_mem_empty _ h
    rw [heq, entryCount_normalize]
    simp [hgS]
  · have hs := s.normalize_ready.resolve_left ht
    by_cases hg : g ∈ available s.normalize.reference s.normalize.depth
    · have heq : s.step g = (s.normalize.child hs g hg).normalize := by
        simp [State.step, ht, hs, hg]
      rw [heq, entryCount_normalize, entryCount_child, entryCount_normalize]
    · have heq : s.step g = s.normalize := by simp [State.step, ht, hs, hg]
      have hgS : g ∉ S := by
        intro h
        have hmem := hS h
        rw [heq] at hmem
        exact hg hmem
      rw [heq, entryCount_normalize]
      simp [hgS]

theorem entryCount_evolve_survivor (s : State m q) (n : ℕ) (w : Fin n → Fin m)
    (S : Finset (Fin m)) (hS : S ⊆ (s.evolve n w).active) :
    entryCount (s.evolve n w) S = entryCount s S +
      ∑ i : Fin n, if w i ∈ S then (1 : ℕ) else 0 := by
  induction n with
  | zero => simp [State.evolve]
  | succ n ih =>
      change entryCount ((s.evolve n (Fin.tail w)).step (w 0)) S = _
      have hprev : S ⊆ (s.evolve n (Fin.tail w)).active :=
        hS.trans ((s.evolve n (Fin.tail w)).step_active_subset (w 0))
      rw [entryCount_step_survivor _ _ _ hS, ih (Fin.tail w) hprev]
      simp only [Fin.sum_univ_succ, Fin.tail]
      omega

theorem raw_count_survivor_le_agents (reference : ReplicaPS.Profile m q)
    (n : ℕ) (w : Fin n → Fin m) (S : Finset (Fin m))
    (hS : S ⊆ ((initialState reference).evolve n w).active) :
    RawSubsetCounts.count S w ≤ (m * q : ℕ) := by
  have heq := entryCount_evolve_survivor (initialState reference) n w S hS
  have hzero : entryCount (initialState reference) S = 0 := by
    simp [entryCount, initialState, survivorAgents]
  rw [hzero, zero_add] at heq
  have hbound := entryCount_le_agents ((initialState reference).evolve n w) S hS
  rw [heq] at hbound
  unfold RawSubsetCounts.count RawSubsetCounts.hit
  exact_mod_cast hbound

theorem raw_count_survivor_eq_entries (reference : ReplicaPS.Profile m q)
    (n : ℕ) (w : Fin n → Fin m) (S : Finset (Fin m))
    (hS : S ⊆ ((initialState reference).evolve n w).active) :
    RawSubsetCounts.count S w = (entryCount ((initialState reference).evolve n w) S : ℝ) := by
  have heq := entryCount_evolve_survivor (initialState reference) n w S hS
  have hzero : entryCount (initialState reference) S = 0 := by
    simp [entryCount, initialState, survivorAgents]
  rw [hzero, zero_add] at heq
  unfold RawSubsetCounts.count RawSubsetCounts.hit
  exact_mod_cast heq.symm

theorem fresh_entryCount_succ_le_agents (s : State m q) (S : Finset (Fin m))
    (hs : stochasticRecording (history s.reference s.depth) = true)
    (hS : S ⊆ s.active) : entryCount s S + 1 ≤ m * q := by
  let agents := PSChoiceMachine.queryAgent (history s.reference s.depth) ::
    survivorAgents s.reference s.depth S
  have hnodup : agents.Nodup := List.nodup_cons.mpr
    ⟨fresh_agent_not_mem s.reference s.depth S hs hS,
      survivorAgents_nodup s.reference s.depth S hS⟩
  have h := agents.toFinset.card_le_univ
  rw [List.toFinset_card_of_nodup hnodup] at h
  simpa [agents, entryCount] using h

/-- The last draw in a phase is counted even if normalization immediately
advances past the exhaustion at the end of that phase. -/
theorem raw_count_before_step_le_agents (reference : ReplicaPS.Profile m q)
    (n : ℕ) (w : Fin (n + 1) → Fin m) (S : Finset (Fin m))
    (hs : stochasticRecording (history
      ((initialState reference).evolve n (Fin.tail w)).normalize.reference
      ((initialState reference).evolve n (Fin.tail w)).normalize.depth) = true)
    (hS : S ⊆ ((initialState reference).evolve n (Fin.tail w)).normalize.active) :
    RawSubsetCounts.count S w ≤ (m * q : ℕ) := by
  let s := (initialState reference).evolve n (Fin.tail w)
  have hS' : S ⊆ s.active := hS.trans s.normalize_active_subset
  have heq := raw_count_survivor_eq_entries reference n (Fin.tail w) S hS'
  have hb := fresh_entryCount_succ_le_agents s.normalize S hs hS
  rw [entryCount_normalize] at hb
  have hbR : (entryCount s S : ℝ) + 1 ≤ (m * q : ℕ) := by exact_mod_cast hb
  have hhit : RawSubsetCounts.hit S (w 0) ≤ 1 := by
    unfold RawSubsetCounts.hit
    split_ifs <;> norm_num
  have hcount : RawSubsetCounts.count S w =
      RawSubsetCounts.hit S (w 0) + RawSubsetCounts.count S (Fin.tail w) :=
    Fin.sum_univ_succ _
  rw [hcount, heq]
  linarith

end ProbabilisticSerial.ReplicaSurvivorEntries
