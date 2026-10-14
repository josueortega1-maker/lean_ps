import PhaseAdapter
import Mathlib.Algebra.BigOperators.Field

/-!
# A history-indexed choice machine for probabilistic serial

The labelled concentration theorem in `LoadBound` expects one total query
policy indexed only by earlier good labels.  This file constructs that policy.
One round contains exactly `n` labels and represents one PS eating phase.
An agent whose previous good survives makes a deterministic singleton query;
a displaced agent makes a fresh query from the current active set.  Hence at
most `n` rounds, or `n^2` labels, contain the complete PS trace.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PSChoiceMachine

open UniformPermutation PSProcess SequentialRevelation AdaptiveCategorical
  StoppedChoices LoadBound

variable {n : ℕ}

/-! ## Event-driven supply update from a supplied choice vector -/

def choiceConsumers (choice : Fin n → Fin n) (g : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => choice i = g)

def choiceDemand (choice : Fin n → Fin n) (g : Fin n) : ℕ :=
  (choiceConsumers choice g).card

def choiceDemandedGoods (q : SupplyState n) (choice : Fin n → Fin n) :
    Finset (Fin n) :=
  (activeGoods q).filter (fun g => 0 < choiceDemand choice g)

def choiceNextDelay (q : SupplyState n) (choice : Fin n → Fin n) : ℝ :=
  if hD : (choiceDemandedGoods q choice).Nonempty then
    ((choiceDemandedGoods q choice).image
      (fun g => q g / (choiceDemand choice g : ℝ))).min' (hD.image _)
  else 0

def choiceStepState (q : SupplyState n) (choice : Fin n → Fin n) :
    SupplyState n :=
  fun g => q g - choiceNextDelay q choice * (choiceDemand choice g : ℝ)

lemma choiceDemand_eq_demand (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) :
    choiceDemand (fun i => favorite (profile i) (activeGoods q) hA) =
      demand profile q hA := by
  funext g
  rfl

lemma choiceDemandedGoods_eq (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) :
    choiceDemandedGoods q
        (fun i => favorite (profile i) (activeGoods q) hA) =
      demandedGoods profile q hA := by
  rfl

lemma choiceNextDelay_eq (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) :
    choiceNextDelay q
        (fun i => favorite (profile i) (activeGoods q) hA) =
      nextDelay profile q hA := by
  have hD : (choiceDemandedGoods q
      (fun i => favorite (profile i) (activeGoods q) hA)).Nonempty := by
    rw [choiceDemandedGoods_eq profile q hA]
    exact demandedGoods_nonempty profile q hA
  rw [choiceNextDelay, dif_pos hD]
  unfold nextDelay
  congr

lemma choiceStepState_eq (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) :
    choiceStepState q
        (fun i => favorite (profile i) (activeGoods q) hA) =
      stepState profile q hA := by
  funext g
  simp only [choiceStepState, stepState, choiceNextDelay_eq,
    choiceDemand_eq_demand]

/-! ## Reading completed rounds from a newest-first labelled history -/

variable [Nonempty (Fin n)]

def defaultGood : Fin n := Classical.choice inferInstance

def tapeGet (tape : List (Fin n)) (k : ℕ) : Fin n :=
  tape.getD k defaultGood

def tapeChoice (tape : List (Fin n)) (round : ℕ) : Fin n → Fin n :=
  fun i => tapeGet tape (round * n + i.val)

def supplyAtRound (tape : List (Fin n)) : ℕ → SupplyState n
  | 0 => initialState n
  | round + 1 =>
      choiceStepState (supplyAtRound tape round) (tapeChoice tape round)

def roundIndex (history : History (Fin n)) : ℕ := history.length / n

def roundOffset (history : History (Fin n)) : ℕ := history.length % n

def queryAgent (history : History (Fin n)) : Fin n :=
  ⟨roundOffset history, by
    have hn : 0 < n := by
      simpa using
        (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin n)))
    exact Nat.mod_lt _ hn⟩

def querySupply (history : History (Fin n)) : SupplyState n :=
  supplyAtRound history.reverse (roundIndex history)

def queryActive (history : History (Fin n)) : Finset (Fin n) :=
  activeGoods (querySupply history)

def previousChoice (history : History (Fin n)) : Option (Fin n) :=
  if hround : 0 < roundIndex history then
    some (tapeChoice history.reverse (roundIndex history - 1)
      (queryAgent history))
  else none

/-- A query is fresh exactly in the initial round or when the agent's previous
choice is no longer active. -/
def FreshQuery (history : History (Fin n)) : Prop :=
  match previousChoice history with
  | none => True
  | some g => g ∉ queryActive history

instance freshQueryDecidable (history : History (Fin n)) :
    Decidable (FreshQuery history) := by
  unfold FreshQuery
  split <;> infer_instance

/-- Total query policy.  After termination a singleton is a deterministic fallback;
during a nonfresh step the singleton query has probability one. -/
def queryAvailable (history : History (Fin n)) : Finset (Fin n) :=
  if hactive : (queryActive history).Nonempty then
    match previousChoice history with
    | none => queryActive history
    | some g => if g ∈ queryActive history then {g} else queryActive history
  else {defaultGood}

lemma queryAvailable_nonempty (history : History (Fin n)) :
    (queryAvailable history).Nonempty := by
  unfold queryAvailable
  split
  next hactive =>
    split
    next hprev => exact hactive
    next g hprev =>
      split
      next hg => exact Finset.singleton_nonempty _
      next hg => exact hactive
  next hactive => exact Finset.singleton_nonempty _

def machineWeight (history : History (Fin n)) (g : Fin n) : ℝ :=
  StoppedChoices.uniformChoiceWeight (queryAvailable (n := n)) history g

lemma machineWeight_valid : ValidLaw (machineWeight (n := n)) :=
  StoppedChoices.uniformChoiceWeight_valid (queryAvailable (n := n))
    queryAvailable_nonempty

/-- Only fresh, nonterminal labels carry new preference information. -/
def stochasticRecording (history : History (Fin n)) : Bool :=
  decide ((queryActive history).Nonempty ∧ FreshQuery history)

/-- The next label generated by a full preference profile. -/
def profileAnswer (profile : Profile n) (history : History (Fin n)) : Fin n :=
  favorite (profile (queryAgent history)) (queryAvailable history)
    (queryAvailable_nonempty history)

def profileHistory (profile : Profile n) : ℕ → History (Fin n)
  | 0 => []
  | depth + 1 =>
      profileAnswer profile (profileHistory profile depth) ::
        profileHistory profile depth

@[simp] lemma profileHistory_zero (profile : Profile n) :
    profileHistory profile 0 = [] := rfl

@[simp] lemma profileHistory_succ (profile : Profile n) (depth : ℕ) :
    profileHistory profile (depth + 1) =
      profileAnswer profile (profileHistory profile depth) ::
        profileHistory profile depth := rfl

lemma profileAnswer_mem (profile : Profile n) (history : History (Fin n)) :
    profileAnswer profile history ∈ queryAvailable history :=
  favorite_mem _ _ _

def ValidMachineHistory : History (Fin n) → Prop
  | [] => True
  | g :: history =>
      ValidMachineHistory history ∧ g ∈ queryAvailable history

instance validMachineHistoryDecidable :
    DecidablePred (ValidMachineHistory (n := n)) := by
  intro history
  induction history with
  | nil => exact instDecidableTrue
  | cons g history ih =>
      rw [ValidMachineHistory]
      infer_instance

lemma profileHistory_valid (profile : Profile n) :
    ∀ depth, ValidMachineHistory (profileHistory profile depth) := by
  intro depth
  induction depth with
  | zero => trivial
  | succ depth ih => exact ⟨ih, profileAnswer_mem profile _⟩

@[simp] lemma profileHistory_length (profile : Profile n) (depth : ℕ) :
    (profileHistory profile depth).length = depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [profileHistory, ih]

lemma profileHistory_reverse_succ (profile : Profile n) (depth : ℕ) :
    (profileHistory profile (depth + 1)).reverse =
      (profileHistory profile depth).reverse ++
        [profileAnswer profile (profileHistory profile depth)] := by
  simp [profileHistory]

lemma tapeGet_append_singleton_at_length (tape : List (Fin n)) (g : Fin n) :
    tapeGet (tape ++ [g]) tape.length = g := by
  induction tape with
  | nil => simp [tapeGet]
  | cons a tape ih => simpa [tapeGet] using ih

lemma tapeGet_append_singleton_of_lt (tape : List (Fin n)) (g : Fin n)
    {k : ℕ} (hk : k < tape.length) :
    tapeGet (tape ++ [g]) k = tapeGet tape k := by
  induction tape generalizing k with
  | nil => simp at hk
  | cons a tape ih =>
      cases k with
      | zero => simp [tapeGet]
      | succ k =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
          simpa [tapeGet] using ih hk

/-- The chronological tape at position `k` contains exactly the answer made
after the first `k` labels. -/
lemma tapeGet_profileHistory_reverse (profile : Profile n) {depth k : ℕ}
    (hk : k < depth) :
    tapeGet (profileHistory profile depth).reverse k =
      profileAnswer profile (profileHistory profile k) := by
  induction depth with
  | zero => omega
  | succ depth ih =>
      rw [profileHistory_reverse_succ]
      by_cases hkd : k < depth
      · rw [tapeGet_append_singleton_of_lt _ _
          (by simpa using hkd)]
        exact ih hkd
      · have hkeq : k = depth := by omega
        subst k
        simpa using tapeGet_append_singleton_at_length
          (profileHistory profile depth).reverse
          (profileAnswer profile (profileHistory profile depth))

/-! ## A total reference recursion for the genuine PS supply states -/

def profileSupply (profile : Profile n) : ℕ → SupplyState n
  | 0 => initialState n
  | round + 1 =>
      let q := profileSupply profile round
      if hA : (activeGoods q).Nonempty then
        stepState profile q hA
      else q

lemma profileSupply_valid (profile : Profile n) :
    ∀ round, ValidState (profileSupply profile round) := by
  intro round
  induction round with
  | zero => exact initialState_valid n
  | succ round ih =>
      rw [profileSupply]
      split
      next hA => exact stepState_valid profile _ ih hA
      next hA => exact ih

lemma profileSupply_active_subset (profile : Profile n) (round : ℕ) :
    activeGoods (profileSupply profile (round + 1)) ⊆
      activeGoods (profileSupply profile round) := by
  rw [profileSupply]
  split
  next hA => exact activeGoods_step_subset profile _ hA
  next hA => exact Finset.Subset.rfl

lemma favorite_congr_set (sigma : UniformPermutation.PreferenceOrder n)
    (S T : Finset (Fin n)) (hS : S.Nonempty) (hT : T.Nonempty)
    (hST : S = T) : favorite sigma S hS = favorite sigma T hT := by
  subst T
  rfl

lemma round_slot_div (round : ℕ) (i : Fin n) :
    (round * n + i.val) / n = round := by
  have hn : 0 < n := by
    simpa using (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (Fin n)))
  rw [Nat.mul_comm round n, Nat.mul_add_div hn,
    Nat.div_eq_of_lt i.isLt, Nat.add_zero]

lemma round_slot_mod (round : ℕ) (i : Fin n) :
    (round * n + i.val) % n = i.val := by
  rw [Nat.mul_comm round n, Nat.mul_add_mod,
    Nat.mod_eq_of_lt i.isLt]

/-- Along a profile-generated path, completed machine rounds are exactly the
event-driven PS supply recursion, and every answer in a nonterminal round is
the agent's genuine favourite among the active goods. -/
theorem profile_machine_correspondence (profile : Profile n) :
    ∀ depth,
      querySupply (profileHistory profile depth) =
          profileSupply profile (depth / n) ∧
        ∀ hA : (activeGoods (profileSupply profile (depth / n))).Nonempty,
          profileAnswer profile (profileHistory profile depth) =
            favorite (profile (queryAgent (profileHistory profile depth)))
              (activeGoods (profileSupply profile (depth / n))) hA := by
  intro depth
  induction depth using Nat.strong_induction_on with
  | h depth ih =>
      have hn : 0 < n := by
        simpa using (Fintype.card_pos_iff.mpr
          (inferInstance : Nonempty (Fin n)))
      have hsupply :
          supplyAtRound (profileHistory profile depth).reverse (depth / n) =
            profileSupply profile (depth / n) := by
        have hinner : ∀ rounds, rounds ≤ depth / n →
            supplyAtRound (profileHistory profile depth).reverse rounds =
              profileSupply profile rounds := by
          intro rounds hrounds
          induction rounds with
          | zero => simp [supplyAtRound, profileSupply]
          | succ round ihr =>
              have hroundLe : round ≤ depth / n := by omega
              have hfull : (round + 1) * n ≤ depth :=
                (Nat.le_div_iff_mul_le hn).mp hrounds
              rw [supplyAtRound, ihr hroundLe, profileSupply]
              split
              next hA =>
                have hchoice :
                    tapeChoice (profileHistory profile depth).reverse round =
                      fun i => favorite (profile i)
                        (activeGoods (profileSupply profile round)) hA := by
                  funext i
                  unfold tapeChoice
                  have hslot : round * n + i.val < depth := by
                    have hi : round * n + i.val < (round + 1) * n := by
                      simp only [Nat.add_mul, Nat.one_mul]
                      omega
                    exact hi.trans_le hfull
                  rw [tapeGet_profileHistory_reverse profile hslot]
                  have hiCorr := ih (round * n + i.val) hslot
                  have hiDiv := round_slot_div round i
                  have hiAgent :
                      queryAgent (profileHistory profile
                        (round * n + i.val)) = i := by
                    apply Fin.ext
                    simp only [queryAgent, roundOffset,
                      profileHistory_length]
                    exact round_slot_mod round i
                  rw [hiDiv] at hiCorr
                  simpa [hiAgent] using hiCorr.2 hA
                rw [hchoice, choiceStepState_eq profile _ hA]
              next hA =>
                have hempty : activeGoods (profileSupply profile round) = ∅ :=
                  Finset.not_nonempty_iff_eq_empty.mp hA
                funext g
                simp [choiceStepState, choiceNextDelay, choiceDemandedGoods,
                  hempty]
        exact hinner (depth / n) le_rfl
      refine ⟨?_, ?_⟩
      · simpa [querySupply, roundIndex, profileHistory_length] using hsupply
      · intro hA
        let history := profileHistory profile depth
        let round := depth / n
        have hactive : queryActive history =
            activeGoods (profileSupply profile round) := by
          simp [queryActive, querySupply, history, round, roundIndex,
            profileHistory_length, hsupply]
        by_cases hround : round = 0
        · have hprev : previousChoice history = none := by
            simp [previousChoice, roundIndex, history, profileHistory_length,
              round, hround]
          have hqueryA : (queryActive history).Nonempty := by
            rw [hactive]
            exact hA
          change profileAnswer profile history =
            favorite (profile (queryAgent history))
              (activeGoods (profileSupply profile round)) hA
          have havailable : queryAvailable history =
              activeGoods (profileSupply profile round) := by
            unfold queryAvailable
            rw [dif_pos hqueryA, hprev, hactive]
          exact favorite_congr_set _ _ _ _ _ havailable
        · have hroundPos : 0 < round := Nat.pos_of_ne_zero hround
          let agent := queryAgent history
          let oldDepth := (round - 1) * n + agent.val
          have hroundMul : round * n ≤ depth := by
            exact Nat.div_mul_le_self depth n
          have holdLtRound : oldDepth < round * n := by
            dsimp [oldDepth]
            have hr : round - 1 + 1 = round := by omega
            calc
              (round - 1) * n + agent.val <
                  (round - 1 + 1) * n := by
                simp only [Nat.add_mul, Nat.one_mul]
                omega
              _ = round * n := by rw [hr]
          have holdDepth : oldDepth < depth := holdLtRound.trans_le hroundMul
          have holdDiv : oldDepth / n = round - 1 := by
            exact round_slot_div (round - 1) agent
          have holdAnswer := (ih oldDepth holdDepth).2
          have hprevActive :
              (activeGoods (profileSupply profile (round - 1))).Nonempty := by
            refine ⟨hA.choose, ?_⟩
            have hsubset := profileSupply_active_subset profile (round - 1)
            have hr : round - 1 + 1 = round := by omega
            rw [hr] at hsubset
            exact hsubset hA.choose_spec
          have hold : tapeChoice history.reverse (round - 1) agent =
              favorite (profile agent)
                (activeGoods (profileSupply profile (round - 1)))
                hprevActive := by
            unfold tapeChoice
            rw [tapeGet_profileHistory_reverse profile holdDepth]
            have hiAgent : queryAgent (profileHistory profile oldDepth) = agent := by
              apply Fin.ext
              simp only [queryAgent, roundOffset, profileHistory_length]
              simpa [oldDepth] using Nat.mod_eq_of_lt agent.isLt
            rw [holdDiv] at holdAnswer
            simpa [hiAgent] using holdAnswer hprevActive
          have hprev : previousChoice history =
              some (tapeChoice history.reverse (round - 1) agent) := by
            simp [previousChoice, roundIndex, history, profileHistory_length,
              round, hroundPos, agent]
          let old := tapeChoice history.reverse (round - 1) agent
          have hqueryA : (queryActive history).Nonempty := by
            rw [hactive]
            exact hA
          by_cases holdMem : old ∈ activeGoods (profileSupply profile round)
          · have hsubset := profileSupply_active_subset profile (round - 1)
            have hr : round - 1 + 1 = round := by omega
            rw [hr] at hsubset
            have hfavorite :
                favorite (profile agent)
                    (activeGoods (profileSupply profile round)) hA = old := by
              calc
                favorite (profile agent)
                    (activeGoods (profileSupply profile round)) hA =
                    favorite (profile agent)
                      (activeGoods (profileSupply profile (round - 1)))
                        hprevActive :=
                  favorite_of_mem_of_subset (profile agent)
                    hprevActive hA hsubset (by
                      change favorite (profile agent)
                          (activeGoods (profileSupply profile (round - 1)))
                            hprevActive ∈
                        activeGoods (profileSupply profile round)
                      rw [← hold]
                      exact holdMem)
                _ = old := hold.symm
            change profileAnswer profile history =
              favorite (profile (queryAgent history))
                (activeGoods (profileSupply profile round)) hA
            have havailable : queryAvailable history = {old} := by
              unfold queryAvailable
              rw [dif_pos hqueryA, hprev]
              simp only
              rw [if_pos (by simpa [old, hactive] using holdMem)]
            calc
              profileAnswer profile history =
                  favorite (profile (queryAgent history)) {old}
                    (Finset.singleton_nonempty old) :=
                favorite_congr_set _ _ _ _ _ havailable
              _ = old := Finset.mem_singleton.mp (favorite_mem _ _ _)
              _ = favorite (profile (queryAgent history))
                    (activeGoods (profileSupply profile round)) hA := by
                simpa [agent] using hfavorite.symm
          · change profileAnswer profile history =
              favorite (profile (queryAgent history))
                (activeGoods (profileSupply profile round)) hA
            have havailable : queryAvailable history =
                activeGoods (profileSupply profile round) := by
              unfold queryAvailable
              rw [dif_pos hqueryA, hprev]
              simp only
              rw [if_neg (by simpa [old, hactive] using holdMem), hactive]
            exact favorite_congr_set _ _ _ _ _ havailable

/-! ## Identifying the total recursion with the phases stored by `run` -/

theorem runFrom_profileSupply_phase_index (profile : Profile n) (start : ℕ) :
    ∀ p ∈ (runFrom profile (profileSupply profile start)
        (profileSupply_valid profile start)).phases,
      ∃ offset,
        offset < (activeGoods (profileSupply profile start)).card ∧
        p.before = profileSupply profile (start + offset) := by
  rw [runFrom]
  split
  next hA =>
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with hp | hp
    · subst p
      refine ⟨0, Finset.card_pos.mpr hA, ?_⟩
      simp
    · have hnext : profileSupply profile (start + 1) =
          stepState profile (profileSupply profile start) hA := by
        simp [profileSupply, hA]
      have hp' : p ∈ (runFrom profile (profileSupply profile (start + 1))
          (profileSupply_valid profile (start + 1))).phases := by
        simpa [hnext] using hp
      obtain ⟨offset, hoffset, hpBefore⟩ :=
        runFrom_profileSupply_phase_index profile (start + 1) p hp'
      refine ⟨offset + 1, ?_, ?_⟩
      · have hstrict :
            (activeGoods (profileSupply profile (start + 1))).card <
              (activeGoods (profileSupply profile start)).card := by
            simpa [hnext] using
              activeGoods_step_card_lt profile (profileSupply profile start) hA
        omega
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpBefore
  next hA =>
    simp
termination_by (activeGoods (profileSupply profile start)).card
decreasing_by
  rw [profileSupply]
  split
  · apply activeGoods_step_card_lt
  · contradiction

theorem run_phase_profileSupply_index (profile : Profile n) (hn : 0 < n)
    (p : Phase n profile) (hp : p ∈ (run profile).phases) :
    ∃ round < n, p.before = profileSupply profile round := by
  have hindexed := runFrom_profileSupply_phase_index profile 0 p (by
    simpa [run, profileSupply] using hp)
  obtain ⟨round, hroundLength, hpBefore⟩ := hindexed
  refine ⟨round, ?_, ?_⟩
  · simpa [profileSupply, activeGoods_initial] using hroundLength
  · simpa using hpBefore

theorem queryAtRound_eq_phase (profile : Profile n) (hn : 0 < n)
    (p : Phase n profile) (hp : p ∈ (run profile).phases) :
    ∃ round < n,
      querySupply (profileHistory profile (round * n)) = p.before ∧
      queryActive (profileHistory profile (round * n)) = p.active := by
  obtain ⟨round, hround, hpBefore⟩ :=
    run_phase_profileSupply_index profile hn p hp
  refine ⟨round, hround, ?_, ?_⟩
  · rw [(profile_machine_correspondence profile (round * n)).1]
    simpa [Nat.mul_div_cancel round hn] using hpBefore.symm
  · unfold queryActive Phase.active
    rw [(profile_machine_correspondence profile (round * n)).1]
    simpa [Nat.mul_div_cancel round hn] using congrArg activeGoods hpBefore.symm

/-! ## Canonical slots and stopped recordings -/

def setRecording (B : Finset (Fin n)) (history : History (Fin n)) : Bool :=
  stochasticRecording history && decide (B ⊆ queryActive history)

def setEntry (B : Finset (Fin n)) :
    History (Fin n) → Fin n → Bool :=
  stoppedEntry B (setRecording B)

lemma queryAgent_at_slot (profile : Profile n) (round : ℕ) (i : Fin n) :
    queryAgent (profileHistory profile (round * n + i.val)) = i := by
  apply Fin.ext
  simp only [queryAgent, roundOffset, profileHistory_length]
  exact round_slot_mod round i

lemma querySupply_at_slot (profile : Profile n) (round : ℕ) (i : Fin n) :
    querySupply (profileHistory profile (round * n + i.val)) =
      profileSupply profile round := by
  rw [(profile_machine_correspondence profile (round * n + i.val)).1]
  rw [round_slot_div]

lemma queryActive_at_slot (profile : Profile n) (round : ℕ) (i : Fin n) :
    queryActive (profileHistory profile (round * n + i.val)) =
      activeGoods (profileSupply profile round) := by
  unfold queryActive
  rw [querySupply_at_slot]

lemma profileAnswer_at_slot (profile : Profile n) (round : ℕ) (i : Fin n)
    (hA : (activeGoods (profileSupply profile round)).Nonempty) :
    profileAnswer profile (profileHistory profile (round * n + i.val)) =
      favorite (profile i) (activeGoods (profileSupply profile round)) hA := by
  have hcorr := (profile_machine_correspondence profile
    (round * n + i.val)).2
  rw [round_slot_div] at hcorr
  simpa [queryAgent_at_slot] using hcorr hA

lemma previousChoice_at_slot_zero (profile : Profile n) (i : Fin n) :
    previousChoice (profileHistory profile i.val) = none := by
  simp [previousChoice, roundIndex, profileHistory_length,
    Nat.div_eq_of_lt i.isLt]

lemma previousChoice_at_slot_succ (profile : Profile n) (round : ℕ)
    (i : Fin n)
    (hA : (activeGoods (profileSupply profile (round + 1))).Nonempty) :
    previousChoice
        (profileHistory profile ((round + 1) * n + i.val)) =
      some (favorite (profile i) (activeGoods (profileSupply profile round))
        (by
          have hnext := profileSupply_active_subset profile round
          exact ⟨hA.choose, hnext hA.choose_spec⟩)) := by
  have hn : 0 < n := by
    simpa using (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (Fin n)))
  let hprev : (activeGoods (profileSupply profile round)).Nonempty := by
    have hnext := profileSupply_active_subset profile round
    exact ⟨hA.choose, hnext hA.choose_spec⟩
  let history := profileHistory profile ((round + 1) * n + i.val)
  have hindex : roundIndex history = round + 1 := by
    simp [roundIndex, history, profileHistory_length, round_slot_div]
  have hagent : queryAgent history = i := by
    simpa [history] using queryAgent_at_slot profile (round + 1) i
  have hslot : round * n + i.val < (round + 1) * n + i.val := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  rw [previousChoice, dif_pos (by rw [hindex]; omega)]
  rw [hindex, Nat.add_sub_cancel, hagent]
  unfold tapeChoice
  rw [tapeGet_profileHistory_reverse profile hslot]
  exact congrArg some (profileAnswer_at_slot profile round i hprev)

lemma successes_profileHistory_add
    (X : History (Fin n) → Fin n → Bool) (profile : Profile n)
    (start count : ℕ) :
    successes X (profileHistory profile (start + count)) =
      successes X (profileHistory profile start) +
        ∑ j ∈ Finset.range count,
          if X (profileHistory profile (start + j))
              (profileAnswer profile (profileHistory profile (start + j)))
            then 1 else 0 := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [show start + Nat.succ count = (start + count) + 1 by omega,
        profileHistory_succ, successes_cons, ih, Finset.sum_range_succ]
      ring

lemma compensator_profileHistory_add
    (weight : History (Fin n) → Fin n → ℝ)
    (X : History (Fin n) → Fin n → Bool) (profile : Profile n)
    (start count : ℕ) :
    compensator weight X (profileHistory profile (start + count)) =
      compensator weight X (profileHistory profile start) +
        ∑ j ∈ Finset.range count,
          successProbability weight X
            (profileHistory profile (start + j)) := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [show start + Nat.succ count = (start + count) + 1 by omega,
        profileHistory_succ, compensator_cons, ih, Finset.sum_range_succ]
      ring

lemma initial_setEntry_eq (profile : Profile n) (B : Finset (Fin n))
    (i : Fin n) (hA : (activeGoods (profileSupply profile 0)).Nonempty)
    (hB : B ⊆ activeGoods (profileSupply profile 0)) :
    setEntry B (profileHistory profile i.val)
        (profileAnswer profile (profileHistory profile i.val)) =
      decide (favorite (profile i) (activeGoods (profileSupply profile 0)) hA
        ∈ B) := by
  have hactive : queryActive (profileHistory profile i.val) =
      activeGoods (profileSupply profile 0) := by
    simpa using queryActive_at_slot profile 0 i
  have hanswer : profileAnswer profile (profileHistory profile i.val) =
      favorite (profile i) (activeGoods (profileSupply profile 0)) hA := by
    simpa using profileAnswer_at_slot profile 0 i hA
  have hprev := previousChoice_at_slot_zero profile i
  simp [setEntry, setRecording, stoppedEntry, stochasticRecording,
    FreshQuery, hactive, hanswer, hprev, hA, hB]

lemma successor_setEntry_eq (profile : Profile n) (B : Finset (Fin n))
    (round : ℕ) (i : Fin n)
    (hA : (activeGoods (profileSupply profile (round + 1))).Nonempty)
    (hB : B ⊆ activeGoods (profileSupply profile (round + 1))) :
    setEntry B
        (profileHistory profile ((round + 1) * n + i.val))
        (profileAnswer profile
          (profileHistory profile ((round + 1) * n + i.val))) =
      decide (
        favorite (profile i) (activeGoods (profileSupply profile round))
            (by
              have hsubset := profileSupply_active_subset profile round
              exact ⟨hA.choose, hsubset hA.choose_spec⟩) ∉
          activeGoods (profileSupply profile (round + 1)) ∧
        favorite (profile i)
            (activeGoods (profileSupply profile (round + 1))) hA ∈ B) := by
  let hprevA : (activeGoods (profileSupply profile round)).Nonempty := by
    have hsubset := profileSupply_active_subset profile round
    exact ⟨hA.choose, hsubset hA.choose_spec⟩
  have hactive := queryActive_at_slot profile (round + 1) i
  have hanswer := profileAnswer_at_slot profile (round + 1) i hA
  have hprev := previousChoice_at_slot_succ profile round i hA
  simp [setEntry, setRecording, stoppedEntry, stochasticRecording,
    FreshQuery, hactive, hanswer, hprev, hA, hB, hprevA]

def roundPhase (profile : Profile n) (round : ℕ)
    (hA : (activeGoods (profileSupply profile round)).Nonempty) :
    Phase n profile :=
  ⟨profileSupply profile round, profileSupply_valid profile round, hA⟩

@[simp] lemma roundPhase_before (profile : Profile n) (round : ℕ)
    (hA : (activeGoods (profileSupply profile round)).Nonempty) :
    (roundPhase profile round hA).before = profileSupply profile round := rfl

@[simp] lemma roundPhase_active (profile : Profile n) (round : ℕ)
    (hA : (activeGoods (profileSupply profile round)).Nonempty) :
    (roundPhase profile round hA).active =
      activeGoods (profileSupply profile round) := rfl

@[simp] lemma roundPhase_choice (profile : Profile n) (round : ℕ)
    (hA : (activeGoods (profileSupply profile round)).Nonempty) (i : Fin n) :
    (roundPhase profile round hA).choice i =
      favorite (profile i) (activeGoods (profileSupply profile round)) hA := rfl

/-- The stopped labelled successes through a completed phase equal its
actual PS load on every set that is still active. -/
theorem successes_at_completed_round (profile : Profile n)
    (B : Finset (Fin n)) :
    ∀ round (hA : (activeGoods (profileSupply profile round)).Nonempty),
      B ⊆ activeGoods (profileSupply profile round) →
      successes (setEntry B)
          (profileHistory profile ((round + 1) * n)) =
        (phaseLoad B (roundPhase profile round hA) : ℝ) := by
  intro round
  induction round with
  | zero =>
      intro hA hB
      rw [show (0 + 1) * n = 0 + n by simp,
        successes_profileHistory_add (setEntry B) profile 0 n]
      simp only [profileHistory_zero, successes_nil, zero_add, Nat.zero_add]
      calc
        (∑ j ∈ Finset.range n,
            if setEntry B (profileHistory profile j)
                (profileAnswer profile (profileHistory profile j))
              then 1 else 0) =
            ∑ i : Fin n,
              if (roundPhase profile 0 hA).choice i ∈ B
                then (1 : ℝ) else 0 := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro j hj
          have hjn : j < n := Finset.mem_range.mp hj
          let i : Fin n := ⟨j, hjn⟩
          have hedge := initial_setEntry_eq profile B i hA hB
          simp only [dif_pos hjn]
          simpa [i, roundPhase_choice] using congrArg
            (fun b => if b then (1 : ℝ) else 0) hedge
        _ = ((phaseEaters B (roundPhase profile 0 hA)).card : ℝ) := by
          simp [phaseEaters]
        _ = (phaseLoad B (roundPhase profile 0 hA) : ℝ) := by
          exact_mod_cast (phaseLoad_eq_card_phaseEaters B
            (roundPhase profile 0 hA)).symm
  | succ round ih =>
      intro hA hB
      let hprevA : (activeGoods (profileSupply profile round)).Nonempty := by
        have hsubset := profileSupply_active_subset profile round
        exact ⟨hA.choose, hsubset hA.choose_spec⟩
      have hBprev : B ⊆ activeGoods (profileSupply profile round) :=
        hB.trans (profileSupply_active_subset profile round)
      have hIH := ih hprevA hBprev
      rw [show (Nat.succ round + 1) * n = (round + 1) * n + n by
        simp [Nat.succ_eq_add_one, Nat.add_mul]]
      rw [successes_profileHistory_add (setEntry B) profile
        ((round + 1) * n) n, hIH]
      have hincrement :
          (∑ j ∈ Finset.range n,
            if setEntry B
                (profileHistory profile ((round + 1) * n + j))
                (profileAnswer profile
                  (profileHistory profile ((round + 1) * n + j)))
              then 1 else 0) =
            ((transitionEntrants B
              (roundPhase profile round hprevA)
              (roundPhase profile (round + 1) hA)).card : ℝ) := by
        calc
          (∑ j ∈ Finset.range n,
              if setEntry B
                  (profileHistory profile ((round + 1) * n + j))
                  (profileAnswer profile
                    (profileHistory profile ((round + 1) * n + j)))
                then 1 else 0) =
              ∑ i : Fin n,
                if i ∈ transitionEntrants B
                    (roundPhase profile round hprevA)
                    (roundPhase profile (round + 1) hA)
                  then (1 : ℝ) else 0 := by
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro j hj
            have hjn : j < n := Finset.mem_range.mp hj
            let i : Fin n := ⟨j, hjn⟩
            have hedge := successor_setEntry_eq profile B round i hA hB
            simp only [dif_pos hjn]
            simpa [i, transitionEntrants, displacedAgents,
              roundPhase_choice, roundPhase_active] using congrArg
                (fun b => if b then (1 : ℝ) else 0) hedge
          _ = ((transitionEntrants B
                (roundPhase profile round hprevA)
                (roundPhase profile (round + 1) hA)).card : ℝ) := by
            simp
      rw [hincrement]
      have hupdate := phaseEaters_card_update B
        (roundPhase profile round hprevA)
        (roundPhase profile (round + 1) hA)
        (by simpa using profileSupply_active_subset profile round) hB
      rw [phaseLoad_eq_card_phaseEaters, phaseLoad_eq_card_phaseEaters]
      exact_mod_cast hupdate.symm

lemma initial_successProbability_eq (profile : Profile n)
    (B : Finset (Fin n)) (i : Fin n)
    (hA : (activeGoods (profileSupply profile 0)).Nonempty)
    (hB : B ⊆ activeGoods (profileSupply profile 0)) :
    successProbability (machineWeight (n := n)) (setEntry B)
        (profileHistory profile i.val) =
      entryParameter B (activeGoods (profileSupply profile 0)) := by
  have hactive : queryActive (profileHistory profile i.val) =
      activeGoods (profileSupply profile 0) := by
    simpa using queryActive_at_slot profile 0 i
  have hprev := previousChoice_at_slot_zero profile i
  have hqueryA : (queryActive (profileHistory profile i.val)).Nonempty := by
    rw [hactive]
    exact hA
  have hrecord : setRecording B (profileHistory profile i.val) = true := by
    simp [setRecording, stochasticRecording, FreshQuery, hprev, hactive,
      hA, hB]
  have havailable : queryAvailable (profileHistory profile i.val) =
      activeGoods (profileSupply profile 0) := by
    unfold queryAvailable
    rw [dif_pos hqueryA, hprev, hactive]
  change successProbability
      (uniformChoiceWeight (queryAvailable (n := n)))
      (stoppedEntry B (setRecording B))
      (profileHistory profile i.val) = _
  rw [uniformChoice_successProbability (queryAvailable (n := n))
    queryAvailable_nonempty]
  simp [hrecord, havailable]

lemma successor_successProbability_eq (profile : Profile n)
    (B : Finset (Fin n)) (round : ℕ) (i : Fin n)
    (hA : (activeGoods (profileSupply profile (round + 1))).Nonempty)
    (hB : B ⊆ activeGoods (profileSupply profile (round + 1))) :
    successProbability (machineWeight (n := n)) (setEntry B)
        (profileHistory profile ((round + 1) * n + i.val)) =
      if favorite (profile i) (activeGoods (profileSupply profile round))
            (by
              have hsubset := profileSupply_active_subset profile round
              exact ⟨hA.choose, hsubset hA.choose_spec⟩) ∉
          activeGoods (profileSupply profile (round + 1)) then
        entryParameter B (activeGoods (profileSupply profile (round + 1)))
      else 0 := by
  let history := profileHistory profile ((round + 1) * n + i.val)
  let hprevA : (activeGoods (profileSupply profile round)).Nonempty := by
    have hsubset := profileSupply_active_subset profile round
    exact ⟨hA.choose, hsubset hA.choose_spec⟩
  let old := favorite (profile i) (activeGoods (profileSupply profile round))
    hprevA
  have hactive : queryActive history =
      activeGoods (profileSupply profile (round + 1)) := by
    simpa [history] using queryActive_at_slot profile (round + 1) i
  have hprev : previousChoice history = some old := by
    simpa [history, old, hprevA] using
      previousChoice_at_slot_succ profile round i hA
  have hqueryA : (queryActive history).Nonempty := by
    rw [hactive]
    exact hA
  change successProbability
      (uniformChoiceWeight (queryAvailable (n := n)))
      (stoppedEntry B (setRecording B)) history = _
  rw [uniformChoice_successProbability (queryAvailable (n := n))
    queryAvailable_nonempty]
  by_cases hold : old ∈ activeGoods (profileSupply profile (round + 1))
  · have hrecord : setRecording B history = false := by
      simp [setRecording, stochasticRecording, FreshQuery, hprev, hactive,
        hA, old, hold]
    simp [hrecord, old, hold]
  · have hrecord : setRecording B history = true := by
      simp [setRecording, stochasticRecording, FreshQuery, hprev, hactive,
        hA, hB, old, hold]
    have havailable : queryAvailable history =
        activeGoods (profileSupply profile (round + 1)) := by
      unfold queryAvailable
      rw [dif_pos hqueryA, hprev]
      simp only
      rw [if_neg (by simpa [old, hactive] using hold), hactive]
    simp [hrecord, havailable, old, hold]

lemma compensator_initial_round (profile : Profile n)
    (B : Finset (Fin n))
    (hA : (activeGoods (profileSupply profile 0)).Nonempty)
    (hB : B ⊆ activeGoods (profileSupply profile 0)) :
    compensator (machineWeight (n := n)) (setEntry B)
        (profileHistory profile n) = (B.card : ℝ) := by
  have hsum := compensator_profileHistory_add (machineWeight (n := n))
    (setEntry B) profile 0 n
  simp only [profileHistory_zero, compensator_nil, zero_add, Nat.zero_add]
    at hsum
  rw [hsum]
  have hterm : ∀ j ∈ Finset.range n,
      successProbability (machineWeight (n := n)) (setEntry B)
          (profileHistory profile j) =
        entryParameter B (activeGoods (profileSupply profile 0)) := by
    intro j hj
    exact initial_successProbability_eq profile B
      ⟨j, Finset.mem_range.mp hj⟩ hA hB
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hactive0 : activeGoods (profileSupply profile 0) = Finset.univ := by
    simp [profileSupply, activeGoods_initial]
  rw [entryParameter_eq_card_div hB, hactive0, Finset.card_univ,
    Fintype.card_fin]
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by
      simpa using (Fintype.card_pos_iff.mpr
        (inferInstance : Nonempty (Fin n))).ne')
  field_simp

lemma compensator_successor_increment (profile : Profile n)
    (B : Finset (Fin n)) (round : ℕ)
    (hA : (activeGoods (profileSupply profile (round + 1))).Nonempty)
    (hB : B ⊆ activeGoods (profileSupply profile (round + 1))) :
    compensator (machineWeight (n := n)) (setEntry B)
        (profileHistory profile ((round + 2) * n)) =
      compensator (machineWeight (n := n)) (setEntry B)
          (profileHistory profile ((round + 1) * n)) +
        (displacedCount
          (roundPhase profile round (by
            have hsubset := profileSupply_active_subset profile round
            exact ⟨hA.choose, hsubset hA.choose_spec⟩))
          (roundPhase profile (round + 1) hA) : ℝ) *
        entryParameter B (activeGoods (profileSupply profile (round + 1))) := by
  rw [show (round + 2) * n = (round + 1) * n + n by
    ring]
  rw [compensator_profileHistory_add (machineWeight (n := n))
    (setEntry B) profile ((round + 1) * n) n]
  congr 1
  calc
    (∑ j ∈ Finset.range n,
        successProbability (machineWeight (n := n)) (setEntry B)
          (profileHistory profile ((round + 1) * n + j))) =
      ∑ i : Fin n,
        if i ∈ displacedAgents
            (roundPhase profile round (by
              have hsubset := profileSupply_active_subset profile round
              exact ⟨hA.choose, hsubset hA.choose_spec⟩))
            (roundPhase profile (round + 1) hA) then
          entryParameter B (activeGoods (profileSupply profile (round + 1)))
        else 0 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn := Finset.mem_range.mp hj
      let i : Fin n := ⟨j, hjn⟩
      have hedge := successor_successProbability_eq profile B round i hA hB
      simp only [dif_pos hjn]
      simpa [i, displacedAgents, roundPhase_choice, roundPhase_active] using hedge
    _ = (displacedCount
          (roundPhase profile round (by
            have hsubset := profileSupply_active_subset profile round
            exact ⟨hA.choose, hsubset hA.choose_spec⟩))
          (roundPhase profile (round + 1) hA) : ℝ) *
        entryParameter B (activeGoods (profileSupply profile (round + 1))) := by
      simp [displacedCount]

/-- While two sets remain active, their predictable volumes are proportional
to their cardinalities. -/
theorem compensator_card_proportional (profile : Profile n) :
    ∀ round (hA : (activeGoods (profileSupply profile round)).Nonempty)
      (B C : Finset (Fin n)),
      B ⊆ activeGoods (profileSupply profile round) →
      C ⊆ activeGoods (profileSupply profile round) →
      compensator (machineWeight (n := n)) (setEntry B)
          (profileHistory profile ((round + 1) * n)) * (C.card : ℝ) =
        compensator (machineWeight (n := n)) (setEntry C)
          (profileHistory profile ((round + 1) * n)) * (B.card : ℝ) := by
  intro round
  induction round with
  | zero =>
      intro hA B C hB hC
      simp only [Nat.zero_add, Nat.one_mul]
      rw [compensator_initial_round profile B hA hB,
        compensator_initial_round profile C hA hC]
      ring
  | succ round ih =>
      intro hA B C hB hC
      let hprevA : (activeGoods (profileSupply profile round)).Nonempty := by
        have hsubset := profileSupply_active_subset profile round
        exact ⟨hA.choose, hsubset hA.choose_spec⟩
      have hBprev : B ⊆ activeGoods (profileSupply profile round) :=
        hB.trans (profileSupply_active_subset profile round)
      have hCprev : C ⊆ activeGoods (profileSupply profile round) :=
        hC.trans (profileSupply_active_subset profile round)
      have hIH := ih hprevA B C hBprev hCprev
      have hBinc := compensator_successor_increment profile B round hA hB
      have hCinc := compensator_successor_increment profile C round hA hC
      have heq : Nat.succ round + 1 = round + 2 := by omega
      rw [heq, hBinc, hCinc]
      rw [entryParameter_eq_card_div hB,
        entryParameter_eq_card_div hC]
      have hs : ((activeGoods
          (profileSupply profile (round + 1))).card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr hA).ne'
      field_simp [hs]
      nlinarith

def inverseLambda (n s : ℕ) : ℝ := (n : ℝ) / (s : ℝ)

def treeLambda (n s : ℕ) : ℝ :=
  max PhaseAdapter.phaseLambdaZero (inverseLambda n s)

def treeFailure (n : ℕ) [Nonempty (Fin n)] : History (Fin n) → Prop :=
  fun h =>
    finiteUnionEvent Finset.univ.powerset
        (potentialFailureEvent (queryAvailable (n := n))
          setRecording etaZero) h ∨
      finiteUnionEvent (Finset.Icc 1 n)
        (activeCardinalityUnderloadEvent (queryAvailable (n := n))
          (fun _s => setRecording) (treeLambda n)) h

noncomputable instance treeFailureDecidable (n : ℕ) [Nonempty (Fin n)] :
    DecidablePred (treeFailure n) := Classical.decPred _

lemma phaseLoad_active_eq_n {profile : Profile n} (p : Phase n profile) :
    phaseLoad p.active p = n := by
  rw [phaseLoad_eq_card_phaseEaters]
  have heq : phaseEaters p.active p = Finset.univ := by
    ext i
    simp [phaseEaters, p.choice_mem_active]
  rw [heq, Finset.card_univ, Fintype.card_fin]

lemma phase_eq_roundPhase_of_before_eq (profile : Profile n)
    (p : Phase n profile) (round : ℕ)
    (hp : p.before = profileSupply profile round) :
    p = roundPhase profile round (by
      rw [← hp]
      exact p.active_nonempty) := by
  cases p with
  | mk before valid active_nonempty =>
      dsimp at hp ⊢
      subst before
      rfl

/-- If a concrete phase violates the desired underload conclusion, the
combined labelled-tree failure event has occurred by the end of its round. -/
theorem treeFailure_of_phase_bad (profile : Profile n) (hn : 0 < n)
    (p : Phase n profile) (hp : p ∈ (run profile).phases)
    (hlambda : PhaseAdapter.phaseLambdaZero ≤
      (n : ℝ) / (p.active.card : ℝ))
    (hbad :
      candidateSize n alphaZero
          ((n : ℝ) / (p.active.card : ℝ)) ≤
        (underloadedGoods p.active p.load
          ((etaZero / 4) *
            ((n : ℝ) / (p.active.card : ℝ)))).card) :
    ∃ depth ≤ n * n,
      treeFailure n (profileHistory profile depth) := by
  obtain ⟨round, hround, hpBefore⟩ :=
    run_phase_profileSupply_index profile hn p hp
  let hA : (activeGoods (profileSupply profile round)).Nonempty := by
    rw [← hpBefore]
    exact p.active_nonempty
  have hpEq : p = roundPhase profile round hA := by
    exact phase_eq_roundPhase_of_before_eq profile p round hpBefore
  let active := activeGoods (profileSupply profile round)
  let s := active.card
  let b := candidateSize n alphaZero (treeLambda n s)
  let history := profileHistory profile ((round + 1) * n)
  have hactiveEq : p.active = active := by
    rw [hpEq]
    rfl
  have hsPos : 0 < s := Finset.card_pos.mpr (by simpa [active] using hA)
  have hsLe : s ≤ n := by
    have hsub : active ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
    simpa [s] using Finset.card_le_card hsub
  have hsMem : s ∈ Finset.Icc 1 n :=
    Finset.mem_Icc.mpr ⟨hsPos, hsLe⟩
  have hLamEq : treeLambda n s = inverseLambda n s := by
    rw [treeLambda, max_eq_right]
    simpa [inverseLambda, s, hactiveEq] using hlambda
  have hbPos : 0 < b := by
    exact candidateSize_pos hn alphaZero (treeLambda n s)
  have hdepth : (round + 1) * n ≤ n * n := by
    exact Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr hround)
  let volumeA := compensator (machineWeight (n := n))
    (setEntry active) history
  by_cases hcomp : volumeA ≤ etaZero * (n : ℝ)
  · refine ⟨(round + 1) * n, hdepth, ?_⟩
    apply Or.inl
    refine ⟨active, by simp, ?_⟩
    refine ⟨?_, hcomp⟩
    have hload := successes_at_completed_round profile active round hA
      (Finset.Subset.rfl)
    change (n : ℝ) ≤ successes (setEntry active) history
    rw [show history = profileHistory profile ((round + 1) * n) by rfl,
      hload]
    exact_mod_cast
      (phaseLoad_active_eq_n (roundPhase profile round hA)).symm.le
  · have hpotential : etaZero * (n : ℝ) < volumeA :=
      lt_of_not_ge hcomp
    have hbad' : b ≤
        (underloadedGoods active (roundPhase profile round hA).load
          ((etaZero / 4) * inverseLambda n s)).card := by
      simpa [b, s, active, inverseLambda, hpEq, hLamEq] using hbad
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hbad'
    have hBactive : B ⊆ active := by
      intro g hg
      exact (Finset.mem_filter.mp (hBsub hg)).1
    have hBmem : B ∈ candidateSets n b := by
      rw [candidateSets, Finset.mem_powersetCard]
      exact ⟨hBactive.trans (Finset.subset_univ _), hBcard⟩
    let volumeB := compensator (machineWeight (n := n))
      (setEntry B) history
    have hprop := compensator_card_proportional profile round hA
      B active hBactive Finset.Subset.rfl
    have hprop' : volumeB * (s : ℝ) = volumeA * (b : ℝ) := by
      simpa [volumeB, volumeA, history, s, active, hBcard] using hprop
    have hsR : (0 : ℝ) < s := by exact_mod_cast hsPos
    have hbR : (0 : ℝ) < b := by exact_mod_cast hbPos
    have hvolumeB : etaZero * (b : ℝ) * treeLambda n s ≤ volumeB := by
      rw [hLamEq]
      apply le_of_lt
      rw [inverseLambda]
      rw [show etaZero * (b : ℝ) * ((n : ℝ) / (s : ℝ)) =
        (etaZero * (b : ℝ) * (n : ℝ)) / (s : ℝ) by ring]
      apply (div_lt_iff₀ hsR).2
      rw [hprop']
      nlinarith [mul_lt_mul_of_pos_right hpotential hbR]
    have hBnonempty : B.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      have : B.card = 0 := by simp [hEmpty]
      omega
    have hsum :
        (phaseLoad B (roundPhase profile round hA) : ℝ) <
          (b : ℝ) * ((etaZero / 4) * inverseLambda n s) := by
      unfold phaseLoad
      have hstrict :
          (∑ g ∈ B, ((roundPhase profile round hA).load g : ℝ)) <
            ∑ _g ∈ B, (etaZero / 4) * inverseLambda n s := by
        apply Finset.sum_lt_sum_of_nonempty hBnonempty
        intro g hg
        exact (Finset.mem_filter.mp (hBsub hg)).2
      simpa [Finset.sum_const, nsmul_eq_mul, hBcard] using hstrict
    have hsuccess := successes_at_completed_round profile B round hA hBactive
    have hsuccessLt : successes (setEntry B) history <
        (etaZero * (b : ℝ) * treeLambda n s) / 4 := by
      rw [hLamEq]
      rw [show history = profileHistory profile ((round + 1) * n) by rfl,
        hsuccess]
      nlinarith
    have hfixed : fixedSetUnderloadFamily (queryAvailable (n := n))
        setRecording etaZero (treeLambda n s) B history := by
      unfold fixedSetUnderloadFamily fixedUnderloadEvent
      simpa [machineWeight, setEntry, hBcard] using ⟨hvolumeB, hsuccessLt⟩
    refine ⟨(round + 1) * n, hdepth, Or.inr ?_⟩
    exact ⟨s, hsMem, B, hBmem, hfixed⟩

/-! ## The genuine fresh-reveal filtration of a profile path -/

lemma queryAvailable_eq_active_of_stochastic
    (history : History (Fin n))
    (hs : stochasticRecording history = true) :
    queryAvailable history = queryActive history := by
  have hsProp : (queryActive history).Nonempty ∧ FreshQuery history := by
    exact of_decide_eq_true (by simpa [stochasticRecording] using hs)
  unfold queryAvailable
  rw [dif_pos hsProp.1]
  cases hprev : previousChoice history with
  | none => rfl
  | some g =>
      have hg : g ∉ queryActive history := by
        simpa [FreshQuery, hprev] using hsProp.2
      simp [hprev, hg]

def profileRevealStep (profile : Profile n) (depth : ℕ) : Option (Reveal n) :=
  let history := profileHistory profile depth
  if hs : stochasticRecording history = true then
    some
      ⟨queryAgent history, queryActive history, profileAnswer profile history,
        by
          rw [← queryAvailable_eq_active_of_stochastic history hs]
          exact profileAnswer_mem profile history⟩
  else none

def profileRevealHistory (profile : Profile n) : ℕ → RevealHistory n
  | 0 => []
  | depth + 1 =>
      profileRevealHistory profile depth ++
        (profileRevealStep profile depth).toList

@[simp] lemma profileRevealHistory_zero (profile : Profile n) :
    profileRevealHistory profile 0 = [] := rfl

@[simp] lemma profileRevealHistory_succ (profile : Profile n) (depth : ℕ) :
    profileRevealHistory profile (depth + 1) =
      profileRevealHistory profile depth ++
        (profileRevealStep profile depth).toList := rfl

lemma profileRevealStep_eq_some (profile : Profile n) (depth : ℕ)
    (hs : stochasticRecording (profileHistory profile depth) = true) :
    profileRevealStep profile depth = some
      ⟨queryAgent (profileHistory profile depth),
        queryActive (profileHistory profile depth),
        profileAnswer profile (profileHistory profile depth), by
          rw [← queryAvailable_eq_active_of_stochastic _ hs]
          exact profileAnswer_mem profile _⟩ := by
  simp [profileRevealStep, hs]

lemma profileRevealStep_eq_none (profile : Profile n) (depth : ℕ)
    (hs : stochasticRecording (profileHistory profile depth) = false) :
    profileRevealStep profile depth = none := by
  simp [profileRevealStep, hs]

lemma mem_profileRevealHistory (profile : Profile n) (depth : ℕ)
    (r : Reveal n) :
    r ∈ profileRevealHistory profile depth ↔
      ∃ k < depth,
        stochasticRecording (profileHistory profile k) = true ∧
        r.agent = queryAgent (profileHistory profile k) ∧
        r.available = queryActive (profileHistory profile k) ∧
        r.chosen = profileAnswer profile (profileHistory profile k) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [profileRevealHistory_succ, List.mem_append, ih]
      by_cases hs : stochasticRecording (profileHistory profile depth) = true
      · rw [profileRevealStep_eq_some profile depth hs]
        simp only [Option.toList_some, List.mem_singleton]
        constructor
        · rintro (hold | rfl)
          · obtain ⟨k, hk, hstep, ha, hav, hc⟩ := hold
            exact ⟨k, by omega, hstep, ha, hav, hc⟩
          · exact ⟨depth, by omega, hs, rfl, rfl, rfl⟩
        · rintro ⟨k, hk, hstep, ha, hav, hc⟩
          by_cases hkd : k < depth
          · exact Or.inl ⟨k, hkd, hstep, ha, hav, hc⟩
          · have hkeq : k = depth := by omega
            subst k
            right
            cases r
            simp_all
      · have hsFalse : stochasticRecording
            (profileHistory profile depth) = false := by
          exact Bool.eq_false_of_not_eq_true hs
        rw [profileRevealStep_eq_none profile depth hsFalse]
        simp only [Option.toList_none, List.not_mem_nil, or_false]
        constructor
        · rintro ⟨k, hk, hstep, ha, hav, hc⟩
          exact ⟨k, by omega, hstep, ha, hav, hc⟩
        · rintro ⟨k, hk, hstep, ha, hav, hc⟩
          refine ⟨k, ?_, hstep, ha, hav, hc⟩
          by_contra hnot
          have hkeq : k = depth := by omega
          subst k
          exact hs hstep

lemma profileRevealHistory_compatible (profile : Profile n) :
    ∀ depth, Compatible profile (profileRevealHistory profile depth) := by
  intro depth
  induction depth with
  | zero => simp [Compatible]
  | succ depth ih =>
      rw [profileRevealHistory_succ]
      by_cases hs : stochasticRecording (profileHistory profile depth) = true
      · rw [profileRevealStep_eq_some profile depth hs]
        simp only [Option.toList_some]
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact ih r hr
        · simp only [List.mem_singleton] at hr
          subst r
          change favorite (profile (queryAgent (profileHistory profile depth)))
              (queryActive (profileHistory profile depth)) _ =
            profileAnswer profile (profileHistory profile depth)
          exact (favorite_congr_set _ _ _ _ _
            (queryAvailable_eq_active_of_stochastic _ hs)).symm
      · have hsFalse : stochasticRecording
            (profileHistory profile depth) = false :=
          Bool.eq_false_of_not_eq_true hs
        rw [profileRevealStep_eq_none profile depth hsFalse]
        simpa using ih

lemma profileSupply_active_subset_of_le (profile : Profile n)
    {earlier later : ℕ} (h : earlier ≤ later) :
    activeGoods (profileSupply profile later) ⊆
      activeGoods (profileSupply profile earlier) := by
  induction later, h using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ later hearlier ih =>
      exact (profileSupply_active_subset profile later).trans ih

/-- Every genuinely fresh query on a profile-generated path is admissible
relative to all earlier fresh queries. -/
theorem profile_fresh_query_admissible (profile : Profile n) (depth : ℕ)
    (hs : stochasticRecording (profileHistory profile depth) = true) :
    AdmissibleQuery (profileRevealHistory profile depth)
      (queryAgent (profileHistory profile depth))
      (queryActive (profileHistory profile depth)) := by
  let history := profileHistory profile depth
  let currentRound := depth / n
  let currentAgent := queryAgent history
  have hsProp : (queryActive history).Nonempty ∧ FreshQuery history :=
    of_decide_eq_true (by simpa [stochasticRecording, history] using hs)
  have hcurrentActive : queryActive history =
      activeGoods (profileSupply profile currentRound) := by
    simp [queryActive, (profile_machine_correspondence profile depth).1,
      history, currentRound]
  apply admissibleQuery_of_nested_displaced
  · intro r hr hrAgent
    obtain ⟨k, hk, hkStochastic, hkAgent, hkAvailable, hkChosen⟩ :=
      (mem_profileRevealHistory profile depth r).mp hr
    have hroundLe : k / n ≤ currentRound := by
      dsimp [currentRound]
      exact Nat.div_le_div_right (Nat.le_of_lt hk)
    have hkActive : queryActive (profileHistory profile k) =
        activeGoods (profileSupply profile (k / n)) := by
      unfold queryActive
      rw [(profile_machine_correspondence profile k).1]
    rw [hkAvailable, hkActive, hcurrentActive]
    exact profileSupply_active_subset_of_le profile hroundLe
  · intro r hr hrAgent
    obtain ⟨k, hk, hkStochastic, hkAgent, hkAvailable, hkChosen⟩ :=
      (mem_profileRevealHistory profile depth r).mp hr
    have hn : 0 < n := by
      simpa using (Fintype.card_pos_iff.mpr
        (inferInstance : Nonempty (Fin n)))
    have hkAgentEq : queryAgent (profileHistory profile k) = currentAgent :=
      hkAgent.symm.trans (hrAgent.trans rfl)
    have hmodEq : k % n = depth % n := by
      have hvals := congrArg Fin.val hkAgentEq
      simpa [queryAgent, roundOffset, history, currentAgent] using hvals
    have hroundLe : k / n ≤ currentRound := by
      dsimp [currentRound]
      exact Nat.div_le_div_right (Nat.le_of_lt hk)
    have hroundNe : k / n ≠ currentRound := by
      intro heq
      have hkDecomp := Nat.mod_add_div k n
      have hdDecomp := Nat.mod_add_div depth n
      dsimp [currentRound] at heq
      rw [heq, hmodEq] at hkDecomp
      omega
    have hroundLt : k / n < currentRound := lt_of_le_of_ne hroundLe hroundNe
    have hcurrentRoundPos : 0 < currentRound := lt_of_le_of_lt (Nat.zero_le _) hroundLt
    let previousRound := currentRound - 1
    have hprevSucc : previousRound + 1 = currentRound := by
      dsimp [previousRound]
      omega
    have hcurrentA :
        (activeGoods (profileSupply profile currentRound)).Nonempty := by
      rw [← hcurrentActive]
      exact hsProp.1
    let hpreviousA :
        (activeGoods (profileSupply profile previousRound)).Nonempty := by
      have hsub := profileSupply_active_subset profile previousRound
      rw [hprevSucc] at hsub
      exact ⟨hcurrentA.choose, hsub hcurrentA.choose_spec⟩
    have hdepthEq : depth = currentRound * n + currentAgent.val := by
      have hdecomp := Nat.mod_add_div depth n
      have hval : currentAgent.val = depth % n := by
        simp [currentAgent, history, queryAgent, roundOffset,
          profileHistory_length]
      calc
        depth = depth % n + n * (depth / n) := hdecomp.symm
        _ = currentRound * n + currentAgent.val := by
          rw [hval]
          simp [currentRound, Nat.add_comm, Nat.mul_comm]
    have hpreviousChoice : previousChoice history =
        some (favorite (profile currentAgent)
          (activeGoods (profileSupply profile previousRound)) hpreviousA) := by
      have hprev := previousChoice_at_slot_succ profile previousRound
        currentAgent (by simpa [hprevSucc] using hcurrentA)
      simpa [history, hdepthEq, hprevSucc] using hprev
    have hpreviousAbsent :
        favorite (profile currentAgent)
            (activeGoods (profileSupply profile previousRound)) hpreviousA ∉
          activeGoods (profileSupply profile currentRound) := by
      simpa [FreshQuery, hpreviousChoice, hcurrentActive] using hsProp.2
    have hkA : (activeGoods (profileSupply profile (k / n))).Nonempty := by
      have hsub := profileSupply_active_subset_of_le profile hroundLe
      exact ⟨hcurrentA.choose, hsub hcurrentA.choose_spec⟩
    have hkAnswer := profileAnswer_at_slot profile (k / n)
      ⟨k % n, Nat.mod_lt _ hn⟩ hkA
    have hkDepthEq : (k / n) * n + (k % n) = k := by
      simpa [Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div k n)
    have hkHistoryEq : profileHistory profile
        ((k / n) * n + (k % n)) = profileHistory profile k :=
      congrArg (profileHistory profile) hkDepthEq
    rw [hkHistoryEq] at hkAnswer
    have hkFinEq : (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n) = currentAgent := by
      have hqueryK : queryAgent (profileHistory profile k) =
          (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n) := by
        apply Fin.ext
        simp [queryAgent, roundOffset, profileHistory_length]
      exact hqueryK.symm.trans hkAgentEq
    have hkChosenEq : r.chosen = favorite (profile currentAgent)
        (activeGoods (profileSupply profile (k / n))) hkA := by
      rw [hkChosen]
      simpa [hkFinEq] using hkAnswer
    intro hrCurrent
    have hprevRoundLe : k / n ≤ previousRound := by
      dsimp [previousRound]
      omega
    have hprevSubset := profileSupply_active_subset_of_le profile hprevRoundLe
    have hrCurrent' : r.chosen ∈
        activeGoods (profileSupply profile currentRound) := by
      rw [← hcurrentActive]
      exact hrCurrent
    have hcurrentPrev := profileSupply_active_subset profile previousRound
    rw [hprevSucc] at hcurrentPrev
    have hrPrevious : r.chosen ∈
        activeGoods (profileSupply profile previousRound) :=
      hcurrentPrev hrCurrent'
    have hfavoriteEq : favorite (profile currentAgent)
        (activeGoods (profileSupply profile previousRound)) hpreviousA =
        favorite (profile currentAgent)
          (activeGoods (profileSupply profile (k / n))) hkA := by
      exact favorite_of_mem_of_subset (profile currentAgent) hkA hpreviousA
        hprevSubset (by simpa [hkChosenEq] using hrPrevious)
    apply hpreviousAbsent
    rw [hfavoriteEq, ← hkChosenEq]
    rw [← hcurrentActive]
    exact hrCurrent

lemma admissibleExtension_append_one (base extension : RevealHistory n)
    (r : Reveal n)
    (hext : AdmissibleExtension base extension)
    (hr : AdmissibleQuery (base ++ extension) r.agent r.available) :
    AdmissibleExtension base (extension ++ [r]) := by
  induction extension generalizing base with
  | nil =>
      simpa [AdmissibleExtension] using hr
  | cons first rest ih =>
      rcases hext with ⟨hfirst, hrest⟩
      refine ⟨hfirst, ?_⟩
      apply ih (base := base ++ [first]) hrest
      simpa [List.append_assoc] using hr

theorem profileRevealHistory_admissible (profile : Profile n) :
    ∀ depth, AdmissibleExtension [] (profileRevealHistory profile depth) := by
  intro depth
  induction depth with
  | zero => trivial
  | succ depth ih =>
      rw [profileRevealHistory_succ]
      by_cases hs : stochasticRecording (profileHistory profile depth) = true
      · rw [profileRevealStep_eq_some profile depth hs]
        simp only [Option.toList_some]
        apply admissibleExtension_append_one [] _ _ ih
        simpa using profile_fresh_query_admissible profile depth hs
      · have hsFalse : stochasticRecording
            (profileHistory profile depth) = false :=
          Bool.eq_false_of_not_eq_true hs
        rw [profileRevealStep_eq_none profile depth hsFalse]
        simpa using ih

lemma profileHistory_prefix_eq {first second : Profile n} {depth : ℕ}
    (heq : profileHistory first depth = profileHistory second depth) :
    ∀ {k}, k ≤ depth →
      profileHistory first k = profileHistory second k := by
  induction depth with
  | zero =>
      intro k hk
      have : k = 0 := by omega
      subst k
      rfl
  | succ depth ih =>
      intro k hk
      by_cases hlast : k = depth + 1
      · subst k
        exact heq
      · have hk' : k ≤ depth := by omega
        apply ih ?_ hk'
        have htail := congrArg List.tail heq
        simpa [profileHistory_succ] using htail

/-- Any profile producing the same labelled prefix is compatible with every
fresh reveal in that prefix. -/
theorem compatible_of_profileHistory_eq (reference other : Profile n)
    (depth : ℕ)
    (heq : profileHistory reference depth = profileHistory other depth) :
    Compatible other (profileRevealHistory reference depth) := by
  intro r hr
  obtain ⟨k, hk, hs, hrAgent, hrAvailable, hrChosen⟩ :=
    (mem_profileRevealHistory reference depth r).mp hr
  have hkEq : profileHistory reference k = profileHistory other k :=
    profileHistory_prefix_eq heq hk.le
  have hkSuccEq : profileHistory reference (k + 1) =
      profileHistory other (k + 1) :=
    profileHistory_prefix_eq heq (by omega)
  have hanswerEq :
      profileAnswer reference (profileHistory reference k) =
        profileAnswer other (profileHistory other k) := by
    have hhead := congrArg List.head? hkSuccEq
    simpa [profileHistory_succ] using hhead
  have havailable := queryAvailable_eq_active_of_stochastic
    (profileHistory reference k) hs
  have hsProp : (queryActive (profileHistory reference k)).Nonempty ∧
      FreshQuery (profileHistory reference k) :=
    of_decide_eq_true (by simpa [stochasticRecording] using hs)
  have hactive : (queryActive (profileHistory reference k)).Nonempty :=
    hsProp.1
  calc
    favorite (other r.agent) r.available r.nonempty =
      favorite (other r.agent)
        (queryActive (profileHistory reference k)) hactive :=
      favorite_congr_set _ _ _ _ _ hrAvailable
    _ = favorite (other (queryAgent (profileHistory reference k)))
        (queryActive (profileHistory reference k)) hactive := by
      rw [hrAgent]
    _ =
      favorite (other (queryAgent (profileHistory reference k)))
        (queryAvailable (profileHistory reference k)) _ :=
      favorite_congr_set _ _ _ _ _ havailable.symm
    _ = profileAnswer other (profileHistory reference k) := by
      unfold profileAnswer
      rfl
    _ = profileAnswer reference (profileHistory reference k) := by
      rw [← hkEq] at hanswerEq
      exact hanswerEq.symm
    _ = r.chosen := hrChosen.symm

lemma queryAvailable_card_eq_one_of_not_stochastic
    (history : History (Fin n))
    (hs : stochasticRecording history = false) :
    (queryAvailable history).card = 1 := by
  have hsNot : ¬ ((queryActive history).Nonempty ∧ FreshQuery history) := by
    intro h
    have : stochasticRecording history = true := by
      simp [stochasticRecording, h]
    simp [hs] at this
  unfold queryAvailable
  by_cases hactive : (queryActive history).Nonempty
  · rw [dif_pos hactive]
    cases hprev : previousChoice history with
    | none =>
        exact False.elim (hsNot ⟨hactive, by simp [FreshQuery, hprev]⟩)
    | some g =>
        have hg : g ∈ queryActive history := by
          by_contra hnot
          exact hsNot ⟨hactive, by simpa [FreshQuery, hprev] using hnot⟩
        simp [hprev, hg]
  · rw [dif_neg hactive]
    simp

def pathWeight {alpha : Type*} [Fintype alpha]
    (weight : History alpha → alpha → ℝ) : History alpha → ℝ
  | [] => 1
  | a :: history => pathWeight weight history * weight history a

@[simp] lemma pathWeight_nil {alpha : Type*} [Fintype alpha]
    (weight : History alpha → alpha → ℝ) :
    pathWeight weight [] = 1 := rfl

@[simp] lemma pathWeight_cons {alpha : Type*} [Fintype alpha]
    (weight : History alpha → alpha → ℝ)
    (history : History alpha) (a : alpha) :
    pathWeight weight (a :: history) =
      pathWeight weight history * weight history a := rfl

/-- The product of transition probabilities along a profile path is exactly
the reciprocal product of its genuinely random reveal-set sizes. -/
theorem profile_pathWeight_mul_revealProduct (profile : Profile n) :
    ∀ depth,
      pathWeight (machineWeight (n := n)) (profileHistory profile depth) *
          ((profileRevealHistory profile depth).map
            (fun r => (r.available.card : ℝ))).prod = 1 := by
  intro depth
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [profileHistory_succ, pathWeight_cons, profileRevealHistory_succ]
      by_cases hs : stochasticRecording (profileHistory profile depth) = true
      · rw [profileRevealStep_eq_some profile depth hs]
        simp only [Option.toList_some, List.map_append, List.map_singleton,
          List.prod_append, List.prod_singleton]
        have havailable := queryAvailable_eq_active_of_stochastic
          (profileHistory profile depth) hs
        have hmem := profileAnswer_mem profile (profileHistory profile depth)
        have hcardPos : (0 : ℝ) <
            (queryAvailable (profileHistory profile depth)).card := by
          exact_mod_cast Finset.card_pos.mpr
            (queryAvailable_nonempty (profileHistory profile depth))
        have hmemActive : profileAnswer profile (profileHistory profile depth) ∈
            queryActive (profileHistory profile depth) := by
          rw [← havailable]
          exact hmem
        have hcardActive : (0 : ℝ) <
            (queryActive (profileHistory profile depth)).card := by
          simpa [havailable] using hcardPos
        simp [machineWeight, uniformChoiceWeight, hmem, hmemActive,
          havailable]
        field_simp [ne_of_gt hcardActive]
        nlinarith [ih]
      · have hsFalse : stochasticRecording
            (profileHistory profile depth) = false :=
          Bool.eq_false_of_not_eq_true hs
        rw [profileRevealStep_eq_none profile depth hsFalse]
        simp only [Option.toList_none, List.append_nil]
        have hmem := profileAnswer_mem profile (profileHistory profile depth)
        have hcard := queryAvailable_card_eq_one_of_not_stochastic
          (profileHistory profile depth) hsFalse
        simp [machineWeight, uniformChoiceWeight, hmem, hcard, ih]

def pathFiber (depth : ℕ) (history : History (Fin n)) :
    Finset (Profile n) :=
  (preferenceProfileSample n).filter
    (fun profile => profileHistory profile depth = history)

lemma reveal_card_product_pos (history : RevealHistory n) :
    0 < (history.map (fun r => r.available.card)).prod := by
  induction history with
  | nil => simp
  | cons r history ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_pos (Finset.card_pos.mpr r.nonempty) ih

lemma pathFiber_card_mul_revealProduct_le (reference : Profile n)
    (depth : ℕ) :
    (pathFiber depth (profileHistory reference depth)).card *
        ((profileRevealHistory reference depth).map
          (fun r => r.available.card)).prod ≤
      (preferenceProfileSample n).card := by
  let trace := profileRevealHistory reference depth
  have hsubset : pathFiber depth (profileHistory reference depth) ⊆
      compatibleProfiles trace := by
    intro other hother
    have hotherData := Finset.mem_filter.mp hother
    rw [mem_compatibleProfiles_iff]
    exact compatible_of_profileHistory_eq reference other depth hotherData.2.symm
  have hcard := Finset.card_le_card hsubset
  have hmul := Nat.mul_le_mul_right
    ((profileRevealHistory reference depth).map
      (fun r => r.available.card)).prod hcard
  have hjoint := sequential_revelation_joint_count [] trace
    (profileRevealHistory_admissible reference depth)
  have hroot : compatibleProfiles ([] : RevealHistory n) =
      preferenceProfileSample n := by
    ext profile
    simp [compatibleProfiles, Compatible]
  rw [hroot] at hjoint
  exact hmul.trans_eq (by simpa [trace] using hjoint)

lemma pathFiber_probability_le_pathWeight (reference : Profile n)
    (depth : ℕ) :
    ((pathFiber depth (profileHistory reference depth)).card : ℝ) /
        (preferenceProfileSample n).card ≤
      pathWeight (machineWeight (n := n))
        (profileHistory reference depth) := by
  let product := ((profileRevealHistory reference depth).map
    (fun r => r.available.card)).prod
  have hproduct : (0 : ℝ) < product := by
    exact_mod_cast reveal_card_product_pos
      (profileRevealHistory reference depth)
  have hsample : (0 : ℝ) < (preferenceProfileSample n).card := by
    exact_mod_cast Finset.card_pos.mpr (preferenceProfileSample_nonempty n)
  have hcountNat := pathFiber_card_mul_revealProduct_le reference depth
  have hcount :
      ((pathFiber depth (profileHistory reference depth)).card : ℝ) *
          (product : ℝ) ≤ (preferenceProfileSample n).card := by
    exact_mod_cast hcountNat
  have hratio :
      ((pathFiber depth (profileHistory reference depth)).card : ℝ) /
          (preferenceProfileSample n).card ≤ 1 / (product : ℝ) := by
    rw [div_le_div_iff₀ hsample hproduct]
    simpa [mul_comm] using hcount
  have hpath := profile_pathWeight_mul_revealProduct reference depth
  have hpathEq : pathWeight (machineWeight (n := n))
      (profileHistory reference depth) = 1 / (product : ℝ) := by
    apply (eq_div_iff (ne_of_gt hproduct)).2
    simpa [product] using hpath
  simpa [hpathEq] using hratio

/-! ## Summing exact labelled paths -/

/-- Product of the transition weights along a chronological label sequence. -/
def sequenceWeight {alpha : Type*} [Fintype alpha]
    (weight : History alpha → alpha → ℝ) :
    (depth : ℕ) → History alpha → (Fin depth → alpha) → ℝ
  | 0, _history, _labels => 1
  | depth + 1, history, labels =>
      weight history (labels 0) *
        sequenceWeight weight depth (labels 0 :: history) (Fin.tail labels)

/-- The newest-first history reached after following a chronological label
sequence. -/
def followSequence {alpha : Type*} :
    (depth : ℕ) → History alpha → (Fin depth → alpha) → History alpha
  | 0, history, _labels => history
  | depth + 1, history, labels =>
      followSequence depth (labels 0 :: history) (Fin.tail labels)

def finSuccEquiv (alpha : Type*) (depth : ℕ) :
    (Fin (depth + 1) → alpha) ≃ alpha × (Fin depth → alpha) where
  toFun labels := (labels 0, Fin.tail labels)
  invFun pair := Fin.cons pair.1 pair.2
  left_inv labels := Fin.cons_self_tail labels
  right_inv pair := by
    rcases pair with ⟨a, tail⟩
    apply Prod.ext
    · simp
    · funext i
      simp

lemma sum_fin_sequence_succ {alpha : Type*} [Fintype alpha]
    (depth : ℕ) (F : (Fin (depth + 1) → alpha) → ℝ) :
    (∑ labels, F labels) =
      ∑ a : alpha, ∑ tail : Fin depth → alpha, F (Fin.cons a tail) := by
  calc
    (∑ labels, F labels) =
        ∑ pair : alpha × (Fin depth → alpha),
          F (Fin.cons pair.1 pair.2) := by
      apply Fintype.sum_equiv (finSuccEquiv alpha depth)
      intro labels
      change F labels = F (Fin.cons (labels 0) (Fin.tail labels))
      rw [Fin.cons_self_tail]
    _ = ∑ a : alpha, ∑ tail : Fin depth → alpha,
          F (Fin.cons a tail) := Fintype.sum_prod_type _

lemma sequenceWeight_sum_one {alpha : Type*} [Fintype alpha]
    {weight : History alpha → alpha → ℝ} (hweight : ValidLaw weight) :
    ∀ depth history, ∑ labels, sequenceWeight weight depth history labels = 1 := by
  intro depth
  induction depth with
  | zero =>
      intro history
      simp [sequenceWeight]
  | succ depth ih =>
      intro history
      rw [sum_fin_sequence_succ]
      simp only [sequenceWeight, Fin.cons_zero, Fin.tail_cons]
      simp_rw [← Finset.mul_sum, ih]
      simpa using (hweight history).2

def PersistentEvent {alpha : Type*}
    (event : History alpha → Prop) : Prop :=
  ∀ history a, event history → event (a :: history)

lemma persistent_followSequence {alpha : Type*}
    (event : History alpha → Prop) (hpersistent : PersistentEvent event) :
    ∀ depth history (labels : Fin depth → alpha),
      event history → event (followSequence depth history labels) := by
  intro depth
  induction depth with
  | zero => simp [followSequence]
  | succ depth ih =>
      intro history labels hevent
      simp only [followSequence]
      exact ih _ _ (hpersistent history (labels 0) hevent)

/-- For a persistent event, the stopped tree probability equals the sum of
terminal path masses whose terminal histories satisfy the event. -/
lemma hitProbability_eq_sum_terminal_of_persistent
    {alpha : Type*} [Fintype alpha]
    {weight : History alpha → alpha → ℝ} (hweight : ValidLaw weight)
    (event : History alpha → Prop) [DecidablePred event]
    (hpersistent : PersistentEvent event) :
    ∀ depth history,
      hitProbability weight event depth history =
        ∑ labels : Fin depth → alpha,
          sequenceWeight weight depth history labels *
            if event (followSequence depth history labels) then 1 else 0 := by
  intro depth
  induction depth with
  | zero =>
      intro history
      simp [hitProbability, sequenceWeight, followSequence]
  | succ depth ih =>
      intro history
      by_cases hevent : event history
      · rw [hitProbability]
        simp only [if_pos hevent]
        rw [sum_fin_sequence_succ]
        simp only [sequenceWeight, Fin.cons_zero, Fin.tail_cons,
          followSequence]
        have hall : ∀ a (tail : Fin depth → alpha),
            event (followSequence depth (a :: history) tail) := by
          intro a tail
          exact persistent_followSequence event hpersistent depth
            (a :: history) tail (hpersistent history a hevent)
        simp_rw [if_pos (hall _ _)]
        simp only [mul_one]
        simpa only [sum_fin_sequence_succ, sequenceWeight, Fin.cons_zero,
          Fin.tail_cons] using
            (sequenceWeight_sum_one hweight (depth + 1) history).symm
      · rw [hitProbability]
        simp only [if_neg hevent]
        rw [sum_fin_sequence_succ]
        simp only [sequenceWeight, Fin.cons_zero, Fin.tail_cons,
          followSequence]
        simp_rw [mul_assoc, ih]
        simp_rw [Finset.mul_sum]

lemma hitProbability_congr {alpha : Type*} [Fintype alpha]
    (firstWeight secondWeight : History alpha → alpha → ℝ)
    (firstEvent secondEvent : History alpha → Prop)
    [DecidablePred firstEvent] [DecidablePred secondEvent]
    (hweight : ∀ history a,
      firstWeight history a = secondWeight history a)
    (hevent : ∀ history, firstEvent history ↔ secondEvent history) :
    ∀ depth history,
      hitProbability firstWeight firstEvent depth history =
        hitProbability secondWeight secondEvent depth history := by
  intro depth
  induction depth with
  | zero =>
      intro history
      simp only [hitProbability]
      by_cases hfirst : firstEvent history
      · have hsecond := (hevent history).mp hfirst
        simp [hfirst, hsecond]
      · have hsecond : ¬secondEvent history :=
          fun h => hfirst ((hevent history).mpr h)
        simp [hfirst, hsecond]
  | succ depth ih =>
      intro history
      simp only [hitProbability]
      by_cases hfirst : firstEvent history
      · have hsecond := (hevent history).mp hfirst
        simp [hfirst, hsecond]
      · have hsecond : ¬secondEvent history :=
          fun h => hfirst ((hevent history).mpr h)
        simp only [if_neg hfirst, if_neg hsecond]
        apply Finset.sum_congr rfl
        intro a ha
        rw [hweight, ih]

lemma sequenceWeight_nonneg {alpha : Type*} [Fintype alpha]
    {weight : History alpha → alpha → ℝ} (hweight : ValidLaw weight) :
    ∀ depth history (labels : Fin depth → alpha),
      0 ≤ sequenceWeight weight depth history labels := by
  intro depth
  induction depth with
  | zero => simp [sequenceWeight]
  | succ depth ih =>
      intro history labels
      exact mul_nonneg ((hweight history).1 (labels 0))
        (ih (labels 0 :: history) (Fin.tail labels))

lemma followSequence_eq_foldl {alpha : Type*} :
    ∀ depth (history : History alpha) (labels : Fin depth → alpha),
      followSequence depth history labels =
        (List.ofFn labels).foldl (fun h a => a :: h) history := by
  intro depth
  induction depth with
  | zero => simp [followSequence]
  | succ depth ih =>
      intro history labels
      simp only [followSequence, List.ofFn_succ, List.foldl_cons]
      exact ih (labels 0 :: history) (Fin.tail labels)

/-- The chronological labels appearing in the genuine profile path. -/
def profileLabels (profile : Profile n) (depth : ℕ) : Fin depth → Fin n :=
  fun i => (profileHistory profile depth).reverse.get
    (Fin.cast (by simp) i)

lemma List.ofFn_get_cast {alpha : Type*} (list : List alpha) (length : ℕ)
    (hlength : length = list.length) :
    List.ofFn (fun i : Fin length => list.get (Fin.cast hlength i)) = list := by
  subst length
  simpa using List.ofFn_get list

lemma profileLabels_ofFn (profile : Profile n) (depth : ℕ) :
    List.ofFn (profileLabels profile depth) =
      (profileHistory profile depth).reverse := by
  unfold profileLabels
  apply List.ofFn_get_cast

lemma followSequence_profileLabels (profile : Profile n) (depth : ℕ) :
    followSequence depth [] (profileLabels profile depth) =
      profileHistory profile depth := by
  rw [followSequence_eq_foldl, profileLabels_ofFn]
  apply List.reverse_injective
  simpa using
    (List.reverse_foldl
      (l := (profileHistory profile depth).reverse))

lemma profileLabels_eq_iff (first second : Profile n) (depth : ℕ) :
    profileLabels first depth = profileLabels second depth ↔
      profileHistory first depth = profileHistory second depth := by
  constructor
  · intro heq
    have hofFn := congrArg List.ofFn heq
    rw [profileLabels_ofFn, profileLabels_ofFn] at hofFn
    exact List.reverse_injective hofFn
  · intro heq
    apply List.ofFn_injective
    rw [profileLabels_ofFn, profileLabels_ofFn, heq]

lemma pathWeight_followSequence {alpha : Type*} [Fintype alpha]
    (weight : History alpha → alpha → ℝ) :
    ∀ depth (history : History alpha) (labels : Fin depth → alpha),
      pathWeight weight (followSequence depth history labels) =
        pathWeight weight history *
          sequenceWeight weight depth history labels := by
  intro depth
  induction depth with
  | zero => simp [followSequence, sequenceWeight]
  | succ depth ih =>
      intro history labels
      rw [followSequence, ih]
      simp only [pathWeight_cons, sequenceWeight]
      ring

/-- An event has occurred somewhere in the newest-first history precisely
when it holds at one of its suffixes. -/
def pastEvent {alpha : Type*} (event : History alpha → Prop) :
    History alpha → Prop :=
  fun history => ∃ dropped ≤ history.length, event (history.drop dropped)

noncomputable instance pastEventDecidable {alpha : Type*}
    (event : History alpha → Prop) : DecidablePred (pastEvent event) :=
  Classical.decPred _

def strictPastEvent {alpha : Type*} (event : History alpha → Prop) :
    History alpha → Prop :=
  fun history => ∃ dropped, 0 < dropped ∧ dropped ≤ history.length ∧
    event (history.drop dropped)

lemma pastEvent_iff_current_or_strictPast {alpha : Type*}
    (event : History alpha → Prop) (history : History alpha) :
    pastEvent event history ↔ event history ∨ strictPastEvent event history := by
  constructor
  · rintro ⟨dropped, hdropped, hevent⟩
    by_cases hzero : dropped = 0
    · subst dropped
      exact Or.inl (by simpa using hevent)
    · exact Or.inr ⟨dropped, Nat.pos_of_ne_zero hzero, hdropped, hevent⟩
  · rintro (hevent | ⟨dropped, hpos, hdropped, hevent⟩)
    · exact ⟨0, by simp, by simpa using hevent⟩
    · exact ⟨dropped, hdropped, hevent⟩

lemma not_strictPastEvent_cons {alpha : Type*}
    (event : History alpha → Prop) (history : History alpha) (a : alpha)
    (hcurrent : ¬event history)
    (hpast : ¬strictPastEvent event history) :
    ¬strictPastEvent event (a :: history) := by
  rintro ⟨dropped, hpositive, hlength, hevent⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpositive.ne'
  simp only [List.drop_succ_cons] at hevent
  by_cases hk : k = 0
  · subst k
    exact hcurrent (by simpa using hevent)
  · apply hpast
    refine ⟨k, Nat.pos_of_ne_zero hk, ?_, hevent⟩
    simp only [List.length_cons] at hlength
    omega

lemma hitProbability_pastEvent_eq_of_no_strictPast
    {alpha : Type*} [Fintype alpha]
    (weight : History alpha → alpha → ℝ)
    (event : History alpha → Prop) [DecidablePred event] :
    ∀ depth history, ¬strictPastEvent event history →
      hitProbability weight (pastEvent event) depth history =
        hitProbability weight event depth history := by
  intro depth
  induction depth with
  | zero =>
      intro history hpast
      simp only [hitProbability]
      have heq : pastEvent event history ↔ event history := by
        rw [pastEvent_iff_current_or_strictPast]
        simp [hpast]
      by_cases hevent : event history <;> simp [hevent, heq]
  | succ depth ih =>
      intro history hpast
      have heq : pastEvent event history ↔ event history := by
        rw [pastEvent_iff_current_or_strictPast]
        simp [hpast]
      by_cases hevent : event history
      · simp [hitProbability, hevent, heq]
      · simp only [hitProbability, if_neg hevent,
          if_neg (heq.not.mpr hevent)]
        apply Finset.sum_congr rfl
        intro a ha
        rw [ih (a :: history)
          (not_strictPastEvent_cons event history a hevent hpast)]

lemma hitProbability_pastEvent_nil {alpha : Type*} [Fintype alpha]
    (weight : History alpha → alpha → ℝ)
    (event : History alpha → Prop) [DecidablePred event] (depth : ℕ) :
    hitProbability weight (pastEvent event) depth [] =
      hitProbability weight event depth [] := by
  apply hitProbability_pastEvent_eq_of_no_strictPast
  rintro ⟨dropped, hpositive, hlength, hevent⟩
  simp only [List.length_nil] at hlength
  omega

lemma pastEvent_persistent {alpha : Type*} (event : History alpha → Prop) :
    PersistentEvent (pastEvent event) := by
  intro history a hevent
  obtain ⟨dropped, hdropped, hhit⟩ := hevent
  refine ⟨dropped + 1, by simp; omega, ?_⟩
  simpa using hhit

lemma profileHistory_drop (profile : Profile n) (start extra : ℕ) :
    (profileHistory profile (start + extra)).drop extra =
      profileHistory profile start := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      simpa only [Nat.add_succ, profileHistory_succ,
        List.drop_succ_cons] using ih

lemma pastEvent_profileHistory_of_hit (profile : Profile n)
    (event : History (Fin n) → Prop) {depth : ℕ}
    (hhit : ∃ k ≤ depth, event (profileHistory profile k)) :
    pastEvent event (profileHistory profile depth) := by
  obtain ⟨k, hk, hevent⟩ := hhit
  refine ⟨depth - k, by simp [profileHistory_length], ?_⟩
  have hdrop := profileHistory_drop profile k (depth - k)
  rw [Nat.add_sub_of_le hk] at hdrop
  rw [hdrop]
  exact hevent

def profileLabelFiber (depth : ℕ) (labels : Fin depth → Fin n) :
    Finset (Profile n) :=
  (preferenceProfileSample n).filter
    (fun profile => profileLabels profile depth = labels)

lemma profileLabelFiber_probability_le_sequenceWeight
    (depth : ℕ) (labels : Fin depth → Fin n) :
    ((profileLabelFiber depth labels).card : ℝ) /
        (preferenceProfileSample n).card ≤
      sequenceWeight (machineWeight (n := n)) depth [] labels := by
  by_cases hfiber : (profileLabelFiber depth labels).Nonempty
  · obtain ⟨reference, hreference⟩ := hfiber
    have hreferenceData := Finset.mem_filter.mp hreference
    have hlabels : profileLabels reference depth = labels :=
      hreferenceData.2
    have hfiberEq : profileLabelFiber depth labels =
        pathFiber depth (profileHistory reference depth) := by
      ext profile
      simp only [profileLabelFiber, pathFiber, Finset.mem_filter]
      constructor
      · intro hprofile
        refine ⟨hprofile.1, (profileLabels_eq_iff profile reference depth).mp ?_⟩
        exact hprofile.2.trans hlabels.symm
      · intro hprofile
        refine ⟨hprofile.1, ?_⟩
        exact ((profileLabels_eq_iff profile reference depth).mpr
          hprofile.2).trans hlabels
    have hpath : pathWeight (machineWeight (n := n))
          (profileHistory reference depth) =
        sequenceWeight (machineWeight (n := n)) depth [] labels := by
      calc
        pathWeight (machineWeight (n := n))
            (profileHistory reference depth) =
            pathWeight (machineWeight (n := n))
              (followSequence depth [] (profileLabels reference depth)) := by
          rw [followSequence_profileLabels]
        _ = pathWeight (machineWeight (n := n)) [] *
              sequenceWeight (machineWeight (n := n)) depth []
                (profileLabels reference depth) :=
          pathWeight_followSequence _ depth [] _
        _ = sequenceWeight (machineWeight (n := n)) depth [] labels := by
          simp [hlabels]
    simpa [hfiberEq, hpath] using
      pathFiber_probability_le_pathWeight reference depth
  · have hcard : (profileLabelFiber depth labels).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.not_nonempty_iff_eq_empty.mp hfiber
    simp only [hcard, Nat.cast_zero, zero_div]
    exact sequenceWeight_nonneg machineWeight_valid depth [] labels

lemma profileLabelFiber_event_ratio_le
    (event : History (Fin n) → Prop) [DecidablePred event]
    (depth : ℕ) (labels : Fin depth → Fin n) :
    (∑ profile ∈ profileLabelFiber depth labels,
        if event (profileHistory profile depth) then (1 : ℝ) else 0) /
          (preferenceProfileSample n).card ≤
      sequenceWeight (machineWeight (n := n)) depth [] labels *
        if event (followSequence depth [] labels) then 1 else 0 := by
  by_cases hevent : event (followSequence depth [] labels)
  · simp only [if_pos hevent, mul_one]
    have hsum :
        (∑ profile ∈ profileLabelFiber depth labels,
          if event (profileHistory profile depth) then (1 : ℝ) else 0) ≤
            ((profileLabelFiber depth labels).card : ℝ) := by
      calc
        (∑ profile ∈ profileLabelFiber depth labels,
          if event (profileHistory profile depth) then (1 : ℝ) else 0) ≤
            ∑ _profile ∈ profileLabelFiber depth labels, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro profile hprofile
          split_ifs <;> norm_num
        _ = ((profileLabelFiber depth labels).card : ℝ) := by simp
    exact (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)).trans
      (profileLabelFiber_probability_le_sequenceWeight depth labels)
  · have hterms :
        (∑ profile ∈ profileLabelFiber depth labels,
          if event (profileHistory profile depth) then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro profile hprofile
      have hlabels := (Finset.mem_filter.mp hprofile).2
      have hhistory : profileHistory profile depth =
          followSequence depth [] labels := by
        rw [← followSequence_profileLabels profile depth, hlabels]
      simp [hhistory, hevent]
    simp [hterms, hevent]

/-- The law of every persistent event on genuine profile paths is dominated
by the corresponding labelled-tree law.  This is the finite law-transfer
statement: no independence assumption is added to the adaptive process. -/
theorem profile_terminal_probability_le_hitProbability
    (event : History (Fin n) → Prop) [DecidablePred event]
    (hpersistent : PersistentEvent event) (depth : ℕ) :
    UniformProduct.probability (preferenceProfileSample n)
        (fun profile => event (profileHistory profile depth)) ≤
      hitProbability (machineWeight (n := n)) event depth [] := by
  have hpartition := Finset.sum_fiberwise
    (preferenceProfileSample n) (fun profile => profileLabels profile depth)
    (fun profile =>
      if event (profileHistory profile depth) then (1 : ℝ) else 0)
  calc
    UniformProduct.probability (preferenceProfileSample n)
        (fun profile => event (profileHistory profile depth)) =
      ∑ labels : Fin depth → Fin n,
        (∑ profile ∈ profileLabelFiber depth labels,
          if event (profileHistory profile depth) then (1 : ℝ) else 0) /
            (preferenceProfileSample n).card := by
      rw [UniformProduct.probability, Finset.expect_eq_sum_div_card,
        ← hpartition, Finset.sum_div]
      rfl
    _ ≤ ∑ labels : Fin depth → Fin n,
        sequenceWeight (machineWeight (n := n)) depth [] labels *
          if event (followSequence depth [] labels) then 1 else 0 := by
      apply Finset.sum_le_sum
      intro labels hlabels
      exact profileLabelFiber_event_ratio_le event depth labels
    _ = hitProbability (machineWeight (n := n)) event depth [] :=
      (hitProbability_eq_sum_terminal_of_persistent machineWeight_valid
        event hpersistent depth []).symm

/-- The probability that a genuine profile path hits an arbitrary event by a
fixed depth is at most the stopped probability on the labelled tree. -/
theorem profile_hit_probability_le_hitProbability
    (event : History (Fin n) → Prop) [DecidablePred event] (depth : ℕ) :
    UniformProduct.probability (preferenceProfileSample n)
        (fun profile => ∃ k ≤ depth, event (profileHistory profile k)) ≤
      hitProbability (machineWeight (n := n)) event depth [] := by
  calc
    UniformProduct.probability (preferenceProfileSample n)
        (fun profile => ∃ k ≤ depth, event (profileHistory profile k)) ≤
      UniformProduct.probability (preferenceProfileSample n)
        (fun profile => pastEvent event (profileHistory profile depth)) := by
      apply UniformProduct.probability_mono
      intro profile hprofile hhit
      exact pastEvent_profileHistory_of_hit profile event hhit
    _ ≤ hitProbability (machineWeight (n := n)) (pastEvent event) depth [] :=
      profile_terminal_probability_le_hitProbability (pastEvent event)
        (pastEvent_persistent event) depth
    _ = hitProbability (machineWeight (n := n)) event depth [] := by
      exact hitProbability_pastEvent_nil _ event depth

/-- The abstract labelled-tree concentration theorem specialized to the PS
choice machine and the concrete absolute phase threshold. -/
theorem treeFailure_hitProbability_le (hn : 0 < n)
    (hlog : 1 ≤ Real.log (n : ℝ)) :
    hitProbability (machineWeight (n := n)) (treeFailure n) (n * n) [] ≤
      Real.exp (-(rateFunction etaZero - Real.log 2) * (n : ℝ)) +
        1 / (n : ℝ) ^ 3 := by
  have hbound := load_bound_tree_failure
    (queryAvailable (n := n)) queryAvailable_nonempty setRecording
    (fun _s => setRecording) (treeLambda n) hn hlog
    (fun s hs => (PhaseAdapter.phaseLambdaZero_pos.le.trans
      (le_max_left _ _)))
    (fun s hs =>
      (PhaseAdapter.phaseLambdaZero_spec.2 (treeLambda n s)
        (le_max_left _ _)).1)
    (fun s hs =>
      (PhaseAdapter.phaseLambdaZero_spec.2 (treeLambda n s)
        (le_max_left _ _)).2.1)
    (n * n)
  convert hbound using 1
  exact hitProbability_congr _ _ _ _
    (fun history a => rfl) (fun history => by rfl) (n * n) []

lemma profile_load_bad_implies_tree_hit (profile : Profile n) (hn : 0 < n)
    (hbad : ¬PhaseAdapter.ConcretePhaseLoadGood profile
      PhaseAdapter.phaseLambdaZero) :
    ∃ depth ≤ n * n, treeFailure n (profileHistory profile depth) := by
  simp only [PhaseAdapter.ConcretePhaseLoadGood] at hbad
  push_neg at hbad
  obtain ⟨phase, hphase, hlambda, hnotGood⟩ := hbad
  exact treeFailure_of_phase_bad profile hn phase hphase hlambda
    hnotGood

omit [Nonempty (Fin n)] in
/-- The missing load-transfer premise in `ConcreteTheoremOne`, now proved on
the genuine uniform permutation-profile sample. -/
theorem concrete_load_transfer (n : ℕ) (hn : 0 < n)
    (hlog : 1 ≤ Real.log (n : ℝ)) :
    UniformProduct.probability (preferenceProfileSample n)
        (fun profile => ¬PhaseAdapter.ConcretePhaseLoadGood profile
          PhaseAdapter.phaseLambdaZero) ≤
      Real.exp (-(rateFunction etaZero - Real.log 2) * (n : ℝ)) +
        1 / (n : ℝ) ^ 3 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  calc
    UniformProduct.probability (preferenceProfileSample n)
        (fun profile => ¬PhaseAdapter.ConcretePhaseLoadGood profile
          PhaseAdapter.phaseLambdaZero) ≤
      UniformProduct.probability (preferenceProfileSample n)
        (fun profile => ∃ depth ≤ n * n,
          treeFailure n (profileHistory profile depth)) := by
      apply UniformProduct.probability_mono
      intro profile hprofile hbad
      exact profile_load_bad_implies_tree_hit profile hn hbad
    _ ≤ hitProbability (machineWeight (n := n))
          (treeFailure n) (n * n) [] :=
      profile_hit_probability_le_hitProbability (treeFailure n) (n * n)
    _ ≤ Real.exp (-(rateFunction etaZero - Real.log 2) * (n : ℝ)) +
          1 / (n : ℝ) ^ 3 := treeFailure_hitProbability_le hn hlog

/-! ## Elementary facts about the round indexing -/

lemma history_length_round_decomposition (history : History (Fin n)) :
    history.length = roundIndex history * n + roundOffset history := by
  unfold roundIndex roundOffset
  simpa [Nat.mul_comm, Nat.add_comm] using
    (Nat.mod_add_div history.length n).symm

lemma queryAgent_val (history : History (Fin n)) :
    (queryAgent history).val = roundOffset history := rfl

lemma roundIndex_cons_of_not_last (history : History (Fin n)) (g : Fin n)
    (h : roundOffset history + 1 < n) :
    roundIndex (g :: history) = roundIndex history := by
  have hn : 0 < n := by
    simpa using
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin n)))
  have hd := Nat.mod_add_div history.length n
  have hu := (Nat.div_mod_unique (a := history.length + 1) (b := n)
    (d := history.length / n) (c := history.length % n + 1) hn).2
      ⟨by omega, by simpa [roundOffset] using h⟩
  simpa [roundIndex] using hu.1

lemma roundOffset_cons_of_not_last (history : History (Fin n)) (g : Fin n)
    (h : roundOffset history + 1 < n) :
    roundOffset (g :: history) = roundOffset history + 1 := by
  have hn : 0 < n := by
    simpa using
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin n)))
  have hd := Nat.mod_add_div history.length n
  have hu := (Nat.div_mod_unique (a := history.length + 1) (b := n)
    (d := history.length / n) (c := history.length % n + 1) hn).2
      ⟨by omega, by simpa [roundOffset] using h⟩
  simpa [roundOffset] using hu.2

lemma roundIndex_cons_of_last (history : History (Fin n)) (g : Fin n)
    (h : roundOffset history + 1 = n) :
    roundIndex (g :: history) = roundIndex history + 1 := by
  have hn : 0 < n := by
    simpa using
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin n)))
  have hd := Nat.mod_add_div history.length n
  have hu := (Nat.div_mod_unique (a := history.length + 1) (b := n)
    (d := history.length / n + 1) (c := 0) hn).2 ⟨?_, by omega⟩
  · simpa [Nat.mul_add] using hu.1
  · simp only [Nat.zero_add, Nat.mul_add, Nat.mul_one]
    simp only [roundOffset] at h
    omega

lemma roundOffset_cons_of_last (history : History (Fin n)) (g : Fin n)
    (h : roundOffset history + 1 = n) :
    roundOffset (g :: history) = 0 := by
  have hn : 0 < n := by
    simpa using
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin n)))
  have hd := Nat.mod_add_div history.length n
  have hu := (Nat.div_mod_unique (a := history.length + 1) (b := n)
    (d := history.length / n + 1) (c := 0) hn).2 ⟨?_, by omega⟩
  · simpa [roundOffset] using hu.2
  · simp only [Nat.zero_add, Nat.mul_add, Nat.mul_one]
    simp only [roundOffset] at h
    omega

end ProbabilisticSerial.PSChoiceMachine
