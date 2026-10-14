import SequentialRevelation
import AdaptiveCategorical

/-!
# Stopped choice counts along probabilistic serial

For a fixed set of goods `B`, the paper records choices entering `B` only
until immediately before the first exhaustion of a good in `B`.  This file
defines the resulting actual count `N_B`, predictable volume `V_B`, and the
event potential `H`.  For every nested PS phase prefix on which `B` remains
active it proves the two identities

`N_B = L_B` and `V_B = |B| (1 + H)`.

The one-step probabilities used in `V_B` are the exact conditional parameters
proved in `SequentialRevelation`, not independent draws imposed on an
endogenous active set.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.StoppedChoices

open UniformPermutation PSProcess SequentialRevelation
open PSProcess.Phase
open AdaptiveCategorical

/-- Uniform categorical transition on a history-dependent available set. The
history contains the identities of all earlier choices, so no filtration
information is discarded. -/
def uniformChoiceWeight {n : ℕ}
    (available : AdaptiveCategorical.History (Fin n) → Finset (Fin n))
    (history : AdaptiveCategorical.History (Fin n)) (g : Fin n) : ℝ :=
  if g ∈ available history then 1 / ((available history).card : ℝ) else 0

lemma uniformChoiceWeight_valid {n : ℕ}
    (available : AdaptiveCategorical.History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty) :
    AdaptiveCategorical.ValidLaw (uniformChoiceWeight available) := by
  intro history
  constructor
  · intro g
    by_cases hg : g ∈ available history
    · simp [uniformChoiceWeight, hg]
    · simp [uniformChoiceWeight, hg]
  · have hcard : ((available history).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr (hnonempty history)).ne'
    simp [uniformChoiceWeight, hcard]

/-- Whether the next labelled choice is recorded as an entry into `B`.  The
Boolean `recording history` implements the predictable stopping rule. -/
def stoppedEntry {n : ℕ} (B : Finset (Fin n))
    (recording : AdaptiveCategorical.History (Fin n) → Bool)
    (history : AdaptiveCategorical.History (Fin n)) (g : Fin n) : Bool :=
  recording history && decide (g ∈ B)

lemma uniformChoice_successProbability {n : ℕ}
    (available : AdaptiveCategorical.History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (B : Finset (Fin n))
    (recording : AdaptiveCategorical.History (Fin n) → Bool)
    (history : AdaptiveCategorical.History (Fin n)) :
    AdaptiveCategorical.successProbability
        (uniformChoiceWeight available) (stoppedEntry B recording) history =
      if recording history then entryParameter B (available history) else 0 := by
  cases hrecording : recording history
  · simp [AdaptiveCategorical.successProbability, uniformChoiceWeight,
      stoppedEntry, hrecording]
  · have hcard : ((available history).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr (hnonempty history)).ne'
    unfold AdaptiveCategorical.successProbability entryParameter
    have hterm (g : Fin n) :
        uniformChoiceWeight available history g *
            (if stoppedEntry B recording history g then 1 else 0) =
          if g ∈ B ∩ available history then
            1 / ((available history).card : ℝ) else 0 := by
      by_cases hgB : g ∈ B <;>
        by_cases hgA : g ∈ available history <;>
          simp [uniformChoiceWeight, stoppedEntry, hrecording, hgB, hgA]
    calc
      (∑ g, uniformChoiceWeight available history g *
        if stoppedEntry B recording history g then 1 else 0) =
          ∑ g, if g ∈ B ∩ available history then
            1 / ((available history).card : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro g hg
        exact hterm g
      _ = ((B ∩ available history).card : ℝ) *
          (1 / ((available history).card : ℝ)) := by
        rw [← Finset.sum_filter]
        have hfilter :
            Finset.univ.filter (fun g : Fin n => g ∈ B ∩ available history) =
              B ∩ available history := by
          ext g
          simp
        rw [hfilter]
        simp
      _ = ((B ∩ available history).card : ℝ) /
          ((available history).card : ℝ) := by ring

/-- Local identification of the finite labelled-tree transition with the
conditional probability on the genuine uniform-permutation profile sample. -/
theorem sequential_revelation_matches_labelled_law {n : ℕ}
    {revealHistory : RevealHistory n} {agent : Fin n}
    {current : Finset (Fin n)} (hcurrent : current.Nonempty)
    (hadmissible : AdmissibleQuery revealHistory agent current)
    (hcompatible : (compatibleProfiles revealHistory).Nonempty)
    (available : AdaptiveCategorical.History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (recording : AdaptiveCategorical.History (Fin n) → Bool)
    (history : AdaptiveCategorical.History (Fin n))
    (havailable : available history = current)
    (hrecording : recording history = true) (B : Finset (Fin n)) :
    conditionalNextProbability revealHistory agent current hcurrent B =
      AdaptiveCategorical.successProbability
        (uniformChoiceWeight available) (stoppedEntry B recording) history := by
  rw [conditional_entry_probability hcurrent hadmissible hcompatible B]
  rw [uniformChoice_successProbability available hnonempty B recording history]
  simp [hrecording, havailable]

/-- The stopped entry process on the full labelled filtration satisfies the
upper time-uniform concentration inequality. -/
theorem stoppedChoice_upper_deviation {n : ℕ}
    (available : AdaptiveCategorical.History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (B : Finset (Fin n))
    (recording : AdaptiveCategorical.History (Fin n) → Bool)
    {x v : ℝ} (hxv : v < x) (hv : 0 < v) (depth : ℕ) :
    AdaptiveCategorical.hitProbability (uniformChoiceWeight available)
        (fun h => x ≤ AdaptiveCategorical.successes
            (stoppedEntry B recording) h ∧
          AdaptiveCategorical.compensator (uniformChoiceWeight available)
            (stoppedEntry B recording) h ≤ v)
        depth [] ≤
      Real.exp (-x * Real.log (x / v) + x - v) :=
  AdaptiveCategorical.upper_deviation
    (uniformChoiceWeight_valid available hnonempty)
    (stoppedEntry B recording) hxv hv depth

/-- The corresponding lower time-uniform concentration inequality. -/
theorem stoppedChoice_lower_deviation {n : ℕ}
    (available : AdaptiveCategorical.History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (B : Finset (Fin n))
    (recording : AdaptiveCategorical.History (Fin n) → Bool)
    {v : ℝ} (hv : 0 ≤ v) (depth : ℕ) :
    AdaptiveCategorical.hitProbability (uniformChoiceWeight available)
        (fun h => v ≤ AdaptiveCategorical.compensator
            (uniformChoiceWeight available) (stoppedEntry B recording) h ∧
          AdaptiveCategorical.successes (stoppedEntry B recording) h ≤
            AdaptiveCategorical.compensator (uniformChoiceWeight available)
              (stoppedEntry B recording) h / 4)
        depth [] ≤
      Real.exp (-AdaptiveBernoulli.lowerRate * v) :=
  AdaptiveCategorical.lower_deviation
    (uniformChoiceWeight_valid available hnonempty)
    (stoppedEntry B recording) hv depth

lemma preimageFinset_mono {n : ℕ} (σ : PreferenceOrder n)
    {S T : Finset (Fin n)} (hST : S ⊆ T) :
    preimageFinset σ S ⊆ preimageFinset σ T := by
  exact Finset.map_subset_map.mpr hST

/-- If an agent's favourite in a larger set survives in a smaller set, it
remains her favourite there. -/
lemma favorite_of_mem_of_subset {n : ℕ} (σ : PreferenceOrder n)
    {S T : Finset (Fin n)} (hS : S.Nonempty) (hT : T.Nonempty)
    (hTS : T ⊆ S) (hf : favorite σ S hS ∈ T) :
    favorite σ T hT = favorite σ S hS := by
  let P := preimageFinset σ S
  let Q := preimageFinset σ T
  have hP : P.Nonempty := preimageFinset_nonempty σ hS
  have hQ : Q.Nonempty := preimageFinset_nonempty σ hT
  have hQP : Q ⊆ P := preimageFinset_mono σ hTS
  have hminP_Q : P.min' hP ∈ Q := by
    have : σ (P.min' hP) ∈ T := by
      simpa [favorite, P] using hf
    simpa [Q, preimageFinset] using this
  have hminQ_P : Q.min' hQ ∈ P := hQP (Q.min'_mem hQ)
  have hle₁ : Q.min' hQ ≤ P.min' hP :=
    Finset.min'_le Q (P.min' hP) hminP_Q
  have hle₂ : P.min' hP ≤ Q.min' hQ :=
    Finset.min'_le P (Q.min' hQ) hminQ_P
  have hmin : Q.min' hQ = P.min' hP := le_antisymm hle₁ hle₂
  unfold favorite
  exact congrArg σ hmin

lemma phase_choice_eq_of_mem {n : ℕ} {profile : Profile n}
    (earlier later : Phase n profile)
    (hsubset : later.active ⊆ earlier.active) (i : Fin n)
    (hsurvives : earlier.choice i ∈ later.active) :
    later.choice i = earlier.choice i := by
  exact favorite_of_mem_of_subset (profile i)
    earlier.active_nonempty later.active_nonempty hsubset hsurvives

/-- Agents eating a good in `B` during a phase. -/
def phaseEaters {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (p : Phase n profile) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p.choice i ∈ B)

/-- Agents displaced between two successive phases. -/
def displacedAgents {n : ℕ} {profile : Profile n}
    (earlier later : Phase n profile) : Finset (Fin n) :=
  Finset.univ.filter (fun i => earlier.choice i ∉ later.active)

def displacedCount {n : ℕ} {profile : Profile n}
    (earlier later : Phase n profile) : ℕ :=
  (displacedAgents earlier later).card

/-- Newly displaced agents whose next choice enters `B`. -/
def transitionEntrants {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (earlier later : Phase n profile) :
    Finset (Fin n) :=
  (displacedAgents earlier later).filter (fun i => later.choice i ∈ B)

/-- Current load on a set of goods. -/
def phaseLoad {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (p : Phase n profile) : ℕ :=
  ∑ g ∈ B, p.load g

lemma phaseLoad_eq_card_phaseEaters {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (p : Phase n profile) :
    phaseLoad B p = (phaseEaters B p).card := by
  unfold phaseLoad phaseEaters
  simp only [Phase.load, demand, consumers]
  rw [Finset.card_filter]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ g ∈ B, if p.choice i = g then 1 else 0) =
    if p.choice i ∈ B then 1 else 0
  simp

lemma phaseEaters_eq_union_transitionEntrants {n : ℕ}
    {profile : Profile n} (B : Finset (Fin n))
    (earlier later : Phase n profile)
    (hsubset : later.active ⊆ earlier.active)
    (hB : B ⊆ later.active) :
    phaseEaters B later =
      phaseEaters B earlier ∪ transitionEntrants B earlier later := by
  ext i
  simp only [phaseEaters, transitionEntrants, displacedAgents,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hlater
    by_cases hsurvives : earlier.choice i ∈ later.active
    · left
      have heq := phase_choice_eq_of_mem earlier later hsubset i hsurvives
      rwa [heq] at hlater
    · exact Or.inr ⟨hsurvives, hlater⟩
  · rintro (hearlier | ⟨hdisplaced, hlater⟩)
    · have hsurvives : earlier.choice i ∈ later.active := hB hearlier
      have heq := phase_choice_eq_of_mem earlier later hsubset i hsurvives
      rwa [heq]
    · exact hlater

lemma phaseEaters_disjoint_transitionEntrants {n : ℕ}
    {profile : Profile n} (B : Finset (Fin n))
    (earlier later : Phase n profile) (hB : B ⊆ later.active) :
    Disjoint (phaseEaters B earlier)
      (transitionEntrants B earlier later) := by
  rw [Finset.disjoint_left]
  intro i hiEarlier hiTransition
  have hiB : earlier.choice i ∈ B :=
    (Finset.mem_filter.mp hiEarlier).2
  have hiNotActive : earlier.choice i ∉ later.active :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hiTransition).1).2
  exact hiNotActive (hB hiB)

lemma phaseEaters_card_update {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (earlier later : Phase n profile)
    (hsubset : later.active ⊆ earlier.active)
    (hB : B ⊆ later.active) :
    (phaseEaters B later).card =
      (phaseEaters B earlier).card +
        (transitionEntrants B earlier later).card := by
  rw [phaseEaters_eq_union_transitionEntrants B earlier later hsubset hB]
  exact Finset.card_union_of_disjoint
    (phaseEaters_disjoint_transitionEntrants B earlier later hB)

/-- New recorded entries after the initial phase. -/
def transitionEntryCount {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) :
    Phase n profile → List (Phase n profile) → ℕ
  | _, [] => 0
  | earlier, later :: rest =>
      (transitionEntrants B earlier later).card +
        transitionEntryCount B later rest

/-- `N_B` for a nonempty phase prefix. -/
def recordedEntryCountFrom {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (first : Phase n profile)
    (rest : List (Phase n profile)) : ℕ :=
  (phaseEaters B first).card + transitionEntryCount B first rest

def lastPhase {n : ℕ} {profile : Profile n} :
    Phase n profile → List (Phase n profile) → Phase n profile
  | first, [] => first
  | _, next :: rest => lastPhase next rest

@[simp] lemma lastPhase_nil {n : ℕ} {profile : Profile n}
    (p : Phase n profile) : lastPhase p [] = p := rfl

@[simp] lemma lastPhase_cons {n : ℕ} {profile : Profile n}
    (p q : Phase n profile) (rest : List (Phase n profile)) :
    lastPhase p (q :: rest) = lastPhase q rest := rfl

/-- The stopping identity `N_B = L_B`: while every good in `B` remains
active, each recorded entrant remains in `B`, and every agent currently in
`B` is either an initial eater or a later recorded entrant. -/
theorem recordedEntryCountFrom_eq_phaseLoad {n : ℕ}
    {profile : Profile n} (B : Finset (Fin n))
    (first : Phase n profile) (rest : List (Phase n profile))
    (hnested : (first :: rest).Pairwise
      (fun earlier later => later.active ⊂ earlier.active))
    (hBactive : ∀ p ∈ first :: rest, B ⊆ p.active) :
    recordedEntryCountFrom B first rest =
      phaseLoad B (lastPhase first rest) := by
  induction rest generalizing first with
  | nil =>
      simp only [recordedEntryCountFrom, transitionEntryCount, add_zero,
        lastPhase_nil]
      exact (phaseLoad_eq_card_phaseEaters B first).symm
  | cons next rest ih =>
      have hpair := List.pairwise_cons.mp hnested
      have hsubsetStrict := hpair.1 next (by simp)
      have hsubset : next.active ⊆ first.active := hsubsetStrict.1
      have hBnext : B ⊆ next.active := hBactive next (by simp)
      have hupdate := phaseEaters_card_update B first next hsubset hBnext
      have hBtail : ∀ p ∈ next :: rest, B ⊆ p.active := by
        intro p hp
        exact hBactive p (by simp [hp])
      have htail := ih next hpair.2 hBtail
      change (phaseEaters B first).card +
          ((transitionEntrants B first next).card +
            transitionEntryCount B next rest) =
        phaseLoad B (lastPhase next rest)
      rw [← Nat.add_assoc, ← hupdate]
      exact htail

/-- The cumulative event potential after the initial choices. -/
def displacementPotentialFrom {n : ℕ} {profile : Profile n} :
    Phase n profile → List (Phase n profile) → ℝ
  | _, [] => 0
  | earlier, later :: rest =>
      (displacedCount earlier later : ℝ) / (later.active.card : ℝ) +
        displacementPotentialFrom later rest

/-- Sum of the exact conditional probabilities of the post-initial choices
entering `B`. -/
def transitionPredictableVolume {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) :
    Phase n profile → List (Phase n profile) → ℝ
  | _, [] => 0
  | earlier, later :: rest =>
      (displacedCount earlier later : ℝ) *
          entryParameter B later.active +
        transitionPredictableVolume B later rest

/-- `V_B` for a nonempty phase prefix, including all `n` initial choices. -/
def predictableVolumeFrom {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (first : Phase n profile)
    (rest : List (Phase n profile)) : ℝ :=
  (n : ℝ) * entryParameter B first.active +
    transitionPredictableVolume B first rest

lemma transitionPredictableVolume_eq_card_mul_potential {n : ℕ}
    {profile : Profile n} (B : Finset (Fin n))
    (first : Phase n profile) (rest : List (Phase n profile))
    (hBactive : ∀ p ∈ rest, B ⊆ p.active) :
    transitionPredictableVolume B first rest =
      (B.card : ℝ) * displacementPotentialFrom first rest := by
  induction rest generalizing first with
  | nil => simp [transitionPredictableVolume, displacementPotentialFrom]
  | cons later rest ih =>
      have hBlater : B ⊆ later.active := hBactive later (by simp)
      have hBrest : ∀ p ∈ rest, B ⊆ p.active := by
        intro p hp
        exact hBactive p (by simp [hp])
      have htail := ih later hBrest
      simp only [transitionPredictableVolume, displacementPotentialFrom]
      rw [entryParameter_eq_card_div hBlater, htail]
      ring

/-- The second stopping identity `V_B = |B| (1 + H)`. The initial `n`
choices contribute `|B|`, and an exhaustion displacing `K` agents while `a`
goods remain contributes `K |B| / a`. -/
theorem predictableVolumeFrom_eq_card_mul_one_add_potential {n : ℕ}
    {profile : Profile n} (hn : 0 < n) (B : Finset (Fin n))
    (first : Phase n profile) (rest : List (Phase n profile))
    (hfirst : first.active = Finset.univ)
    (hBactive : ∀ p ∈ rest, B ⊆ p.active) :
    predictableVolumeFrom B first rest =
      (B.card : ℝ) * (1 + displacementPotentialFrom first rest) := by
  have hBfirst : B ⊆ first.active := by
    rw [hfirst]
    exact Finset.subset_univ B
  have hinitialParameter := entryParameter_eq_card_div hBfirst
  have htransition :=
    transitionPredictableVolume_eq_card_mul_potential B first rest hBactive
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold predictableVolumeFrom
  rw [hinitialParameter, hfirst, Finset.card_univ, Fintype.card_fin,
    htransition]
  field_simp
  ring

/-- Both equations labelled `load-mean` in the paper, packaged for one
nonempty stopped phase prefix. -/
theorem load_mean_identities {n : ℕ} {profile : Profile n}
    (hn : 0 < n) (B : Finset (Fin n))
    (first : Phase n profile) (rest : List (Phase n profile))
    (hnested : (first :: rest).Pairwise
      (fun earlier later => later.active ⊂ earlier.active))
    (hfirst : first.active = Finset.univ)
    (hBactive : ∀ p ∈ first :: rest, B ⊆ p.active) :
    recordedEntryCountFrom B first rest =
        phaseLoad B (lastPhase first rest) ∧
      predictableVolumeFrom B first rest =
        (B.card : ℝ) * (1 + displacementPotentialFrom first rest) := by
  constructor
  · exact recordedEntryCountFrom_eq_phaseLoad B first rest hnested hBactive
  · apply predictableVolumeFrom_eq_card_mul_one_add_potential hn B first rest
      hfirst
    intro p hp
    exact hBactive p (by simp [hp])

lemma run_phases_nonempty_head_active_univ {n : ℕ}
    (profile : Profile n) (hn : 0 < n) :
    ∃ first rest, (run profile).phases = first :: rest ∧
      first.active = Finset.univ := by
  have hA : (activeGoods (initialState n)).Nonempty := by
    rw [activeGoods_initial]
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rw [run, runFrom]
  split
  next hactive =>
    refine ⟨⟨initialState n, initialState_valid n, hactive⟩,
      (runFrom profile
        (stepState profile (initialState n) hactive)
        (stepState_valid profile (initialState n)
          (initialState_valid n) hactive)).phases, rfl, ?_⟩
    exact activeGoods_initial n
  next hactive =>
    exact (hactive hA).elim

/-- Concrete `load-mean` theorem for every nonempty prefix of the actual PS
run that stops before a good of `B` is exhausted. -/
theorem run_prefix_load_mean {n : ℕ} (profile : Profile n) (hn : 0 < n)
    (B : Finset (Fin n)) (first : Phase n profile)
    (rest : List (Phase n profile))
    (hprefix : first :: rest <+: (run profile).phases)
    (hBactive : ∀ p ∈ first :: rest, B ⊆ p.active) :
    recordedEntryCountFrom B first rest =
        phaseLoad B (lastPhase first rest) ∧
      predictableVolumeFrom B first rest =
        (B.card : ℝ) * (1 + displacementPotentialFrom first rest) := by
  have hnested : (first :: rest).Pairwise
      (fun earlier later => later.active ⊂ earlier.active) :=
    List.Pairwise.sublist hprefix.sublist (run_phases_pairwise profile)
  obtain ⟨runFirst, runRest, hrun, hrunFirst⟩ :=
    run_phases_nonempty_head_active_univ profile hn
  have hprefEq := List.prefix_iff_eq_append.mp hprefix
  rw [hrun] at hprefEq
  have hheads := congrArg List.head? hprefEq
  have hfirstEq : first = runFirst := by
    simpa using hheads
  have hfirstActive : first.active = Finset.univ := by
    rw [hfirstEq]
    exact hrunFirst
  exact load_mean_identities hn B first rest hnested hfirstActive hBactive

end ProbabilisticSerial.StoppedChoices
