import ReplicaPS
import SequentialRevelation

/-!
# Exact type-choice law in replica markets

This generalizes the existing permutation-fiber proof to `m*q` agents with
independent rankings of `m` types. It proves conditional uniformity and joint
finite-history counts. It does not assume independent repeated choices.
ReplicaHistory proves admissibility on the generated replica trace, and
ReplicaLaw transfers the weighted process to that trace. Repeated within-type
copy changes are not recorded as fresh type choices.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaRevelation

open UniformPermutation PSProcess
open SequentialRevelation (favorite_swap_of_mem)

/-- One answer already exposed from one agent's preference order. -/
structure Reveal (m q : ℕ) where
  agent : Fin (m * q)
  available : Finset (Fin m)
  chosen : Fin m
  chosen_mem : chosen ∈ available

namespace Reveal

def nonempty {m q : ℕ} (r : Reveal m q) : r.available.Nonempty :=
  ⟨r.chosen, r.chosen_mem⟩

end Reveal

abbrev RevealHistory (m q : ℕ) := List (Reveal m q)

/-- A full preference profile agrees with every answer exposed in `history`. -/
def Compatible {m q : ℕ} (profile : ReplicaPS.Profile m q)
    (history : RevealHistory m q) : Prop :=
  ∀ r ∈ history,
    favorite (profile r.agent) r.available r.nonempty = r.chosen

noncomputable instance instDecidableCompatible {m q : ℕ}
    (profile : ReplicaPS.Profile m q) (history : RevealHistory m q) :
    Decidable (Compatible profile history) :=
  Classical.propDecidable _

/-- The profiles left possible after a revealed history. -/
def compatibleProfiles {m q : ℕ} (history : RevealHistory m q) :
    Finset (ReplicaPS.Profile m q) :=
  (ReplicaPS.profileSample m q).filter (fun profile => Compatible profile history)

/-- A later query is nested below every earlier query made to the same agent,
and excludes each earlier answer. -/
def AdmissibleQuery {m q : ℕ} (history : RevealHistory m q)
    (agent : Fin (m * q)) (available : Finset (Fin m)) : Prop :=
  ∀ r ∈ history, r.agent = agent → available ⊆ r.available.erase r.chosen

/-- Relabel `g` and `h` in one agent's preference order. -/
def swapProfileAt {m q : ℕ} (agent : Fin (m * q)) (g h : Fin m)
    (profile : ReplicaPS.Profile m q) : ReplicaPS.Profile m q :=
  fun i => if i = agent then Equiv.swap g h * profile i else profile i

lemma swapProfileAt_apply_same {m q : ℕ} (agent : Fin (m * q)) (g h : Fin m)
    (profile : ReplicaPS.Profile m q) :
    swapProfileAt agent g h profile agent = Equiv.swap g h * profile agent := by
  simp [swapProfileAt]

lemma swapProfileAt_apply_of_ne {m q : ℕ} {agent i : Fin (m * q)} {g h : Fin m}
    (profile : ReplicaPS.Profile m q) (hi : i ≠ agent) :
    swapProfileAt agent g h profile i = profile i := by
  simp [swapProfileAt, hi]

lemma swapProfileAt_involutive {m q : ℕ} (agent : Fin (m * q)) (g h : Fin m) :
    Function.Involutive (swapProfileAt agent g h) := by
  intro profile
  funext i
  by_cases hi : i = agent
  · subst i
    simp only [swapProfileAt_apply_same]
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  · simp only [swapProfileAt_apply_of_ne _ hi]

def swapProfileEmbedding {m q : ℕ} (agent : Fin (m * q)) (g h : Fin m) :
    ReplicaPS.Profile m q ↪ ReplicaPS.Profile m q :=
  ⟨swapProfileAt agent g h,
    (swapProfileAt_involutive agent g h).injective⟩

lemma swapProfileAt_compatible {m q : ℕ} {history : RevealHistory m q}
    {agent : Fin (m * q)} {available : Finset (Fin m)}
    (hadmissible : AdmissibleQuery history agent available)
    {g h : Fin m} (hg : g ∈ available) (hh : h ∈ available)
    {profile : ReplicaPS.Profile m q} (hcompatible : Compatible profile history) :
    Compatible (swapProfileAt agent g h profile) history := by
  intro r hr
  by_cases hra : r.agent = agent
  · have hsub := hadmissible r hr hra
    have hgEarlier := Finset.mem_erase.mp (hsub hg)
    have hhEarlier := Finset.mem_erase.mp (hsub hh)
    have hprevious := hcompatible r hr
    rw [hra] at hprevious
    rw [hra]
    rw [swapProfileAt_apply_same]
    rw [favorite_swap_of_mem (profile agent) r.available r.nonempty
      hgEarlier.2 hhEarlier.2]
    rw [hprevious]
    exact Equiv.swap_apply_of_ne_of_ne hgEarlier.1.symm hhEarlier.1.symm
  · rw [swapProfileAt_apply_of_ne profile hra]
    exact hcompatible r hr

lemma profileSample_eq_univ (m q : ℕ) :
    ReplicaPS.profileSample m q = Finset.univ := by
  ext profile
  simp [ReplicaPS.profileSample, UniformProduct.productSample,
    preferenceSample, permutationSample]

lemma mem_compatibleProfiles_iff {m q : ℕ} {history : RevealHistory m q}
    {profile : ReplicaPS.Profile m q} :
    profile ∈ compatibleProfiles history ↔ Compatible profile history := by
  rw [compatibleProfiles, profileSample_eq_univ]
  simp

/-- Compatible profiles giving a specified answer to the next query. -/
def answerFiber {m q : ℕ} (history : RevealHistory m q) (agent : Fin (m * q))
    (available : Finset (Fin m)) (havailable : available.Nonempty)
    (g : Fin m) : Finset (ReplicaPS.Profile m q) :=
  (compatibleProfiles history).filter (fun profile =>
    favorite (profile agent) available havailable = g)

lemma mem_answerFiber_iff {m q : ℕ} {history : RevealHistory m q}
    {agent : Fin (m * q)} {available : Finset (Fin m)}
    {havailable : available.Nonempty} {g : Fin m} {profile : ReplicaPS.Profile m q} :
    profile ∈ answerFiber history agent available havailable g ↔
      Compatible profile history ∧
        favorite (profile agent) available havailable = g := by
  simp [answerFiber, mem_compatibleProfiles_iff]

lemma answerFiber_map_swap {m q : ℕ} {history : RevealHistory m q}
    {agent : Fin (m * q)} {available : Finset (Fin m)}
    (havailable : available.Nonempty)
    (hadmissible : AdmissibleQuery history agent available)
    {g h : Fin m} (hg : g ∈ available) (hh : h ∈ available) :
    (answerFiber history agent available havailable g).map
        (swapProfileEmbedding agent g h) =
      answerFiber history agent available havailable h := by
  ext profile
  simp only [Finset.mem_map, mem_answerFiber_iff]
  constructor
  · rintro ⟨source, ⟨hsourceCompatible, hsourceAnswer⟩, rfl⟩
    constructor
    · exact swapProfileAt_compatible hadmissible hg hh hsourceCompatible
    · change favorite ((swapProfileAt agent g h source) agent)
          available havailable = h
      rw [swapProfileAt_apply_same]
      rw [favorite_swap_of_mem (source agent) available havailable hg hh]
      rw [hsourceAnswer, Equiv.swap_apply_left]
  · rintro ⟨hprofileCompatible, hprofileAnswer⟩
    refine ⟨swapProfileAt agent g h profile, ?_,
      swapProfileAt_involutive agent g h profile⟩
    constructor
    · exact swapProfileAt_compatible hadmissible hg hh hprofileCompatible
    · change favorite ((swapProfileAt agent g h profile) agent)
          available havailable = g
      rw [swapProfileAt_apply_same]
      rw [favorite_swap_of_mem (profile agent) available havailable hg hh]
      rw [hprofileAnswer, Equiv.swap_apply_right]

/-- Every still-available answer has the same conditional count after any
compatible admissible history. -/
theorem answerFiber_card_eq {m q : ℕ} {history : RevealHistory m q}
    {agent : Fin (m * q)} {available : Finset (Fin m)}
    (havailable : available.Nonempty)
    (hadmissible : AdmissibleQuery history agent available)
    {g h : Fin m} (hg : g ∈ available) (hh : h ∈ available) :
    (answerFiber history agent available havailable g).card =
      (answerFiber history agent available havailable h).card := by
  rw [← answerFiber_map_swap havailable hadmissible hg hh]
  exact (Finset.card_map (swapProfileEmbedding agent g h)).symm

def answerInProfiles {m q : ℕ} (history : RevealHistory m q) (agent : Fin (m * q))
    (available : Finset (Fin m)) (havailable : available.Nonempty)
    (B : Finset (Fin m)) : Finset (ReplicaPS.Profile m q) :=
  (compatibleProfiles history).filter (fun profile =>
    favorite (profile agent) available havailable ∈ B)

lemma sum_answerFiber_card_on {m q : ℕ} (history : RevealHistory m q)
    (agent : Fin (m * q)) (available : Finset (Fin m))
    (havailable : available.Nonempty) (B : Finset (Fin m)) :
    (∑ g ∈ B,
      (answerFiber history agent available havailable g).card) =
      (answerInProfiles history agent available havailable B).card := by
  simp only [answerFiber, answerInProfiles, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro profile hprofile
  by_cases hchoice :
      favorite (profile agent) available havailable ∈ B
  · rw [if_pos hchoice]
    simp [hchoice]
  · rw [if_neg hchoice]
    simp [hchoice]

lemma sum_answerFiber_card_available {m q : ℕ}
    (history : RevealHistory m q) (agent : Fin (m * q))
    (available : Finset (Fin m)) (havailable : available.Nonempty) :
    (∑ g ∈ available,
      (answerFiber history agent available havailable g).card) =
      (compatibleProfiles history).card := by
  rw [sum_answerFiber_card_on]
  congr 1
  ext profile
  simp only [answerInProfiles, Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, favorite_mem (profile agent) available havailable⟩

/-- Exact finite conditional-count form of sequential revelation. -/
theorem sequential_revelation_count {m q : ℕ} {history : RevealHistory m q}
    {agent : Fin (m * q)} {available : Finset (Fin m)}
    (havailable : available.Nonempty)
    (hadmissible : AdmissibleQuery history agent available)
    (B : Finset (Fin m)) :
    (answerInProfiles history agent available havailable B).card *
        available.card =
      (compatibleProfiles history).card * (B ∩ available).card := by
  let anchor := havailable.choose
  have hanchor : anchor ∈ available := havailable.choose_spec
  let c := (answerFiber history agent available havailable anchor).card
  have hequal (g : Fin m) (hg : g ∈ available) :
      (answerFiber history agent available havailable g).card = c := by
    exact answerFiber_card_eq havailable hadmissible hg hanchor
  have htotal :
      (compatibleProfiles history).card = available.card * c := by
    rw [← sum_answerFiber_card_available history agent available havailable]
    apply Finset.sum_const_nat
    intro g hg
    exact hequal g hg
  have hevent :
      (answerInProfiles history agent available havailable B).card =
        (B ∩ available).card * c := by
    have hrestrict :
        answerInProfiles history agent available havailable B =
          answerInProfiles history agent available havailable
            (B ∩ available) := by
      ext profile
      simp only [answerInProfiles, Finset.mem_filter, Finset.mem_inter]
      constructor
      · intro hp
        exact ⟨hp.1, hp.2,
          favorite_mem (profile agent) available havailable⟩
      · exact fun hp => ⟨hp.1, hp.2.1⟩
    rw [hrestrict]
    rw [← sum_answerFiber_card_on history agent available havailable
      (B ∩ available)]
    apply Finset.sum_const_nat
    intro g hg
    exact hequal g (Finset.mem_inter.mp hg).2
  rw [htotal, hevent]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Conditional probability of the next answer entering `B`, under the
uniform distribution on all profiles compatible with the revealed history. -/
def conditionalNextProbability {m q : ℕ} (history : RevealHistory m q)
    (agent : Fin (m * q)) (available : Finset (Fin m))
    (havailable : available.Nonempty) (B : Finset (Fin m)) : ℝ :=
  ((answerInProfiles history agent available havailable B).card : ℝ) /
    (compatibleProfiles history).card

/-- Conditional on every compatible nested reveal history, the next favourite
is exactly uniform on the currently available set. -/
theorem sequential_revelation_probability {m q : ℕ}
    {history : RevealHistory m q} {agent : Fin (m * q)}
    {available : Finset (Fin m)} (havailable : available.Nonempty)
    (hadmissible : AdmissibleQuery history agent available)
    (hcompatible : (compatibleProfiles history).Nonempty)
    (B : Finset (Fin m)) :
    conditionalNextProbability history agent available havailable B =
      ((B ∩ available).card : ℝ) / available.card := by
  have hcount := sequential_revelation_count havailable hadmissible B
  have hhistoryNat : 0 < (compatibleProfiles history).card :=
    Finset.card_pos.mpr hcompatible
  have havailableNat : 0 < available.card :=
    Finset.card_pos.mpr havailable
  have hhistoryReal : ((compatibleProfiles history).card : ℝ) ≠ 0 := by
    exact_mod_cast hhistoryNat.ne'
  have havailableReal : (available.card : ℝ) ≠ 0 := by
    exact_mod_cast havailableNat.ne'
  unfold conditionalNextProbability
  apply (div_eq_div_iff hhistoryReal havailableReal).2
  have hcountReal :
      ((answerInProfiles history agent available havailable B).card : ℝ) *
          (available.card : ℝ) =
        ((compatibleProfiles history).card : ℝ) *
          ((B ∩ available).card : ℝ) := by
    exact_mod_cast hcount
  simpa [mul_comm] using hcountReal

/-- Append one observed answer to a reveal history. -/
def extendHistory {m q : ℕ} (history : RevealHistory m q) (agent : Fin (m * q))
    (available : Finset (Fin m)) (g : Fin m) (hg : g ∈ available) :
    RevealHistory m q :=
  history ++ [⟨agent, available, g, hg⟩]

lemma compatibleProfiles_extendHistory {m q : ℕ}
    (history : RevealHistory m q) (agent : Fin (m * q))
    (available : Finset (Fin m)) (havailable : available.Nonempty)
    (g : Fin m) (hg : g ∈ available) :
    compatibleProfiles (extendHistory history agent available g hg) =
      answerFiber history agent available havailable g := by
  ext profile
  rw [mem_compatibleProfiles_iff, mem_answerFiber_iff]
  constructor
  · intro hextended
    constructor
    · intro r hr
      exact hextended r (List.mem_append.mpr (Or.inl hr))
    · have hlast := hextended (⟨agent, available, g, hg⟩ : Reveal m q)
        (List.mem_append.mpr (Or.inr (by simp)))
      exact hlast
  · rintro ⟨hprevious, hanswer⟩
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hprevious r hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact hanswer

lemma answerInProfiles_singleton_eq_answerFiber {m q : ℕ}
    (history : RevealHistory m q) (agent : Fin (m * q))
    (available : Finset (Fin m)) (havailable : available.Nonempty)
    (g : Fin m) :
    answerInProfiles history agent available havailable {g} =
      answerFiber history agent available havailable g := by
  ext profile
  simp [answerInProfiles, answerFiber]

lemma answerFiber_card_mul_available {m q : ℕ}
    {history : RevealHistory m q} {agent : Fin (m * q)}
    {available : Finset (Fin m)} (havailable : available.Nonempty)
    (hadmissible : AdmissibleQuery history agent available)
    {g : Fin m} (hg : g ∈ available) :
    (answerFiber history agent available havailable g).card *
        available.card =
      (compatibleProfiles history).card := by
  have hcount := sequential_revelation_count havailable hadmissible ({g})
  rw [answerInProfiles_singleton_eq_answerFiber] at hcount
  simpa [hg] using hcount

/-- Each answer in an extension is an admissible deferred-decision query at
the moment it is revealed. -/
def AdmissibleExtension {m q : ℕ} :
    RevealHistory m q → RevealHistory m q → Prop
  | _, [] => True
  | history, r :: rest =>
      AdmissibleQuery history r.agent r.available ∧
        AdmissibleExtension (history ++ [r]) rest

/-- Exact joint-count factorization for any finite sequentially admissible
extension. This is the finite conditional-independence statement: every
successive answer contributes the reciprocal of its available-set size. -/
theorem sequential_revelation_joint_count {m q : ℕ}
    (history extension : RevealHistory m q)
    (hadmissible : AdmissibleExtension history extension) :
    (compatibleProfiles (history ++ extension)).card *
        (extension.map (fun r => r.available.card)).prod =
      (compatibleProfiles history).card := by
  induction extension generalizing history with
  | nil => simp
  | cons r rest ih =>
      rcases hadmissible with ⟨hrAdmissible, hrestAdmissible⟩
      have hrNonempty : r.available.Nonempty := r.nonempty
      have hfirst := answerFiber_card_mul_available hrNonempty
        hrAdmissible r.chosen_mem
      rw [← compatibleProfiles_extendHistory history r.agent r.available
        hrNonempty r.chosen r.chosen_mem] at hfirst
      have htail := ih (history ++ [r]) hrestAdmissible
      simp only [List.map_cons, List.prod_cons]
      calc
        (compatibleProfiles (history ++ r :: rest)).card *
            (r.available.card *
              (rest.map (fun r => r.available.card)).prod) =
            ((compatibleProfiles ((history ++ [r]) ++ rest)).card *
              (rest.map (fun r => r.available.card)).prod) *
                r.available.card := by
          rw [show history ++ r :: rest =
            (history ++ [r]) ++ rest by simp]
          ac_rfl
        _ = (compatibleProfiles (history ++ [r])).card *
            r.available.card := by rw [htail]
        _ = (compatibleProfiles history).card := hfirst

end ProbabilisticSerial.ReplicaRevelation
