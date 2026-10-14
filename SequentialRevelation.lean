import PSProcess

/-!
# Sequential revelation of uniform preferences

This file formalizes the deferred-decisions lemma used by the probabilistic
serial proof.  A reveal records that one agent chose the favourite element of
a nonempty available set.  A later query to the same agent is admissible when
its available set is contained in every earlier queried set with the earlier
answer removed.

For any compatible history, swapping two goods in the new available set is a
bijection of the compatible preference profiles.  Consequently all possible
answers to the new query have exactly the same conditional count.  This is the
finite uniform-permutation form of sequential revelation and remains valid
when the query itself was selected from the earlier revealed history.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.SequentialRevelation

open UniformPermutation PSProcess

/-- One answer already exposed from one agent's preference order. -/
structure Reveal (n : ℕ) where
  agent : Fin n
  available : Finset (Fin n)
  chosen : Fin n
  chosen_mem : chosen ∈ available

namespace Reveal

def nonempty {n : ℕ} (r : Reveal n) : r.available.Nonempty :=
  ⟨r.chosen, r.chosen_mem⟩

end Reveal

abbrev RevealHistory (n : ℕ) := List (Reveal n)

/-- A full preference profile agrees with every answer exposed in `history`. -/
def Compatible {n : ℕ} (profile : Profile n)
    (history : RevealHistory n) : Prop :=
  ∀ r ∈ history,
    favorite (profile r.agent) r.available r.nonempty = r.chosen

noncomputable instance instDecidableCompatible {n : ℕ}
    (profile : Profile n) (history : RevealHistory n) :
    Decidable (Compatible profile history) :=
  Classical.propDecidable _

/-- The profiles left possible after a revealed history. -/
def compatibleProfiles {n : ℕ} (history : RevealHistory n) :
    Finset (Profile n) :=
  (preferenceProfileSample n).filter (fun profile => Compatible profile history)

/-- A later query is nested below every earlier query made to the same agent,
and excludes each earlier answer. -/
def AdmissibleQuery {n : ℕ} (history : RevealHistory n)
    (agent : Fin n) (available : Finset (Fin n)) : Prop :=
  ∀ r ∈ history, r.agent = agent → available ⊆ r.available.erase r.chosen

lemma favorite_map {n : ℕ} (τ σ : PreferenceOrder n)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    favorite (τ * σ) (S.map τ.toEmbedding)
        (Finset.Nonempty.map (f := τ.toEmbedding) hS) =
      τ (favorite σ S hS) := by
  have hpre :
      preimageFinset (τ * σ) (S.map τ.toEmbedding) =
        preimageFinset σ S :=
    preimageFinset_mul_of_map_eq τ σ rfl
  have hmin :
      (preimageFinset (τ * σ) (S.map τ.toEmbedding)).min'
          (preimageFinset_nonempty (τ * σ)
            (Finset.Nonempty.map (f := τ.toEmbedding) hS)) =
        (preimageFinset σ S).min' (preimageFinset_nonempty σ hS) := by
    congr 1
  unfold favorite
  rw [Equiv.Perm.mul_apply, hmin]

lemma favorite_congr {n : ℕ} (σ : PreferenceOrder n)
    {S T : Finset (Fin n)} (hS : S.Nonempty) (hT : T.Nonempty)
    (hST : S = T) :
    favorite σ S hS = favorite σ T hT := by
  subst T
  rfl

lemma map_swap_eq_of_mem {n : ℕ} (S : Finset (Fin n))
    {g h : Fin n} (hg : g ∈ S) (hh : h ∈ S) :
    S.map (Equiv.swap g h).toEmbedding = S := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hyg : y = g
    · subst y
      simpa using hh
    · by_cases hyh : y = h
      · subst y
        simpa using hg
      · simpa [Equiv.swap_apply_of_ne_of_ne hyg hyh] using hy
  · intro hx
    refine ⟨Equiv.swap g h x, ?_, Equiv.swap_apply_self g h x⟩
    by_cases hxg : x = g
    · subst x
      simpa using hh
    · by_cases hxh : x = h
      · subst x
        simpa using hg
      · simpa [Equiv.swap_apply_of_ne_of_ne hxg hxh] using hx

lemma favorite_swap_of_mem {n : ℕ} (σ : PreferenceOrder n)
    (S : Finset (Fin n)) (hS : S.Nonempty) {g h : Fin n}
    (hg : g ∈ S) (hh : h ∈ S) :
    favorite (Equiv.swap g h * σ) S hS =
      Equiv.swap g h (favorite σ S hS) := by
  have hmap := map_swap_eq_of_mem S hg hh
  have hmapNonempty :
      (S.map (Equiv.swap g h).toEmbedding).Nonempty :=
    Finset.Nonempty.map (f := (Equiv.swap g h).toEmbedding) hS
  have hm := favorite_map (Equiv.swap g h) σ S hS
  calc
    favorite (Equiv.swap g h * σ) S hS =
        favorite (Equiv.swap g h * σ)
          (S.map (Equiv.swap g h).toEmbedding) hmapNonempty :=
      favorite_congr _ hS hmapNonempty hmap.symm
    _ = Equiv.swap g h (favorite σ S hS) := hm

/-- Relabel `g` and `h` in one agent's preference order. -/
def swapProfileAt {n : ℕ} (agent g h : Fin n)
    (profile : Profile n) : Profile n :=
  fun i => if i = agent then Equiv.swap g h * profile i else profile i

lemma swapProfileAt_apply_same {n : ℕ} (agent g h : Fin n)
    (profile : Profile n) :
    swapProfileAt agent g h profile agent = Equiv.swap g h * profile agent := by
  simp [swapProfileAt]

lemma swapProfileAt_apply_of_ne {n : ℕ} {agent i g h : Fin n}
    (profile : Profile n) (hi : i ≠ agent) :
    swapProfileAt agent g h profile i = profile i := by
  simp [swapProfileAt, hi]

lemma swapProfileAt_involutive {n : ℕ} (agent g h : Fin n) :
    Function.Involutive (swapProfileAt agent g h) := by
  intro profile
  funext i
  by_cases hi : i = agent
  · subst i
    simp only [swapProfileAt_apply_same]
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  · simp only [swapProfileAt_apply_of_ne _ hi]

def swapProfileEmbedding {n : ℕ} (agent g h : Fin n) :
    Profile n ↪ Profile n :=
  ⟨swapProfileAt agent g h,
    (swapProfileAt_involutive agent g h).injective⟩

lemma swapProfileAt_compatible {n : ℕ} {history : RevealHistory n}
    {agent : Fin n} {available : Finset (Fin n)}
    (hadmissible : AdmissibleQuery history agent available)
    {g h : Fin n} (hg : g ∈ available) (hh : h ∈ available)
    {profile : Profile n} (hcompatible : Compatible profile history) :
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

lemma preferenceProfileSample_eq_univ (n : ℕ) :
    preferenceProfileSample n = Finset.univ := by
  ext profile
  simp [preferenceProfileSample, UniformProduct.productSample,
    preferenceSample, permutationSample]

lemma mem_compatibleProfiles_iff {n : ℕ} {history : RevealHistory n}
    {profile : Profile n} :
    profile ∈ compatibleProfiles history ↔ Compatible profile history := by
  rw [compatibleProfiles, preferenceProfileSample_eq_univ]
  simp

/-- Compatible profiles giving a specified answer to the next query. -/
def answerFiber {n : ℕ} (history : RevealHistory n) (agent : Fin n)
    (available : Finset (Fin n)) (havailable : available.Nonempty)
    (g : Fin n) : Finset (Profile n) :=
  (compatibleProfiles history).filter (fun profile =>
    favorite (profile agent) available havailable = g)

lemma mem_answerFiber_iff {n : ℕ} {history : RevealHistory n}
    {agent : Fin n} {available : Finset (Fin n)}
    {havailable : available.Nonempty} {g : Fin n} {profile : Profile n} :
    profile ∈ answerFiber history agent available havailable g ↔
      Compatible profile history ∧
        favorite (profile agent) available havailable = g := by
  simp [answerFiber, mem_compatibleProfiles_iff]

lemma answerFiber_map_swap {n : ℕ} {history : RevealHistory n}
    {agent : Fin n} {available : Finset (Fin n)}
    (havailable : available.Nonempty)
    (hadmissible : AdmissibleQuery history agent available)
    {g h : Fin n} (hg : g ∈ available) (hh : h ∈ available) :
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
theorem answerFiber_card_eq {n : ℕ} {history : RevealHistory n}
    {agent : Fin n} {available : Finset (Fin n)}
    (havailable : available.Nonempty)
    (hadmissible : AdmissibleQuery history agent available)
    {g h : Fin n} (hg : g ∈ available) (hh : h ∈ available) :
    (answerFiber history agent available havailable g).card =
      (answerFiber history agent available havailable h).card := by
  rw [← answerFiber_map_swap havailable hadmissible hg hh]
  exact (Finset.card_map (swapProfileEmbedding agent g h)).symm

def answerInProfiles {n : ℕ} (history : RevealHistory n) (agent : Fin n)
    (available : Finset (Fin n)) (havailable : available.Nonempty)
    (B : Finset (Fin n)) : Finset (Profile n) :=
  (compatibleProfiles history).filter (fun profile =>
    favorite (profile agent) available havailable ∈ B)

lemma sum_answerFiber_card_on {n : ℕ} (history : RevealHistory n)
    (agent : Fin n) (available : Finset (Fin n))
    (havailable : available.Nonempty) (B : Finset (Fin n)) :
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

lemma sum_answerFiber_card_available {n : ℕ}
    (history : RevealHistory n) (agent : Fin n)
    (available : Finset (Fin n)) (havailable : available.Nonempty) :
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
theorem sequential_revelation_count {n : ℕ} {history : RevealHistory n}
    {agent : Fin n} {available : Finset (Fin n)}
    (havailable : available.Nonempty)
    (hadmissible : AdmissibleQuery history agent available)
    (B : Finset (Fin n)) :
    (answerInProfiles history agent available havailable B).card *
        available.card =
      (compatibleProfiles history).card * (B ∩ available).card := by
  let anchor := havailable.choose
  have hanchor : anchor ∈ available := havailable.choose_spec
  let c := (answerFiber history agent available havailable anchor).card
  have hequal (g : Fin n) (hg : g ∈ available) :
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
def conditionalNextProbability {n : ℕ} (history : RevealHistory n)
    (agent : Fin n) (available : Finset (Fin n))
    (havailable : available.Nonempty) (B : Finset (Fin n)) : ℝ :=
  ((answerInProfiles history agent available havailable B).card : ℝ) /
    (compatibleProfiles history).card

/-- Conditional on every compatible nested reveal history, the next favourite
is exactly uniform on the currently available set. -/
theorem sequential_revelation_probability {n : ℕ}
    {history : RevealHistory n} {agent : Fin n}
    {available : Finset (Fin n)} (havailable : available.Nonempty)
    (hadmissible : AdmissibleQuery history agent available)
    (hcompatible : (compatibleProfiles history).Nonempty)
    (B : Finset (Fin n)) :
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

/-- Bernoulli parameter for the event that a uniform next choice from
`available` enters `B`. -/
def entryParameter {n : ℕ} (B available : Finset (Fin n)) : ℝ :=
  ((B ∩ available).card : ℝ) / available.card

lemma entryParameter_nonneg {n : ℕ} (B available : Finset (Fin n)) :
    0 ≤ entryParameter B available := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma entryParameter_le_one {n : ℕ} (B available : Finset (Fin n))
    (havailable : available.Nonempty) :
    entryParameter B available ≤ 1 := by
  have hcard : (B ∩ available).card ≤ available.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hpositive : (0 : ℝ) < available.card := by
    exact_mod_cast Finset.card_pos.mpr havailable
  apply (div_le_iff₀ hpositive).2
  simpa using hcard

lemma entryParameter_valid {n : ℕ} (B available : Finset (Fin n))
    (havailable : available.Nonempty) :
    0 ≤ entryParameter B available ∧ entryParameter B available ≤ 1 :=
  ⟨entryParameter_nonneg B available,
    entryParameter_le_one B available havailable⟩

/-- The exact conditional probability from sequential revelation is the
valid adaptive Bernoulli parameter `|B ∩ A| / |A|`. -/
theorem conditional_entry_probability {n : ℕ}
    {history : RevealHistory n} {agent : Fin n}
    {available : Finset (Fin n)} (havailable : available.Nonempty)
    (hadmissible : AdmissibleQuery history agent available)
    (hcompatible : (compatibleProfiles history).Nonempty)
    (B : Finset (Fin n)) :
    conditionalNextProbability history agent available havailable B =
      entryParameter B available :=
  sequential_revelation_probability havailable hadmissible hcompatible B

lemma entryParameter_eq_card_div {n : ℕ} {B available : Finset (Fin n)}
    (hB : B ⊆ available) :
    entryParameter B available = (B.card : ℝ) / available.card := by
  rw [entryParameter, Finset.inter_eq_left.mpr hB]

/-- Append one observed answer to a reveal history. -/
def extendHistory {n : ℕ} (history : RevealHistory n) (agent : Fin n)
    (available : Finset (Fin n)) (g : Fin n) (hg : g ∈ available) :
    RevealHistory n :=
  history ++ [⟨agent, available, g, hg⟩]

lemma compatibleProfiles_extendHistory {n : ℕ}
    (history : RevealHistory n) (agent : Fin n)
    (available : Finset (Fin n)) (havailable : available.Nonempty)
    (g : Fin n) (hg : g ∈ available) :
    compatibleProfiles (extendHistory history agent available g hg) =
      answerFiber history agent available havailable g := by
  ext profile
  rw [mem_compatibleProfiles_iff, mem_answerFiber_iff]
  constructor
  · intro hextended
    constructor
    · intro r hr
      exact hextended r (List.mem_append.mpr (Or.inl hr))
    · have hlast := hextended (⟨agent, available, g, hg⟩ : Reveal n)
        (List.mem_append.mpr (Or.inr (by simp)))
      exact hlast
  · rintro ⟨hprevious, hanswer⟩
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hprevious r hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact hanswer

lemma answerInProfiles_singleton_eq_answerFiber {n : ℕ}
    (history : RevealHistory n) (agent : Fin n)
    (available : Finset (Fin n)) (havailable : available.Nonempty)
    (g : Fin n) :
    answerInProfiles history agent available havailable {g} =
      answerFiber history agent available havailable g := by
  ext profile
  simp [answerInProfiles, answerFiber]

lemma answerFiber_card_mul_available {n : ℕ}
    {history : RevealHistory n} {agent : Fin n}
    {available : Finset (Fin n)} (havailable : available.Nonempty)
    (hadmissible : AdmissibleQuery history agent available)
    {g : Fin n} (hg : g ∈ available) :
    (answerFiber history agent available havailable g).card *
        available.card =
      (compatibleProfiles history).card := by
  have hcount := sequential_revelation_count havailable hadmissible ({g})
  rw [answerInProfiles_singleton_eq_answerFiber] at hcount
  simpa [hg] using hcount

/-- Each answer in an extension is an admissible deferred-decision query at
the moment it is revealed. -/
def AdmissibleExtension {n : ℕ} :
    RevealHistory n → RevealHistory n → Prop
  | _, [] => True
  | history, r :: rest =>
      AdmissibleQuery history r.agent r.available ∧
        AdmissibleExtension (history ++ [r]) rest

/-- Exact joint-count factorization for any finite sequentially admissible
extension. This is the finite conditional-independence statement: every
successive answer contributes the reciprocal of its available-set size. -/
theorem sequential_revelation_joint_count {n : ℕ}
    (history extension : RevealHistory n)
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

section ConcretePS

open PSProcess.Phase

/-- Every phase reached from `q` has an active set contained in the active set
at `q`. -/
theorem runFrom_phase_active_subset {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hq : ValidState q) :
    ∀ p ∈ (runFrom profile q hq).phases,
      p.active ⊆ activeGoods q := by
  rw [runFrom]
  split
  next hA =>
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Finset.Subset.rfl
    · have htail := runFrom_phase_active_subset profile
        (stepState profile q hA) (stepState_valid profile q hq hA) p hp
      exact htail.trans (activeGoods_step_subset profile q hA)
  next hA =>
    simp
termination_by (activeGoods q).card
decreasing_by
  apply activeGoods_step_card_lt

/-- The phase active sets in a concrete PS run form a strictly decreasing
chain, including across simultaneous exhaustions. -/
theorem runFrom_phases_pairwise {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hq : ValidState q) :
    (runFrom profile q hq).phases.Pairwise
      (fun earlier later => later.active ⊂ earlier.active) := by
  rw [runFrom]
  split
  next hA =>
    apply List.pairwise_cons.mpr
    constructor
    · intro later hlater
      have hwithin := runFrom_phase_active_subset profile
        (stepState profile q hA) (stepState_valid profile q hq hA)
        later hlater
      change later.active ⊂ activeGoods q
      exact Finset.ssubset_of_subset_of_ssubset hwithin
        (activeGoods_step_ssubset profile q hA)
    · exact runFrom_phases_pairwise profile
        (stepState profile q hA) (stepState_valid profile q hq hA)
  next hA =>
    simp
termination_by (activeGoods q).card
decreasing_by
  apply activeGoods_step_card_lt

theorem run_phases_pairwise {n : ℕ} (profile : Profile n) :
    (run profile).phases.Pairwise
      (fun earlier later => later.active ⊂ earlier.active) :=
  runFrom_phases_pairwise profile (initialState n) (initialState_valid n)

/-- The reveal made when agent `i` starts consuming in phase `p`. -/
def phaseReveal {n : ℕ} {profile : Profile n}
    (p : Phase n profile) (i : Fin n) : Reveal n :=
  ⟨i, p.active, p.choice i, p.choice_mem_active i⟩

@[simp] lemma phaseReveal_agent {n : ℕ} {profile : Profile n}
    (p : Phase n profile) (i : Fin n) :
    (phaseReveal p i).agent = i := rfl

@[simp] lemma phaseReveal_available {n : ℕ} {profile : Profile n}
    (p : Phase n profile) (i : Fin n) :
    (phaseReveal p i).available = p.active := rfl

@[simp] lemma phaseReveal_chosen {n : ℕ} {profile : Profile n}
    (p : Phase n profile) (i : Fin n) :
    (phaseReveal p i).chosen = p.choice i := rfl

lemma phaseReveals_compatible {n : ℕ} {profile : Profile n}
    (phases : List (Phase n profile)) (i : Fin n) :
    Compatible profile (phases.map (fun p => phaseReveal p i)) := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  rfl

/-- A query is admissible whenever its available set is nested below the
earlier sets for that agent and the earlier selected goods have disappeared.
This is the deterministic bridge used at every PS exhaustion event. -/
lemma admissibleQuery_of_nested_displaced {n : ℕ}
    (history : RevealHistory n) (agent : Fin n)
    (available : Finset (Fin n))
    (hnested : ∀ r ∈ history, r.agent = agent →
      available ⊆ r.available)
    (hdisplaced : ∀ r ∈ history, r.agent = agent →
      r.chosen ∉ available) :
    AdmissibleQuery history agent available := by
  intro r hr hra g hg
  apply Finset.mem_erase.mpr
  exact ⟨fun hgr => hdisplaced r hr hra (hgr ▸ hg), hnested r hr hra hg⟩

/-- In particular, any collection of earlier PS selections for an agent gives
an admissible next reveal once those selected goods are no longer active. -/
lemma phase_query_admissible {n : ℕ} {profile : Profile n}
    (current : Phase n profile) (history : RevealHistory n)
    (agent : Fin n)
    (hEarlier : ∀ r ∈ history, r.agent = agent →
      current.active ⊆ r.available)
    (hExhausted : ∀ r ∈ history, r.agent = agent →
      r.chosen ∉ current.active) :
    AdmissibleQuery history agent current.active :=
  admissibleQuery_of_nested_displaced history agent current.active
    hEarlier hExhausted

/-- Concrete phase form of sequential revelation. Earlier records may include
choices by every agent; only the same agent's earlier answers enter the
admissibility check. -/
theorem phase_choice_conditional_uniform {n : ℕ} {profile : Profile n}
    (current : Phase n profile) (history : RevealHistory n)
    (agent : Fin n)
    (hcompatible : Compatible profile history)
    (hEarlier : ∀ r ∈ history, r.agent = agent →
      current.active ⊆ r.available)
    (hExhausted : ∀ r ∈ history, r.agent = agent →
      r.chosen ∉ current.active)
    (B : Finset (Fin n)) :
    conditionalNextProbability history agent current.active
        current.active_nonempty B =
      entryParameter B current.active := by
  have hprofileMem : profile ∈ compatibleProfiles history :=
    mem_compatibleProfiles_iff.mpr hcompatible
  exact conditional_entry_probability current.active_nonempty
    (phase_query_admissible current history agent hEarlier hExhausted)
    ⟨profile, hprofileMem⟩ B

end ConcretePS

end ProbabilisticSerial.SequentialRevelation
