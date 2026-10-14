import ReplicaPS
import SequentialRevelation
import Mathlib.Order.Interval.Finset.Fin

/-!
# Conditional rank increments by finite permutation counting

Swapping a skipped good with any surviving good gives disjoint injections
into the compatible preference profiles. This proves the rank-jump bound
directly for finite uniform permutations, including the previously removed
goods whose relative positions have not been revealed.
-/

noncomputable section
set_option maxHeartbeats 2000000

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PSRankIncrement

open UniformPermutation PSProcess SequentialRevelation

lemma rankOf_injective {n : ℕ} (σ : PreferenceOrder n) : Function.Injective (rankOf σ) := by
  intro g h heq
  apply σ.symm.injective
  apply Fin.ext
  unfold rankOf at heq
  omega

lemma favorite_eq_of_rank_le {n : ℕ} (σ : PreferenceOrder n)
    (S : Finset (Fin n)) (hS : S.Nonempty) {g : Fin n} (hg : g ∈ S)
    (hmin : ∀ a ∈ S, rankOf σ g ≤ rankOf σ a) : favorite σ S hS = g := by
  apply rankOf_injective σ
  exact le_antisymm (ReplicaPS.favorite_rank_le σ S hS g hg)
    (hmin _ (favorite_mem σ S hS))

lemma rankOf_swap {n : ℕ} (σ : PreferenceOrder n) (g h a : Fin n) :
    rankOf (Equiv.swap g h * σ) a = rankOf σ (Equiv.swap g h a) := by
  simp [rankOf, Equiv.Perm.mul_def]

lemma favorite_swap_of_lt {n : ℕ} (σ : PreferenceOrder n)
    (S : Finset (Fin n)) (hS : S.Nonempty) (g h : Fin n)
    (hg : rankOf σ (favorite σ S hS) < rankOf σ g)
    (hh : rankOf σ (favorite σ S hS) < rankOf σ h) :
    favorite (Equiv.swap g h * σ) S hS = favorite σ S hS := by
  have hcg : favorite σ S hS ≠ g := by intro he; rw [he] at hg; omega
  have hch : favorite σ S hS ≠ h := by intro he; rw [he] at hh; omega
  apply favorite_eq_of_rank_le _ S hS (favorite_mem σ S hS)
  intro a ha
  rw [rankOf_swap, Equiv.swap_apply_of_ne_of_ne hcg hch, rankOf_swap]
  by_cases hag : a = g
  · subst a
    simpa using hh.le
  · by_cases hah : a = h
    · subst a
      simpa using hg.le
    · rw [Equiv.swap_apply_of_ne_of_ne hag hah]
      exact ReplicaPS.favorite_rank_le σ S hS a ha

def skippedProfiles {n : ℕ} (history : RevealHistory n) (agent previous : Fin n)
    (A : Finset (Fin n)) (g : Fin n) : Finset (Profile n) :=
  (compatibleProfiles history).filter (fun profile =>
    rankOf (profile agent) previous < rankOf (profile agent) g ∧
    favorite (profile agent) (insert g A) (Finset.insert_nonempty _ _) = g)

lemma mem_skippedProfiles {n : ℕ} (history : RevealHistory n) (agent previous : Fin n)
    (A : Finset (Fin n)) (g : Fin n) (profile : Profile n) :
    profile ∈ skippedProfiles history agent previous A g ↔
      Compatible profile history ∧
      rankOf (profile agent) previous < rankOf (profile agent) g ∧
      favorite (profile agent) (insert g A) (Finset.insert_nonempty _ _) = g := by
  simp [skippedProfiles, mem_compatibleProfiles_iff, and_assoc]

/-- Each skipped-good event injects into every possible first answer on
`insert g A`, even though `g` itself need not still be available. -/
lemma skipped_map_subset {n : ℕ} (history : RevealHistory n) (agent previous : Fin n)
    (A : Finset (Fin n)) (g : Fin n)
    (hprevious : ∀ r ∈ history, r.agent = agent → previous ∈ r.available)
    (b : Fin n) (hb : b ∈ insert g A) :
    (skippedProfiles history agent previous A g).map (swapProfileEmbedding agent g b) ⊆
      answerFiber history agent (insert g A) (Finset.insert_nonempty _ _) b := by
  intro target ht
  obtain ⟨profile, hp, rfl⟩ := Finset.mem_map.mp ht
  rcases (mem_skippedProfiles history agent previous A g profile).mp hp with ⟨hc, hpg, hfirst⟩
  apply mem_answerFiber_iff.mpr
  constructor
  · intro r hr
    change favorite (swapProfileAt agent g b profile r.agent) r.available _ = r.chosen
    by_cases hra : r.agent = agent
    · have hchosen := hc r hr
      rw [hra] at hchosen
      have hle := ReplicaPS.favorite_rank_le (profile agent) r.available r.nonempty
        previous (hprevious r hr hra)
      have hgb := ReplicaPS.favorite_rank_le (profile agent) (insert g A)
        (Finset.insert_nonempty _ _) b hb
      rw [hfirst] at hgb
      have hltg := hle.trans_lt hpg
      have hltb := hltg.trans_le hgb
      rw [hra, swapProfileAt_apply_same, favorite_swap_of_lt _ _ _ g b hltg hltb]
      exact hchosen
    · rw [swapProfileAt_apply_of_ne profile hra]
      exact hc r hr
  · change favorite (swapProfileAt agent g b profile agent) (insert g A) _ = b
    rw [swapProfileAt_apply_same, favorite_swap_of_mem _ _ _ (Finset.mem_insert_self _ _) hb,
      hfirst, Equiv.swap_apply_left]

theorem skipped_card_mul_le {n : ℕ} (history : RevealHistory n) (agent previous : Fin n)
    (A : Finset (Fin n)) (g : Fin n) (hg : g ∉ A)
    (hprevious : ∀ r ∈ history, r.agent = agent → previous ∈ r.available) :
    (skippedProfiles history agent previous A g).card * (A.card + 1) ≤
      (compatibleProfiles history).card := by
  have h (b : Fin n) (hb : b ∈ insert g A) :
      (skippedProfiles history agent previous A g).card ≤
        (answerFiber history agent (insert g A) (Finset.insert_nonempty _ _) b).card := by
    simpa using Finset.card_le_card (skipped_map_subset history agent previous A g hprevious b hb)
  have hs := Finset.sum_le_sum h
  rw [sum_answerFiber_card_available] at hs
  simpa [Finset.card_insert_of_not_mem hg, Nat.mul_comm] using hs

lemma favorite_insert_eq_iff {n : ℕ} (σ : PreferenceOrder n) (A : Finset (Fin n))
    (hA : A.Nonempty) (g : Fin n) (hg : g ∉ A) :
    favorite σ (insert g A) (Finset.insert_nonempty _ _) = g ↔
      rankOf σ g < rankOf σ (favorite σ A hA) := by
  constructor
  · intro h
    have hle := ReplicaPS.favorite_rank_le σ (insert g A) (Finset.insert_nonempty _ _)
      (favorite σ A hA) (Finset.mem_insert_of_mem (favorite_mem σ A hA))
    rw [h] at hle
    have hne : rankOf σ g ≠ rankOf σ (favorite σ A hA) := by
      intro he
      exact hg ((rankOf_injective σ he).symm ▸ favorite_mem σ A hA)
    omega
  · intro h
    apply favorite_eq_of_rank_le _ _ _ (Finset.mem_insert_self _ _)
    intro b hb
    rcases Finset.mem_insert.mp hb with hb | hb
    · subst b
      exact le_rfl
    · exact h.le.trans (ReplicaPS.favorite_rank_le σ A hA b hb)

def between {n : ℕ} (σ : PreferenceOrder n) (previous next : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun g => rankOf σ previous < rankOf σ g ∧ rankOf σ g < rankOf σ next)

lemma between_card {n : ℕ} (σ : PreferenceOrder n) (previous next : Fin n) :
    (between σ previous next).card = (σ.symm next).val - (σ.symm previous).val - 1 := by
  have hc : (between σ previous next).card = (Finset.Ioo (σ.symm previous) (σ.symm next)).card := by
    apply Finset.card_bij (fun g _ => σ.symm g)
    · intro g hg
      have h := (Finset.mem_filter.mp hg).2
      apply Finset.mem_Ioo.mpr
      change (σ.symm previous).val < (σ.symm g).val ∧
        (σ.symm g).val < (σ.symm next).val
      unfold rankOf at h
      omega
    · intro g hg h hh heq
      exact σ.symm.injective heq
    · intro k hk
      refine ⟨σ k, ?_, by simp⟩
      simp only [between, Finset.mem_filter, Finset.mem_univ, true_and, rankOf,
        Equiv.symm_apply_apply]
      have h := Finset.mem_Ioo.mp hk
      constructor <;> omega
  rw [hc, Fin.card_Ioo]

lemma rank_jump_eq_between {n : ℕ} (σ : PreferenceOrder n) (previous next : Fin n)
    (h : rankOf σ previous < rankOf σ next) :
    (rankOf σ next : ℝ) - rankOf σ previous = 1 + (between σ previous next).card := by
  have hn : rankOf σ next = rankOf σ previous + 1 + (between σ previous next).card := by
    rw [between_card]
    unfold rankOf at h ⊢
    omega
  have hr : (rankOf σ next : ℝ) = rankOf σ previous + 1 + (between σ previous next).card := by
    exact_mod_cast hn
  linarith

lemma between_eq_skipped_filter {n : ℕ} (history : RevealHistory n)
    (agent previous : Fin n) (A : Finset (Fin n)) (hA : A.Nonempty)
    (profile : Profile n) (hc : Compatible profile history) :
    between (profile agent) previous (favorite (profile agent) A hA) =
      (Finset.univ \ insert previous A).filter
        (fun g => profile ∈ skippedProfiles history agent previous A g) := by
  ext g
  simp only [between, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff, Finset.mem_insert, not_or]
  constructor
  · rintro ⟨hpg, hgn⟩
    have hgp : g ≠ previous := by intro he; subst g; omega
    have hgA : g ∉ A := by
      intro hg
      have h := ReplicaPS.favorite_rank_le (profile agent) A hA g hg
      omega
    refine ⟨⟨hgp, hgA⟩, (mem_skippedProfiles _ _ _ _ _ _).mpr ⟨hc, hpg, ?_⟩⟩
    exact (favorite_insert_eq_iff _ _ hA g hgA).mpr hgn
  · rintro ⟨⟨hgp, hgA⟩, hp⟩
    rcases (mem_skippedProfiles _ _ _ _ _ _).mp hp with ⟨_, hpg, hf⟩
    exact ⟨hpg, (favorite_insert_eq_iff _ _ hA g hgA).mp hf⟩

lemma sum_between_card {n : ℕ} (history : RevealHistory n)
    (agent previous : Fin n) (A : Finset (Fin n)) (hA : A.Nonempty) :
    (∑ profile ∈ compatibleProfiles history,
      (between (profile agent) previous (favorite (profile agent) A hA)).card) =
      ∑ g ∈ Finset.univ \ insert previous A, (skippedProfiles history agent previous A g).card := by
  calc
    _ = ∑ profile ∈ compatibleProfiles history,
        ∑ g ∈ Finset.univ \ insert previous A,
          if profile ∈ skippedProfiles history agent previous A g then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro profile hp
      rw [between_eq_skipped_filter history agent previous A hA profile
        (mem_compatibleProfiles_iff.mp hp), Finset.card_filter]
    _ = ∑ g ∈ Finset.univ \ insert previous A,
        ∑ profile ∈ compatibleProfiles history,
          if profile ∈ skippedProfiles history agent previous A g then 1 else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [← Finset.card_filter]
      congr 1
      ext profile
      simp [skippedProfiles]

/-- The paper's conditional expected rank-jump inequality, on an exact
compatible-profile fiber. Its inputs are properties of the revealed labels,
not independence assumptions on the endogenous available set. -/
theorem expected_rank_jump_le {n : ℕ} (history : RevealHistory n)
    (agent previous : Fin n) (A : Finset (Fin n)) (hA : A.Nonempty)
    (hC : (compatibleProfiles history).Nonempty)
    (hquery : AdmissibleQuery history agent A)
    (hprevious : ∀ r ∈ history, r.agent = agent → previous ∈ r.available)
    (hrecord : ∃ r ∈ history, r.agent = agent ∧ r.chosen = previous) :
    (𝔼 profile ∈ compatibleProfiles history,
      ((rankOf (profile agent) (favorite (profile agent) A hA) : ℝ) -
        rankOf (profile agent) previous)) ≤ (n : ℝ) / (A.card + 1) := by
  obtain ⟨r, hr, hra, hrp⟩ := hrecord
  have hpA : previous ∉ A := by
    intro hp
    have h := Finset.mem_erase.mp (hquery r hr hra hp)
    exact h.1 hrp.symm
  have hjump (profile : Profile n) (hp : profile ∈ compatibleProfiles history) :
      rankOf (profile agent) previous <
        rankOf (profile agent) (favorite (profile agent) A hA) := by
    have hc := mem_compatibleProfiles_iff.mp hp
    have hselected := hc r hr
    rw [hra, hrp] at hselected
    have hmem := Finset.mem_erase.mp (hquery r hr hra (favorite_mem (profile agent) A hA))
    have hle := ReplicaPS.favorite_rank_le (profile agent) r.available r.nonempty
      (favorite (profile agent) A hA) hmem.2
    rw [hselected] at hle
    have hne : rankOf (profile agent) previous ≠
        rankOf (profile agent) (favorite (profile agent) A hA) := by
      intro he
      exact hmem.1 ((rankOf_injective _ he).symm.trans hrp.symm)
    omega
  let T := Finset.univ \ insert previous A
  have hcount : (∑ g ∈ T, (skippedProfiles history agent previous A g).card) * (A.card + 1) ≤
      T.card * (compatibleProfiles history).card := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ _g ∈ T, (compatibleProfiles history).card := by
        apply Finset.sum_le_sum
        intro g hg
        have hgA : g ∉ A := by
          have h := (Finset.mem_sdiff.mp hg).2
          exact fun hmem => h (Finset.mem_insert_of_mem hmem)
        exact skipped_card_mul_le history agent previous A g hgA hprevious
      _ = _ := by simp
  have hcard : T.card + (A.card + 1) = n := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (insert previous A))
    simpa [T, Finset.card_insert_of_not_mem hpA] using h
  have hsum :
      (∑ profile ∈ compatibleProfiles history,
        ((rankOf (profile agent) (favorite (profile agent) A hA) : ℝ) -
          rankOf (profile agent) previous)) =
        ((compatibleProfiles history).card : ℝ) +
          ((∑ g ∈ T, (skippedProfiles history agent previous A g).card : ℕ) : ℝ) := by
    calc
      _ = ∑ profile ∈ compatibleProfiles history,
          (1 + ((between (profile agent) previous (favorite (profile agent) A hA)).card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro profile hp
        exact rank_jump_eq_between _ _ _ (hjump profile hp)
      _ = ((compatibleProfiles history).card : ℝ) +
          ((∑ profile ∈ compatibleProfiles history,
            (between (profile agent) previous (favorite (profile agent) A hA)).card : ℕ) : ℝ) := by
        simp [Finset.sum_add_distrib]
      _ = _ := by rw [sum_between_card]
  have hCR : (0 : ℝ) < (compatibleProfiles history).card := by
    exact_mod_cast Finset.card_pos.mpr hC
  rw [Finset.expect_eq_sum_div_card]
  apply (div_le_div_iff₀ hCR (by positivity : (0 : ℝ) < A.card + 1)).2
  rw [hsum]
  have hcountR :
      ((∑ g ∈ T, (skippedProfiles history agent previous A g).card : ℕ) : ℝ) * (A.card + 1) ≤
        (T.card : ℝ) * (compatibleProfiles history).card := by exact_mod_cast hcount
  have hcardR : (T.card : ℝ) + (A.card + 1) = n := by exact_mod_cast hcard
  rw [← hcardR]
  nlinarith

end ProbabilisticSerial.PSRankIncrement
