import UniformSubsetRank
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Perm

/-!
# Uniform random preference profiles

A strict preference order on n goods is represented by a permutation sending
each rank position to the good at that position. This file proves that, for
every fixed active set S, the positions occupied by S under a uniform
permutation are a uniform subset of the appropriate cardinality.

The proof does not postulate this marginal law. It derives it by averaging over
the permutation action on equal-cardinality finsets. It then places all
nonempty active sets on one common product sample of n independent preference
orders and proves the simultaneous exponential active-rank bound.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.UniformPermutation

open UniformProduct UniformSubsetRank

def permutationSample (α : Type*) [Fintype α] [DecidableEq α] :
    Finset (Equiv.Perm α) :=
  Finset.univ

def preimageFinset {α : Type*} (σ : Equiv.Perm α) (S : Finset α) : Finset α :=
  S.map σ.symm.toEmbedding

lemma exists_perm_map_eq {α : Type*} [Fintype α] [DecidableEq α]
    {S T : Finset α} (hcard : S.card = T.card) :
    ∃ τ : Equiv.Perm α, S.map τ.toEmbedding = T := by
  have htypes : Fintype.card S = Fintype.card T := by
    simpa using hcard
  let e : S ≃ T := Classical.choice (Fintype.card_eq.mp htypes)
  let τ : Equiv.Perm α := e.extendSubtype
  refine ⟨τ, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_map.mp hy
    exact e.extendSubtype_mem x hxS
  · intro hyT
    let z : T := ⟨y, hyT⟩
    let x : S := e.symm z
    have hxS : (x : α) ∈ S := x.property
    apply Finset.mem_map.mpr
    refine ⟨x, hxS, ?_⟩
    change e.extendSubtype (x : α) = y
    rw [e.extendSubtype_apply_of_mem _ hxS]
    change (e x : α) = y
    simp [x, z]

lemma preimageFinset_mul_of_map_eq {α : Type*} [Fintype α] [DecidableEq α]
    {S T : Finset α} (τ σ : Equiv.Perm α)
    (hmap : S.map τ.toEmbedding = T) :
    preimageFinset (τ * σ) T = preimageFinset σ S := by
  rw [← hmap]
  ext x
  simp [preimageFinset, Equiv.Perm.mul_apply]

lemma preimage_sum_eq_of_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset α → ℝ) {S T : Finset α} (hcard : S.card = T.card) :
    (∑ σ : Equiv.Perm α, F (preimageFinset σ S)) =
      ∑ σ : Equiv.Perm α, F (preimageFinset σ T) := by
  obtain ⟨τ, hτ⟩ := exists_perm_map_eq hcard
  apply Fintype.sum_bijective (Equiv.mulLeft τ) (Equiv.mulLeft τ).bijective
  intro σ
  congr 1
  exact (preimageFinset_mul_of_map_eq τ σ hτ).symm

lemma preimage_expect_eq_of_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset α → ℝ) {S T : Finset α} (hcard : S.card = T.card) :
    (𝔼 σ ∈ permutationSample α, F (preimageFinset σ S)) =
      𝔼 σ ∈ permutationSample α, F (preimageFinset σ T) := by
  simp only [permutationSample, Finset.expect_eq_sum_div_card]
  congr 1
  simpa using preimage_sum_eq_of_card_eq F hcard

lemma powerset_preimage_expect {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (σ : Equiv.Perm α) (F : Finset α → ℝ) :
    (𝔼 T ∈ (Finset.univ : Finset α).powersetCard k,
        F (preimageFinset σ T)) =
      𝔼 T ∈ (Finset.univ : Finset α).powersetCard k, F T := by
  let P := (Finset.univ : Finset α).powersetCard k
  let E := (Finset.mapEmbedding σ.symm.toEmbedding).toEmbedding
  have hmap : P.map E = P := by
    have hp := Finset.powersetCard_map σ.symm.toEmbedding k
      (Finset.univ : Finset α)
    rw [Finset.univ_map_equiv_to_embedding] at hp
    exact hp.symm
  simp only [Finset.expect_eq_sum_div_card]
  congr 1
  calc
    (∑ T ∈ P, F (preimageFinset σ T)) = ∑ U ∈ P.map E, F U := by
      change (∑ T ∈ P, F (E T)) = ∑ U ∈ P.map E, F U
      exact (Finset.sum_map P E F).symm
    _ = ∑ U ∈ P, F U := by rw [hmap]

theorem perm_preimage_expect_eq_powerset_expect
    {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (F : Finset α → ℝ) :
    (𝔼 σ ∈ permutationSample α, F (preimageFinset σ S)) =
      𝔼 T ∈ (Finset.univ : Finset α).powersetCard S.card, F T := by
  let P := (Finset.univ : Finset α).powersetCard S.card
  have hP : P.Nonempty := by
    dsimp [P]
    rw [Finset.powersetCard_nonempty]
    exact S.card_le_univ
  calc
    (𝔼 σ ∈ permutationSample α, F (preimageFinset σ S)) =
        𝔼 _T ∈ P, 𝔼 σ ∈ permutationSample α,
          F (preimageFinset σ S) := by
      rw [Finset.expect_const hP]
    _ = 𝔼 T ∈ P, 𝔼 σ ∈ permutationSample α,
          F (preimageFinset σ T) := by
      apply Finset.expect_congr rfl
      intro T hT
      apply preimage_expect_eq_of_card_eq
      exact (Finset.mem_powersetCard.mp hT).2.symm
    _ = 𝔼 σ ∈ permutationSample α, 𝔼 T ∈ P,
          F (preimageFinset σ T) := by
      exact Finset.expect_comm P (permutationSample α)
        (fun T σ => F (preimageFinset σ T))
    _ = 𝔼 σ ∈ permutationSample α, 𝔼 T ∈ P, F T := by
      apply Finset.expect_congr rfl
      intro σ hσ
      exact powerset_preimage_expect S.card σ F
    _ = 𝔼 T ∈ P, F T := by
      rw [Finset.expect_const (by simp [permutationSample])]

abbrev PreferenceOrder (n : ℕ) := Equiv.Perm (Fin n)

/-- All strict preference orders on the n goods, with the uniform law.  A
permutation sends a rank position to the good occupying that position. -/
def preferenceSample (n : ℕ) : Finset (PreferenceOrder n) :=
  permutationSample (Fin n)

/-- One common sample space for the n independent preference orders. -/
def preferenceProfileSample (n : ℕ) :
    Finset (Fin n → PreferenceOrder n) :=
  productSample (preferenceSample n) n

lemma preferenceSample_nonempty (n : ℕ) : (preferenceSample n).Nonempty := by
  refine ⟨Equiv.refl (Fin n), ?_⟩
  simp [preferenceSample, permutationSample]

lemma preferenceProfileSample_nonempty (n : ℕ) :
    (preferenceProfileSample n).Nonempty := by
  exact productSample_nonempty (preferenceSample_nonempty n) n

/-- Natural-number positions occupied by the goods in S under σ. -/
def activePositions {n : ℕ} (S : Finset (Fin n)) (σ : PreferenceOrder n) :
    Finset ℕ :=
  (preimageFinset σ S).map Fin.valEmbedding

/-- One-indexed rank of the first good in S. -/
def activeRank {n : ℕ} (S : Finset (Fin n)) (σ : PreferenceOrder n) : ℕ :=
  firstRank (activePositions S σ)

/-- The paper's scaled active-rank statistic, (card S / n) * rank. -/
def scaledActiveRank (n : ℕ) (S : Finset (Fin n))
    (σ : PreferenceOrder n) : ℝ :=
  ((S.card : ℝ) / n) * activeRank S σ

lemma activePositions_mem_rankSample {n : ℕ} (S : Finset (Fin n))
    (σ : PreferenceOrder n) :
    activePositions S σ ∈ rankSample n S.card := by
  rw [rankSample, Finset.mem_powersetCard]
  constructor
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hr
    exact Finset.mem_range.mpr i.isLt
  · simp [activePositions, preimageFinset]

lemma finSubset_expect_eq_rankSample (n s : ℕ) (F : Finset ℕ → ℝ) :
    (𝔼 T ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        F (T.map Fin.valEmbedding)) =
      𝔼 U ∈ rankSample n s, F U := by
  let P := (Finset.univ : Finset (Fin n)).powersetCard s
  let E : Finset (Fin n) ↪ Finset ℕ :=
    (Finset.mapEmbedding (Fin.valEmbedding : Fin n ↪ ℕ)).toEmbedding
  have huniv :
      (Finset.univ : Finset (Fin n)).map Fin.valEmbedding = Finset.range n := by
    ext r
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact i.isLt
    · intro hr
      exact ⟨⟨r, hr⟩, rfl⟩
  have hmap : P.map E = rankSample n s := by
    have hp := Finset.powersetCard_map Fin.valEmbedding s
      (Finset.univ : Finset (Fin n))
    rw [huniv] at hp
    exact hp.symm
  rw [← hmap]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_map]
  congr 1
  change (∑ T ∈ P, F (E T)) = ∑ U ∈ P.map E, F U
  exact (Finset.sum_map P E F).symm

/-- The positions of any fixed active set in a uniform permutation have
exactly the uniform-subset law used in UniformSubsetRank. -/
theorem activePositions_expect_eq_rankSample (n : ℕ) (S : Finset (Fin n))
    (F : Finset ℕ → ℝ) :
    (𝔼 σ ∈ preferenceSample n, F (activePositions S σ)) =
      𝔼 T ∈ rankSample n S.card, F T := by
  calc
    (𝔼 σ ∈ preferenceSample n, F (activePositions S σ)) =
        𝔼 T ∈ (Finset.univ : Finset (Fin n)).powersetCard S.card,
          F (T.map Fin.valEmbedding) := by
      exact perm_preimage_expect_eq_powerset_expect S
        (fun T => F (T.map Fin.valEmbedding))
    _ = 𝔼 T ∈ rankSample n S.card, F T :=
      finSubset_expect_eq_rankSample n S.card F

/-- Exact one-agent active-rank tail law on the genuine permutation sample. -/
theorem activeRank_tail_probability {n r : ℕ} {S : Finset (Fin n)}
    (hS : S.Nonempty) (hr : r ≤ n) :
    probability (preferenceSample n) (fun σ => r < activeRank S σ) =
      (Nat.choose (n - r) S.card : ℝ) / Nat.choose n S.card := by
  unfold probability
  change (𝔼 σ ∈ preferenceSample n,
      if r < firstRank (activePositions S σ) then (1 : ℝ) else 0) = _
  rw [activePositions_expect_eq_rankSample n S
    (fun T => if r < firstRank T then (1 : ℝ) else 0)]
  exact firstRank_tail_probability (Finset.card_pos.mpr hS) hr

/-- The one-coordinate MGF estimate now stated for an actual uniform strict
preference order rather than an abstract subset sample. -/
theorem activeRank_scaled_mgf {n : ℕ} (hn : 0 < n)
    {S : Finset (Fin n)} (hS : S.Nonempty) :
    (𝔼 σ ∈ preferenceSample n,
        Real.exp ((1 / 2 : ℝ) * scaledActiveRank n S σ)) ≤
      1 + Real.exp 1 := by
  change (𝔼 σ ∈ preferenceSample n,
      Real.exp ((1 / 2 : ℝ) *
        (((S.card : ℝ) / n) * firstRank (activePositions S σ)))) ≤ _
  rw [activePositions_expect_eq_rankSample n S
    (fun T => Real.exp ((1 / 2 : ℝ) *
      (((S.card : ℝ) / n) * firstRank T)))]
  exact firstRank_scaled_mgf hn (Finset.card_pos.mpr hS)
    (by simpa using S.card_le_univ)

/-- All nonempty active sets.  These coexist on the same preference profile;
they are not sampled independently. -/
def nonemptyActiveSets (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter Finset.Nonempty

lemma mem_nonemptyActiveSets_iff {n : ℕ} {S : Finset (Fin n)} :
    S ∈ nonemptyActiveSets n ↔ S.Nonempty := by
  simp [nonemptyActiveSets]

lemma card_nonemptyActiveSets_le (n : ℕ) :
    (nonemptyActiveSets n).card ≤ 2 ^ n := by
  calc
    (nonemptyActiveSets n).card ≤
        (Finset.univ : Finset (Finset (Fin n))).card :=
      Finset.card_filter_le _ _
    _ = 2 ^ n := by simp

/-- The complete simultaneous active-rank concentration theorem on one common
profile of n independent uniform strict preferences. -/
theorem uniform_active_rank_exponential_profile {n : ℕ} (hn : 0 < n)
    {K c : ℝ}
    (hK : Real.log 2 + c ≤
      (1 / 2 : ℝ) * K - Real.log (1 + Real.exp 1)) :
    probability (preferenceProfileSample n)
        (fun profile => ∃ S ∈ nonemptyActiveSets n,
          K * n ≤ ∑ i : Fin n, scaledActiveRank n S (profile i)) ≤
      Real.exp (-c * n) := by
  apply uniform_active_rank_exponential
    (preferenceSample n) (nonemptyActiveSets n)
    (scaledActiveRank n)
  · intro S hS
    exact activeRank_scaled_mgf hn (mem_nonemptyActiveSets_iff.mp hS)
  · exact hK
  · exact card_nonemptyActiveSets_le n

end ProbabilisticSerial.UniformPermutation
