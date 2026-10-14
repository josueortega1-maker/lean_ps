import PSRankAllocation
import PSExposureBound
import ConcreteTheoremOne

/-! The expectation bridge from concrete PS allocation ranks to exposure. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PSChoiceMachine
open UniformPermutation PSProcess SequentialRevelation
variable {n : ℕ} [Nonempty (Fin n)]

lemma same_history_roundTime (reference other : Profile n) (r : ℕ) (i : Fin n)
    (heq : profileHistory other (r * n + i.val) = profileHistory reference (r * n + i.val)) :
    roundTime other r = roundTime reference r := by
  rw [← queryTime_at_slot other r i, heq, queryTime_at_slot]

lemma same_history_supply (reference other : Profile n) (r : ℕ) (i : Fin n)
    (heq : profileHistory other (r * n + i.val) = profileHistory reference (r * n + i.val)) :
    profileSupply other r = profileSupply reference r := by
  rw [← querySupply_at_slot other r i, heq, querySupply_at_slot]

lemma same_history_previous_choice (reference other : Profile n) (r : ℕ) (i : Fin n)
    (heq : profileHistory other ((r + 1) * n + i.val) =
      profileHistory reference ((r + 1) * n + i.val))
    (hA : (activeGoods (profileSupply reference (r + 1))).Nonempty) :
    roundChoice other r i = roundChoice reference r i := by
  have hq := same_history_supply reference other (r + 1) i heq
  have hAo : (activeGoods (profileSupply other (r + 1))).Nonempty := by rw [hq]; exact hA
  have hp := congrArg previousChoice heq
  rw [previousChoice_at_slot_succ other r i hAo,
    previousChoice_at_slot_succ reference r i hA] at hp
  simp only [Option.some.injEq] at hp
  rw [roundChoice_eq other r i ⟨hAo.choose, profileSupply_active_subset other r hAo.choose_spec⟩,
    roundChoice_eq reference r i ⟨hA.choose, profileSupply_active_subset reference r hA.choose_spec⟩]
  exact hp

def exposureAtom (profile : Profile n) (i : Fin n) (r : ℕ) : ℝ :=
  arrivalWeight (profileHistory profile (r * n + i.val)) * max (1 - roundTime profile r) 0

lemma same_history_exposureAtom (reference other : Profile n) (r : ℕ) (i : Fin n)
    (heq : profileHistory other (r * n + i.val) = profileHistory reference (r * n + i.val)) :
    exposureAtom other i r = exposureAtom reference i r := by
  unfold exposureAtom
  rw [heq, same_history_roundTime reference other r i heq]

lemma pathFiber_nonempty (reference : Profile n) (depth : ℕ) :
    (pathFiber depth (profileHistory reference depth)).Nonempty := by
  refine ⟨reference, ?_⟩
  simp [pathFiber, preferenceProfileSample_eq_univ]

theorem expected_rank_jump_fiber_le (reference : Profile n) (r : ℕ) (i : Fin n) :
    (𝔼 other ∈ pathFiber ((r + 1) * n + i.val)
        (profileHistory reference ((r + 1) * n + i.val)), weightedRankJump other i (r + 1)) ≤
      n * exposureAtom reference i (r + 1) := by
  classical
  let C := pathFiber ((r + 1) * n + i.val)
    (profileHistory reference ((r + 1) * n + i.val))
  have hmem (other : Profile n) (ho : other ∈ C) :
      profileHistory other ((r + 1) * n + i.val) =
        profileHistory reference ((r + 1) * n + i.val) := (Finset.mem_filter.mp ho).2
  by_cases ht : roundTime reference (r + 1) < 1
  · have hA := (roundTime_lt_one_iff reference (r + 1)).mp ht
    by_cases hs : stochasticRecording
        (profileHistory reference ((r + 1) * n + i.val)) = true
    · let previous := roundChoice reference r i
      have hbound := expected_rank_jump_at_slot_le reference r i hA hs
      have hprevious : previous = favorite (reference i)
          (activeGoods (profileSupply reference r))
          (by exact ⟨hA.choose, profileSupply_active_subset reference r hA.choose_spec⟩) :=
        roundChoice_eq reference r i _
      dsimp only at hbound
      rw [← hprevious] at hbound
      have hrewrite :
          (𝔼 other ∈ C, weightedRankJump other i (r + 1)) =
            max (1 - roundTime reference (r + 1)) 0 *
              (𝔼 other ∈ C,
                ((rankOf (other i) (favorite (other i)
                  (activeGoods (profileSupply reference (r + 1))) hA) : ℝ) -
                    rankOf (other i) previous)) := by
        rw [Finset.mul_expect]
        apply Finset.expect_congr rfl
        intro other ho
        have heq := hmem other ho
        have hq := same_history_supply reference other (r + 1) i heq
        have hAo : (activeGoods (profileSupply other (r + 1))).Nonempty := by rw [hq]; exact hA
        simp only [weightedRankJump, roundRank,
          same_history_roundTime reference other (r + 1) i heq,
          same_history_previous_choice reference other r i heq hA,
          roundChoice_eq other (r + 1) i hAo]
        simp only [hq, previous]
      change (𝔼 other ∈ C, weightedRankJump other i (r + 1)) ≤ _
      rw [hrewrite]
      have ha : (0 : ℝ) < (activeGoods (profileSupply reference (r + 1))).card := by
        exact_mod_cast Finset.card_pos.mpr hA
      calc
        _ ≤ max (1 - roundTime reference (r + 1)) 0 *
            ((n : ℝ) / ((activeGoods (profileSupply reference (r + 1))).card + 1)) :=
          mul_le_mul_of_nonneg_left hbound (le_max_right _ _)
        _ ≤ max (1 - roundTime reference (r + 1)) 0 *
            ((n : ℝ) / (activeGoods (profileSupply reference (r + 1))).card) := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) ha (by linarith)
        _ = _ := by
          simp only [exposureAtom, arrivalWeight, hs, Bool.true_eq, if_true, queryActive_at_slot]
          ring
    · have hzero : (𝔼 other ∈ C, weightedRankJump other i (r + 1)) = 0 := by
        apply Finset.expect_eq_zero
        intro other ho
        have heq := hmem other ho
        have hq := same_history_supply reference other (r + 1) i heq
        have hAo : (activeGoods (profileSupply other (r + 1))).Nonempty := by rw [hq]; exact hA
        rw [weightedRankJump, rank_jump_zero_of_not_stochastic other r i hAo
          (by rw [heq]; exact Bool.eq_false_of_not_eq_true hs), mul_zero]
      change (𝔼 other ∈ C, weightedRankJump other i (r + 1)) ≤ _
      rw [hzero]
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (arrivalWeight_nonneg _) (le_max_right _ _))
  · have hzero : (𝔼 other ∈ C, weightedRankJump other i (r + 1)) = 0 := by
      apply Finset.expect_eq_zero
      intro other ho
      rw [weightedRankJump, same_history_roundTime reference other (r + 1) i (hmem other ho),
        max_eq_right (by linarith : 1 - roundTime reference (r + 1) ≤ 0), zero_mul]
    change (𝔼 other ∈ C, weightedRankJump other i (r + 1)) ≤ _
    rw [hzero]
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (arrivalWeight_nonneg _) (le_max_right _ _))

lemma expect_le_of_fiberwise {α β : Type*} [DecidableEq β] (s : Finset α)
    (f : α → β) (F G : α → ℝ)
    (h : ∀ reference ∈ s,
      (𝔼 other ∈ s.filter (fun a => f a = f reference), F other) ≤
        𝔼 other ∈ s.filter (fun a => f a = f reference), G other) :
    (𝔼 a ∈ s, F a) ≤ 𝔼 a ∈ s, G a := by
  classical
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) F,
    ← Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) G]
  apply Finset.sum_le_sum
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  have hh := mul_le_mul_of_nonneg_left (h a ha)
    (Nat.cast_nonneg ((s.filter (fun a' => f a' = f a)).card) :
      (0 : ℝ) ≤ (s.filter (fun a' => f a' = f a)).card)
  simpa only [Finset.card_mul_expect] using hh

theorem expected_weightedRankJump_le (r : ℕ) (i : Fin n) :
    (𝔼 profile ∈ preferenceProfileSample n, weightedRankJump profile i r) ≤
      𝔼 profile ∈ preferenceProfileSample n, (n : ℝ) * exposureAtom profile i r := by
  cases r with
  | zero =>
      apply Finset.expect_le_expect
      intro profile hp
      rw [weightedRankJump_initial]
      simp only [exposureAtom, arrivalWeight_initial, roundTime_zero]
      have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (market_pos (n := n)).ne'
      simp [hn]
  | succ r =>
      apply expect_le_of_fiberwise (preferenceProfileSample n)
        (fun p => profileHistory p ((r + 1) * n + i.val))
      intro reference href
      change (𝔼 other ∈ pathFiber _ _, weightedRankJump other i (r + 1)) ≤
        𝔼 other ∈ pathFiber _ _, (n : ℝ) * exposureAtom other i (r + 1)
      have he : (𝔼 other ∈ pathFiber ((r + 1) * n + i.val)
          (profileHistory reference ((r + 1) * n + i.val)),
          (n : ℝ) * exposureAtom other i (r + 1)) = n * exposureAtom reference i (r + 1) := by
        calc
          _ = 𝔼 _other ∈ pathFiber ((r + 1) * n + i.val)
              (profileHistory reference ((r + 1) * n + i.val)),
                (n : ℝ) * exposureAtom reference i (r + 1) := by
            apply Finset.expect_congr rfl
            intro other ho
            rw [same_history_exposureAtom reference other (r + 1) i (Finset.mem_filter.mp ho).2]
          _ = _ := Finset.expect_const (pathFiber_nonempty _ _) _
      rw [he]
      exact expected_rank_jump_fiber_le reference r i

theorem expectedPS_le_expected_exposure : ConcreteTheoremOne.expectedPS n ≤
    𝔼 profile ∈ preferenceProfileSample n, profileExposure profile := by
  unfold ConcreteTheoremOne.expectedPS
  simp_rw [averageRank_eq_weighted_jumps]
  rw [← Finset.mul_expect]
  simp_rw [Finset.expect_sum_comm]
  have hsum : (∑ r ∈ Finset.range n, ∑ i : Fin n,
      𝔼 p ∈ preferenceProfileSample n, weightedRankJump p i r) ≤
      ∑ r ∈ Finset.range n, ∑ i : Fin n,
        𝔼 p ∈ preferenceProfileSample n, (n : ℝ) * exposureAtom p i r := by
    apply Finset.sum_le_sum
    intro r hr
    exact Finset.sum_le_sum (fun i _ => expected_weightedRankJump_le r i)
  calc
    _ ≤ (1 / (n : ℝ)) *
        (∑ r ∈ Finset.range n, ∑ i : Fin n,
          𝔼 p ∈ preferenceProfileSample n, (n : ℝ) * exposureAtom p i r) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      simp_rw [← Finset.mul_expect, ← Finset.mul_sum]
      rw [← mul_assoc, one_div_mul_cancel (by exact_mod_cast (market_pos (n := n)).ne'), one_mul]
      simp_rw [← Finset.expect_sum_comm]
      rfl

end ProbabilisticSerial.PSChoiceMachine
