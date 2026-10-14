import ReplicaRankAllocation
import ReplicaExposureBound

/-! Unconditional expectation bridge for every positive integer quota. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators
namespace ProbabilisticSerial.ReplicaChoiceMachine
open UniformPermutation PSProcess ReplicaPS ReplicaRevelation PSChoiceMachine
variable {m q : ℕ} [Nonempty (Fin (m * q))]

lemma same_history_roundTime (reference other : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q))
    (heq : history other (r * (m * q) + i.val) = history reference (r * (m * q) + i.val)) :
    roundTime other r = roundTime reference r := PSChoiceMachine.same_history_roundTime _ _ r i heq

lemma same_history_types (reference other : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q))
    (heq : history other (r * (m * q) + i.val) = history reference (r * (m * q) + i.val)) :
    roundTypes other r = roundTypes reference r := by
  rw [← queryTypes_at_slot other r i, heq, queryTypes_at_slot]

lemma same_history_previous_choice (reference other : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q))
    (heq : history other ((r + 1) * (m * q) + i.val) = history reference ((r + 1) * (m * q) + i.val))
    (hA : (roundTypes reference (r + 1)).Nonempty) : roundChoice other r i = roundChoice reference r i :=
  congrArg typeOf (PSChoiceMachine.same_history_previous_choice (liftedProfile reference)
    (liftedProfile other) r i heq (Finset.image_nonempty.mp hA))

def exposureAtom (profile : ReplicaPS.Profile m q) (i : Fin (m * q)) (r : ℕ) : ℝ :=
  arrivalWeight (history profile (r * (m * q) + i.val)) * max (1 - roundTime profile r) 0

lemma same_history_exposureAtom (reference other : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q))
    (heq : history other (r * (m * q) + i.val) = history reference (r * (m * q) + i.val)) :
    exposureAtom other i r = exposureAtom reference i r := by
  unfold exposureAtom
  rw [heq, same_history_roundTime reference other r i heq]

theorem expected_rank_jump_fiber_le_refined (reference : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q)) :
    (𝔼 other ∈ pathFiber ((r + 1) * (m * q) + i.val)
        (history reference ((r + 1) * (m * q) + i.val)), weightedRankJump other i (r + 1)) ≤
      ((m : ℝ) - 1) * exposureAtom reference i (r + 1) := by
  classical
  have hmOne : (1 : ℝ) ≤ m := by
    exact_mod_cast Nat.succ_le_of_lt (type_count_pos (m := m) (q := q))
  let C := pathFiber ((r + 1) * (m * q) + i.val)
    (history reference ((r + 1) * (m * q) + i.val))
  have hmem (other : ReplicaPS.Profile m q) (ho : other ∈ C) :
      history other ((r + 1) * (m * q) + i.val) =
        history reference ((r + 1) * (m * q) + i.val) := (Finset.mem_filter.mp ho).2
  by_cases ht : roundTime reference (r + 1) < 1
  · have hA := (roundTime_lt_one_iff reference (r + 1)).mp ht
    by_cases hs : stochasticRecording
        (history reference ((r + 1) * (m * q) + i.val)) = true
    · let previous := roundChoice reference r i
      have hbound := expected_rank_jump_at_slot_le reference r i hA hs
      have hgone : previous ∉ roundTypes reference (r + 1) := by
        have hfresh : FreshQuery
            (history reference ((r + 1) * (m * q) + i.val)) :=
          (of_decide_eq_true hs).2
        simpa only [FreshQuery, previousType_at_slot_succ reference r i hA,
          queryTypes_at_slot, previous, roundChoice_eq reference r i
            (hA.mono (roundTypes_subset reference (Nat.le_succ r)))] using hfresh
      have hcard : (roundTypes reference (r + 1)).card < m := by
        have hne : roundTypes reference (r + 1) ≠ Finset.univ := by
          intro heq
          exact hgone (by rw [heq]; exact Finset.mem_univ previous)
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.subset_univ _, hne⟩)
      have hprevious : previous = favorite (reference i)
          (roundTypes reference r)
          (by exact ⟨hA.choose, roundTypes_subset reference (Nat.le_succ r) hA.choose_spec⟩) :=
        roundChoice_eq reference r i _
      dsimp only at hbound
      rw [← hprevious] at hbound
      have hrewrite :
          (𝔼 other ∈ C, weightedRankJump other i (r + 1)) =
            max (1 - roundTime reference (r + 1)) 0 *
              (𝔼 other ∈ C,
                ((rankOf (other i) (favorite (other i)
                  (roundTypes reference (r + 1)) hA) : ℝ) -
                    rankOf (other i) previous)) := by
        rw [Finset.mul_expect]
        apply Finset.expect_congr rfl
        intro other ho
        have heq := hmem other ho
        have hq := same_history_types reference other (r + 1) i heq
        have hAo : (roundTypes other (r + 1)).Nonempty := by rw [hq]; exact hA
        simp only [weightedRankJump, roundRank,
          same_history_roundTime reference other (r + 1) i heq,
          same_history_previous_choice reference other r i heq hA,
          roundChoice_eq other (r + 1) i hAo]
        simp only [hq, previous]
      change (𝔼 other ∈ C, weightedRankJump other i (r + 1)) ≤ _
      rw [hrewrite]
      have ha : (0 : ℝ) < (roundTypes reference (r + 1)).card := by
        exact_mod_cast Finset.card_pos.mpr hA
      calc
        _ ≤ max (1 - roundTime reference (r + 1)) 0 *
            ((m : ℝ) / ((roundTypes reference (r + 1)).card + 1)) :=
          mul_le_mul_of_nonneg_left hbound (le_max_right _ _)
        _ ≤ max (1 - roundTime reference (r + 1)) 0 *
            (((m : ℝ) - 1) / (roundTypes reference (r + 1)).card) := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          apply (div_le_div_iff₀ (by linarith :
            0 < ((roundTypes reference (r + 1)).card : ℝ) + 1) ha).2
          have hcardR : ((roundTypes reference (r + 1)).card : ℝ) + 1 ≤ m := by
            exact_mod_cast Nat.succ_le_of_lt hcard
          nlinarith
        _ = _ := by
          simp only [exposureAtom, arrivalWeight, hs, Bool.true_eq, if_true, queryTypes_at_slot]
          ring
    · have hzero : (𝔼 other ∈ C, weightedRankJump other i (r + 1)) = 0 := by
        apply Finset.expect_eq_zero
        intro other ho
        have heq := hmem other ho
        have hq := same_history_types reference other (r + 1) i heq
        have hAo : (roundTypes other (r + 1)).Nonempty := by rw [hq]; exact hA
        rw [weightedRankJump, rank_jump_zero_of_not_stochastic other r i hAo
          (by rw [heq]; exact Bool.eq_false_of_not_eq_true hs), mul_zero]
      change (𝔼 other ∈ C, weightedRankJump other i (r + 1)) ≤ _
      rw [hzero]
      exact mul_nonneg (sub_nonneg.mpr hmOne) (mul_nonneg (arrivalWeight_nonneg _) (le_max_right _ _))
  · have hzero : (𝔼 other ∈ C, weightedRankJump other i (r + 1)) = 0 := by
      apply Finset.expect_eq_zero
      intro other ho
      rw [weightedRankJump, same_history_roundTime reference other (r + 1) i (hmem other ho),
        max_eq_right (by linarith : 1 - roundTime reference (r + 1) ≤ 0), zero_mul]
    change (𝔼 other ∈ C, weightedRankJump other i (r + 1)) ≤ _
    rw [hzero]
    exact mul_nonneg (sub_nonneg.mpr hmOne) (mul_nonneg (arrivalWeight_nonneg _) (le_max_right _ _))

/-- The earlier bridge remains available as a weaker corollary. -/
theorem expected_rank_jump_fiber_le (reference : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q)) :
    (𝔼 other ∈ pathFiber ((r + 1) * (m * q) + i.val)
        (history reference ((r + 1) * (m * q) + i.val)), weightedRankJump other i (r + 1)) ≤
      m * exposureAtom reference i (r + 1) := by
  refine (expected_rank_jump_fiber_le_refined reference r i).trans ?_
  apply mul_le_mul_of_nonneg_right (by linarith)
  exact mul_nonneg (arrivalWeight_nonneg _) (le_max_right _ _)


theorem expected_weightedRankJump_le_affine (r : ℕ) (i : Fin (m * q)) :
    (𝔼 profile ∈ ReplicaPS.profileSample m q, weightedRankJump profile i r) ≤
      (𝔼 profile ∈ ReplicaPS.profileSample m q, ((m : ℝ) - 1) * exposureAtom profile i r) +
        (if r = 0 then 1 / (m : ℝ) else 0) := by
  cases r with
  | zero =>
      have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (type_count_pos (m := m) (q := q)).ne'
      simp only [weightedRankJump_initial, exposureAtom, arrivalWeight_initial,
        roundTime_zero, sub_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), mul_one,
        Finset.expect_const (ReplicaPS.profileSample_nonempty m q), if_pos rfl]
      apply le_of_eq
      field_simp [hm]
  | succ r =>
      rw [if_neg (Nat.succ_ne_zero r), add_zero]
      apply expect_le_of_fiberwise (ReplicaPS.profileSample m q)
        (fun p => history p ((r + 1) * (m * q) + i.val))
      intro reference href
      change (𝔼 other ∈ pathFiber _ _, weightedRankJump other i (r + 1)) ≤
        𝔼 other ∈ pathFiber _ _, ((m : ℝ) - 1) * exposureAtom other i (r + 1)
      have he : (𝔼 other ∈ pathFiber ((r + 1) * (m * q) + i.val)
          (history reference ((r + 1) * (m * q) + i.val)),
          ((m : ℝ) - 1) * exposureAtom other i (r + 1)) = ((m : ℝ) - 1) * exposureAtom reference i (r + 1) := by
        calc
          _ = 𝔼 _other ∈ pathFiber ((r + 1) * (m * q) + i.val)
              (history reference ((r + 1) * (m * q) + i.val)),
                ((m : ℝ) - 1) * exposureAtom reference i (r + 1) := by
            apply Finset.expect_congr rfl
            intro other ho
            rw [same_history_exposureAtom reference other (r + 1) i (Finset.mem_filter.mp ho).2]
          _ = _ := Finset.expect_const (pathFiber_nonempty _ _) _
      rw [he]
      exact expected_rank_jump_fiber_le_refined reference r i


/-- Compatibility version without the finite-market affine improvement. -/
theorem expected_weightedRankJump_le (r : ℕ) (i : Fin (m * q)) :
    (𝔼 profile ∈ ReplicaPS.profileSample m q, weightedRankJump profile i r) ≤
      𝔼 profile ∈ ReplicaPS.profileSample m q, (m : ℝ) * exposureAtom profile i r := by
  cases r with
  | zero =>
      apply Finset.expect_le_expect
      intro profile hp
      rw [weightedRankJump_initial]
      simp only [exposureAtom, arrivalWeight_initial, roundTime_zero]
      have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (type_count_pos (m := m) (q := q)).ne'
      simp [hn]
  | succ r =>
      have h := expected_weightedRankJump_le_affine (r + 1) i
      rw [if_neg (Nat.succ_ne_zero r), add_zero] at h
      refine h.trans (Finset.expect_le_expect (fun p _ => ?_))
      apply mul_le_mul_of_nonneg_right (by linarith)
      exact mul_nonneg (arrivalWeight_nonneg _) (le_max_right _ _)


/-- Sum an affine bound on the rank increments, counting the initial
correction once per agent. This also supplies the earlier linear bridge. -/
theorem expectedPS_le_of_affine_jumps (A B : ℝ)
    (hjump : ∀ (r : ℕ) (i : Fin (m * q)),
      (𝔼 profile ∈ ReplicaPS.profileSample m q, weightedRankJump profile i r) ≤
        (𝔼 profile ∈ ReplicaPS.profileSample m q, A * exposureAtom profile i r) +
          (if r = 0 then B else 0)) :
    ReplicaPS.expectedPS m q ≤
      (A / ((m * q : ℕ) : ℝ)) *
        (𝔼 profile ∈ ReplicaPS.profileSample m q, profileExposure profile) + B := by
  have hn : 0 < m * q := Nat.mul_pos (type_count_pos (m := m) (q := q))
    (quota_pos (m := m) (q := q))
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (type_count_pos (m := m) (q := q)).ne'
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (quota_pos (m := m) (q := q)).ne'
  have hexposure :
      (∑ r ∈ Finset.range (m * q), ∑ i : Fin (m * q),
        𝔼 p ∈ ReplicaPS.profileSample m q, A * exposureAtom p i r) =
      A * (𝔼 p ∈ ReplicaPS.profileSample m q, profileExposure p) := by
    simp_rw [← Finset.mul_expect, ← Finset.mul_sum, ← Finset.expect_sum_comm]
    rfl
  have hcorrection :
      (∑ r ∈ Finset.range (m * q), ∑ _i : Fin (m * q),
        if r = 0 then B else 0) = ((m * q : ℕ) : ℝ) * B := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    simp [hn]
  unfold ReplicaPS.expectedPS
  simp_rw [averageRank_eq_weighted_jumps]
  rw [← Finset.mul_expect]
  simp_rw [Finset.expect_sum_comm]
  calc
    _ ≤ (1 / ((m * q : ℕ) : ℝ)) *
        (∑ r ∈ Finset.range (m * q), ∑ i : Fin (m * q),
          ((𝔼 p ∈ ReplicaPS.profileSample m q, A * exposureAtom p i r) +
            (if r = 0 then B else 0))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun i _ => hjump r i))
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [hexposure, hcorrection]
      field_simp [hm, hq]
      ring

/-- The paper's finite-market factor is retained: the initial choice has
rank one, and every later genuine switch has at most m-1 available types. -/
theorem expectedPS_le_expected_exposure_affine : ReplicaPS.expectedPS m q ≤
    1 + (1 - 1 / (m : ℝ)) *
      ((𝔼 profile ∈ ReplicaPS.profileSample m q, profileExposure profile) / q - 1) := by
  have h := expectedPS_le_of_affine_jumps (m := m) (q := q) ((m : ℝ) - 1) (1 / (m : ℝ))
    expected_weightedRankJump_le_affine
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (type_count_pos (m := m) (q := q)).ne'
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (quota_pos (m := m) (q := q)).ne'
  convert h using 1
  rw [Nat.cast_mul]
  field_simp [hm, hq]
  ring

theorem expectedPS_le_expected_exposure : ReplicaPS.expectedPS m q ≤
    (𝔼 profile ∈ ReplicaPS.profileSample m q, profileExposure profile) / q := by
  have h := expectedPS_le_of_affine_jumps (m := m) (q := q) (m : ℝ) 0
    (fun r i => by simpa using expected_weightedRankJump_le r i)
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (type_count_pos (m := m) (q := q)).ne'
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (quota_pos (m := m) (q := q)).ne'
  convert h using 1
  rw [Nat.cast_mul]
  field_simp [hm, hq]
  ring

/-- Unconditional affine rank bound for the normalized actual exposure. -/
theorem expectedPS_le_actualExposure_affine : ReplicaPS.expectedPS m q ≤
    1 + (1 - 1 / (m : ℝ)) *
      (FiniteAtomicExposure.value (actualExposure (m := m) (q := q)) 1 - 1) := by
  rw [actualExposure_value]
  exact expectedPS_le_expected_exposure_affine


theorem expectedPS_le_actualExposure : ReplicaPS.expectedPS m q ≤
    FiniteAtomicExposure.value (actualExposure (m := m) (q := q)) 1 := by
  rw [actualExposure_value]
  exact expectedPS_le_expected_exposure

end ProbabilisticSerial.ReplicaChoiceMachine
