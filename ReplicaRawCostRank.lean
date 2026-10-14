import RawPrefixGood

/-! Static rank concentration converts raw-prefix cost into PS allocation rank. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaRawCostRank
open UniformPermutation UniformProduct CouponLowerBound ReplicaPS ReplicaChoiceMachine ReplicaRawStep ReplicaRawProcess
  ReplicaLowerRank ReplicaRawRankBridge RawPrefixGood

variable {m q : ℕ} [Nonempty (Fin (m * q))]

def smallSets (m hi : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun S => S.card ≤ hi)

lemma mean_roundRank_eq (p : ReplicaPS.Profile m q) (r : ℕ)
    (hS : (roundTypes p r).Nonempty) :
    (𝔼 i : Fin (m * q), roundRank p i r) =
      𝔼 i : Fin (m * q), (activeRank (roundTypes p r) (p i) : ℝ) := by
  apply Finset.expect_congr rfl
  intro i hi
  rw [roundRank, roundChoice_eq p r i hS, PSProcess.rankOf_favorite_eq_activeRank]

lemma averageRank_eq_mean_round_sum (p : ReplicaPS.Profile m q) :
    ReplicaPS.averageRank p = ∑ r ∈ Finset.range (m * q),
      roundDuration p r * (𝔼 i : Fin (m * q), roundRank p i r) := by
  rw [averageRank_eq_round_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_fin]
  ring

theorem rawCost_rank_reduction (hm : 0 < m) (hq : 0 < q)
    (reference : ReplicaPS.Profile m q) (N : ℕ) (w : Fin N → Fin m)
    (p : ReplicaPS.Profile m q)
    (hp : p ∈ fiber ((initialState reference).evolve N w).reference
      ((initialState reference).evolve N w).depth)
    {lo hi : ℕ} (hhi : 0 < hi) (hlm : lo ≤ m) (hlh : lo ≤ hi)
    {α K : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K)
    (hcutoff : N / (m : ℝ) ≤ α * (m * q : ℕ) / lo)
    (hcoarse : CountsGood w Finset.univ 4 (m * q : ℕ))
    (hfine : CountsGood w (smallSets m hi) α (m * q : ℕ))
    (hrank : UniformLowerRankGood p K lo hi) :
    K * rawBandCost (initialState reference) N w ≤
      (α * q) * ReplicaPS.averageRank p + K * (4 * (m * q : ℕ) / hi) := by
  have hhiR : (0 : ℝ) < hi := by exact_mod_cast hhi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let C : ℝ := 4 * (m * q : ℕ) / hi
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : 0 ≤ α * (q : ℝ) := mul_nonneg hα (Nat.cast_nonneg _)
  have hterm (r : ℕ) :
      roundDuration p r * (K * ((rawRoundCount (initialState reference) r N w : ℝ) / m)) ≤
        roundDuration p r * ((α * q) * (𝔼 i : Fin (m * q), roundRank p i r) + K * C) := by
    have hd : 0 ≤ roundDuration p r := PSChoiceMachine.roundDuration_nonneg (liftedProfile p) r
    by_cases hS : (roundTypes p r).Nonempty
    · apply mul_le_mul_of_nonneg_left _ hd
      have hspos : (0 : ℝ) < (roundTypes p r).card := by
        exact_mod_cast Finset.card_pos.mpr hS
      have hrnonneg : 0 ≤ 𝔼 i : Fin (m * q), roundRank p i r :=
        Finset.expect_nonneg (fun i _ => Nat.cast_nonneg _)
      by_cases hsmall : (roundTypes p r).card ≤ hi
      · have hrl := meanRank_lower_with_cutoff hm hq hlm hlh hrank (roundTypes p r) hS hsmall
        rw [← mean_roundRank_eq p r hS] at hrl
        have hcnt : ((rawRoundCount (initialState reference) r N w : ℝ) / m) ≤
            α * (m * q : ℕ) / (max lo (roundTypes p r).card : ℕ) := by
          by_cases hlarge : lo ≤ (roundTypes p r).card
          · rw [max_eq_right hlarge]
            exact rawRoundCount_bound hm reference N w p hp (smallSets m hi) hα hfine r
              (by simpa [smallSets] using hsmall) hS
          · rw [max_eq_left (le_of_not_ge hlarge)]
            apply le_trans _ hcutoff
            exact div_le_div_of_nonneg_right (by
              exact_mod_cast rawRoundCount_le_length (initialState reference) r N w) hmR.le
        have hmul := mul_le_mul_of_nonneg_left hcnt hK
        have hrlmul := mul_le_mul_of_nonneg_left hrl ha
        have heq : K * (α * (m * q : ℕ) / (max lo (roundTypes p r).card : ℕ)) =
            (α * q) * (K * ((m : ℝ) / (max lo (roundTypes p r).card : ℕ))) := by
          rw [Nat.cast_mul]
          ring
        rw [heq] at hmul
        have hKC := mul_nonneg hK hC
        linarith
      · have hb := rawRoundCount_bound hm reference N w p hp Finset.univ
          (by norm_num : (0 : ℝ) ≤ 4) hcoarse r (Finset.mem_univ _) hS
        have hh : (hi : ℝ) ≤ (roundTypes p r).card := by exact_mod_cast (le_of_not_ge hsmall)
        have hdiv := div_le_div_of_nonneg_left
          (show 0 ≤ (4 : ℝ) * (m * q : ℕ) by positivity) hhiR hh
        have hkc := mul_le_mul_of_nonneg_left (hb.trans hdiv) hK
        have hrr := mul_nonneg ha hrnonneg
        change _ ≤ K * C at hkc
        linarith
    · have he : ¬ (PSProcess.activeGoods (PSChoiceMachine.profileSupply (liftedProfile p) r)).Nonempty :=
        fun hh => hS (hh.image typeOf)
      have hz : roundDuration p r = 0 := by
        simp [roundDuration, PSChoiceMachine.roundDuration, he]
      rw [hz, zero_mul, zero_mul]
  rw [rawBandCost_eq_round_counts (initialState reference) N w p hp, Finset.mul_sum]
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.range (m * q)) => hterm r)
  have htotal : (∑ r ∈ Finset.range (m * q), roundDuration p r) = 1 := by
    calc
      _ = roundTime p (m * q) := PSChoiceMachine.sum_roundDuration (liftedProfile p) (m * q)
      _ = 1 := roundTime_terminal p
  have heq : (∑ r ∈ Finset.range (m * q),
      roundDuration p r * ((α * q) * (𝔼 i : Fin (m * q), roundRank p i r) + K * C)) =
      (α * q) * ReplicaPS.averageRank p + K * C := by
    rw [averageRank_eq_mean_round_sum]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [htotal, one_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [heq] at hsum
  simpa only [mul_assoc, mul_left_comm, mul_comm, C] using hsum

def RawGood {N : ℕ} (w : Fin N → Fin m) (hi : ℕ) (α : ℝ) : Prop :=
  CountsGood w Finset.univ 4 (m * q : ℕ) ∧
    CountsGood w (smallSets m hi) α (m * q : ℕ)

noncomputable instance {N : ℕ} (w : Fin N → Fin m) (hi : ℕ) (α : ℝ) :
    Decidable (RawGood (q := q) w hi α) := Classical.propDecidable _

theorem rawGood_failure_probability (hm : 0 < m) (N hi : ℕ)
    {α : ℝ} (hα : 1 < α) :
    probability (labelSample m N) (fun w => ¬RawGood (q := q) w hi α) ≤
      (N + 1 : ℕ) * ((2 : ℝ) ^ m) * Real.exp (-(3 - Real.log 4) * (m * q : ℕ)) +
        (N + 1 : ℕ) * ((smallSets m hi).card : ℝ) *
          Real.exp (-(α - 1 - Real.log α) * (m * q : ℕ)) := by
  have hsplit : probability (labelSample m N) (fun w => ¬RawGood (q := q) w hi α) ≤
      probability (labelSample m N) (fun w => ¬CountsGood w Finset.univ 4 (m * q : ℕ)) +
      probability (labelSample m N) (fun w => ¬CountsGood w (smallSets m hi) α (m * q : ℕ)) := by
    unfold probability
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_le_expect
    intro w hw
    by_cases h1 : CountsGood w Finset.univ 4 (m * q : ℕ)
    <;> by_cases h2 : CountsGood w (smallSets m hi) α (m * q : ℕ)
    <;> simp only [RawGood, h1, h2, true_and, false_and, and_true, and_false,
      not_true_eq_false, not_false_eq_true, if_true, if_false]
    <;> norm_num
  have h1 := countsGood_failure_probability (N := N) hm (Finset.univ : Finset (Finset (Fin m)))
    (n := (m * q : ℕ)) (by norm_num : (1 : ℝ) < 4)
  have h2 := countsGood_failure_probability (N := N) hm (smallSets m hi) (n := (m * q : ℕ)) hα
  apply hsplit.trans
  have hcard : ((Finset.univ : Finset (Finset (Fin m))).card : ℝ) = 2 ^ m := by simp
  rw [hcard] at h1
  norm_num only at h1
  exact add_le_add h1 h2

/-- Both exceptional-event costs are retained. The raw simulation's exact
profile marginal is used to average the static rank event. -/
theorem expectedPS_lower_from_rawCost (hm : 0 < m) (hq : 0 < q)
    (reference : ReplicaPS.Profile m q) (N : ℕ)
    {lo hi : ℕ} (hhi : 0 < hi) (hlm : lo ≤ m) (hlh : lo ≤ hi)
    {α K : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K)
    (hcutoff : N / (m : ℝ) ≤ α * (m * q : ℕ) / lo) :
    K * (𝔼 w ∈ labelSample m N, rawBandCost (initialState reference) N w) -
      K * (4 * (m * q : ℕ) / hi) -
      (K * (N / (m : ℝ))) *
        (probability (labelSample m N) (fun w => ¬RawGood (q := q) w hi α) +
          probability (ReplicaPS.profileSample m q)
            (fun p => ¬UniformLowerRankGood p K lo hi)) ≤
      (α * q) * ReplicaPS.expectedPS m q := by
  let C : ℝ := 4 * (m * q : ℕ) / hi
  let L : ℝ := K * (N / (m : ℝ))
  have hC : 0 ≤ K * C := by dsimp [C]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have ha : 0 ≤ α * (q : ℝ) := mul_nonneg hα (Nat.cast_nonneg _)
  have hpoint (w : Fin N → Fin m) (p : ReplicaPS.Profile m q)
      (hp : p ∈ fiber ((initialState reference).evolve N w).reference
        ((initialState reference).evolve N w).depth) :
      K * rawBandCost (initialState reference) N w ≤
        (α * q) * ReplicaPS.averageRank p + K * C +
          L * (if ¬RawGood (q := q) w hi α then 1 else 0) +
          L * (if ¬UniformLowerRankGood p K lo hi then 1 else 0) := by
    have hr : 0 ≤ (α * q) * ReplicaPS.averageRank p :=
      mul_nonneg ha ((ReplicaPS.averageRank_bounds p hm hq).1.trans' (by norm_num))
    have hb := mul_le_mul_of_nonneg_left (rawBandCost_le_length (initialState reference) N w) hK
    change _ ≤ L at hb
    by_cases hw : RawGood (q := q) w hi α
    · by_cases hpRank : UniformLowerRankGood p K lo hi
      · simp only [hw, hpRank, not_true_eq_false, if_false, mul_zero, add_zero]
        exact rawCost_rank_reduction hm hq reference N w p hp hhi hlm hlh hα hK
          hcutoff hw.1 hw.2 hpRank
      · simp only [hw, hpRank, not_true_eq_false, not_false_eq_true, if_false, if_true,
          mul_zero, mul_one, add_zero]
        linarith
    · have he : 0 ≤ L * (if ¬UniformLowerRankGood p K lo hi then (1 : ℝ) else 0) :=
        mul_nonneg hL (by split_ifs <;> norm_num)
      simp only [hw, not_false_eq_true, if_true, mul_one]
      linarith
  have hconditional (w : Fin N → Fin m) :
      K * rawBandCost (initialState reference) N w ≤
        (α * q) * (((initialState reference).evolve N w).posterior ReplicaPS.averageRank) +
          K * C + L * (if ¬RawGood (q := q) w hi α then 1 else 0) +
          L * (((initialState reference).evolve N w).posterior
            (fun p => if ¬UniformLowerRankGood p K lo hi then 1 else 0)) := by
    let s := (initialState reference).evolve N w
    have hf : (fiber s.reference s.depth).Nonempty := ⟨s.reference, s.reference_mem_fiber⟩
    have h := Finset.expect_le_expect (s := fiber s.reference s.depth)
      (fun p hp => hpoint w p hp)
    simpa only [Finset.expect_const hf, Finset.expect_add_distrib, ← Finset.mul_expect,
      State.posterior] using h
  have hsamp : (labelSample m N).Nonempty := UniformProduct.productSample_nonempty
    (show (Finset.univ : Finset (Fin m)).Nonempty from ⟨⟨0, hm⟩, Finset.mem_univ _⟩) N
  have h := Finset.expect_le_expect (s := labelSample m N) (fun w _ => hconditional w)
  simp only [Finset.expect_add_distrib, Finset.expect_const hsamp, ← Finset.mul_expect] at h
  rw [raw_prefix_profile_marginal hm reference ReplicaPS.averageRank N,
    raw_prefix_profile_marginal hm reference
      (fun p => if ¬UniformLowerRankGood p K lo hi then (1 : ℝ) else 0) N] at h
  change _ ≤ (α * q) * ReplicaPS.expectedPS m q + K * C +
    L * probability (labelSample m N) (fun w => ¬RawGood (q := q) w hi α) +
    L * probability (ReplicaPS.profileSample m q)
      (fun p => ¬UniformLowerRankGood p K lo hi) at h
  dsimp only [L, C] at h
  linarith

end ProbabilisticSerial.ReplicaRawCostRank
