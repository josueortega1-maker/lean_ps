import AsymptoticClosure
import Mathlib.Data.Nat.Choose.Sum

/-!
# Random priority as an explicit finite mechanism

This file defines random priority (serial dictatorship) on the same finite
uniform preference-profile space as probabilistic serial.  A uniformly random
priority permutation chooses the service order.  Each agent, when served,
takes her most-preferred remaining good.

The expectation is then calculated from the model itself.  In particular,
`rpExpectedRank_eq_knuth_formula` proves Knuth's harmonic expression; the
expression is not used as the definition of the mechanism.
-/

noncomputable section

open Finset Filter
open scoped BigOperators Topology Asymptotics

namespace ProbabilisticSerial.RandomPriority

open UniformProduct UniformSubsetRank UniformPermutation PSProcess
open AsymptoticClosure

/-! ## The exact mean of the first active rank -/

lemma expect_nat_eq_tail_sum {α : Type*} (sample : Finset α)
    (X : α → ℕ) (bound : ℕ) (hX : ∀ a ∈ sample, X a ≤ bound) :
    (𝔼 a ∈ sample, (X a : ℝ)) =
      ∑ r ∈ Finset.range bound,
        probability sample (fun a => r < X a) := by
  calc
    (𝔼 a ∈ sample, (X a : ℝ)) =
        𝔼 a ∈ sample,
          ∑ r ∈ Finset.range bound,
            if r < X a then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro a ha
      have hXa : X a ≤ bound := hX a ha
      have hfilter :
          (Finset.range bound).filter (fun r => r < X a) =
            Finset.range (X a) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      simp [hfilter]
    _ = ∑ r ∈ Finset.range bound,
          𝔼 a ∈ sample, if r < X a then (1 : ℝ) else 0 := by
      exact Finset.expect_sum_comm sample (Finset.range bound)
        (fun a r => if r < X a then (1 : ℝ) else 0)
    _ = ∑ r ∈ Finset.range bound,
          probability sample (fun a => r < X a) := rfl

lemma sum_choose_sub_range (n s : ℕ) :
    (∑ r ∈ Finset.range n, Nat.choose (n - r) s) =
      ∑ m ∈ Finset.Ico 1 (n + 1), Nat.choose m s := by
  calc
    (∑ r ∈ Finset.range n, Nat.choose (n - r) s) =
        ∑ r ∈ Finset.range n, Nat.choose (n - 1 - r + 1) s := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrn : r < n := Finset.mem_range.mp hr
      congr 2
      omega
    _ = ∑ r ∈ Finset.range n, Nat.choose (r + 1) s := by
      simpa using Finset.sum_range_reflect (fun r => Nat.choose (r + 1) s) n
    _ = ∑ m ∈ Finset.Ico 1 (n + 1), Nat.choose m s := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]

lemma sum_choose_sub_range_eq_choose_succ {n s : ℕ}
    (hs0 : 0 < s) :
    (∑ r ∈ Finset.range n, Nat.choose (n - r) s) =
      Nat.choose (n + 1) (s + 1) := by
  rw [sum_choose_sub_range]
  have hsubset : Finset.Icc s n ⊆ Finset.Ico 1 (n + 1) := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    exact Finset.mem_Ico.mpr ⟨hs0.trans_le hm'.1, Nat.lt_succ_of_le hm'.2⟩
  calc
    (∑ m ∈ Finset.Ico 1 (n + 1), Nat.choose m s) =
        ∑ m ∈ Finset.Icc s n, Nat.choose m s := by
      symm
      apply Finset.sum_subset hsubset
      intro m hmLarge hmSmall
      have hmlt : m < s := by
        have hmOne : 1 ≤ m := (Finset.mem_Ico.mp hmLarge).1
        have hmTop : m ≤ n := by
          exact Nat.le_of_lt_succ (Finset.mem_Ico.mp hmLarge).2
        have hmNot : ¬(s ≤ m ∧ m ≤ n) := by
          simpa [Finset.mem_Icc] using hmSmall
        omega
      exact Nat.choose_eq_zero_of_lt hmlt
    _ = Nat.choose (n + 1) (s + 1) := Nat.sum_Icc_choose n s

lemma choose_succ_ratio {n s : ℕ} (hsn : s ≤ n) :
    (Nat.choose (n + 1) (s + 1) : ℝ) / Nat.choose n s =
      ((n + 1 : ℕ) : ℝ) / (s + 1) := by
  have hchoose : (Nat.choose n s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hsn).ne'
  have hs : (s : ℝ) + 1 ≠ 0 := by positivity
  apply (div_eq_div_iff hchoose hs).2
  have hidentity :
      ((n : ℝ) + 1) * (Nat.choose n s : ℝ) =
        (Nat.choose (n + 1) (s + 1) : ℝ) * ((s : ℝ) + 1) := by
    exact_mod_cast Nat.succ_mul_choose_eq n s
  norm_num [Nat.cast_add, Nat.cast_one] at hidentity ⊢
  exact hidentity.symm

theorem firstRank_expectation {n s : ℕ} (hs0 : 0 < s) (hsn : s ≤ n) :
    (𝔼 T ∈ rankSample n s, (firstRank T : ℝ)) =
      ((n + 1 : ℕ) : ℝ) / (s + 1) := by
  rw [expect_nat_eq_tail_sum (rankSample n s) firstRank n
    (fun _T hT => firstRank_le_market hs0 hT)]
  calc
    (∑ r ∈ Finset.range n,
        probability (rankSample n s) (fun T => r < firstRank T)) =
        ∑ r ∈ Finset.range n,
          (Nat.choose (n - r) s : ℝ) / Nat.choose n s := by
      apply Finset.sum_congr rfl
      intro r hr
      exact firstRank_tail_probability hs0
        (Nat.le_of_lt (Finset.mem_range.mp hr))
    _ = (∑ r ∈ Finset.range n, (Nat.choose (n - r) s : ℝ)) /
          Nat.choose n s := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ = (Nat.choose (n + 1) (s + 1) : ℝ) / Nat.choose n s := by
      congr 1
      norm_cast
      exact sum_choose_sub_range_eq_choose_succ hs0
    _ = ((n + 1 : ℕ) : ℝ) / (s + 1) := choose_succ_ratio hsn

theorem activeRank_expectation {n : ℕ} {S : Finset (Fin n)}
    (hS : S.Nonempty) :
    (𝔼 σ ∈ preferenceSample n, (activeRank S σ : ℝ)) =
      ((n + 1 : ℕ) : ℝ) / (S.card + 1) := by
  change (𝔼 σ ∈ preferenceSample n,
      (firstRank (activePositions S σ) : ℝ)) = _
  rw [activePositions_expect_eq_rankSample n S
    (fun T => (firstRank T : ℝ))]
  apply firstRank_expectation (Finset.card_pos.mpr hS)
  simpa using S.card_le_univ

/-! ## Serial dictatorship and its expectation -/

/-- Sum of the original one-indexed ranks obtained by `k` serial dictators.
At every step the next agent chooses her favourite remaining good. -/
def serialRankSum {n : ℕ} :
    ∀ k : ℕ, Finset (Fin n) → (Fin k → PreferenceOrder n) → ℝ
  | 0, _S, _orders => 0
  | k + 1, S, orders =>
      if hS : S.Nonempty then
        (rankOf (orders 0) (favorite (orders 0) S hS) : ℝ) +
          serialRankSum k (S.erase (favorite (orders 0) S hS))
            (Fin.tail orders)
      else 0

@[simp] lemma serialRankSum_zero {n : ℕ} (S : Finset (Fin n))
    (orders : Fin 0 → PreferenceOrder n) :
    serialRankSum 0 S orders = 0 := rfl

lemma preferenceSample_eq_univ (n : ℕ) :
    preferenceSample n = Finset.univ := rfl

lemma preferenceProfileSample_eq_univ (n : ℕ) :
    preferenceProfileSample n = Finset.univ := by
  simp [preferenceProfileSample, productSample, preferenceSample,
    permutationSample, Fintype.piFinset_univ]

theorem serialRankSum_expectation {n k : ℕ} (S : Finset (Fin n))
    (hcard : S.card = k) :
    (𝔼 orders : Fin k → PreferenceOrder n, serialRankSum k S orders) =
      ((n + 1 : ℕ) : ℝ) * ((harmonic (k + 1) : ℝ) - 1) := by
  induction k generalizing S with
  | zero =>
      simp [serialRankSum, harmonic, hcard]
  | succ k ih =>
      have hS : S.Nonempty := Finset.card_pos.mp (by
        rw [hcard]
        omega)
      let E := Fin.consEquiv (fun _ : Fin (k + 1) => PreferenceOrder n)
      calc
        (𝔼 orders : Fin (k + 1) → PreferenceOrder n,
            serialRankSum (k + 1) S orders) =
            𝔼 pair : PreferenceOrder n × (Fin k → PreferenceOrder n),
              serialRankSum (k + 1) S (E pair) := by
          symm
          exact Fintype.expect_equiv E
            (fun pair => serialRankSum (k + 1) S (E pair))
            (fun orders => serialRankSum (k + 1) S orders)
            (fun _ => rfl)
        _ = 𝔼 σ : PreferenceOrder n,
              𝔼 tail : Fin k → PreferenceOrder n,
                serialRankSum (k + 1) S (Fin.cons σ tail) := by
          simpa [E] using
            (Finset.expect_product
              (Finset.univ : Finset (PreferenceOrder n))
              (Finset.univ : Finset (Fin k → PreferenceOrder n))
              (fun pair => serialRankSum (k + 1) S (E pair)))
        _ = 𝔼 σ : PreferenceOrder n,
              ((activeRank S σ : ℝ) +
                ((n + 1 : ℕ) : ℝ) * ((harmonic (k + 1) : ℝ) - 1)) := by
          apply Finset.expect_congr rfl
          intro σ hσ
          simp only [serialRankSum, dif_pos hS, Fin.cons_zero, Fin.tail_cons]
          rw [Finset.expect_add_distrib]
          rw [Fintype.expect_const]
          rw [ih (S.erase (favorite σ S hS))]
          · rw [rankOf_favorite_eq_activeRank]
          · rw [Finset.card_erase_of_mem (favorite_mem σ S hS), hcard]
            omega
        _ = ((n + 1 : ℕ) : ℝ) / (S.card + 1) +
              ((n + 1 : ℕ) : ℝ) * ((harmonic (k + 1) : ℝ) - 1) := by
          rw [Finset.expect_add_distrib]
          change (𝔼 σ ∈ preferenceSample n, (activeRank S σ : ℝ)) +
              (𝔼 _σ ∈ preferenceSample n,
                ((n + 1 : ℕ) : ℝ) * ((harmonic (k + 1) : ℝ) - 1)) = _
          rw [activeRank_expectation hS,
            Finset.expect_const (preferenceSample_nonempty n)]
        _ = ((n + 1 : ℕ) : ℝ) * ((harmonic (k + 2) : ℝ) - 1) := by
          rw [harmonic_succ]
          push_cast
          rw [hcard]
          field_simp
          ring

/-- Reindex a profile by a priority permutation.  Coordinate zero becomes the
first-served agent, coordinate one the second-served agent, and so on. -/
def reindexProfile {n : ℕ} (priority : Equiv.Perm (Fin n)) :
    Profile n ≃ Profile n where
  toFun profile k := profile (priority k)
  invFun orders i := orders (priority.symm i)
  left_inv profile := by
    funext i
    simp
  right_inv orders := by
    funext k
    simp

/-- The finite uniform sample of a random service order and an independent
uniform i.i.d. preference profile. -/
def randomPrioritySample (n : ℕ) :
    Finset (Equiv.Perm (Fin n) × Profile n) :=
  permutationSample (Fin n) ×ˢ preferenceProfileSample n

/-- Average original rank produced by serial dictatorship for one draw. -/
def randomPriorityRank {n : ℕ}
    (draw : Equiv.Perm (Fin n) × Profile n) : ℝ :=
  serialRankSum n Finset.univ (reindexProfile draw.1 draw.2) / n

/-- Expected average rank of the explicitly modelled RP mechanism. -/
def rpExpectedRank (n : ℕ) : ℝ :=
  𝔼 draw ∈ randomPrioritySample n, randomPriorityRank draw

lemma serialRankSum_reindex_expectation (n : ℕ)
    (priority : Equiv.Perm (Fin n)) :
    (𝔼 profile : Profile n,
        serialRankSum n Finset.univ (reindexProfile priority profile)) =
      (𝔼 orders : Profile n,
        serialRankSum n Finset.univ orders) := by
  exact Fintype.expect_equiv (reindexProfile priority)
    (fun profile => serialRankSum n Finset.univ
      (reindexProfile priority profile))
    (fun orders => serialRankSum n Finset.univ orders)
    (fun _ => rfl)

/-- Knuth's harmonic formula, proved from the actual finite RP process. -/
theorem rpExpectedRank_eq_knuth_formula (n : ℕ) :
    rpExpectedRank n = rpExpectation n := by
  cases n with
  | zero =>
      simp [rpExpectedRank, randomPrioritySample, randomPriorityRank,
        rpExpectation, serialRankSum]
  | succ n =>
      rw [rpExpectedRank, randomPrioritySample, Finset.expect_product]
      calc
        (𝔼 priority ∈ permutationSample (Fin (n + 1)),
            𝔼 profile ∈ preferenceProfileSample (n + 1),
              randomPriorityRank (priority, profile)) =
            𝔼 priority ∈ permutationSample (Fin (n + 1)),
              rpExpectation (n + 1) := by
          apply Finset.expect_congr rfl
          intro priority hpriority
          rw [preferenceProfileSample_eq_univ]
          simp only [randomPriorityRank]
          change (𝔼 profile : Profile (n + 1),
              serialRankSum (n + 1) Finset.univ
                (reindexProfile priority profile) /
                  ((n + 1 : ℕ) : ℝ)) = _
          rw [← Finset.expect_div, serialRankSum_reindex_expectation]
          rw [serialRankSum_expectation Finset.univ (by simp)]
          rw [rpExpectation]
          ring
        _ = rpExpectation (n + 1) := by
          rw [Finset.expect_const]
          exact preferenceSample_nonempty (n + 1)

theorem rpExpectedRank_isEquivalent_log :
    rpExpectedRank ~[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  have hfun : rpExpectedRank = rpExpectation := by
    funext n
    exact rpExpectedRank_eq_knuth_formula n
  rw [hfun]
  exact rpExpectation_isEquivalent_log

end ProbabilisticSerial.RandomPriority
