import RankMGF
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Exact one-agent active-rank law

For a fixed active set of `s` goods in an `n`-good market, its positions in a
uniform random strict preference order form a uniform `s`-subset of
`{0, ..., n-1}`.  This file makes that finite sample space explicit and proves
the exact hypergeometric tail count.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.UniformSubsetRank

open UniformProduct

/-- The uniform sample space of the `s` positions occupied by a fixed set of
active goods in an `n`-element strict preference order. -/
def rankSample (n s : ℕ) : Finset (Finset ℕ) :=
  (range n).powersetCard s

/-- One-indexed position of the first active good.  The empty-set value is
irrelevant when `s > 0`, but makes the definition total. -/
def firstRank (T : Finset ℕ) : ℕ :=
  if h : T.Nonempty then T.min' h + 1 else 0

/-- No active good occurs in one of the first `r` positions. -/
def avoidsPrefix (r : ℕ) (T : Finset ℕ) : Prop :=
  ∀ k ∈ T, r ≤ k

instance (r : ℕ) : DecidablePred (avoidsPrefix r) := by
  intro T
  unfold avoidsPrefix
  infer_instance

lemma firstRank_gt_iff (T : Finset ℕ) (hT : T.Nonempty) (r : ℕ) :
    r < firstRank T ↔ avoidsPrefix r T := by
  simp only [firstRank, dif_pos hT, avoidsPrefix]
  rw [Nat.lt_add_one_iff, Finset.le_min'_iff]

lemma member_rankSample_nonempty {n s : ℕ} (hs : 0 < s)
    {T : Finset ℕ} (hT : T ∈ rankSample n s) : T.Nonempty := by
  rw [rankSample, mem_powersetCard] at hT
  exact card_pos.mp (hT.2.symm ▸ hs)

lemma probability_eq_card_filter_div {α : Type*} (sample : Finset α)
    (event : α → Prop) [DecidablePred event] :
    probability sample event =
      ((sample.filter event).card : ℝ) / sample.card := by
  rw [probability, Finset.expect_eq_sum_div_card]
  congr 1
  simp

lemma avoidsPrefix_filter_rankSample {n s r : ℕ} (hr : r ≤ n) :
    (rankSample n s).filter (avoidsPrefix r) = (Ico r n).powersetCard s := by
  classical
  ext T
  simp only [rankSample, mem_filter, mem_powersetCard, avoidsPrefix, mem_range, mem_Ico]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hprefix⟩
    exact ⟨fun k hk => Finset.mem_Ico.mpr ⟨hprefix k hk, mem_range.mp (hsub hk)⟩, hcard⟩
  · rintro ⟨hsub, hcard⟩
    constructor
    · exact ⟨fun k hk => mem_range.mpr (Finset.mem_Ico.mp (hsub hk)).2, hcard⟩
    · exact fun k hk => (Finset.mem_Ico.mp (hsub hk)).1

/-- Exact hypergeometric tail law for the first active position. -/
theorem avoidsPrefix_probability {n s r : ℕ} (hr : r ≤ n) :
    probability (rankSample n s) (avoidsPrefix r) =
      (Nat.choose (n - r) s : ℝ) / Nat.choose n s := by
  classical
  rw [probability_eq_card_filter_div, avoidsPrefix_filter_rankSample hr]
  simp [rankSample, card_powersetCard, Nat.card_Ico, hr]

/-- The same exact law stated using the one-indexed first active rank. -/
theorem firstRank_tail_probability {n s r : ℕ} (hs : 0 < s) (hr : r ≤ n) :
    probability (rankSample n s) (fun T => r < firstRank T) =
      (Nat.choose (n - r) s : ℝ) / Nat.choose n s := by
  classical
  have hevents :
      (rankSample n s).filter (fun T => r < firstRank T) =
        (rankSample n s).filter (avoidsPrefix r) := by
    apply filter_congr
    intro T hT
    exact firstRank_gt_iff T (member_rankSample_nonempty hs hT) r
  rw [probability_eq_card_filter_div, hevents]
  rw [← probability_eq_card_filter_div]
  exact avoidsPrefix_probability hr

lemma firstRank_le_market {n s : ℕ} (hs : 0 < s)
    {T : Finset ℕ} (hT : T ∈ rankSample n s) : firstRank T ≤ n := by
  have hnonempty := member_rankSample_nonempty hs hT
  rw [firstRank, dif_pos hnonempty]
  have hminmem := T.min'_mem hnonempty
  have hsubset := (mem_powersetCard.mp hT).1
  have hlt : T.min' hnonempty < n := mem_range.mp (hsubset hminmem)
  omega

lemma descFactorial_ratio_prod (n r s : ℕ) :
    ((n - r).descFactorial s : ℝ) / (n.descFactorial s : ℝ) =
      ∏ i ∈ range s, (((n - r - i : ℕ) : ℝ) / ((n - i : ℕ) : ℝ)) := by
  rw [prod_div_distrib]
  norm_cast
  simp only [Nat.descFactorial_eq_prod_range]

lemma descFactorial_ratio_le_pow {n r s : ℕ} (hn : 0 < n)
    (hr : r ≤ n) (hs : s ≤ n - r) :
    ((n - r).descFactorial s : ℝ) / (n.descFactorial s : ℝ) ≤
      (((n - r : ℕ) : ℝ) / n) ^ s := by
  rw [descFactorial_ratio_prod]
  have hconst :
      (∏ _i ∈ range s, (((n - r : ℕ) : ℝ) / n)) =
        (((n - r : ℕ) : ℝ) / n) ^ s := by
    rw [Finset.prod_const, Finset.card_range, div_pow]
  rw [← hconst]
  apply Finset.prod_le_prod
  · intro i hi
    positivity
  · intro i hi
    have his : i < s := mem_range.mp hi
    have hi_nr : i ≤ n - r := le_trans (Nat.le_of_lt his) hs
    have hi_n : i < n :=
      lt_of_lt_of_le his (le_trans hs (Nat.sub_le n r))
    have hnsub : 0 < ((n - i : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hi_n
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [div_le_div_iff₀ hnsub hnr]
    push_cast [Nat.cast_sub hi_nr, Nat.cast_sub hr,
      Nat.cast_sub (Nat.le_of_lt hi_n)]
    nlinarith

lemma choose_ratio_eq_descFactorial {n r s : ℕ} (hs : s ≤ n - r) :
    (Nat.choose (n - r) s : ℝ) / Nat.choose n s =
      ((n - r).descFactorial s : ℝ) / n.descFactorial s := by
  have hsn : s ≤ n := hs.trans (Nat.sub_le n r)
  have hc : (Nat.choose n s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hsn).ne'
  have hd : (n.descFactorial s : ℝ) ≠ 0 := by
    exact_mod_cast
      (Nat.descFactorial_eq_zero_iff_lt.not.mpr (not_lt_of_ge hsn))
  apply (div_eq_div_iff hc hd).2
  have hnum := Nat.descFactorial_eq_factorial_mul_choose (n - r) s
  have hden := Nat.descFactorial_eq_factorial_mul_choose n s
  rw [hnum, hden]
  push_cast
  ring

lemma ratio_pow_le_exp {n r s : ℕ} (hn : 0 < n) (hr : r ≤ n) :
    (((n - r : ℕ) : ℝ) / n) ^ s ≤
      Real.exp (-((s : ℝ) / n) * r) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrR : (r : ℝ) ≤ n := by exact_mod_cast hr
  have hbase : 0 ≤ 1 - (r : ℝ) / n := by
    rw [sub_nonneg, div_le_one hnR]
    exact hrR
  calc
    (((n - r : ℕ) : ℝ) / n) ^ s = (1 - (r : ℝ) / n) ^ s := by
      rw [Nat.cast_sub hr]
      congr 1
      field_simp
    _ ≤ Real.exp (-((r : ℝ) / n)) ^ s :=
      pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg ((r : ℝ) / n)) s
    _ = Real.exp (-((s : ℝ) / n) * r) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp

/-- The geometric tail inequality used in the paper:
`choose (n-r) s / choose n s ≤ exp(-(s/n)r)`. -/
theorem choose_ratio_le_exp {n r s : ℕ} (hn : 0 < n)
    (hr : r ≤ n) :
    (Nat.choose (n - r) s : ℝ) / Nat.choose n s ≤
      Real.exp (-((s : ℝ) / n) * r) := by
  by_cases hsr : s ≤ n - r
  · calc
      (Nat.choose (n - r) s : ℝ) / Nat.choose n s =
          ((n - r).descFactorial s : ℝ) / n.descFactorial s :=
        choose_ratio_eq_descFactorial hsr
      _ ≤ (((n - r : ℕ) : ℝ) / n) ^ s :=
        descFactorial_ratio_le_pow hn hr hsr
      _ ≤ Real.exp (-((s : ℝ) / n) * r) := ratio_pow_le_exp hn hr
  · have hlt : n - r < s := Nat.lt_of_not_ge hsr
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_div]
    exact (Real.exp_pos _).le

/-- Complete one-agent rank tail bound for the explicit uniform subset model. -/
theorem firstRank_tail_le_exp {n s r : ℕ} (hn : 0 < n) (hs : 0 < s)
    (hr : r ≤ n) :
    probability (rankSample n s) (fun T => r < firstRank T) ≤
      Real.exp (-((s : ℝ) / n) * r) := by
  rw [firstRank_tail_probability hs hr]
  exact choose_ratio_le_exp hn hr

lemma rankSample_nonempty {n s : ℕ} (hs : s ≤ n) :
    (rankSample n s).Nonempty := by
  rw [rankSample, powersetCard_nonempty]
  simpa using hs

/-- MGF estimate for a fixed active set in a uniform random preference. -/
theorem firstRank_scaled_mgf {n s : ℕ} (hn : 0 < n) (hs0 : 0 < s)
    (hsn : s ≤ n) :
    (𝔼 T ∈ rankSample n s,
        Real.exp ((1 / 2 : ℝ) * (((s : ℝ) / n) * firstRank T))) ≤
      1 + Real.exp 1 := by
  apply UniformRank.mgf_scaled_rank_le_one_add_exp
    (rankSample n s) (rankSample_nonempty hsn) firstRank n
  · intro T hT
    exact firstRank_le_market hs0 hT
  · exact div_pos (by exact_mod_cast hs0) (by exact_mod_cast hn)
  · apply (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).2
    exact_mod_cast hsn
  · intro r hr
    exact firstRank_tail_le_exp hn hs0 (Nat.le_of_lt hr)

/-- Fixed-active-set concentration for `n` independent uniform preferences.
After scaling ranks by `s/n`, this is exactly the Chernoff step in the proof of
the uniform active-rank lemma. -/
theorem fixed_active_set_sum_tail {n s : ℕ} (hn : 0 < n) (hs0 : 0 < s)
    (hsn : s ≤ n) (K : ℝ) :
    probability (productSample (rankSample n s) n)
        (fun profile =>
          K * n ≤ ∑ i : Fin n, ((s : ℝ) / n) * firstRank (profile i)) ≤
      Real.exp (-(n : ℝ) *
        ((1 / 2 : ℝ) * K - Real.log (1 + Real.exp 1))) := by
  exact chernoff_sum (rankSample n s)
    (fun T => ((s : ℝ) / n) * firstRank T)
    (by norm_num) (by positivity) (firstRank_scaled_mgf hn hs0 hsn) n

end ProbabilisticSerial.UniformSubsetRank
