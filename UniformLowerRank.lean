import UniformPermutationProfile
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Lower concentration for the best available rank

The sample is the same uniform permutation sample used by `ReplicaPS`.
We compute its exact mean and prove a lower exponential moment estimate.
The second-moment constant is deliberately loose; only its independence of
the market and active-set sizes matters for the fixed-quota lower bound.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.UniformLowerRank
open UniformProduct UniformSubsetRank UniformPermutation

lemma rank_eq_tail_sum {N r : ℕ} (hr : r ≤ N) :
    (r : ℝ) = ∑ k ∈ range N, if k < r then (1 : ℝ) else 0 := by
  have hf : (range N).filter (fun k => k < r) = range r := by
    ext k
    simp only [mem_filter, mem_range]
    omega
  rw [← sum_filter, hf]
  simp

theorem expect_rank_eq_tail_sum {α : Type*} (sample : Finset α)
    (R : α → ℕ) (N : ℕ) (hR : ∀ a ∈ sample, R a ≤ N) :
    (𝔼 a ∈ sample, (R a : ℝ)) =
      ∑ k ∈ range N, probability sample (fun a => k < R a) := by
  calc
    (𝔼 a ∈ sample, (R a : ℝ)) =
        𝔼 a ∈ sample, ∑ k ∈ range N, if k < R a then (1 : ℝ) else 0 :=
      Finset.expect_congr rfl (fun a ha => rank_eq_tail_sum (hR a ha))
    _ = _ := by rw [Finset.expect_sum_comm]; rfl

lemma sum_choose_successors (n s : ℕ) (hs : 0 < s) :
    (∑ r ∈ range n, (r + 1).choose s) = (n + 1).choose (s + 1) := by
  induction n with
  | zero => simp [Nat.choose_eq_zero_of_lt (by omega : 1 < s + 1)]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simpa only [Nat.succ_eq_add_one, Nat.add_comm] using
        (Nat.choose_succ_succ (n + 1) s).symm

theorem expected_firstRank {n s : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    (𝔼 T ∈ rankSample n s, (firstRank T : ℝ)) = (n + 1 : ℝ) / (s + 1) := by
  rw [expect_rank_eq_tail_sum (rankSample n s) firstRank n
    (fun _ hT => firstRank_le_market hs hT)]
  have htail : (∑ r ∈ range n, probability (rankSample n s) (fun T => r < firstRank T)) =
      ∑ r ∈ range n, ((n - r).choose s : ℝ) / n.choose s := by
    apply Finset.sum_congr rfl
    intro r hr
    exact firstRank_tail_probability hs (Nat.le_of_lt (mem_range.mp hr))
  rw [htail]
  rw [← Finset.sum_div]
  have hsum : (∑ r ∈ range n, (n - r).choose s) = (n + 1).choose (s + 1) := by
    have h := Finset.sum_range_reflect (fun r => (r + 1).choose s) n
    have heq : (∑ r ∈ range n, (n - r).choose s) =
        ∑ r ∈ range n, (n - 1 - r + 1).choose s := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      have := mem_range.mp hr
      omega
    rw [heq, h]
    exact sum_choose_successors n s hs
  have hsumR : (∑ r ∈ range n, ((n - r).choose s : ℝ)) =
      ((n + 1).choose (s + 1) : ℝ) := by exact_mod_cast hsum
  rw [hsumR]
  have hc : (0 : ℝ) < n.choose s := by exact_mod_cast Nat.choose_pos hsn
  have hid : (n + 1 : ℝ) * n.choose s =
      ((n + 1).choose (s + 1) : ℝ) * (s + 1) := by
    exact_mod_cast Nat.succ_mul_choose_eq n s
  apply (div_eq_div_iff hc.ne' (by positivity : (s + 1 : ℝ) ≠ 0)).2
  linarith

theorem expected_scaledActiveRank {m : ℕ} {S : Finset (Fin m)}
    (hS : S.Nonempty) :
    (𝔼 σ ∈ preferenceSample m, scaledActiveRank m S σ) =
      (S.card : ℝ) / m * ((m + 1 : ℝ) / (S.card + 1)) := by
  unfold scaledActiveRank activeRank
  rw [← Finset.mul_expect,
    activePositions_expect_eq_rankSample m S (fun T => (firstRank T : ℝ)),
    expected_firstRank (Finset.card_pos.mpr hS) (by simpa using S.card_le_univ)]

theorem expected_scaledActiveRank_ge {m : ℕ} (hm : 0 < m)
    {S : Finset (Fin m)} (hS : S.Nonempty) :
    1 - 1 / (S.card + 1 : ℝ) ≤
      𝔼 σ ∈ preferenceSample m, scaledActiveRank m S σ := by
  rw [expected_scaledActiveRank hS]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsR : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hden : (0 : ℝ) < S.card + 1 := by positivity
  have hleft : 1 - 1 / (S.card + 1 : ℝ) = (S.card : ℝ) / (S.card + 1) := by
    field_simp
    <;> ring
  rw [hleft]
  have hratio : (1 : ℝ) ≤ (m + 1 : ℝ) / m := (le_div_iff₀ hmR).2 (by linarith)
  calc
    (S.card : ℝ) / (S.card + 1) = (S.card : ℝ) / (S.card + 1) * 1 := by ring
    _ ≤ (S.card : ℝ) / (S.card + 1) * ((m + 1 : ℝ) / m) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

lemma sq_le_sixteen_exp_half {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 ≤ 16 * Real.exp (x / 2) := by
  have h := Real.add_one_le_exp (x / 4)
  have he : Real.exp (x / 4) * Real.exp (x / 4) = Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hp := mul_self_le_mul_self (by positivity : 0 ≤ x / 4 + 1) h
  rw [he] at hp
  nlinarith

theorem scaledActiveRank_second_moment_le {m : ℕ} (hm : 0 < m)
    {S : Finset (Fin m)} (hS : S.Nonempty) :
    (𝔼 σ ∈ preferenceSample m, (scaledActiveRank m S σ) ^ 2) ≤
      16 * (1 + Real.exp 1) := by
  calc
    _ ≤ 𝔼 σ ∈ preferenceSample m,
        16 * Real.exp ((1 / 2 : ℝ) * scaledActiveRank m S σ) := by
      apply expect_mono
      intro σ hσ
      simpa only [one_div_mul_eq_div] using
        sq_le_sixteen_exp_half (by unfold scaledActiveRank; positivity)
    _ = 16 * (𝔼 σ ∈ preferenceSample m,
        Real.exp ((1 / 2 : ℝ) * scaledActiveRank m S σ)) := by rw [Finset.mul_expect]
    _ ≤ _ := mul_le_mul_of_nonneg_left (activeRank_scaled_mgf hm hS) (by norm_num)

lemma exp_neg_le_one_sub_add_sq {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 := by
  have hxp : 0 < 1 + x := by linarith
  have hupper : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hxp (by linarith [Real.add_one_le_exp x])
  apply hupper.trans
  apply (div_le_iff₀ hxp).2
  nlinarith [pow_nonneg hx 3]

theorem scaledActiveRank_lower_mgf {m : ℕ} (hm : 0 < m)
    {S : Finset (Fin m)} (hS : S.Nonempty) {θ a : ℝ} (hθ : 0 ≤ θ)
    (ha : a ≤ 1 - 1 / (S.card + 1 : ℝ)) :
    (𝔼 σ ∈ preferenceSample m, Real.exp (-θ * scaledActiveRank m S σ)) ≤
      Real.exp (-θ * a + θ ^ 2 * (16 * (1 + Real.exp 1))) := by
  have hmean := expected_scaledActiveRank_ge hm hS
  have hsecond := scaledActiveRank_second_moment_le hm hS
  have h : (𝔼 σ ∈ preferenceSample m,
      Real.exp (-θ * scaledActiveRank m S σ)) ≤
      1 - θ * (𝔼 σ ∈ preferenceSample m, scaledActiveRank m S σ) +
        θ ^ 2 * (𝔼 σ ∈ preferenceSample m, (scaledActiveRank m S σ) ^ 2) := by
    calc
      _ ≤ 𝔼 σ ∈ preferenceSample m,
          (1 - θ * scaledActiveRank m S σ + θ ^ 2 * (scaledActiveRank m S σ) ^ 2) := by
        apply expect_mono
        intro σ hσ
        have hx : 0 ≤ θ * scaledActiveRank m S σ := by
          unfold scaledActiveRank
          positivity
        simpa only [neg_mul, mul_pow] using exp_neg_le_one_sub_add_sq hx
      _ = _ := by
        rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
          Finset.expect_const (preferenceSample_nonempty m),
          ← Finset.mul_expect, ← Finset.mul_expect]
  have h1 := mul_le_mul_of_nonneg_left (ha.trans hmean) hθ
  have h2 := mul_le_mul_of_nonneg_left hsecond (sq_nonneg θ)
  have hpoly : 1 - θ * (𝔼 σ ∈ preferenceSample m, scaledActiveRank m S σ) +
        θ ^ 2 * (𝔼 σ ∈ preferenceSample m, (scaledActiveRank m S σ) ^ 2) ≤
      1 + (-θ * a + θ ^ 2 * (16 * (1 + Real.exp 1))) := by linarith
  have he := Real.add_one_le_exp (-θ * a + θ ^ 2 * (16 * (1 + Real.exp 1)))
  exact h.trans (hpoly.trans (by linarith))

theorem fixed_set_lower_tail {m n : ℕ} (hm : 0 < m)
    {S : Finset (Fin m)} (hS : S.Nonempty) {θ a b : ℝ} (hθ : 0 < θ)
    (ha : a ≤ 1 - 1 / (S.card + 1 : ℝ)) :
    probability (productSample (preferenceSample m) n)
      (fun profile => (∑ i : Fin n, scaledActiveRank m S (profile i)) ≤ b * n) ≤
      Real.exp (-(n : ℝ) * (θ * (a - b) - θ ^ 2 * (16 * (1 + Real.exp 1)))) := by
  have h := chernoff_sum (preferenceSample m) (fun σ => -scaledActiveRank m S σ)
    (K := -b) (B := Real.exp (-θ * a + θ ^ 2 * (16 * (1 + Real.exp 1))))
    hθ (Real.exp_pos _)
    (by simpa only [mul_neg, neg_mul] using scaledActiveRank_lower_mgf hm hS hθ.le ha) n
  simp only [Finset.sum_neg_distrib, neg_mul, mul_neg, neg_le_neg_iff, Real.log_exp] at h
  convert h using 1 <;> congr 1 <;> ring

end ProbabilisticSerial.UniformLowerRank
