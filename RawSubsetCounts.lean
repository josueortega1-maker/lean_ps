import CouponLowerBound

/-! Lower deviations for counts in fixed subsets of the iid raw labels. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.RawSubsetCounts
open UniformProduct CouponLowerBound

def hit {m : ℕ} (S : Finset (Fin m)) (g : Fin m) : ℝ := if g ∈ S then 1 else 0

def count {m k : ℕ} (S : Finset (Fin m)) (w : Fin k → Fin m) : ℝ := ∑ i, hit S (w i)

lemma expect_hit {m : ℕ} (S : Finset (Fin m)) :
    (𝔼 g : Fin m, hit S g) = (S.card : ℝ) / m := by
  simp [hit, Finset.expect_eq_sum_div_card]

lemma count_lower_mgf {m : ℕ} (hm : 0 < m) (S : Finset (Fin m)) (θ : ℝ) :
    (𝔼 g : Fin m, Real.exp (-θ * hit S g)) ≤
      Real.exp (((S.card : ℝ) / m) * (Real.exp (-θ) - 1)) := by
  have hs : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have heq (g : Fin m) : Real.exp (-θ * hit S g) =
      1 + (Real.exp (-θ) - 1) * hit S g := by
    by_cases hg : g ∈ S <;> simp [hit, hg]
  simp_rw [heq]
  rw [Finset.expect_add_distrib, Finset.expect_const hs, ← Finset.mul_expect, expect_hit]
  have h := Real.add_one_le_exp (((S.card : ℝ) / m) * (Real.exp (-θ) - 1))
  nlinarith

theorem count_lower_tail {m : ℕ} (hm : 0 < m) (S : Finset (Fin m)) (k : ℕ)
    {θ N : ℝ} (hθ : 0 < θ) :
    probability (labelSample m k) (fun w => count S w ≤ N) ≤
      Real.exp (θ * N + k * ((S.card : ℝ) / m) * (Real.exp (-θ) - 1)) := by
  have hmarkov := markov_div (labelSample m k) (fun w => count S w ≤ N)
    (fun w => Real.exp (-θ * count S w))
    (a := Real.exp (-θ * N)) (Real.exp_pos _)
    (fun _ _ => (Real.exp_pos _).le)
    (by
      intro w hw hlow
      apply Real.exp_le_exp.mpr
      nlinarith)
  have hexpect : (𝔼 w ∈ labelSample m k, Real.exp (-θ * count S w)) =
      (𝔼 g : Fin m, Real.exp (-θ * hit S g)) ^ k :=
    exp_sum_expect_eq_pow Finset.univ (hit S) (-θ) k
  rw [hexpect] at hmarkov
  have hpow := pow_le_pow_left₀
    (Finset.expect_nonneg (fun g _ => (Real.exp_pos (-θ * hit S g)).le))
    (count_lower_mgf hm S θ) k
  calc
    _ ≤ (𝔼 g : Fin m, Real.exp (-θ * hit S g)) ^ k / Real.exp (-θ * N) := hmarkov
    _ ≤ (Real.exp (((S.card : ℝ) / m) * (Real.exp (-θ) - 1))) ^ k /
        Real.exp (-θ * N) := div_le_div_of_nonneg_right hpow (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_sub]
      congr 1
      ring

theorem count_lower_tail_of_mean_ge {m : ℕ} (hm : 0 < m) (S : Finset (Fin m)) (k : ℕ)
    {α N : ℝ} (hα : 1 < α) (hmean : α * N ≤ k * ((S.card : ℝ) / m)) :
    probability (labelSample m k) (fun w => count S w ≤ N) ≤
      Real.exp (-(α - 1 - Real.log α) * N) := by
  have hαpos : 0 < α := by linarith
  have hlog : 0 < Real.log α := Real.log_pos hα
  have hexp : Real.exp (-Real.log α) = 1 / α := by
    rw [Real.exp_neg, Real.exp_log hαpos, one_div]
  have hnegative : 1 / α - 1 ≤ 0 := by
    have h := (div_le_one hαpos).2 hα.le
    linarith
  have hmul := mul_le_mul_of_nonpos_right hmean hnegative
  have hidentity : Real.log α * N + (α * N) * (1 / α - 1) =
      -(α - 1 - Real.log α) * N := by
    field_simp
    <;> ring
  apply (count_lower_tail hm S k hlog).trans
  apply Real.exp_le_exp.mpr
  rw [hexp]
  linarith

end ProbabilisticSerial.RawSubsetCounts
