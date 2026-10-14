import UniformProductChernoff
import Mathlib.Algebra.GeomSum

/-!
# From the one-agent rank tail to a uniform MGF bound

This file formalizes the tail-sum calculation in the uniform active-rank
lemma.  A natural-valued rank `R`, bounded by `N`, is sampled uniformly from a
finite set.  If `P(R > r) ≤ exp(-δ r)`, then the MGF of the scaled rank at
parameter `1/2` is bounded by the absolute constant `1 + e`.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.UniformRank

open UniformProduct

lemma exp_nat_increment_nonneg {c : ℝ} (hc : 0 ≤ c) (r : ℕ) :
    0 ≤ Real.exp (c * (r + 1)) - Real.exp (c * r) := by
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  norm_num
  nlinarith

lemma exp_rank_tail_sum {α : Type*} (R : α → ℕ) (N : ℕ)
    (a : α) (hRa : R a ≤ N) (c : ℝ) :
    Real.exp (c * R a) =
      1 + ∑ r ∈ range N,
        if r < R a then
          (Real.exp (c * (r + 1)) - Real.exp (c * r))
        else 0 := by
  have hfilter : (range N).filter (fun r => r < R a) = range (R a) := by
    ext r
    simp only [mem_filter, mem_range]
    constructor
    · exact fun h => h.2
    · intro hr
      exact ⟨hr.trans_le hRa, hr⟩
  rw [← sum_filter]
  rw [hfilter]
  have htel := sum_range_sub (fun r : ℕ => Real.exp (c * r)) (R a)
  norm_num at htel ⊢
  linarith

lemma expect_exp_rank_eq_tail_sum {α : Type*} (sample : Finset α)
    (hs : sample.Nonempty) (R : α → ℕ) (N : ℕ)
    (hR : ∀ a ∈ sample, R a ≤ N)
    (c : ℝ) :
    (𝔼 a ∈ sample, Real.exp (c * R a)) =
      1 + ∑ r ∈ range N,
        (Real.exp (c * (r + 1)) - Real.exp (c * r)) *
          probability sample (fun a => r < R a) := by
  calc
    (𝔼 a ∈ sample, Real.exp (c * R a)) =
        Finset.expect sample (fun a =>
          1 + ∑ r ∈ range N,
            if r < R a then
              (Real.exp (c * (r + 1)) - Real.exp (c * r))
            else 0) := by
      apply Finset.expect_congr rfl
      intro a ha
      exact exp_rank_tail_sum R N a (hR a ha) c
    _ = (𝔼 _a ∈ sample, (1 : ℝ)) +
          Finset.expect sample (fun a =>
            ∑ r ∈ range N,
              if r < R a then
                (Real.exp (c * (r + 1)) - Real.exp (c * r))
              else 0) := by
      rw [Finset.expect_add_distrib]
    _ = 1 + ∑ r ∈ range N,
          𝔼 a ∈ sample,
            if r < R a then
              (Real.exp (c * (r + 1)) - Real.exp (c * r))
            else 0 := by
      rw [Finset.expect_const hs, Finset.expect_sum_comm]
    _ = 1 + ∑ r ∈ range N,
          (Real.exp (c * (r + 1)) - Real.exp (c * r)) *
            probability sample (fun a => r < R a) := by
      congr 1
      apply sum_congr rfl
      intro r hr
      change (𝔼 a ∈ sample,
          if r < R a then
            (Real.exp (c * (r + 1)) - Real.exp (c * r))
          else 0) =
        (Real.exp (c * (r + 1)) - Real.exp (c * r)) *
          (𝔼 a ∈ sample, if r < R a then (1 : ℝ) else 0)
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro a ha
      by_cases h : r < R a <;> simp [h]

lemma increment_mul_tail_eq_geometric (δ : ℝ) (r : ℕ) :
    (Real.exp ((δ / 2) * (r + 1)) - Real.exp ((δ / 2) * r)) *
        Real.exp (-δ * r) =
      (Real.exp (δ / 2) - 1) * (Real.exp (-(δ / 2))) ^ r := by
  rw [← Real.exp_nat_mul]
  have hsucc :
      Real.exp ((δ / 2) * ((r : ℝ) + 1)) =
        Real.exp ((δ / 2) * r) * Real.exp (δ / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  norm_num at hsucc ⊢
  rw [hsucc]
  have hcombine :
      Real.exp (δ / 2 * ↑r) * Real.exp (-(δ * ↑r)) =
        Real.exp (-(↑r * (δ / 2))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (Real.exp (δ / 2 * ↑r) * Real.exp (δ / 2) - Real.exp (δ / 2 * ↑r)) *
        Real.exp (-(δ * ↑r)) =
      (Real.exp (δ / 2) - 1) *
        (Real.exp (δ / 2 * ↑r) * Real.exp (-(δ * ↑r))) := by ring
    _ = (Real.exp (δ / 2) - 1) * Real.exp (-(↑r * (δ / 2))) := by
      rw [hcombine]

lemma geometric_increment_sum_le_exp_half {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∑ r ∈ range N,
        (Real.exp (δ / 2) - 1) * (Real.exp (-(δ / 2))) ^ r ≤
      Real.exp (δ / 2) := by
  let q := Real.exp (-(δ / 2))
  let A := Real.exp (δ / 2) - 1
  have hc : 0 < δ / 2 := by linarith
  have hA : 0 ≤ A := by
    dsimp [A]
    exact sub_nonneg.mpr (Real.one_le_exp hc.le)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : ∑ r ∈ range N, q ^ r ≤ (1 - q)⁻¹ := by
    simpa [Nat.Ico_zero_eq_range] using
      (geom_sum_Ico_le_of_lt_one hq0.le hq1 (m := 0) (n := N))
  calc
    ∑ r ∈ range N, A * q ^ r = A * ∑ r ∈ range N, q ^ r := by
      rw [mul_sum]
    _ ≤ A * (1 - q)⁻¹ := mul_le_mul_of_nonneg_left hgeom hA
    _ = Real.exp (δ / 2) := by
      dsimp [A, q]
      rw [Real.exp_neg]
      let x := Real.exp (δ / 2)
      have hx : 1 < x := by
        dsimp [x]
        exact Real.one_lt_exp_iff.mpr hc
      have hx0 : x ≠ 0 := ne_of_gt (lt_trans (by norm_num) hx)
      have hxm1 : x - 1 ≠ 0 := by linarith
      have hform : 1 - x⁻¹ = (x - 1) / x := by
        rw [inv_eq_one_div]
        field_simp [hx0]
      change (x - 1) * (1 - x⁻¹)⁻¹ = x
      rw [hform, inv_div]
      field_simp [hxm1]

/-- The paper's one-coordinate MGF estimate.  The geometric tail is required
only up to the deterministic rank bound `N`. -/
theorem mgf_scaled_rank_le_one_add_exp {α : Type*} (sample : Finset α)
    (hs : sample.Nonempty) (R : α → ℕ) (N : ℕ)
    (hR : ∀ a ∈ sample, R a ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (htail : ∀ r < N,
      probability sample (fun a => r < R a) ≤ Real.exp (-δ * r)) :
    (𝔼 a ∈ sample, Real.exp ((1 / 2 : ℝ) * (δ * R a))) ≤
      1 + Real.exp 1 := by
  have hc : 0 ≤ δ / 2 := (div_nonneg hδ.le (by norm_num))
  rw [show (fun a => Real.exp ((1 / 2 : ℝ) * (δ * R a))) =
      (fun a => Real.exp ((δ / 2) * R a)) by
    funext a
    congr 1
    ring]
  rw [expect_exp_rank_eq_tail_sum sample hs R N hR (δ / 2)]
  have hsum :
      ∑ r ∈ range N,
          (Real.exp ((δ / 2) * (r + 1)) - Real.exp ((δ / 2) * r)) *
            probability sample (fun a => r < R a) ≤
        ∑ r ∈ range N,
          (Real.exp (δ / 2) - 1) * (Real.exp (-(δ / 2))) ^ r := by
    apply sum_le_sum
    intro r hr
    calc
      (Real.exp ((δ / 2) * (r + 1)) - Real.exp ((δ / 2) * r)) *
          probability sample (fun a => r < R a) ≤
        (Real.exp ((δ / 2) * (r + 1)) - Real.exp ((δ / 2) * r)) *
          Real.exp (-δ * r) :=
        mul_le_mul_of_nonneg_left (htail r (mem_range.mp hr))
          (exp_nat_increment_nonneg hc r)
      _ = (Real.exp (δ / 2) - 1) * (Real.exp (-(δ / 2))) ^ r :=
        increment_mul_tail_eq_geometric δ r
  calc
    1 + ∑ r ∈ range N,
        (Real.exp ((δ / 2) * (r + 1)) - Real.exp ((δ / 2) * r)) *
          probability sample (fun a => r < R a)
        ≤ 1 + ∑ r ∈ range N,
            (Real.exp (δ / 2) - 1) * (Real.exp (-(δ / 2))) ^ r :=
      add_le_add_left hsum 1
    _ ≤ 1 + Real.exp (δ / 2) :=
      add_le_add_left (geometric_increment_sum_le_exp_half hδ N) 1
    _ ≤ 1 + Real.exp 1 := by
      apply add_le_add_left
      apply Real.exp_le_exp.mpr
      linarith

end ProbabilisticSerial.UniformRank
