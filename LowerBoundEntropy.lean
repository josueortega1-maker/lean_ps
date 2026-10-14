import CouponLowerBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Exponential bounds for families of small type sets. -/

noncomputable section
open Finset Filter
open scoped BigOperators Topology

namespace ProbabilisticSerial.LowerBoundEntropy

lemma sum_exp_card (m : ℕ) (B : ℝ) :
    (∑ S : Finset (Fin m), Real.exp (-B * S.card)) = (1 + Real.exp (-B)) ^ m := by
  have h := (Finset.prod_one_add (f := fun _ : Fin m => Real.exp (-B)) Finset.univ).symm
  simpa [← Real.exp_nat_mul, mul_comm] using h

theorem small_family_card_le (m hi : ℕ) (family : Finset (Finset (Fin m)))
    {B : ℝ} (hB : 0 ≤ B) (hsize : ∀ S ∈ family, S.card ≤ hi) :
    (family.card : ℝ) ≤ Real.exp (m * Real.exp (-B) + B * hi) := by
  have hsum : (family.card : ℝ) * Real.exp (-B * hi) ≤
      Real.exp (m * Real.exp (-B)) := by
    calc
      _ = ∑ _S ∈ family, Real.exp (-B * hi) := by simp
      _ ≤ ∑ S ∈ family, Real.exp (-B * S.card) := by
        apply Finset.sum_le_sum
        intro S hS
        apply Real.exp_le_exp.mpr
        have hcard : (S.card : ℝ) ≤ hi := by exact_mod_cast hsize S hS
        nlinarith
      _ ≤ ∑ S : Finset (Fin m), Real.exp (-B * S.card) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun S _ _ => (Real.exp_pos _).le)
      _ = (1 + Real.exp (-B)) ^ m := sum_exp_card m B
      _ ≤ (Real.exp (Real.exp (-B))) ^ m :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (Real.exp (-B))]) m
      _ = _ := (Real.exp_nat_mul _ _).symm
  have heq : Real.exp (m * Real.exp (-B) + B * hi) * Real.exp (-B * hi) =
      Real.exp (m * Real.exp (-B)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  exact (mul_le_mul_iff_of_pos_right (Real.exp_pos (-B * hi))).mp (hsum.trans_eq heq.symm)

theorem small_family_card_le_rate (m hi : ℕ) (family : Finset (Finset (Fin m)))
    {B : ℝ} (hB : 0 ≤ B) (hsize : ∀ S ∈ family, S.card ≤ hi)
    (hhi : (hi : ℝ) ≤ m * Real.exp (-B)) :
    (family.card : ℝ) ≤ Real.exp (((B + 1) * Real.exp (-B)) * m) := by
  apply (small_family_card_le m hi family hB hsize).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hhi hB
  nlinarith

theorem exists_small_family_rate {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ (B + 1) * Real.exp (-B) < c := by
  have h1 : Tendsto (fun B : ℝ => B * Real.exp (-B)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h0 : Tendsto (fun B : ℝ => Real.exp (-B)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have hlim : Tendsto (fun B : ℝ => (B + 1) * Real.exp (-B)) atTop (𝓝 0) := by
    simpa [add_mul] using h1.add h0
  exact ((eventually_ge_atTop (0 : ℝ)).and (hlim.eventually (gt_mem_nhds hc))).exists

end ProbabilisticSerial.LowerBoundEntropy
