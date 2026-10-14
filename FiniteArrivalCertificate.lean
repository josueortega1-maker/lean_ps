import FiniteAtomicExposure

/-!+# Positive finite certificates for exposure bounds

A certificate combines finitely many exponential-arrival inequalities with
nonnegative coefficients. Concavity between consecutive test horizons reduces
the required pointwise domination to finitely many endpoint checks.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.FiniteArrivalCertificate

open FiniteAtomicExposure

def kernel (θ t r : ℝ) : ℝ := arrivalCost θ (max (t - r) 0)

def combination {κ : Type*} [Fintype κ] (mass θ t : κ → ℝ) (r : ℝ) : ℝ :=
  ∑ k, mass k * kernel (θ k) (t k) r

lemma kernel_concave_gap {θ t l h a b : ℝ}
    (hlh : l ≤ h) (hgap : t ≤ l ∨ h ≤ t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * kernel θ t l + b * kernel θ t h ≤ kernel θ t (a * l + b * h) := by
  have haeq : a = 1 - b := by linarith
  have hblend : l ≤ a * l + b * h ∧ a * l + b * h ≤ h := by
    rw [haeq]
    constructor
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr hlh)]
    · have h := mul_nonneg ha (sub_nonneg.mpr hlh)
      rw [haeq] at h
      nlinarith
  rcases hgap with ht | ht
  · simp only [kernel, max_eq_right (show t - l ≤ 0 by linarith),
      max_eq_right (show t - h ≤ 0 by linarith),
      max_eq_right (show t - (a * l + b * h) ≤ 0 by linarith),
      arrivalCost, mul_zero, Real.exp_zero, sub_self, add_zero, le_refl]
  · have he := convexOn_exp.2 (Set.mem_univ (-θ * (t - l)))
      (Set.mem_univ (-θ * (t - h))) ha hb hab
    simp only [smul_eq_mul] at he
    have hid : a * (-θ * (t - l)) + b * (-θ * (t - h)) =
        -θ * (t - (a * l + b * h)) := by rw [haeq]; ring
    rw [hid] at he
    simp only [kernel, max_eq_left (show 0 ≤ t - l by linarith),
      max_eq_left (show 0 ≤ t - h by linarith),
      max_eq_left (show 0 ≤ t - (a * l + b * h) by linarith), arrivalCost]
    nlinarith

lemma combination_concave_gap {κ : Type*} [Fintype κ] (mass θ t : κ → ℝ)
    (hmass : ∀ k, 0 ≤ mass k) {l h a b : ℝ} (hlh : l ≤ h)
    (hgap : ∀ k, t k ≤ l ∨ h ≤ t k)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * combination mass θ t l + b * combination mass θ t h ≤
      combination mass θ t (a * l + b * h) := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset κ))
    (fun k _ => mul_le_mul_of_nonneg_left
      (kernel_concave_gap (θ := θ k) hlh (hgap k) ha hb hab) (hmass k))
  simpa only [combination, Finset.mul_sum, ← Finset.sum_add_distrib,
    mul_add, mul_assoc, mul_left_comm] using hs

lemma domination_between {κ : Type*} [Fintype κ] (mass θ t : κ → ℝ)
    (hmass : ∀ k, 0 ≤ mass k) {l h r : ℝ} (hlh : l < h)
    (hlr : l ≤ r) (hrh : r ≤ h) (hgap : ∀ k, t k ≤ l ∨ h ≤ t k)
    (hl : 1 - l ≤ combination mass θ t l)
    (hh : 1 - h ≤ combination mass θ t h) :
    1 - r ≤ combination mass θ t r := by
  let a := (h - r) / (h - l)
  let b := (r - l) / (h - l)
  have hd : 0 < h - l := sub_pos.mpr hlh
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hrh) hd.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hlr) hd.le
  have hab : a + b = 1 := by dsimp [a, b]; field_simp <;> ring
  have hr : a * l + b * h = r := by dsimp [a, b]; field_simp <;> ring
  have hc := combination_concave_gap mass θ t hmass hlh.le hgap ha hb hab
  rw [hr] at hc
  have hineq := add_le_add (mul_le_mul_of_nonneg_left hl ha) (mul_le_mul_of_nonneg_left hh hb)
  have hid : a * (1 - l) + b * (1 - h) = 1 - r := by nlinarith [hab, hr]
  rw [hid] at hineq
  exact hineq.trans hc

lemma exists_grid_interval (g : ℕ → ℝ) (N : ℕ) {r : ℝ}
    (h0 : g 0 ≤ r) (hN : r ≤ g (N + 1)) :
    ∃ j ≤ N, g j ≤ r ∧ r ≤ g (j + 1) := by
  induction N with
  | zero => exact ⟨0, le_rfl, h0, hN⟩
  | succ N ih =>
      by_cases h : r ≤ g (N + 1)
      · obtain ⟨j, hj, hl, hr⟩ := ih h
        exact ⟨j, by omega, hl, hr⟩
      · exact ⟨N + 1, le_rfl, (le_of_not_ge h), hN⟩

theorem grid_domination {κ : Type*} [Fintype κ] (mass θ t : κ → ℝ)
    (hmass : ∀ k, 0 ≤ mass k) (hθ : ∀ k, 0 ≤ θ k)
    (g : ℕ → ℝ) (N : ℕ) (hg0 : g 0 = 0) (hgN : g (N + 1) = 1)
    (hgstep : ∀ j ≤ N, g j < g (j + 1))
    (hgap : ∀ j ≤ N, ∀ k, t k ≤ g j ∨ g (j + 1) ≤ t k)
    (hcheck : ∀ j ≤ N + 1, 1 - g j ≤ combination mass θ t (g j)) :
    ∀ r, 0 ≤ r → max (1 - r) 0 ≤ combination mass θ t r := by
  intro r hr
  by_cases hr1 : r ≤ 1
  · obtain ⟨j, hj, hl, hh⟩ := exists_grid_interval g N
      (by simpa only [hg0] using hr) (by simpa only [hgN] using hr1)
    rw [max_eq_left (sub_nonneg.mpr hr1)]
    exact domination_between mass θ t hmass (hgstep j hj) hl hh (hgap j hj)
      (hcheck j (by omega)) (hcheck (j + 1) (by omega))
  · rw [max_eq_right (by linarith)]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hmass k)
      (arrivalCost_nonneg (hθ k) (le_max_right _ _))

/-- Soundness of a positive finite arrival certificate. -/
theorem value_le_certificate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Data ι) (mass θ t price : κ → ℝ) (hmass : ∀ k, 0 ≤ mass k)
    (hdom : ∀ r, 0 ≤ r → max (1 - r) 0 ≤ combination mass θ t r)
    (hcost : ∀ k, cost D (θ k) (t k) ≤ price k) :
    value D 1 ≤ ∑ k, mass k * price k := by
  calc
    value D 1 ≤ ∑ i, D.weight i * combination mass θ t (D.time i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hdom _ (D.time_nonneg i)) (D.weight_nonneg i)
    _ = ∑ k, mass k * cost D (θ k) (t k) := by
      simp only [combination, cost, kernel, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hcost k) (hmass k)

/-- A polynomial lower enclosure of exp gives an upper enclosure of exp(-x). -/
lemma exp_neg_le_of_taylor {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) (N : ℕ)
    (hpoly : 1 ≤ b * ∑ k ∈ Finset.range N, x ^ k / (k.factorial : ℝ)) :
    Real.exp (-x) ≤ b := by
  have h := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx N) hb.le
  rw [Real.exp_neg, ← one_div]
  apply (div_le_iff₀ (Real.exp_pos x)).2
  linarith

end ProbabilisticSerial.FiniteArrivalCertificate
