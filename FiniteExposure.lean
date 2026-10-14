import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic

/-!
# Finite exposure: exact maximization and the quota reduction

This file proves the closed form of the function Φ in equations `finite-h`
and `finite-h-bound`, including attainment of its maximum and monotonicity
after division by its first argument. All logarithms and constants are real;
no floating-point evaluation is used.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.FiniteExposure

def objective (lam u a : ℝ) : ℝ := -Real.log a + lam * (1 - u / a)

def phi (lam u : ℝ) : ℝ :=
  if lam ≤ 1 then -Real.log u
  else if lam ≤ 1 / u then -Real.log u + lam - 1 - Real.log lam
  else lam * (1 - u)

lemma objective_le_small {lam u a : ℝ}
    (hlam : lam ≤ 1) (hu : 0 < u) (hua : u ≤ a) :
    objective lam u a ≤ -Real.log u := by
  have ha : 0 < a := hu.trans_le hua
  have hratio : u / a ≤ 1 := (div_le_one ha).2 hua
  have hlog := Real.log_le_sub_one_of_pos (div_pos hu ha)
  rw [Real.log_div hu.ne' ha.ne'] at hlog
  dsimp [objective]
  nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (sub_nonneg.mpr hratio)]

lemma objective_le_middle {lam u a : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (ha : 0 < a) :
    objective lam u a ≤ -Real.log u + lam - 1 - Real.log lam := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos hlam hu) ha)
  rw [Real.log_div (mul_pos hlam hu).ne' ha.ne',
    Real.log_mul hlam.ne' hu.ne'] at hlog
  dsimp [objective]
  rw [mul_div_assoc] at hlog
  nlinarith

lemma objective_le_large {lam u a : ℝ}
    (hu : 0 < u) (ha : 0 < a) (ha1 : a ≤ 1) (hlam : 1 / u ≤ lam) :
    objective lam u a ≤ lam * (1 - u) := by
  have hlu : 1 ≤ lam * u := (div_le_iff₀ hu).mp hlam
  have hai : 1 ≤ 1 / a := (le_div_iff₀ ha).2 (by simpa using ha1)
  have hlog := Real.log_le_sub_one_of_pos (one_div_pos.mpr ha)
  rw [Real.log_div one_ne_zero ha.ne', Real.log_one, zero_sub] at hlog
  have hprod := mul_nonneg (sub_nonneg.mpr hlu) (sub_nonneg.mpr hai)
  have heq : (lam * u) * (1 / a) = lam * (u / a) := by ring
  dsimp [objective]
  nlinarith

theorem objective_le_phi {lam u a : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (hua : u ≤ a) (ha1 : a ≤ 1) :
    objective lam u a ≤ phi lam u := by
  unfold phi
  split_ifs with hsmall hmiddle
  · exact objective_le_small hsmall hu hua
  · exact objective_le_middle hlam hu (hu.trans_le hua)
  · exact objective_le_large hu (hu.trans_le hua) ha1 (le_of_not_ge hmiddle)

/-- The displayed piecewise expression really is a maximum, rather than just
an upper bound. Its maximizing argument is respectively `u`, `lam*u`, or `1`. -/
theorem phi_attained {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) (hu1 : u ≤ 1) :
    ∃ a : ℝ, u ≤ a ∧ a ≤ 1 ∧ objective lam u a = phi lam u := by
  by_cases hsmall : lam ≤ 1
  · refine ⟨u, le_rfl, hu1, ?_⟩
    simp [phi, hsmall, objective, hu.ne']
  · by_cases hmiddle : lam ≤ 1 / u
    · refine ⟨lam * u, ?_, ?_, ?_⟩
      · nlinarith [le_of_not_ge hsmall]
      · exact (le_div_iff₀ hu).mp hmiddle
      · have hdiv : u / (lam * u) = 1 / lam := by field_simp <;> ring
        simp only [phi, if_neg hsmall, if_pos hmiddle, objective,
          Real.log_mul hlam.ne' hu.ne', hdiv]
        field_simp
        <;> ring
    · refine ⟨1, hu1, le_rfl, ?_⟩
      simp only [phi, if_neg hsmall, if_neg hmiddle, objective,
        Real.log_one, div_one, neg_zero, zero_add]

lemma normalized_objective {lam u a : ℝ} (hlam : lam ≠ 0) :
    objective lam u a / lam = -Real.log a / lam + (1 - u / a) := by
  simp [objective, add_div, hlam]

/-- The quota-uniform reduction immediately after equation `finite-volterra`. -/
theorem phi_div_antitone {lam μ u : ℝ}
    (hlam : 0 < lam) (hlamμ : lam ≤ μ) (hu : 0 < u) (hu1 : u ≤ 1) :
    phi μ u / μ ≤ phi lam u / lam := by
  have hμ : 0 < μ := hlam.trans_le hlamμ
  obtain ⟨a, hua, ha1, ha⟩ := phi_attained hμ hu hu1
  have ha0 : 0 < a := hu.trans_le hua
  have hlog : 0 ≤ -Real.log a := neg_nonneg.mpr (Real.log_nonpos ha0.le ha1)
  rw [← ha]
  calc
    objective μ u a / μ = -Real.log a / μ + (1 - u / a) :=
      normalized_objective hμ.ne'
    _ ≤ -Real.log a / lam + (1 - u / a) :=
      add_le_add_right (div_le_div_of_nonneg_left hlog hlam hlamμ) _
    _ = objective lam u a / lam := (normalized_objective hlam.ne').symm
    _ ≤ phi lam u / lam :=
      div_le_div_of_nonneg_right (objective_le_phi hlam hu hua ha1) hlam.le

theorem phi_quota_reduction {q θ u : ℝ}
    (hq : 1 ≤ q) (hθ : 0 < θ) (hu : 0 < u) (hu1 : u ≤ 1) :
    phi (q * θ) u / (q * θ) ≤ phi θ u / θ := by
  apply phi_div_antitone hθ _ hu hu1
  nlinarith

/-- A finite expectation of a positive random variable at most one controls
the expectation of its logarithm. This is enough for the random-survivor
argument and avoids conditioning on the surviving set. -/
theorem expect_log_le_zero {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty)
    (Y : Ω → ℝ) (hY : ∀ ω ∈ s, 0 < Y ω)
    (hmean : (𝔼 ω ∈ s, Y ω) ≤ 1) :
    (𝔼 ω ∈ s, Real.log (Y ω)) ≤ 0 := by
  calc
    (𝔼 ω ∈ s, Real.log (Y ω)) ≤ 𝔼 ω ∈ s, (Y ω - 1) := by
      apply Finset.expect_le_expect
      intro ω hω
      exact Real.log_le_sub_one_of_pos (hY ω hω)
    _ = (𝔼 ω ∈ s, Y ω) - 1 := by
      rw [Finset.expect_sub_distrib, Finset.expect_const hs]
    _ ≤ 0 := sub_nonpos.mpr hmean

/-- Abstract finite-expectation closure of the log-of-total-mass argument.
The hypotheses are explicit deterministic inequalities, so applying this to
PS still requires proving the capacity/compensator identities for its trace. -/
theorem expect_le_of_log_envelope {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty)
    (F Y : Ω → ℝ) (B : ℝ) (hY : ∀ ω ∈ s, 0 < Y ω)
    (hmean : (𝔼 ω ∈ s, Y ω) ≤ 1)
    (henv : ∀ ω ∈ s, F ω ≤ B + Real.log (Y ω)) :
    (𝔼 ω ∈ s, F ω) ≤ B := by
  calc
    (𝔼 ω ∈ s, F ω) ≤ 𝔼 ω ∈ s, (B + Real.log (Y ω)) :=
      Finset.expect_le_expect henv
    _ = B + (𝔼 ω ∈ s, Real.log (Y ω)) := by
      rw [Finset.expect_add_distrib, Finset.expect_const hs]
    _ ≤ B := by linarith [expect_log_le_zero s hs Y hY hmean]

end ProbabilisticSerial.FiniteExposure
