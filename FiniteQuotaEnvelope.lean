import FiniteAtomicExposure
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Quota-sensitive closure of the terminal exposure bound

A finite exposure trace whose terminal exponential cost is at most
`theta + a` has value at most `(theta + a)/(1-exp(-theta))`.
Choosing `theta = sqrt (2*a)` gives `1 + sqrt (2*a) + a` when `a > 0`.
The process-specific cost hypothesis remains explicit in this analytic module.
-/

noncomputable section

namespace ProbabilisticSerial.FiniteQuotaEnvelope

open FiniteAtomicExposure

variable {ι : Type*} [Fintype ι]

theorem value_one_le_exponential (D : Data ι) {a θ : ℝ} (hθ : 0 < θ)
    (hcost : cost D θ 1 ≤ θ + a) :
    value D 1 ≤ (θ + a) / (1 - Real.exp (-θ)) := by
  have h := increment_le D (s := 0) (t := 1) (by norm_num) hθ hcost
  simpa only [value_zero, sub_zero, one_mul, arrivalCost, mul_one] using h

/-- A quadratic exponential lower bound optimizes the elementary envelope
without introducing an implicitly defined root. -/
theorem exponential_envelope_le {a : ℝ} (ha : 0 < a) :
    (Real.sqrt (2 * a) + a) / (1 - Real.exp (-Real.sqrt (2 * a))) ≤
      1 + Real.sqrt (2 * a) + a := by
  let x := Real.sqrt (2 * a)
  have hx : 0 < x := Real.sqrt_pos.2 (by positivity)
  have hsq : x ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
  have hexp : 1 + x + a ≤ Real.exp x := by
    nlinarith [Real.quadratic_le_exp_of_nonneg hx.le]
  have hinv : Real.exp (-x) ≤ 1 / (1 + x + a) := by
    simpa only [Real.exp_neg, one_div] using
      (one_div_le_one_div_of_le (by positivity : 0 < 1 + x + a) hexp)
  have hproduct : Real.exp (-x) * (1 + x + a) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 1 + x + a)).mp hinv
  have hden : 0 < 1 - Real.exp (-x) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by linarith)
  change (x + a) / (1 - Real.exp (-x)) ≤ 1 + x + a
  apply (div_le_iff₀ hden).2
  nlinarith

/-- The endpoint cost law gives a concrete bound for a genuine finite trace. -/
theorem value_one_le_one_add_sqrt_add (D : Data ι) {a : ℝ} (ha : 0 < a)
    (hcost : ∀ θ, 0 < θ → cost D θ 1 ≤ θ + a) :
    value D 1 ≤ 1 + Real.sqrt (2 * a) + a := by
  have hθ : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
  exact (value_one_le_exponential D hθ (hcost _ hθ)).trans
    (exponential_envelope_le ha)

end ProbabilisticSerial.FiniteQuotaEnvelope
