import ReplicaRawCostRank
import LowerBoundEntropy

/-! An explicit finite-market PS rank lower bound, with every error retained. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.FiniteLowerBound
open UniformProduct CouponLowerBound UniformRawPrefixes ReplicaPS ReplicaRawProcess
  ReplicaLowerRank ReplicaRawCostRank ReplicaBandLower

variable {m q : ℕ} [Nonempty (Fin (m * q))]

def exceptionalBound (m q N lo hi : ℕ) (α θ a K : ℝ) : ℝ :=
  (N + 1 : ℕ) * ((2 : ℝ) ^ m) * Real.exp (-(3 - Real.log 4) * (m * q : ℕ)) +
    (N + 1 : ℕ) * ((smallSets m hi).card : ℝ) *
      Real.exp (-(α - 1 - Real.log α) * (m * q : ℕ)) +
    ((activeSizeBand m lo hi).card : ℝ) *
      Real.exp (-(m * q : ℕ) * (θ * (a - K) - θ ^ 2 * (16 * (1 + Real.exp 1))))

theorem expectedPS_ge_explicit_bands (hm : 2 ≤ m) (hq : 0 < q)
    (reference : ReplicaPS.Profile m q) (N J : ℕ) (cutoff survivors : ℕ → ℕ)
    (hmono : Monotone cutoff) (horizon : cutoff J ≤ N)
    {lo hi : ℕ} (hhi : 0 < hi) (hlm : lo ≤ m) (hlh : lo ≤ hi)
    {α K θ a : ℝ} (hα : 1 < α) (hK : 0 ≤ K) (hθ : 0 < θ)
    (ha : a ≤ 1 - 1 / (lo + 1 : ℝ))
    (hcutoff : N / (m : ℝ) ≤ α * (m * q : ℕ) / lo)
    (hmean : ∀ j < J, (4 : ℝ) * (m * q : ℕ) ≤
      cutoff (j + 1) * ((survivors j : ℝ) / m)) :
    K * (∑ j ∈ Finset.range J,
        bandLowerValue m q (cutoff j) (cutoff (j + 1)) (survivors j) 4) -
      K * (4 * (m * q : ℕ) / hi) -
      (K * (N / (m : ℝ))) * exceptionalBound m q N lo hi α θ a K ≤
      (α * q) * ReplicaPS.expectedPS m q := by
  have hmpos : 0 < m := by omega
  have hbands := expected_cost_ge_band_sum hm reference cutoff survivors hmono
    (by norm_num : (1 : ℝ) < 4) J hmean
  have hmonoCost := expected_rawCost_mono hmpos (initialState reference) horizon
  have hbandTotal := mul_le_mul_of_nonneg_left (hbands.trans hmonoCost) hK
  have hrank := expectedPS_lower_from_rawCost hmpos hq reference N hhi hlm hlh
    (by linarith : 0 ≤ α) hK hcutoff
  rw [labelSample_eq_univ] at hrank
  have herr := add_le_add (rawGood_failure_probability (q := q) hmpos N hi hα)
    (uniformLowerRankGood_failure_probability (q := q) (lo := lo) (hi := hi)
      (K := K) (θ := θ) (a := a) hmpos hθ ha)
  rw [labelSample_eq_univ] at herr
  have herrmul := mul_le_mul_of_nonneg_left herr
    (show 0 ≤ K * (N / (m : ℝ)) by positivity)
  unfold exceptionalBound
  linarith

end ProbabilisticSerial.FiniteLowerBound
