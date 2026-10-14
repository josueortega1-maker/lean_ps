import ConcreteTheoremOneFinal
import StandardLogStar
import RandomPriority
import PSExpectedRank

/-!
# Theorem 1 in the manuscript's own notation

The earlier development naturally produces an inverse-exponential phase
counter and then compares PS with Knuth's closed formula.  This final wrapper
closes both presentational gaps:

* `StandardLogStar.logStar` is literally the least number of natural-log
  iterations required to reach a value at most one;
* `RandomPriority.rpExpectedRank` is the expectation of an explicit random
  priority / serial-dictatorship process.

Thus `paper_theorem_one` states the September 3 conclusions directly with
the paper's `log*` and actual RP mechanism. The finite theorems below add the
sharpened expectation and below-five bounds for the same one-copy PS model.
The later replica theorem, including its quota threshold for RP, has a
separate interface in `PaperReplicaInterface`.
-/

noncomputable section

open Finset Filter
open scoped BigOperators Topology
open Asymptotics

namespace ProbabilisticSerial.PaperTheoremOne

open UniformProduct UniformPermutation PSProcess
open PhaseAdapter LoadBound
open ConcreteTheoremOne StandardLogStar RandomPriority

/-- The sharpened finite expectation estimate for actual uniform one-copy PS.
The constant is the exact rational 17/5, and no arrival or rank-bridge
hypothesis is left in this statement. -/
theorem expectedPS_lt_logStar_add_three_point_four (n : ℕ) (hn : 0 < n) :
    ConcreteTheoremOne.expectedPS n < (logStar n : ℝ) + 17 / 5 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  by_cases hlarge : 3 ≤ n
  · exact PSChoiceMachine.expectedPS_le_expected_exposure.trans_lt
      (PSChoiceMachine.expected_profileExposure_lt_logStar_add hlarge)
  · have h := expectedPS_le_marketSize n hn
    have hnR : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
    have hk : (0 : ℝ) ≤ logStar n := Nat.cast_nonneg _
    linarith

theorem expectedPS_le_logStar_add_three_point_four (n : ℕ) (hn : 0 < n) :
    ConcreteTheoremOne.expectedPS n ≤ (logStar n : ℝ) + 17 / 5 :=
  (expectedPS_lt_logStar_add_three_point_four n hn).le

/-- The exact 21-test certificate gives an unconditional bound below five
for every positive one-copy market up to 10^80 agents and goods. -/
theorem expectedPS_lt_five (n : ℕ) (hn : 0 < n) (hmax : n ≤ 10 ^ 80) :
    ConcreteTheoremOne.expectedPS n < 5 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmaxR : (n : ℝ) ≤ (10 : ℝ) ^ 80 := by exact_mod_cast hmax
  have hlog : Real.log (n : ℝ) ≤ 80 * Real.log 10 := by
    have h := Real.log_le_log hnR hmaxR
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hcost : ∀ t, 0 < t → t < 1 → ∀ θ, 0 < θ →
      FiniteAtomicExposure.cost (PSChoiceMachine.actualExposure (n := n)) θ t ≤
        FiniteExposure.phi θ (1 - t) := by
    intro t ht ht1 θ hθ
    rw [PSChoiceMachine.actualExposure_cost]
    exact PSChoiceMachine.expected_profileExposureCost_le t θ ht ht1 hθ
  have hend : FiniteAtomicExposure.cost (PSChoiceMachine.actualExposure (n := n)) 1600 1 ≤
      1600 + 80 * Real.log 10 := by
    rw [PSChoiceMachine.actualExposure_cost]
    exact (PSChoiceMachine.expected_profileExposureCost_endpoint_le 1600 (by norm_num)).trans
      (add_le_add_left hlog _)
  have h := FiniteFiveCertificate.value_lt_five PSChoiceMachine.actualExposure hcost hend
  rw [PSChoiceMachine.actualExposure_value] at h
  exact PSChoiceMachine.expectedPS_le_expected_exposure.trans_lt h

/-- The harmless factor two absorbs the one-step comparison between the
phase counter and the manuscript's literal `log*`. -/
def paperRankConstant : ℝ := 2 * rankThresholdConstant

lemma paperRankConstant_pos : 0 < paperRankConstant := by
  exact mul_pos (by norm_num) rankThresholdConstant_pos

/-- A single constant for both the rank threshold and the inverse-cubic term
in the manuscript's displayed tail bound. -/
def paperConstant : ℝ := max paperRankConstant 1

/-- A single exponential rate absorbing both exponential errors in the
finite bound.  Halving the smaller rate absorbs their factor two eventually. -/
def paperRate : ℝ := min 1 loadRate / 2

lemma paperConstant_pos : 0 < paperConstant := by
  exact zero_lt_one.trans_le (le_max_right _ _)

lemma paperRate_pos : 0 < paperRate := by
  exact div_pos (lt_min zero_lt_one loadRate_pos) (by norm_num)

theorem paper_tail_bound (n : ℕ) (hn : 0 < n)
    (hlog : 1 ≤ Real.log (n : ℝ)) :
    probability (preferenceProfileSample n)
        (fun profile =>
          paperRankConstant * (1 + (logStar n : ℝ)) <
            averageRank (run profile)) ≤ failureError n := by
  have hphase := one_add_psLogStar_le_two_mul_one_add_logStar n
  have hthreshold :
      rankThresholdConstant * (1 + psLogStar n) ≤
        paperRankConstant * (1 + (logStar n : ℝ)) := by
    rw [paperRankConstant]
    nlinarith [rankThresholdConstant_pos]
  exact (probability_mono (preferenceProfileSample n)
    (fun profile hprofile hbad => hthreshold.trans_lt hbad)).trans
      (concrete_theorem_one.1 n hn hlog)

/-- Pointwise expectation estimate with literal `log*`. Keeping the additive
one-step comparison avoids the factor-two relaxation used for the tail. -/
theorem expectedPS_le_paperLogStar (n : ℕ) (hn : 0 < n)
    (hlog : 1 ≤ Real.log (n : ℝ)) :
    ConcreteTheoremOne.expectedPS n ≤
      rankThresholdConstant * (2 + (logStar n : ℝ)) +
        (n : ℝ) * failureError n := by
  have hscale : 1 + psLogStar n ≤ 2 + (logStar n : ℝ) := by
    linarith [psLogStar_le_logStar_add_one n]
  exact (expectedPS_le_phase_bound n hn hlog).trans
    (add_le_add_right
      (mul_le_mul_of_nonneg_left hscale rankThresholdConstant_pos.le) _)

/-- Combine the existing concentration estimate with the deterministic
market-size bound. No numerical constant is substituted for the original
phase and rank multipliers. -/
theorem expectedPS_le_finite_min (n : ℕ) (hn : 0 < n)
    (hlog : 1 ≤ Real.log (n : ℝ)) :
    ConcreteTheoremOne.expectedPS n ≤
      min (n : ℝ)
        (rankThresholdConstant * (2 + (logStar n : ℝ)) +
          (n : ℝ) * failureError n) := by
  exact le_min (expectedPS_le_marketSize n hn)
    (expectedPS_le_paperLogStar n hn hlog)

lemma phaseScale_isBigO_paperLogStar :
    (fun n : ℕ => 1 + psLogStar n) =O[atTop]
      (fun n : ℕ => 1 + (logStar n : ℝ)) := by
  apply IsBigO.of_bound 2
  filter_upwards with n
  have hleft : 0 ≤ 1 + psLogStar n := by
    linarith [psLogStar_nonneg n]
  have hright : 0 ≤ 1 + (logStar n : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleft,
    Real.norm_eq_abs, abs_of_nonneg hright]
  exact one_add_psLogStar_le_two_mul_one_add_logStar n

theorem expectedPS_isBigO_paperLogStar :
    ConcreteTheoremOne.expectedPS =O[atTop]
      (fun n : ℕ => 1 + (logStar n : ℝ)) :=
  concrete_theorem_one.2.1.trans phaseScale_isBigO_paperLogStar

theorem expectedPS_div_actual_RP_tendsto_zero :
    Tendsto (fun n : ℕ =>
      ConcreteTheoremOne.expectedPS n / rpExpectedRank n)
      atTop (𝓝 0) := by
  simpa only [rpExpectedRank_eq_knuth_formula] using
    concrete_theorem_one.2.2

/-- The fully explicit finite error is eventually bounded by the exact error
shape displayed in the manuscript. -/
theorem failureError_le_paper_tail_eventually :
    ∀ᶠ n : ℕ in atTop,
      failureError n ≤ tailError paperConstant paperRate n := by
  let r : ℝ := min 1 loadRate
  have hrPos : 0 < r := by
    dsimp [r]
    exact lt_min zero_lt_one loadRate_pos
  have hlarge : ∀ᶠ n : ℕ in atTop,
      Real.log 2 ≤ paperRate * (n : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop paperRate_pos).eventually_ge_atTop _
  filter_upwards [hlarge] with n hnLarge
  have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrOne : r ≤ 1 := min_le_left _ _
  have hrLoad : r ≤ loadRate := min_le_right _ _
  have hRankExp :
      Real.exp (-(n : ℝ)) ≤ Real.exp (-r * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hLoadExp :
      Real.exp (-loadRate * (n : ℝ)) ≤ Real.exp (-r * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hAbsorb :
      Real.exp (-r * (n : ℝ)) + Real.exp (-r * (n : ℝ)) ≤
        Real.exp (-paperRate * (n : ℝ)) := by
    calc
      Real.exp (-r * (n : ℝ)) + Real.exp (-r * (n : ℝ)) =
          (2 : ℝ) * Real.exp (-r * (n : ℝ)) := by ring
      _ = Real.exp (Real.log 2 + (-r * (n : ℝ))) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp (-paperRate * (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        dsimp [paperRate, r] at hnLarge ⊢
        nlinarith
  have hPoly : 1 / (n : ℝ) ^ 3 ≤ paperConstant / (n : ℝ) ^ 3 := by
    exact div_le_div_of_nonneg_right (le_max_right paperRankConstant 1)
      (pow_nonneg hnNonneg 3)
  calc
    failureError n = Real.exp (-(n : ℝ)) +
        Real.exp (-loadRate * (n : ℝ)) + 1 / (n : ℝ) ^ 3 := rfl
    _ ≤ Real.exp (-r * (n : ℝ)) +
        Real.exp (-r * (n : ℝ)) + paperConstant / (n : ℝ) ^ 3 :=
      add_le_add (add_le_add hRankExp hLoadExp) hPoly
    _ ≤ Real.exp (-paperRate * (n : ℝ)) +
        paperConstant / (n : ℝ) ^ 3 := add_le_add_right hAbsorb _
    _ = tailError paperConstant paperRate n := by
      simp only [tailError, polynomialTail]
      ring

theorem paper_tail_displayed_form :
    ∀ᶠ n : ℕ in atTop,
      probability (preferenceProfileSample n)
          (fun profile =>
            paperConstant * (1 + (logStar n : ℝ)) <
              averageRank (run profile)) ≤
        tailError paperConstant paperRate n := by
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    AsymptoticClosure.tendsto_log_nat_atTop.eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog,
    failureError_le_paper_tail_eventually] with n hn hlogn herror
  have hnPos : 0 < n := by omega
  have hscale : 0 ≤ 1 + (logStar n : ℝ) := by positivity
  have hthreshold :
      paperRankConstant * (1 + (logStar n : ℝ)) ≤
        paperConstant * (1 + (logStar n : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hscale
  calc
    probability (preferenceProfileSample n)
        (fun profile =>
          paperConstant * (1 + (logStar n : ℝ)) <
            averageRank (run profile)) ≤
        probability (preferenceProfileSample n)
          (fun profile =>
            paperRankConstant * (1 + (logStar n : ℝ)) <
              averageRank (run profile)) := by
      apply probability_mono
      intro profile hprofile hbad
      exact hthreshold.trans_lt hbad
    _ ≤ failureError n := paper_tail_bound n hnPos hlogn
    _ ≤ tailError paperConstant paperRate n := herror

/-- The displayed tail shape holds for every positive one-copy market size
after increasing the absolute threshold constant to cover the finite initial
segment. This removes the eventual-size restriction, but does not generalize
the preference law to replica markets. -/
theorem paper_tail_all_positive :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 0 < n →
      probability (preferenceProfileSample n)
        (fun profile => C * (1 + (logStar n : ℝ)) < averageRank (run profile)) ≤
          tailError C c n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 paper_tail_displayed_form
  let C : ℝ := max paperConstant (N : ℝ)
  have hC : paperConstant ≤ C := le_max_left _ _
  have hNC : (N : ℝ) ≤ C := le_max_right _ _
  have hCpos : 0 < C := paperConstant_pos.trans_le hC
  refine ⟨C, paperRate, hCpos, paperRate_pos, ?_⟩
  intro n hn
  have hscale : 0 ≤ 1 + (logStar n : ℝ) := by positivity
  by_cases hlarge : N ≤ n
  · calc
      probability (preferenceProfileSample n)
          (fun profile => C * (1 + (logStar n : ℝ)) < averageRank (run profile)) ≤
        probability (preferenceProfileSample n)
          (fun profile => paperConstant * (1 + (logStar n : ℝ)) <
            averageRank (run profile)) := by
          apply probability_mono
          intro profile hprofile hbad
          exact (mul_le_mul_of_nonneg_right hC hscale).trans_lt hbad
      _ ≤ tailError paperConstant paperRate n := hN n hlarge
      _ ≤ tailError C paperRate n := by
          apply add_le_add_right
          exact div_le_div_of_nonneg_right hC (by positivity)
  · have hnN : (n : ℝ) ≤ N := by exact_mod_cast (le_of_not_ge hlarge)
    have hthreshold : (n : ℝ) ≤ C * (1 + (logStar n : ℝ)) := by
      have hnonneg : 0 ≤ (logStar n : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hprob : probability (preferenceProfileSample n)
        (fun profile => C * (1 + (logStar n : ℝ)) < averageRank (run profile)) = 0 := by
      unfold probability
      have hempty (profile : PSProcess.Profile n) :
          ¬ C * (1 + (logStar n : ℝ)) < averageRank (run profile) :=
        not_lt_of_ge ((run_averageRank_le_marketSize profile hn).trans hthreshold)
      simp [hempty]
    rw [hprob]
    exact tailError_nonneg hCpos.le n

/-- The September 3 manuscript's three probabilistic conclusions on explicit
finite sample spaces.  There are no premises naming unproved paper lemmas. -/
theorem paper_theorem_one :
    (∀ n : ℕ, 0 < n → 1 ≤ Real.log (n : ℝ) →
      probability (preferenceProfileSample n)
          (fun profile =>
            paperRankConstant * (1 + (logStar n : ℝ)) <
              averageRank (run profile)) ≤ failureError n) ∧
    ConcreteTheoremOne.expectedPS =O[atTop]
      (fun n : ℕ => 1 + (logStar n : ℝ)) ∧
    Tendsto (fun n : ℕ =>
      ConcreteTheoremOne.expectedPS n / rpExpectedRank n)
      atTop (𝓝 0) := by
  exact ⟨paper_tail_bound, expectedPS_isBigO_paperLogStar,
    expectedPS_div_actual_RP_tendsto_zero⟩

/-- The September 3 theorem in its displayed asymptotic form, with explicit
positive absolute constants and the standard “for all sufficiently large n”
interpretation.  Expanding `tailError` gives
`paperConstant / n^3 + exp (-paperRate*n)`. -/
theorem paper_theorem_one_as_stated :
    0 < paperConstant ∧ 0 < paperRate ∧
    (∀ᶠ n : ℕ in atTop,
      probability (preferenceProfileSample n)
          (fun profile =>
            paperConstant * (1 + (logStar n : ℝ)) <
              averageRank (run profile)) ≤
        tailError paperConstant paperRate n) ∧
    ConcreteTheoremOne.expectedPS =O[atTop]
      (fun n : ℕ => 1 + (logStar n : ℝ)) ∧
    Tendsto (fun n : ℕ =>
      ConcreteTheoremOne.expectedPS n / rpExpectedRank n)
      atTop (𝓝 0) := by
  exact ⟨paperConstant_pos, paperRate_pos, paper_tail_displayed_form,
    expectedPS_isBigO_paperLogStar,
    expectedPS_div_actual_RP_tendsto_zero⟩

end ProbabilisticSerial.PaperTheoremOne
