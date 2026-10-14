import PSTheorem1
import AsymptoticClosure

/-!
# Theorem 1 on the explicit uniform preference-profile space

Unlike the measure-theoretic assembly in `PSTheorem1`, this file uses the
finite sample `preferenceProfileSample n` directly.  Every deterministic and
analytic input is discharged by the concrete PS construction.  The only
named premise of the final theorem is the remaining law-transfer statement
from the labelled stopped-choice tree to the concrete phase-load event.
-/

noncomputable section

open Finset Filter
open scoped BigOperators Topology
open Asymptotics

namespace ProbabilisticSerial.ConcreteTheoremOne

open UniformProduct UniformPermutation PSProcess PhaseAdapter LoadBound
open AsymptoticClosure

/-- A convenient concrete choice in the simultaneous active-rank Chernoff
bound, leaving exponential rate one. -/
def rankConstant : ℝ :=
  2 * (Real.log 2 + 1 + Real.log (1 + Real.exp 1))

lemma rankConstant_pos : 0 < rankConstant := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogSum : 0 < Real.log (1 + Real.exp 1) := by
    apply Real.log_pos
    linarith [Real.exp_pos (1 : ℝ)]
  unfold rankConstant
  positivity

lemma rankConstant_chernoff_condition :
    Real.log 2 + 1 ≤
      (1 / 2 : ℝ) * rankConstant - Real.log (1 + Real.exp 1) := by
  unfold rankConstant
  ring_nf
  exact le_rfl

/-- The exponent contributed by the load proposition's first union bound. -/
def loadRate : ℝ := rateFunction etaZero - Real.log 2

lemma loadRate_pos : 0 < loadRate := by
  exact sub_pos.mpr rateFunction_etaZero_gt_log_two

/-- The rank multiplier obtained by composing the concrete rank reduction
with the concrete phase-integral estimate. -/
def rankThresholdConstant : ℝ := rankConstant * concretePhaseConstant

lemma rankThresholdConstant_pos : 0 < rankThresholdConstant :=
  mul_pos rankConstant_pos concretePhaseConstant_pos

/-- The exact finite-sample expectation of PS average rank. -/
def expectedPS (n : ℕ) : ℝ :=
  𝔼 profile ∈ preferenceProfileSample n, averageRank (run profile)

/-- The explicit error furnished by the two independent proof components:
one exponential active-rank error, one exponential potential error, and the
inverse-cubic underload error. -/
def failureError (n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ)) + Real.exp (-loadRate * (n : ℝ)) +
    1 / (n : ℝ) ^ 3

lemma failureError_nonneg (n : ℕ) : 0 ≤ failureError n := by
  unfold failureError
  positivity

/-- Union bound for two events on one explicit finite uniform sample. -/
lemma probability_or_le {α : Type*} (sample : Finset α)
    (event₁ event₂ : α → Prop) [DecidablePred event₁]
    [DecidablePred event₂] :
    probability sample (fun x => event₁ x ∨ event₂ x) ≤
      probability sample event₁ + probability sample event₂ := by
  calc
    probability sample (fun x => event₁ x ∨ event₂ x) ≤
        𝔼 x ∈ sample, (
          (if event₁ x then (1 : ℝ) else 0) +
            (if event₂ x then 1 else 0)) := by
      apply expect_mono
      intro x hx
      by_cases h₁ : event₁ x <;> by_cases h₂ : event₂ x <;>
        simp [probability, h₁, h₂]
    _ = probability sample event₁ + probability sample event₂ := by
      rw [Finset.expect_add_distrib]
      rfl

lemma averageRank_nonneg {n : ℕ} (profile : Profile n) :
    0 ≤ averageRank (run profile) := by
  unfold averageRank
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro g hg
  exact mul_nonneg (Nat.cast_nonneg _) (run_allocation_nonneg profile i g)

/-- On the intersection of the two concrete good events, all paper-specific
deterministic inequalities have been discharged. -/
theorem rank_le_on_concrete_good {n : ℕ} (profile : Profile n) (hn : 0 < n)
    (hrank : UniformRankGood profile rankConstant)
    (hload : ConcretePhaseLoadGood profile phaseLambdaZero) :
    averageRank (run profile) ≤
      rankThresholdConstant * (1 + psLogStar n) := by
  have hreduce := run_rankReduction profile hn hrank
  have hphase := concrete_eatingIntegral_le_logStar profile hn hload
  have hmul := mul_le_mul_of_nonneg_left hphase rankConstant_pos.le
  exact hreduce.trans (by
    simpa [rankThresholdConstant, mul_assoc] using hmul)

/-- The Step 3 active-rank event already has its complete concrete profile
probability bound. -/
theorem concrete_uniformRank_failure {n : ℕ} (hn : 0 < n) :
    probability (preferenceProfileSample n)
      (fun profile => ¬UniformRankGood profile rankConstant) ≤
        Real.exp (-(n : ℝ)) := by
  simpa using uniformRankGood_failure_probability_le hn
    rankConstant_chernoff_condition

/-- Exact finite-profile tail bound, conditional only on the final labelled
tree-to-profile load transfer. -/
theorem concrete_tail_of_load_transfer
    (loadTransfer : ∀ n : ℕ, 0 < n → 1 ≤ Real.log (n : ℝ) →
      probability (preferenceProfileSample n)
          (fun profile =>
            ¬ConcretePhaseLoadGood profile phaseLambdaZero) ≤
        Real.exp (-loadRate * (n : ℝ)) + 1 / (n : ℝ) ^ 3)
    {n : ℕ} (hn : 0 < n) (hlog : 1 ≤ Real.log (n : ℝ)) :
    probability (preferenceProfileSample n)
        (fun profile =>
          rankThresholdConstant * (1 + psLogStar n) <
            averageRank (run profile)) ≤ failureError n := by
  let rankBad : Profile n → Prop :=
    fun profile => ¬UniformRankGood profile rankConstant
  let loadBad : Profile n → Prop :=
    fun profile => ¬ConcretePhaseLoadGood profile phaseLambdaZero
  have hsubset : ∀ profile ∈ preferenceProfileSample n,
      rankThresholdConstant * (1 + psLogStar n) <
          averageRank (run profile) → rankBad profile ∨ loadBad profile := by
    intro profile hprofile htail
    by_contra hnot
    push_neg at hnot
    have hrank : UniformRankGood profile rankConstant := by
      simpa [rankBad] using hnot.1
    have hload : ConcretePhaseLoadGood profile phaseLambdaZero := by
      simpa [loadBad] using hnot.2
    exact (not_lt_of_ge
      (rank_le_on_concrete_good profile hn hrank hload)) htail
  calc
    probability (preferenceProfileSample n)
        (fun profile =>
          rankThresholdConstant * (1 + psLogStar n) <
            averageRank (run profile)) ≤
        probability (preferenceProfileSample n)
          (fun profile => rankBad profile ∨ loadBad profile) :=
      probability_mono _ hsubset
    _ ≤ probability (preferenceProfileSample n) rankBad +
          probability (preferenceProfileSample n) loadBad :=
      probability_or_le _ _ _
    _ ≤ Real.exp (-(n : ℝ)) +
          (Real.exp (-loadRate * (n : ℝ)) + 1 / (n : ℝ) ^ 3) :=
      add_le_add (concrete_uniformRank_failure hn) (loadTransfer n hn hlog)
    _ = failureError n := by rw [failureError]; ring

lemma failureError_cost_tendsto_zero :
    Tendsto (fun n : ℕ => (n : ℝ) * failureError n) atTop (𝓝 0) := by
  have hRank := tailError_cost_tendsto_zero 1 1 (by norm_num)
  have hLoad : Tendsto
      (fun n : ℕ => (n : ℝ) * Real.exp (-loadRate * (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (1 : ℝ) loadRate loadRate_pos).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsum := hRank.add hLoad
  simpa only [zero_add] using hsum.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp only [failureError, tailError, polynomialTail]
    field_simp [hn0]
    <;> ring)

/-- Finite-sample expectation split using the deterministic bound
`averageRank ≤ n` on the bad event. -/
theorem expectation_le_of_load_transfer
    (loadTransfer : ∀ n : ℕ, 0 < n → 1 ≤ Real.log (n : ℝ) →
      probability (preferenceProfileSample n)
          (fun profile =>
            ¬ConcretePhaseLoadGood profile phaseLambdaZero) ≤
        Real.exp (-loadRate * (n : ℝ)) + 1 / (n : ℝ) ^ 3)
    {n : ℕ} (hn : 0 < n) (hlog : 1 ≤ Real.log (n : ℝ)) :
    expectedPS n ≤ rankThresholdConstant * (1 + psLogStar n) +
      (n : ℝ) * failureError n := by
  let threshold := rankThresholdConstant * (1 + psLogStar n)
  let bad : Profile n → Prop := fun profile =>
    threshold < averageRank (run profile)
  have hpoint : ∀ profile ∈ preferenceProfileSample n,
      averageRank (run profile) ≤
        threshold + (n : ℝ) * (if bad profile then 1 else 0) := by
    intro profile hprofile
    by_cases hbad : bad profile
    · have hall := run_averageRank_le_marketSize profile hn
      simp only [if_pos hbad]
      have hthreshold : 0 ≤ threshold := by
        dsimp [threshold]
        exact mul_nonneg rankThresholdConstant_pos.le
          (by linarith [psLogStar_nonneg n])
      linarith
    · simp only [if_neg hbad]
      have hle := le_of_not_gt hbad
      simpa [bad] using hle
  have hprob : probability (preferenceProfileSample n) bad ≤
      failureError n := by
    simpa [bad, threshold] using
      concrete_tail_of_load_transfer loadTransfer hn hlog
  calc
    expectedPS n ≤ 𝔼 profile ∈ preferenceProfileSample n, (
        threshold + (n : ℝ) * (if bad profile then 1 else 0)) :=
      expect_mono _ hpoint
    _ = threshold + (n : ℝ) * probability
          (preferenceProfileSample n) bad := by
      rw [Finset.expect_add_distrib,
        Finset.expect_const (preferenceProfileSample_nonempty n),
        ← Finset.mul_expect]
      rfl
    _ ≤ threshold + (n : ℝ) * failureError n := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hprob (Nat.cast_nonneg n)) _
    _ = rankThresholdConstant * (1 + psLogStar n) +
          (n : ℝ) * failureError n := rfl

/-- The expected concrete PS rank is `O(1 + psLogStar n)`. -/
theorem expectedPS_isBigO_of_load_transfer
    (loadTransfer : ∀ n : ℕ, 0 < n → 1 ≤ Real.log (n : ℝ) →
      probability (preferenceProfileSample n)
          (fun profile =>
            ¬ConcretePhaseLoadGood profile phaseLambdaZero) ≤
        Real.exp (-loadRate * (n : ℝ)) + 1 / (n : ℝ) ^ 3) :
    expectedPS =O[atTop] (fun n : ℕ => 1 + psLogStar n) := by
  have hcost : ∀ᶠ n : ℕ in atTop, (n : ℝ) * failureError n < 1 :=
    failureError_cost_tendsto_zero.eventually (Iio_mem_nhds zero_lt_one)
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    tendsto_log_nat_atTop.eventually_ge_atTop 1
  apply IsBigO.of_bound (rankThresholdConstant + 1)
  filter_upwards [hcost, hlog, eventually_ge_atTop (1 : ℕ)] with n hcost hlog hn
  have hnpos : 0 < n := by omega
  have hexpectNonneg : 0 ≤ expectedPS n := by
    unfold expectedPS
    have hmono := expect_mono (preferenceProfileSample n)
      (f := fun _ => (0 : ℝ))
      (g := fun profile => averageRank (run profile))
      (by intro profile hp; exact averageRank_nonneg profile)
    simpa using hmono
  have hscaleNonneg : 0 ≤ 1 + psLogStar n := by
    linarith [psLogStar_nonneg n]
  rw [Real.norm_eq_abs, abs_of_nonneg hexpectNonneg,
    Real.norm_eq_abs, abs_of_nonneg hscaleNonneg]
  calc
    expectedPS n ≤ rankThresholdConstant * (1 + psLogStar n) +
        (n : ℝ) * failureError n :=
      expectation_le_of_load_transfer loadTransfer hnpos hlog
    _ ≤ rankThresholdConstant * (1 + psLogStar n) + 1 := by linarith
    _ ≤ (rankThresholdConstant + 1) * (1 + psLogStar n) := by
      nlinarith [psLogStar_nonneg n]

/-- The concrete expected-rank ratio tends to zero. -/
theorem expectedPS_div_RP_tendsto_zero_of_load_transfer
    (loadTransfer : ∀ n : ℕ, 0 < n → 1 ≤ Real.log (n : ℝ) →
      probability (preferenceProfileSample n)
          (fun profile =>
            ¬ConcretePhaseLoadGood profile phaseLambdaZero) ≤
        Real.exp (-loadRate * (n : ℝ)) + 1 / (n : ℝ) ^ 3) :
    Tendsto (fun n : ℕ => expectedPS n / rpExpectation n) atTop (𝓝 0) := by
  have hPSLog : expectedPS =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) :=
    (expectedPS_isBigO_of_load_transfer loadTransfer).trans_isLittleO
      psLogStar_small_relative_to_log
  have hPSRP : expectedPS =o[atTop] rpExpectation :=
    hPSLog.trans_isEquivalent rpExpectation_isEquivalent_log.symm
  exact hPSRP.tendsto_div_nhds_zero

/-- All three conclusions of Theorem 1 on the genuine finite profile sample,
with the exact remaining load-transfer proposition made explicit. -/
theorem concrete_theorem_one_of_load_transfer
    (loadTransfer : ∀ n : ℕ, 0 < n → 1 ≤ Real.log (n : ℝ) →
      probability (preferenceProfileSample n)
          (fun profile =>
            ¬ConcretePhaseLoadGood profile phaseLambdaZero) ≤
        Real.exp (-loadRate * (n : ℝ)) + 1 / (n : ℝ) ^ 3) :
    (∀ n : ℕ, 0 < n → 1 ≤ Real.log (n : ℝ) →
      probability (preferenceProfileSample n)
          (fun profile =>
            rankThresholdConstant * (1 + psLogStar n) <
              averageRank (run profile)) ≤ failureError n) ∧
    expectedPS =O[atTop] (fun n : ℕ => 1 + psLogStar n) ∧
    Tendsto (fun n : ℕ => expectedPS n / rpExpectation n) atTop (𝓝 0) := by
  exact ⟨fun n hn hlog =>
      concrete_tail_of_load_transfer loadTransfer hn hlog,
    expectedPS_isBigO_of_load_transfer loadTransfer,
    expectedPS_div_RP_tendsto_zero_of_load_transfer loadTransfer⟩

end ProbabilisticSerial.ConcreteTheoremOne
