import ConcreteTheoremOne
import PSChoiceMachine

/-!
# Unconditional concrete Theorem 1

This module discharges the load-transfer premise of `ConcreteTheoremOne` by
the genuine profile-to-labelled-tree coupling in `PSChoiceMachine`.
-/

noncomputable section

open Finset Filter
open scoped BigOperators Topology
open Asymptotics

namespace ProbabilisticSerial.ConcreteTheoremOne

open UniformProduct UniformPermutation PSProcess PhaseAdapter LoadBound
open AsymptoticClosure

/-- The concrete simultaneous phase-load estimate, with no probabilistic
premise: it follows from sequential revelation and the labelled-tree bound. -/
theorem concrete_load_transfer :
    ∀ n : ℕ, 0 < n → 1 ≤ Real.log (n : ℝ) →
      probability (preferenceProfileSample n)
          (fun profile =>
            ¬ConcretePhaseLoadGood profile phaseLambdaZero) ≤
        Real.exp (-loadRate * (n : ℝ)) + 1 / (n : ℝ) ^ 3 := by
  intro n hn hlog
  simpa [loadRate] using
    PSChoiceMachine.concrete_load_transfer n hn hlog

/-- The finite expectation estimate already proved by the September 3
argument, with its load-transfer premise discharged. This retains the
original multiplicative constant and the full exceptional-event cost. -/
theorem expectedPS_le_phase_bound (n : ℕ) (hn : 0 < n)
    (hlog : 1 ≤ Real.log (n : ℝ)) :
    expectedPS n ≤ rankThresholdConstant * (1 + psLogStar n) +
      (n : ℝ) * failureError n :=
  expectation_le_of_load_transfer concrete_load_transfer hn hlog

/-- A finite bound valid also for the small markets excluded by the
logarithmic hypothesis of the concentration argument. -/
theorem expectedPS_le_marketSize (n : ℕ) (hn : 0 < n) :
    expectedPS n ≤ (n : ℝ) := by
  unfold expectedPS
  calc
    (𝔼 profile ∈ preferenceProfileSample n, averageRank (run profile)) ≤
        𝔼 _profile ∈ preferenceProfileSample n, (n : ℝ) := by
      apply expect_mono
      intro profile hprofile
      exact run_averageRank_le_marketSize profile hn
    _ = (n : ℝ) :=
      Finset.expect_const (preferenceProfileSample_nonempty n) _

/-- All three September 3 conclusions on the explicit uniform preference
profile space, now with every central probabilistic claim discharged. -/
theorem concrete_theorem_one :
    (∀ n : ℕ, 0 < n → 1 ≤ Real.log (n : ℝ) →
      probability (preferenceProfileSample n)
          (fun profile =>
            rankThresholdConstant * (1 + psLogStar n) <
              averageRank (run profile)) ≤ failureError n) ∧
    expectedPS =O[atTop] (fun n : ℕ => 1 + psLogStar n) ∧
    Tendsto (fun n : ℕ => expectedPS n / rpExpectation n) atTop (𝓝 0) := by
  exact concrete_theorem_one_of_load_transfer concrete_load_transfer

end ProbabilisticSerial.ConcreteTheoremOne
