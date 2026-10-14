import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import AdaptiveBernoulli
import RankMGF
import StoppedChoices
import LoadBound
import PhaseIntegral
import PhaseAdapter

/-!
# Theorem 1 from `PS_ECMA.tex`

This file formalizes the *main-theorem assembly* in the paper: the uniform-rank
event and the load/phase event imply the advertised tail bound; the deterministic
bound `Rank(PS) ≤ n` turns that tail estimate into the expectation estimate; and
Knuth's RP asymptotic plus `logStar = o(log)` gives the vanishing ratio.

The remaining paper-specific inputs are fields of `TheoremOneInputs`, with
names that match the LaTeX proof. They are hypotheses here, not hidden axioms.
The companion files imported above fully prove the finite active-rank counting,
the common uniform random-permutation profile, MGF/Chernoff and union-bound
steps, the adaptive Bernoulli/Ville calculations, and a finite event-driven
construction of the continuous-time PS eating process with its exact
dynamic-rank identity and deterministic rank reduction. Sequential revelation
is derived by an exact permutation-fiber bijection, including histories whose
available sets are generated endogenously by the earlier process.
The stopped counts and compensators are identified with phase loads and the
paper's event potential, and the adaptive deviation bounds are proved on a
labelled-history tree retaining the full revealed filtration.
The load proposition's finite union bounds, entropy estimate, ceiling case
split, absolute constants, and deterministic demand conversion are proved in
`LoadBound`. The deterministic survivor-block consumption argument, active
size recurrence, iterated-exponential phase count, and certified assembly of
the eating-integral bound are proved in `PhaseIntegral`. The greedy partition
of the actual PS trace and the concrete `C(1+logStar n)` bound on its load-good
event are proved in `PhaseAdapter`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology
open Asymptotics

namespace ProbabilisticSerial

/-- The scale appearing in Theorem 1: `1 + logStar n`. We keep `logStar`
abstract because the main proof only uses its nonnegativity and its elementary
asymptotic relation to `log`. -/
def logStarScale (logStar : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 + logStar n

/-- The polynomial part of the exceptional-event probability. -/
def polynomialTail (C : ℝ) (n : ℕ) : ℝ :=
  C / (n : ℝ) ^ 3

/-- The complete tail expression in equation (1) of the paper. -/
def tailError (C c : ℝ) (n : ℕ) : ℝ :=
  polynomialTail C n + Real.exp (-c * (n : ℝ))

lemma polynomialTail_nonneg {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ polynomialTail C n := by
  exact div_nonneg hC (pow_nonneg (Nat.cast_nonneg n) 3)

lemma tailError_nonneg {C c : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ tailError C c n := by
  exact add_nonneg (polynomialTail_nonneg hC n) (Real.exp_pos _).le

/-- Multiplying the exceptional-event probability by the deterministic bound
`Rank(PS) ≤ n` produces a term tending to zero. This is the analytic content
of the paper's sentence "the failure probability contributes `o(1)`". -/
lemma tailError_cost_tendsto_zero (C c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * tailError C c n) atTop (𝓝 0) := by
  have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inverse_atTop_nhds_zero_nat
  have hPolyModel :
      Tendsto (fun n : ℕ => C * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hInv.pow 2)
  have hPoly :
      Tendsto (fun n : ℕ => (n : ℝ) * polynomialTail C n) atTop (𝓝 0) := by
    apply hPolyModel.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0_nat : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hn)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn0_nat
    simp only [polynomialTail]
    field_simp
    ring
  have hExp :
      Tendsto
        (fun n : ℕ => (n : ℝ) * Real.exp (-c * (n : ℝ)))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) c hc).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [tailError, mul_add, zero_add] using hPoly.add hExp

/-- Inputs already established before the final paragraph of the paper's proof.

`rankReduction` is equation (6), and `phaseIntegralBound` is Proposition 2.
The two failure bounds are Lemma 2 and Proposition 1 after choosing absolute
constants. `knuthRP` packages Lemma 1's asymptotic conclusion. -/
structure TheoremOneInputs (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  psRank : ℕ → Ω → ℝ
  rpExpectation : ℕ → ℝ
  logStar : ℕ → ℝ
  eatingIntegral : ℕ → Ω → ℝ
  uniformRankEvent : ℕ → Set Ω
  loadPhaseEvent : ℕ → Set Ω
  C₀ : ℝ
  Cphase : ℝ
  Cload : ℝ
  cRank : ℝ
  C₀_pos : 0 < C₀
  Cphase_pos : 0 < Cphase
  Cload_pos : 0 < Cload
  cRank_pos : 0 < cRank
  logStar_nonneg : ∀ n, 0 ≤ logStar n
  psRank_integrable : ∀ n, Integrable (psRank n) μ
  psRank_nonneg : ∀ n ω, 0 ≤ psRank n ω
  psRank_le_marketSize : ∀ n ω, psRank n ω ≤ (n : ℝ)
  uniformRankEvent_measurable : ∀ n, MeasurableSet (uniformRankEvent n)
  loadPhaseEvent_measurable : ∀ n, MeasurableSet (loadPhaseEvent n)
  rankReduction : ∀ n ω, ω ∈ uniformRankEvent n →
    psRank n ω ≤ C₀ * eatingIntegral n ω
  phaseIntegralBound : ∀ n ω, ω ∈ loadPhaseEvent n →
    eatingIntegral n ω ≤ Cphase * logStarScale logStar n
  uniformRank_failure : ∀ n, 1 ≤ n →
    μ (uniformRankEvent n)ᶜ ≤ ENNReal.ofReal (Real.exp (-cRank * (n : ℝ)))
  loadPhase_failure : ∀ n, 1 ≤ n →
    μ (loadPhaseEvent n)ᶜ ≤ ENNReal.ofReal (polynomialTail Cload n)
  logStar_small_relative_to_log :
    (fun n : ℕ => logStarScale logStar n) =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ))
  knuthRP :
    rpExpectation ~[atTop] (fun n : ℕ => Real.log (n : ℝ))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The expected average PS rank. -/
def expectedPS (h : TheoremOneInputs Ω μ) (n : ℕ) : ℝ :=
  ∫ ω, h.psRank n ω ∂μ

/-- A convenient single constant dominating both the good-event rank constant
and the polynomial failure constant. -/
def theoremConstant (h : TheoremOneInputs Ω μ) : ℝ :=
  max (h.C₀ * h.Cphase) h.Cload

lemma theoremConstant_pos (h : TheoremOneInputs Ω μ) :
    0 < theoremConstant h := by
  exact h.Cload_pos.trans_le (le_max_right _ _)

lemma logStarScale_nonneg (h : TheoremOneInputs Ω μ) (n : ℕ) :
    0 ≤ logStarScale h.logStar n := by
  dsimp [logStarScale]
  linarith [h.logStar_nonneg n]

lemma logStarScale_one_le (h : TheoremOneInputs Ω μ) (n : ℕ) :
    1 ≤ logStarScale h.logStar n := by
  dsimp [logStarScale]
  linarith [h.logStar_nonneg n]

/-- Equations (6) and (18) combine on the intersection of their good events. -/
lemma rank_le_on_good_intersection (h : TheoremOneInputs Ω μ) (n : ℕ) (ω : Ω)
    (hω : ω ∈ h.uniformRankEvent n ∩ h.loadPhaseEvent n) :
    h.psRank n ω ≤ theoremConstant h * logStarScale h.logStar n := by
  have hReduce := h.rankReduction n ω hω.1
  have hPhase := h.phaseIntegralBound n ω hω.2
  have hC₀_nonneg : 0 ≤ h.C₀ := h.C₀_pos.le
  have hScale_nonneg := logStarScale_nonneg h n
  calc
    h.psRank n ω ≤ h.C₀ * h.eatingIntegral n ω := hReduce
    _ ≤ h.C₀ * (h.Cphase * logStarScale h.logStar n) :=
      mul_le_mul_of_nonneg_left hPhase hC₀_nonneg
    _ = (h.C₀ * h.Cphase) * logStarScale h.logStar n := by ring
    _ ≤ theoremConstant h * logStarScale h.logStar n :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hScale_nonneg

/-- The union bound for the two exceptional events cited by Theorem 1. -/
lemma good_intersection_failure (h : TheoremOneInputs Ω μ) (n : ℕ) (hn : 1 ≤ n) :
    μ (h.uniformRankEvent n ∩ h.loadPhaseEvent n)ᶜ ≤
      ENNReal.ofReal (tailError (theoremConstant h) h.cRank n) := by
  have hExpNonneg : 0 ≤ Real.exp (-h.cRank * (n : ℝ)) := (Real.exp_pos _).le
  have hPolyLoadNonneg : 0 ≤ polynomialTail h.Cload n :=
    polynomialTail_nonneg h.Cload_pos.le n
  have hLoadConst : h.Cload ≤ theoremConstant h := le_max_right _ _
  have hDenomNonneg : 0 ≤ (n : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg n) 3
  have hPolyMono :
      polynomialTail h.Cload n ≤ polynomialTail (theoremConstant h) n := by
    exact div_le_div_of_nonneg_right hLoadConst hDenomNonneg
  calc
    μ (h.uniformRankEvent n ∩ h.loadPhaseEvent n)ᶜ
        = μ ((h.uniformRankEvent n)ᶜ ∪ (h.loadPhaseEvent n)ᶜ) := by
      simp only [compl_inter]
    _ ≤ μ (h.uniformRankEvent n)ᶜ + μ (h.loadPhaseEvent n)ᶜ :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-h.cRank * (n : ℝ))) +
          ENNReal.ofReal (polynomialTail h.Cload n) :=
      add_le_add (h.uniformRank_failure n hn) (h.loadPhase_failure n hn)
    _ = ENNReal.ofReal
          (Real.exp (-h.cRank * (n : ℝ)) + polynomialTail h.Cload n) := by
      rw [ENNReal.ofReal_add hExpNonneg hPolyLoadNonneg]
    _ ≤ ENNReal.ofReal
          (polynomialTail (theoremConstant h) n + Real.exp (-h.cRank * (n : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      linarith
    _ = ENNReal.ofReal (tailError (theoremConstant h) h.cRank n) := by
      rfl

/-- The exact probability estimate in equation (1). -/
lemma theorem_one_tail (h : TheoremOneInputs Ω μ) (n : ℕ) (hn : 1 ≤ n) :
    μ {ω | theoremConstant h * logStarScale h.logStar n < h.psRank n ω} ≤
      ENNReal.ofReal (tailError (theoremConstant h) h.cRank n) := by
  have hSubset :
      {ω | theoremConstant h * logStarScale h.logStar n < h.psRank n ω} ⊆
        (h.uniformRankEvent n ∩ h.loadPhaseEvent n)ᶜ := by
    intro ω hTail hGood
    exact (not_lt_of_ge (rank_le_on_good_intersection h n ω hGood)) hTail
  exact (measure_mono hSubset).trans (good_intersection_failure h n hn)

/-- Split an expectation into a good event and its complement. This is a
general measure-theoretic lemma, independent of the matching model. -/
lemma integral_le_good_plus_bad [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {s : Set Ω} {B M : ℝ}
    (hf : Integrable f μ) (hs : MeasurableSet s)
    (hB : 0 ≤ B)
    (hGood : ∀ ω ∈ s, f ω ≤ B) (hAll : ∀ ω, f ω ≤ M) :
    (∫ ω, f ω ∂μ) ≤ B + M * μ.real sᶜ := by
  have hGoodIntegral : (∫ ω in s, f ω ∂μ) ≤ B * μ.real s := by
    calc
      (∫ ω in s, f ω ∂μ) ≤ ∫ _ω in s, B ∂μ :=
        setIntegral_mono_on hf.integrableOn (integrable_const B).integrableOn hs hGood
      _ = μ.real s * B := setIntegral_const B
      _ = B * μ.real s := mul_comm _ _
  have hBadIntegral : (∫ ω in sᶜ, f ω ∂μ) ≤ M * μ.real sᶜ := by
    calc
      (∫ ω in sᶜ, f ω ∂μ) ≤ ∫ _ω in sᶜ, M ∂μ :=
        setIntegral_mono_on hf.integrableOn (integrable_const M).integrableOn hs.compl
          (fun ω _ => hAll ω)
      _ = μ.real sᶜ * M := setIntegral_const M
      _ = M * μ.real sᶜ := mul_comm _ _
  rw [← integral_add_compl hs hf]
  calc
    (∫ ω in s, f ω ∂μ) + ∫ ω in sᶜ, f ω ∂μ
        ≤ B * μ.real s + M * μ.real sᶜ := add_le_add hGoodIntegral hBadIntegral
    _ ≤ B + M * μ.real sᶜ := by
      have hs_le_one : μ.real s ≤ 1 := measureReal_le_one
      calc
        B * μ.real s + M * μ.real sᶜ ≤ B * 1 + M * μ.real sᶜ :=
          add_le_add_right (mul_le_mul_of_nonneg_left hs_le_one hB) _
        _ = B + M * μ.real sᶜ := by ring

/-- Explicit expectation bound obtained from the tail estimate and
`Rank(PS) ≤ n`. -/
lemma theorem_one_expectation_bound [IsProbabilityMeasure μ]
    (h : TheoremOneInputs Ω μ) (n : ℕ) (hn : 1 ≤ n) :
    expectedPS h n ≤
      theoremConstant h * logStarScale h.logStar n +
        (n : ℝ) * tailError (theoremConstant h) h.cRank n := by
  let good := h.uniformRankEvent n ∩ h.loadPhaseEvent n
  have hGoodMeas : MeasurableSet good :=
    (h.uniformRankEvent_measurable n).inter (h.loadPhaseEvent_measurable n)
  have hSplit := integral_le_good_plus_bad
    (h.psRank_integrable n) hGoodMeas
    (mul_nonneg (theoremConstant_pos h).le (logStarScale_nonneg h n))
    (rank_le_on_good_intersection h n)
    (h.psRank_le_marketSize n)
  have hBadMeasureENN := good_intersection_failure h n hn
  have hTailNonneg : 0 ≤ tailError (theoremConstant h) h.cRank n :=
    tailError_nonneg (theoremConstant_pos h).le n
  have hBadMeasureReal : μ.real goodᶜ ≤ tailError (theoremConstant h) h.cRank n := by
    have hToReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top μ goodᶜ) ENNReal.ofReal_ne_top).2
        hBadMeasureENN
    simpa only [Measure.real, ENNReal.toReal_ofReal hTailNonneg] using hToReal
  exact hSplit.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left hBadMeasureReal (Nat.cast_nonneg n)) _)

/-- Equation (2): expected PS average rank is `O(1 + logStar n)`. -/
lemma theorem_one_expectation_bigO [IsProbabilityMeasure μ]
    (h : TheoremOneInputs Ω μ) :
    (fun n : ℕ => expectedPS h n) =O[atTop]
      (fun n : ℕ => logStarScale h.logStar n) := by
  have hCost := tailError_cost_tendsto_zero (theoremConstant h) h.cRank h.cRank_pos
  have hCostSmall :
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * tailError (theoremConstant h) h.cRank n < 1 :=
    hCost.eventually (Iio_mem_nhds zero_lt_one)
  apply IsBigO.of_bound (theoremConstant h + 1)
  filter_upwards [hCostSmall, eventually_ge_atTop (1 : ℕ)] with n hSmall hn
  have hExpectationNonneg : 0 ≤ expectedPS h n :=
    integral_nonneg (h.psRank_nonneg n)
  have hScaleNonneg := logStarScale_nonneg h n
  rw [Real.norm_eq_abs, abs_of_nonneg hExpectationNonneg,
    Real.norm_eq_abs, abs_of_nonneg hScaleNonneg]
  calc
    expectedPS h n ≤ theoremConstant h * logStarScale h.logStar n +
        (n : ℝ) * tailError (theoremConstant h) h.cRank n :=
      theorem_one_expectation_bound h n hn
    _ ≤ theoremConstant h * logStarScale h.logStar n + 1 := by linarith
    _ ≤ (theoremConstant h + 1) * logStarScale h.logStar n := by
      nlinarith [logStarScale_one_le h n]

/-- Equation (3): the expected-rank ratio between PS and RP tends to zero. -/
lemma theorem_one_ratio [IsProbabilityMeasure μ]
    (h : TheoremOneInputs Ω μ) :
    Tendsto (fun n : ℕ => expectedPS h n / h.rpExpectation n) atTop (𝓝 0) := by
  have hPSvsScale := theorem_one_expectation_bigO h
  have hPSvsLog :
      (fun n : ℕ => expectedPS h n) =o[atTop]
        (fun n : ℕ => Real.log (n : ℝ)) :=
    hPSvsScale.trans_isLittleO h.logStar_small_relative_to_log
  have hPSvsRP :
      (fun n : ℕ => expectedPS h n) =o[atTop] h.rpExpectation :=
    hPSvsLog.trans_isEquivalent h.knuthRP.symm
  exact hPSvsRP.tendsto_div_nhds_zero

/-- Lean implementation of Theorem 1's final proof. -/
theorem theorem_one [IsProbabilityMeasure μ] (h : TheoremOneInputs Ω μ) :
    ∃ C > 0, ∃ c > 0,
      (∀ n : ℕ, 1 ≤ n →
        μ {ω | C * logStarScale h.logStar n < h.psRank n ω} ≤
          ENNReal.ofReal (tailError C c n)) ∧
      (fun n : ℕ => expectedPS h n) =O[atTop]
        (fun n : ℕ => logStarScale h.logStar n) ∧
      Tendsto (fun n : ℕ => expectedPS h n / h.rpExpectation n) atTop (𝓝 0) := by
  refine ⟨theoremConstant h, theoremConstant_pos h,
    h.cRank, h.cRank_pos, ?_, theorem_one_expectation_bigO h, theorem_one_ratio h⟩
  intro n hn
  exact theorem_one_tail h n hn

end ProbabilisticSerial
