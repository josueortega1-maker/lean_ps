import ReplicaConsumptionLower
import CouponUntouched
import RawSurvivorBound

/-! A finite lower bound for the expected contribution of a raw-label band. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaBandLower
open UniformProduct CouponLowerBound UniformRawPrefixes ReplicaPS ReplicaChoiceMachine
  ReplicaRawProcess ReplicaSurvivorEntries ReplicaConsumptionLower

variable {m q : ℕ} [Nonempty (Fin (m * q))]

def totalResidual (s : State m q) : ℝ := ∑ g : Fin m, residual s.reference s.clock g

lemma totalResidual_nonneg (s : State m q) : 0 ≤ totalResidual s :=
  Finset.sum_nonneg (fun g _ => residual_nonneg _ _ _)

theorem expected_band_lower_by_residual (hm : 2 ≤ m)
    (reference : ReplicaPS.Profile m q) (k r : ℕ) :
    (q : ℝ) * (1 - 4 / meanUnseen m k) -
      (𝔼 w : Fin (k + r) → Fin m, totalResidual ((initialState reference).evolve (k + r) w)) /
        (meanUnseen m k / 2) ≤
      𝔼 old : Fin k → Fin m, 𝔼 new : Fin r → Fin m,
        rawBandCost ((initialState reference).evolve k old) r new := by
  have hmpos : 0 < m := by omega
  let μ := meanUnseen m k
  have hμ : 0 < μ := meanUnseen_pos hm k
  have hu : 0 < μ / 2 := by positivity
  let R (old : Fin k → Fin m) : ℝ :=
    𝔼 new : Fin r → Fin m, totalResidual (((initialState reference).evolve k old).evolve r new)
  let B (old : Fin k → Fin m) : ℝ :=
    𝔼 new : Fin r → Fin m, rawBandCost ((initialState reference).evolve k old) r new
  have hR (old : Fin k → Fin m) : 0 ≤ R old :=
    Finset.expect_nonneg (fun new _ => totalResidual_nonneg _)
  have hB (old : Fin k → Fin m) : 0 ≤ B old :=
    Finset.expect_nonneg (fun new _ => rawBandCost_nonneg _ _ _)
  have hpoint (old : Fin k → Fin m) :
      (q : ℝ) - q * (if ((untouchedTypes old).card : ℝ) < μ / 2 then 1 else 0) -
        R old / (μ / 2) ≤ B old := by
    by_cases hbad : ((untouchedTypes old).card : ℝ) < μ / 2
    · rw [if_pos hbad]
      have hdiv := div_nonneg (hR old) hu.le
      linarith [hB old]
    · have hcard : μ / 2 ≤ ((untouchedTypes old).card : ℝ) := le_of_not_gt hbad
      have hpositive : 0 < (untouchedTypes old).card := by
        exact_mod_cast (hu.trans_le hcard)
      have hS (g : Fin m) (hg : g ∈ untouchedTypes old) :
          entryCount ((initialState reference).evolve k old) {g} = 0 :=
        ReplicaUntouched.untouched_entryCount_zero reference k old g
          ((mem_untouchedTypes old g).1 hg)
      have h := expected_bandCost_lower hmpos ((initialState reference).evolve k old)
        (untouchedTypes old) (Finset.card_pos.mp hpositive) hS r
      change (q : ℝ) - R old / (untouchedTypes old).card ≤ B old at h
      have hdiv := div_le_div_of_nonneg_left (hR old) hu hcard
      rw [if_neg hbad]
      linarith
  have hsample : (Finset.univ : Finset (Fin k → Fin m)).Nonempty :=
    ⟨fun _ => ⟨0, hmpos⟩, Finset.mem_univ _⟩
  have havg := Finset.expect_le_expect (s := Finset.univ) (fun old _ => hpoint old)
  simp only [Finset.expect_sub_distrib, Finset.expect_const hsample,
    ← Finset.mul_expect, ← Finset.expect_div] at havg
  have hp : (𝔼 old : Fin k → Fin m,
      if ((untouchedTypes old).card : ℝ) < μ / 2 then (1 : ℝ) else 0) ≤ 4 / μ := by
    simpa only [probability, labelSample_eq_univ] using untouched_card_lower_tail hm k
  have hRavg : (𝔼 old : Fin k → Fin m, R old) =
      𝔼 w : Fin (k + r) → Fin m, totalResidual ((initialState reference).evolve (k + r) w) :=
    expected_restart hmpos (initialState reference) k r totalResidual
  rw [hRavg] at havg
  have hqp := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg q)
  change _ ≤ 𝔼 old : Fin k → Fin m, B old
  dsimp only [μ] at *
  linarith

/-- All terms are explicit finite bounds on the actual replica PS process.
This is the per-band input to the fixed-quota asymptotic argument. -/
theorem expected_band_lower (hm : 2 ≤ m)
    (reference : ReplicaPS.Profile m q) (k r s : ℕ) {α : ℝ} (hα : 1 < α)
    (hmean : α * (m * q : ℕ) ≤ (k + r : ℕ) * ((s : ℝ) / m)) :
    (q : ℝ) * (1 - 4 / meanUnseen m k) -
      (q * (s : ℝ) + (q * (m : ℝ)) * ((RawSurvivorBound.survivorFamily m s).card : ℝ) *
        Real.exp (-(α - 1 - Real.log α) * (m * q : ℕ))) / (meanUnseen m k / 2) ≤
      𝔼 old : Fin k → Fin m, 𝔼 new : Fin r → Fin m,
        rawBandCost ((initialState reference).evolve k old) r new := by
  have hres := RawSurvivorBound.expected_residual_le (by omega : 0 < m)
    reference (k + r) s hα hmean
  rw [labelSample_eq_univ] at hres
  have hdiv := div_le_div_of_nonneg_right hres
    (div_nonneg (meanUnseen_pos hm k).le (by norm_num : (0 : ℝ) ≤ 2))
  have hband := expected_band_lower_by_residual hm reference k r
  unfold totalResidual at hband
  linarith

def bandLowerValue (m q k ending survivors : ℕ) (α : ℝ) : ℝ :=
  (q : ℝ) * (1 - 4 / meanUnseen m k) -
    (q * (survivors : ℝ) + (q * (m : ℝ)) *
      ((RawSurvivorBound.survivorFamily m survivors).card : ℝ) *
      Real.exp (-(α - 1 - Real.log α) * (m * q : ℕ))) / (meanUnseen m k / 2)

/-- Adding finitely many bands keeps all finite-market error terms. -/
theorem expected_cost_ge_band_sum (hm : 2 ≤ m)
    (reference : ReplicaPS.Profile m q) (cutoff survivors : ℕ → ℕ)
    (hmono : Monotone cutoff) {α : ℝ} (hα : 1 < α) (J : ℕ)
    (hmean : ∀ j < J,
      α * (m * q : ℕ) ≤ cutoff (j + 1) * ((survivors j : ℝ) / m)) :
    (∑ j ∈ Finset.range J, bandLowerValue m q (cutoff j) (cutoff (j + 1)) (survivors j) α) ≤
      𝔼 w : Fin (cutoff J) → Fin m, rawBandCost (initialState reference) (cutoff J) w := by
  induction J with
  | zero =>
      simp only [Finset.sum_range_zero]
      exact Finset.expect_nonneg (fun w _ => rawBandCost_nonneg _ _ _)
  | succ J ih =>
      have hle := hmono (Nat.le_succ J)
      have hlength : cutoff J + (cutoff (J + 1) - cutoff J) = cutoff (J + 1) :=
        Nat.add_sub_of_le hle
      have hb := expected_band_lower hm reference (cutoff J) (cutoff (J + 1) - cutoff J)
        (survivors J) hα (by rw [hlength]; exact hmean J (by omega))
      change bandLowerValue m q (cutoff J) (cutoff (J + 1)) (survivors J) α ≤ _ at hb
      have hadd := expected_bandCost_add (by omega : 0 < m) (initialState reference)
        (cutoff J) (cutoff (J + 1) - cutoff J)
      rw [hlength] at hadd
      have hprev := ih (fun j hj => hmean j (by omega))
      rw [Finset.sum_range_succ]
      linarith

end ProbabilisticSerial.ReplicaBandLower
