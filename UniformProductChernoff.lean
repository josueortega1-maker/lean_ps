import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Chernoff bounds for finite uniform product spaces

The preference profile in Theorem 1 is a product of independent uniform
preferences.  This file proves the concentration step on an explicit finite
uniform product space.  Thus independence is not postulated as a typeclass: it is
the concrete `Fintype.piFinset` sample space, and factorisation of the moment
generating function is proved from `Finset.expect_pow`.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.UniformProduct

/-- Probability of an event under the uniform distribution on `sample`.
For the empty sample this follows mathlib's convention and is zero. -/
def probability {α : Type*} (sample : Finset α) (event : α → Prop)
    [DecidablePred event] : ℝ :=
  𝔼 a ∈ sample, if event a then 1 else 0

lemma expect_mono {α : Type*} (sample : Finset α) {f g : α → ℝ}
    (hfg : ∀ a ∈ sample, f a ≤ g a) :
    (𝔼 a ∈ sample, f a) ≤ 𝔼 a ∈ sample, g a := by
  simp only [Finset.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right (sum_le_sum hfg) (Nat.cast_nonneg _)

lemma probability_nonneg {α : Type*} (sample : Finset α) (event : α → Prop)
    [DecidablePred event] : 0 ≤ probability sample event := by
  have h := expect_mono sample
    (f := fun _ => (0 : ℝ))
    (g := fun a => if event a then 1 else 0)
    (by
      intro a ha
      change 0 ≤ if event a then (1 : ℝ) else 0
      by_cases h : event a <;> simp [h])
  simpa [probability] using h

lemma probability_mono {α : Type*} (sample : Finset α)
    {event₁ event₂ : α → Prop} [DecidablePred event₁] [DecidablePred event₂]
    (h : ∀ a ∈ sample, event₁ a → event₂ a) :
    probability sample event₁ ≤ probability sample event₂ := by
  apply expect_mono sample
  intro a ha
  by_cases h₁ : event₁ a
  · simp [h₁, h a ha h₁]
  · by_cases h₂ : event₂ a <;> simp [h₁, h₂]

/-- Markov's inequality on a finite uniform sample space. -/
lemma markov {α : Type*} (sample : Finset α) (event : α → Prop)
    [DecidablePred event] (Y : α → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hY : ∀ x ∈ sample, 0 ≤ Y x)
    (hevent : ∀ x ∈ sample, event x → a ≤ Y x) :
    a * probability sample event ≤ 𝔼 x ∈ sample, Y x := by
  change a * (𝔼 x ∈ sample, if event x then (1 : ℝ) else 0) ≤
    𝔼 x ∈ sample, Y x
  rw [Finset.mul_expect]
  apply expect_mono sample
  intro x hx
  by_cases he : event x
  · simpa [he] using hevent x hx he
  · simpa [he] using hY x hx

lemma markov_div {α : Type*} (sample : Finset α) (event : α → Prop)
    [DecidablePred event] (Y : α → ℝ) {a : ℝ} (ha : 0 < a)
    (hY : ∀ x ∈ sample, 0 ≤ Y x)
    (hevent : ∀ x ∈ sample, event x → a ≤ Y x) :
    probability sample event ≤ (𝔼 x ∈ sample, Y x) / a := by
  rw [le_div_iff₀ ha]
  simpa [mul_comm] using markov sample event Y ha.le hY hevent

/-- Union bound for finitely many events on a finite uniform sample. -/
lemma union_bound {α κ : Type*} (sample : Finset α) (indices : Finset κ)
    (event : κ → α → Prop) [DecidableRel event] :
    probability sample (fun x => ∃ k ∈ indices, event k x) ≤
      ∑ k ∈ indices, probability sample (event k) := by
  calc
    probability sample (fun x => ∃ k ∈ indices, event k x)
        ≤ 𝔼 x ∈ sample, ∑ k ∈ indices, if event k x then (1 : ℝ) else 0 := by
      apply expect_mono sample
      intro x hx
      by_cases he : ∃ k ∈ indices, event k x
      · have he' := he
        obtain ⟨k, hk, hek⟩ := he
        have hone : (1 : ℝ) ≤ ∑ j ∈ indices, if event j x then 1 else 0 := by
          have hnonneg : ∀ j ∈ indices,
              0 ≤ (if event j x then (1 : ℝ) else 0) := by
            intro j hj
            by_cases hjx : event j x <;> simp [hjx]
          calc
            (1 : ℝ) = if event k x then 1 else 0 := by simp [hek]
            _ ≤ ∑ j ∈ indices, if event j x then 1 else 0 :=
              single_le_sum hnonneg hk
        rw [if_pos he']
        exact hone
      · rw [if_neg he]
        exact sum_nonneg fun j hj => by
          by_cases hjx : event j x <;> simp [hjx]
    _ = ∑ k ∈ indices, probability sample (event k) := by
      rw [Finset.expect_sum_comm]
      rfl

/-- The explicit sample space of `n` independent draws from `sample`. -/
def productSample {α : Type*} (sample : Finset α) (n : ℕ) :
    Finset (Fin n → α) :=
  Fintype.piFinset fun _ : Fin n => sample

lemma productSample_nonempty {α : Type*} {sample : Finset α}
    (hs : sample.Nonempty) (n : ℕ) : (productSample sample n).Nonempty := by
  simp [productSample, hs]

/-- The exponential moment of a sum over the explicit product sample factors
as the `n`th power of the one-coordinate moment. -/
lemma exp_sum_expect_eq_pow {α : Type*} (sample : Finset α)
    (X : α → ℝ) (θ : ℝ) (n : ℕ) :
    (𝔼 profile ∈ productSample sample n,
        Real.exp (θ * ∑ i : Fin n, X (profile i))) =
      (𝔼 a ∈ sample, Real.exp (θ * X a)) ^ n := by
  calc
    (𝔼 profile ∈ productSample sample n,
        Real.exp (θ * ∑ i : Fin n, X (profile i))) =
        𝔼 profile ∈ productSample sample n,
          ∏ i : Fin n, Real.exp (θ * X (profile i)) := by
      apply Finset.expect_congr rfl
      intro profile hprofile
      rw [← Real.exp_sum]
      congr 1
      rw [mul_sum]
    _ = (𝔼 a ∈ sample, Real.exp (θ * X a)) ^ n := by
      exact (Finset.expect_pow sample (fun a => Real.exp (θ * X a)) n).symm

/-- Chernoff bound for a sum of independent uniform finite random variables.
The MGF hypothesis is only one-dimensional; its `n`th power is derived in
`exp_sum_expect_eq_pow`. -/
theorem chernoff_sum {α : Type*} (sample : Finset α) (X : α → ℝ)
    {θ B K : ℝ} (hθ : 0 < θ) (hB : 0 < B)
    (hmgf : (𝔼 a ∈ sample, Real.exp (θ * X a)) ≤ B) (n : ℕ) :
    probability (productSample sample n)
        (fun profile => K * n ≤ ∑ i : Fin n, X (profile i)) ≤
      Real.exp (-(n : ℝ) * (θ * K - Real.log B)) := by
  let threshold := Real.exp (θ * K * n)
  let Y : (Fin n → α) → ℝ :=
    fun profile => Real.exp (θ * ∑ i : Fin n, X (profile i))
  have hthreshold : 0 < threshold := Real.exp_pos _
  have hevent : ∀ profile ∈ productSample sample n,
      K * n ≤ ∑ i : Fin n, X (profile i) → threshold ≤ Y profile := by
    intro profile hprofile hsum
    dsimp [threshold, Y]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hsum hθ.le
    norm_num at this ⊢
    simpa [mul_assoc] using this
  have hmarkov := markov_div (productSample sample n)
    (fun profile => K * n ≤ ∑ i : Fin n, X (profile i)) Y
    hthreshold (fun _ _ => (Real.exp_pos _).le) hevent
  rw [exp_sum_expect_eq_pow] at hmarkov
  have hmoment_nonneg :
      0 ≤ 𝔼 a ∈ sample, Real.exp (θ * X a) := by
    have h := expect_mono sample
      (f := fun _ => (0 : ℝ))
      (g := fun a => Real.exp (θ * X a))
      (by intro a ha; exact (Real.exp_pos _).le)
    simpa using h
  have hpow :
      (𝔼 a ∈ sample, Real.exp (θ * X a)) ^ n ≤ B ^ n := by
    exact pow_le_pow_left₀ hmoment_nonneg hmgf n
  calc
    probability (productSample sample n)
        (fun profile => K * n ≤ ∑ i : Fin n, X (profile i))
        ≤ (𝔼 a ∈ sample, Real.exp (θ * X a)) ^ n / threshold := hmarkov
    _ ≤ B ^ n / threshold :=
      div_le_div_of_nonneg_right hpow hthreshold.le
    _ = Real.exp (-(n : ℝ) * (θ * K - Real.log B)) := by
      dsimp [threshold]
      rw [← Real.exp_log hB, ← Real.exp_nat_mul, ← Real.exp_sub]
      congr 1
      norm_num
      ring

/-- Simultaneous Chernoff bound over a finite family of statistics.  This is
the union-bound step used for all active sets in the uniform-rank lemma. -/
theorem simultaneous_chernoff {α κ : Type*} (sample : Finset α)
    (indices : Finset κ) (X : κ → α → ℝ)
    {θ B K : ℝ} (hθ : 0 < θ) (hB : 0 < B)
    (hmgf : ∀ k ∈ indices,
      (𝔼 a ∈ sample, Real.exp (θ * X k a)) ≤ B) (n : ℕ) :
    probability (productSample sample n)
        (fun profile => ∃ k ∈ indices,
          K * n ≤ ∑ i : Fin n, X k (profile i)) ≤
      (indices.card : ℝ) * Real.exp (-(n : ℝ) * (θ * K - Real.log B)) := by
  calc
    probability (productSample sample n)
        (fun profile => ∃ k ∈ indices,
          K * n ≤ ∑ i : Fin n, X k (profile i))
        ≤ ∑ k ∈ indices,
            probability (productSample sample n)
              (fun profile => K * n ≤ ∑ i : Fin n, X k (profile i)) :=
      union_bound (productSample sample n) indices
        (fun k profile => K * n ≤ ∑ i : Fin n, X k (profile i))
    _ ≤ ∑ _k ∈ indices,
          Real.exp (-(n : ℝ) * (θ * K - Real.log B)) := by
      apply sum_le_sum
      intro k hk
      exact chernoff_sum sample (X k) hθ hB (hmgf k hk) n
    _ = (indices.card : ℝ) *
          Real.exp (-(n : ℝ) * (θ * K - Real.log B)) := by
      simp

/-- Paper-specialized constants: if every scaled active-rank statistic has
MGF at `1/2` bounded by `1+e`, then all active sets satisfy the desired
average bound except with the displayed exponentially small probability. -/
theorem uniform_active_rank_from_mgf {α κ : Type*} (sample : Finset α)
    (activeSets : Finset κ) (scaledRank : κ → α → ℝ)
    (hmgf : ∀ S ∈ activeSets,
      (𝔼 pref ∈ sample, Real.exp ((1 / 2 : ℝ) * scaledRank S pref)) ≤
        1 + Real.exp 1)
    (K : ℝ) (n : ℕ) :
    probability (productSample sample n)
        (fun profile => ∃ S ∈ activeSets,
          K * n ≤ ∑ i : Fin n, scaledRank S (profile i)) ≤
      (activeSets.card : ℝ) *
        Real.exp (-(n : ℝ) * ((1 / 2 : ℝ) * K - Real.log (1 + Real.exp 1))) := by
  exact simultaneous_chernoff sample activeSets scaledRank
    (by norm_num) (by positivity) hmgf n

/-- The final `2^n` union-bound calculation in the uniform active-rank lemma.
If `K` leaves an extra exponent `c` beyond `log 2`, the simultaneous failure
probability is at most `exp(-c n)`. -/
theorem uniform_active_rank_exponential {α κ : Type*} (sample : Finset α)
    (activeSets : Finset κ) (scaledRank : κ → α → ℝ)
    (hmgf : ∀ S ∈ activeSets,
      (𝔼 pref ∈ sample, Real.exp ((1 / 2 : ℝ) * scaledRank S pref)) ≤
        1 + Real.exp 1)
    {K c : ℝ}
    (hK : Real.log 2 + c ≤
      (1 / 2 : ℝ) * K - Real.log (1 + Real.exp 1))
    (n : ℕ) (hcard : activeSets.card ≤ 2 ^ n) :
    probability (productSample sample n)
        (fun profile => ∃ S ∈ activeSets,
          K * n ≤ ∑ i : Fin n, scaledRank S (profile i)) ≤
      Real.exp (-c * n) := by
  let a := (1 / 2 : ℝ) * K - Real.log (1 + Real.exp 1)
  have hsim := uniform_active_rank_from_mgf sample activeSets scaledRank hmgf K n
  have hcardR : (activeSets.card : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have htwo : ((2 ^ n : ℕ) : ℝ) = Real.exp ((n : ℝ) * Real.log 2) := by
    push_cast
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    probability (productSample sample n)
        (fun profile => ∃ S ∈ activeSets,
          K * n ≤ ∑ i : Fin n, scaledRank S (profile i))
        ≤ (activeSets.card : ℝ) * Real.exp (-(n : ℝ) * a) := hsim
    _ ≤ ((2 ^ n : ℕ) : ℝ) * Real.exp (-(n : ℝ) * a) :=
      mul_le_mul_of_nonneg_right hcardR (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ) * Real.log 2 - (n : ℝ) * a) := by
      rw [htwo, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-c * n) := by
      apply Real.exp_le_exp.mpr
      have ha : Real.log 2 + c ≤ a := hK
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith

end ProbabilisticSerial.UniformProduct
