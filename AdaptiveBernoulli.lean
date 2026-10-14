import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.List.Count
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Adaptive Bernoulli concentration on a finite probability tree

This file gives a self-contained, finite-horizon version of the adaptive
Bernoulli lemma used in the proof of Theorem 1.  A node of the tree is the
chronological list of observations already revealed.  The function `p h` is
the conditional probability of seeing `true` after history `h`.

No independence assumption is made: `p` may depend arbitrarily on the entire
past.  The proofs construct the exponential supermartingales explicitly and
prove their maximal inequalities by induction on the remaining depth (the
finite-tree form of Ville's inequality).
-/

noncomputable section

open Finset

namespace ProbabilisticSerial.AdaptiveBernoulli

/-- A finite chronological history of Bernoulli observations. -/
abbrev History := List Bool

/-- Number of successes in a history, viewed as a real number. -/
def successes (h : History) : ℝ := h.count true

/-- Predictable compensator: the sum of the conditional success probabilities
seen along the strict prefixes of `h`. -/
def compensator (p : History → ℝ) (h : History) : ℝ :=
  ∑ j ∈ range h.length, p (h.take j)

@[simp] lemma successes_nil : successes [] = 0 := by
  simp [successes]

@[simp] lemma successes_snoc (h : History) (b : Bool) :
    successes (h ++ [b]) = successes h + if b then 1 else 0 := by
  cases b <;> simp [successes]

@[simp] lemma compensator_nil (p : History → ℝ) : compensator p [] = 0 := by
  simp [compensator]

@[simp] lemma compensator_snoc (p : History → ℝ) (h : History) (b : Bool) :
    compensator p (h ++ [b]) = compensator p h + p h := by
  simp only [compensator, List.length_append, List.length_singleton, Nat.add_comm,
    sum_range_succ, List.take_length]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [List.take_append_of_le_length]
  exact Nat.le_of_lt (mem_range.mp hj)
  rw [List.take_append_of_le_length (le_refl h.length), List.take_length]

/-- A valid adaptive Bernoulli law has a transition probability in `[0,1]` at
every history. -/
def ValidLaw (p : History → ℝ) : Prop := ∀ h, 0 ≤ p h ∧ p h ≤ 1

/-- Probability, under the adaptive law `p`, of seeing `event` at the current
node or at one of the next `depth` nodes. -/
def hitProbability (p : History → ℝ) (event : History → Prop)
    [DecidablePred event] : ℕ → History → ℝ
  | 0, h => if event h then 1 else 0
  | depth + 1, h =>
      if event h then 1
      else p h * hitProbability p event depth (h ++ [true]) +
        (1 - p h) * hitProbability p event depth (h ++ [false])

/-- The local one-step definition of a nonnegative supermartingale on the
adaptive binary tree. -/
def IsTreeSupermartingale (p Z : History → ℝ) : Prop :=
  (∀ h, 0 ≤ Z h) ∧
  ∀ h, p h * Z (h ++ [true]) + (1 - p h) * Z (h ++ [false]) ≤ Z h

lemma hitProbability_nonneg {p : History → ℝ} (hp : ValidLaw p)
    (event : History → Prop) [DecidablePred event] :
    ∀ depth h, 0 ≤ hitProbability p event depth h := by
  intro depth
  induction depth with
  | zero =>
      intro h
      simp only [hitProbability]
      split_ifs <;> norm_num
  | succ depth ih =>
      intro h
      simp only [hitProbability]
      split_ifs
      · norm_num
      · exact add_nonneg
          (mul_nonneg (hp h).1 (ih _))
          (mul_nonneg (sub_nonneg.mpr (hp h).2) (ih _))

/-- Finite-tree Ville inequality in multiplicative form.  If every occurrence
of `event` forces a nonnegative supermartingale to be at least `a`, then
`a * P(event occurs by depth) ≤ Z(initial history)`. -/
lemma threshold_mul_hitProbability_le {p Z : History → ℝ}
    (hp : ValidLaw p) (hZ : IsTreeSupermartingale p Z)
    {event : History → Prop} [DecidablePred event]
    {a : ℝ} (ha : 0 ≤ a) (h_event : ∀ h, event h → a ≤ Z h) :
    ∀ depth h, a * hitProbability p event depth h ≤ Z h := by
  intro depth
  induction depth with
  | zero =>
      intro h
      simp only [hitProbability]
      by_cases he : event h
      · simp [he, h_event h he]
      · simp [he, hZ.1 h]
  | succ depth ih =>
      intro h
      simp only [hitProbability]
      by_cases he : event h
      · simp [he, h_event h he]
      · rw [if_neg he, mul_add]
        have hp0 := (hp h).1
        have hp1 : 0 ≤ 1 - p h := sub_nonneg.mpr (hp h).2
        have hreassoc :
            a * (p h * hitProbability p event depth (h ++ [true])) +
                a * ((1 - p h) * hitProbability p event depth (h ++ [false])) =
              p h * (a * hitProbability p event depth (h ++ [true])) +
                (1 - p h) * (a * hitProbability p event depth (h ++ [false])) := by
          ring
        rw [hreassoc]
        calc
          p h * (a * hitProbability p event depth (h ++ [true])) +
              (1 - p h) * (a * hitProbability p event depth (h ++ [false]))
              ≤ p h * Z (h ++ [true]) + (1 - p h) * Z (h ++ [false]) :=
            add_le_add
              (mul_le_mul_of_nonneg_left (ih _) hp0)
              (mul_le_mul_of_nonneg_left (ih _) hp1)
          _ ≤ Z h := hZ.2 h

/-- Finite-tree Ville inequality in its usual probability form. -/
lemma hitProbability_le_inv {p Z : History → ℝ}
    (hp : ValidLaw p) (hZ : IsTreeSupermartingale p Z)
    {event : History → Prop} [DecidablePred event]
    {a : ℝ} (ha : 0 < a) (h_event : ∀ h, event h → a ≤ Z h)
    (depth : ℕ) (h : History) :
    hitProbability p event depth h ≤ Z h / a := by
  rw [le_div_iff₀ ha]
  simpa [mul_comm] using
    threshold_mul_hitProbability_le hp hZ ha.le h_event depth h

/-- Exponential supermartingale used for upper deviations of the success
count relative to its compensator. -/
def upperProcess (p : History → ℝ) (θ : ℝ) (h : History) : ℝ :=
  Real.exp (θ * successes h - (Real.exp θ - 1) * compensator p h)

/-- Exponential supermartingale used for lower deviations. -/
def lowerProcess (p : History → ℝ) (θ : ℝ) (h : History) : ℝ :=
  Real.exp (-θ * successes h + (1 - Real.exp (-θ)) * compensator p h)

lemma exp_neg_mul_one_add_le_one (z : ℝ) :
    Real.exp (-z) * (1 + z) ≤ 1 := by
  have h := Real.add_one_le_exp z
  have hpos : 0 ≤ Real.exp (-z) := (Real.exp_pos _).le
  calc
    Real.exp (-z) * (1 + z) ≤ Real.exp (-z) * Real.exp z :=
      mul_le_mul_of_nonneg_left (by simpa [add_comm] using h) hpos
    _ = 1 := by rw [← Real.exp_add]; simp

lemma upperProcess_supermartingale {p : History → ℝ} (hp : ValidLaw p) (θ : ℝ) :
    IsTreeSupermartingale p (upperProcess p θ) := by
  constructor
  · intro h
    exact (Real.exp_pos _).le
  · intro h
    let q := Real.exp θ - 1
    let z := p h * q
    have htrue :
        upperProcess p θ (h ++ [true]) =
          upperProcess p θ h * Real.exp (θ - z) := by
      simp only [upperProcess, successes_snoc, if_true, compensator_snoc]
      rw [← Real.exp_add]
      congr 1
      dsimp [q, z]
      ring
    have hfalse :
        upperProcess p θ (h ++ [false]) =
          upperProcess p θ h * Real.exp (-z) := by
      simp only [upperProcess, successes_snoc, if_false, add_zero, compensator_snoc]
      rw [← Real.exp_add]
      congr 1
      dsimp [q, z]
      ring
    rw [htrue, hfalse]
    have hexpθ : Real.exp (θ - z) = Real.exp (-z) * Real.exp θ := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexpθ]
    calc
      p h * (upperProcess p θ h * (Real.exp (-z) * Real.exp θ)) +
          (1 - p h) * (upperProcess p θ h * Real.exp (-z))
          = upperProcess p θ h * (Real.exp (-z) * (1 + z)) := by
            dsimp [z, q]
            ring
      _ ≤ upperProcess p θ h * 1 :=
        mul_le_mul_of_nonneg_left (exp_neg_mul_one_add_le_one z)
          (Real.exp_pos _).le
      _ = upperProcess p θ h := mul_one _

lemma lowerProcess_eq_upperProcess_neg (p : History → ℝ) (θ : ℝ) (h : History) :
    lowerProcess p θ h = upperProcess p (-θ) h := by
  simp only [lowerProcess, upperProcess]
  ring_nf

lemma lowerProcess_supermartingale {p : History → ℝ} (hp : ValidLaw p) (θ : ℝ) :
    IsTreeSupermartingale p (lowerProcess p θ) := by
  rw [show lowerProcess p θ = upperProcess p (-θ) by
    funext h
    exact lowerProcess_eq_upperProcess_neg p θ h]
  exact upperProcess_supermartingale hp (-θ)

@[simp] lemma upperProcess_nil (p : History → ℝ) (θ : ℝ) :
    upperProcess p θ [] = 1 := by
  simp [upperProcess]

@[simp] lemma lowerProcess_nil (p : History → ℝ) (θ : ℝ) :
    lowerProcess p θ [] = 1 := by
  simp [lowerProcess]

/-- Adaptive Bernoulli upper-tail bound.  This is part (i) of the paper's
adaptive concentration lemma, for an arbitrary finite horizon `depth`.

The left side is the probability that at some prefix we have simultaneously
`N ≥ x` and `V ≤ v`. -/
theorem upper_deviation {p : History → ℝ} (hp : ValidLaw p)
    {x v : ℝ} (hxv : v < x) (hv : 0 < v) (depth : ℕ) :
    hitProbability p (fun h => x ≤ successes h ∧ compensator p h ≤ v) depth [] ≤
      Real.exp (-x * Real.log (x / v) + x - v) := by
  let θ := Real.log (x / v)
  let a := Real.exp (x * Real.log (x / v) - x + v)
  have hvx : 0 < x := hv.trans hxv
  have hratio : 0 < x / v := div_pos hvx hv
  have hexpθ : Real.exp θ = x / v := by
    dsimp [θ]
    exact Real.exp_log hratio
  have hθ : 0 ≤ θ := by
    dsimp [θ]
    apply Real.log_nonneg
    apply (le_div_iff₀ hv).2
    simpa using hxv.le
  have ha : 0 < a := Real.exp_pos _
  have hevent : ∀ h,
      (x ≤ successes h ∧ compensator p h ≤ v) → a ≤ upperProcess p θ h := by
    intro h hh
    apply Real.exp_le_exp.mpr
    change x * Real.log (x / v) - x + v ≤
      θ * successes h - (Real.exp θ - 1) * compensator p h
    rw [hexpθ]
    have hq : 0 ≤ x / v - 1 := by
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hv).2
      simpa using hxv.le
    calc
      x * Real.log (x / v) - x + v
          = θ * x - (x / v - 1) * v := by
            dsimp [θ]
            field_simp
            ring
      _ ≤ θ * successes h - (x / v - 1) * compensator p h := by
        exact sub_le_sub
          (mul_le_mul_of_nonneg_left hh.1 hθ)
          (mul_le_mul_of_nonneg_left hh.2 hq)
  have hville := hitProbability_le_inv hp (upperProcess_supermartingale hp θ)
    ha hevent depth []
  rw [upperProcess_nil] at hville
  calc
    hitProbability p (fun h => x ≤ successes h ∧ compensator p h ≤ v) depth []
        ≤ 1 / a := hville
    _ = Real.exp (-x * Real.log (x / v) + x - v) := by
      dsimp [a]
      rw [one_div, ← Real.exp_neg]
      congr 1 <;> ring

/-- Positive constant appearing in part (ii), with the paper's choice
`θ = log 2`. -/
def lowerRate : ℝ := 1 / 2 - Real.log 2 / 4

lemma lowerRate_pos : 0 < lowerRate := by
  have hlog2 : Real.log 2 < 1 := by
    have h2exp : (2 : ℝ) < Real.exp 1 := by
      have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      norm_num at h ⊢
      exact h
    exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < (2 : ℝ))).2 h2exp
  dsimp [lowerRate]
  linarith

/-- Adaptive Bernoulli lower-tail bound.  This is part (ii) of the paper's
adaptive concentration lemma, again for an arbitrary finite horizon.

The left side is the probability that at some prefix `V ≥ v` while
`N ≤ V/4`. -/
theorem lower_deviation {p : History → ℝ} (hp : ValidLaw p)
    {v : ℝ} (hv : 0 ≤ v) (depth : ℕ) :
    hitProbability p
        (fun h => v ≤ compensator p h ∧ successes h ≤ compensator p h / 4)
        depth [] ≤
      Real.exp (-lowerRate * v) := by
  let θ := Real.log 2
  let a := Real.exp (lowerRate * v)
  have hθ : 0 ≤ θ := by
    dsimp [θ]
    exact Real.log_nonneg (by norm_num)
  have hexpneg : Real.exp (-θ) = (1 : ℝ) / 2 := by
    dsimp [θ]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have ha : 0 < a := Real.exp_pos _
  have hevent : ∀ h,
      (v ≤ compensator p h ∧ successes h ≤ compensator p h / 4) →
        a ≤ lowerProcess p θ h := by
    intro h hh
    apply Real.exp_le_exp.mpr
    change lowerRate * v ≤
      -θ * successes h + (1 - Real.exp (-θ)) * compensator p h
    rw [hexpneg]
    have hcomp : 0 ≤ compensator p h := hv.trans hh.1
    calc
      lowerRate * v ≤ lowerRate * compensator p h :=
        mul_le_mul_of_nonneg_left hh.1 lowerRate_pos.le
      _ = -(Real.log 2) * (compensator p h / 4) +
            (1 - (1 : ℝ) / 2) * compensator p h := by
          dsimp [lowerRate]
          ring
      _ ≤ -θ * successes h + (1 - (1 : ℝ) / 2) * compensator p h := by
        apply add_le_add_right
        exact mul_le_mul_of_nonpos_left hh.2 (neg_nonpos.mpr hθ)
  have hville := hitProbability_le_inv hp (lowerProcess_supermartingale hp θ)
    ha hevent depth []
  rw [lowerProcess_nil] at hville
  calc
    hitProbability p
        (fun h => v ≤ compensator p h ∧ successes h ≤ compensator p h / 4)
        depth [] ≤ 1 / a := hville
    _ = Real.exp (-lowerRate * v) := by
      dsimp [a]
      rw [one_div, ← Real.exp_neg]
      congr 1
      ring

end ProbabilisticSerial.AdaptiveBernoulli
