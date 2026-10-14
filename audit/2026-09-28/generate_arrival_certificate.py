#!/usr/bin/env python3
"""Generate Lean source from the 21-test rational arrival certificate.

The Python assertions are a diagnostic only. The generated Lean file proves
the rational enclosure checks using norm_num and the real analysis soundness
lemmas in FiniteArrivalCertificate. No floating point is used here.
"""
import json
import math
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
d = json.loads((HERE / 'arrival-certificate-21.json').read_text())
theta, grid, mass, allowance, price = [list(map(F, d[k])) for k in
    ('theta', 'grid', 'mass', 'log_allowance', 'price')]
lower = [list(map(F, row)) for row in d['lower_cost']]
assert len(theta) == len(mass) == len(price) == 21
assert grid == [F(1)-F(1,2**j) for j in range(21)] + [F(1)]
for i in range(21):
    for j in range(22):
        x = theta[i] * max(grid[i+1]-grid[j], F(0))
        assert 1 <= (1-lower[i][j])*sum(x**k/F(math.factorial(k)) for k in range(9))
for i in range(20):
    assert 1 <= theta[i]*(1-grid[i+1])*sum(allowance[i]**k/F(math.factorial(k)) for k in range(12))
for j in range(22):
    assert 1-grid[j] <= sum(mass[i]*lower[i][j] for i in range(21))
assert sum(mass[i]*price[i] for i in range(21)) < 5

def lean(x):
    return str(x.numerator) if x.denominator == 1 else f'({x.numerator} / {x.denominator})'

def vec(xs):
    return '![' + ', '.join(map(lean, xs)) + ']'

source = '''import FiniteArrivalCertificate

/-!
# A 21-test below-five certificate for finite atomic exposure

Generated from exact rational data by generate_arrival_certificate.py.
The conclusion is for exposure data satisfying the displayed arrival bounds;
the separate probabilistic connection to replica PS remains necessary.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.FiniteFiveCertificate

open FiniteAtomicExposure FiniteArrivalCertificate FiniteExposure

def grid (j : ℕ) : ℝ := if j ≤ 20 then 1 - (1 / 2 : ℝ) ^ j else 1
def horizon (i : Fin 21) : ℝ := grid (i.val + 1)
'''
def table(name, xs):
    out = f'def {name} (i : Fin {len(xs)}) : ℝ :=\n  match i.val with\n'
    out += ''.join(f'  | {i} => {lean(x)}\n' for i,x in enumerate(xs))
    return out + '  | _ => 0\n'

source += table('parameter', theta)
source += table('mass', mass)
source += table('price', price)
source += table('allowance', allowance)
source += 'def lowerCost (i : Fin 21) (j : Fin 22) : ℝ :=\n  match i.val, j.val with\n'
source += ''.join(f'  | {i}, {j} => {lean(x)}\n' for i,row in enumerate(lower) for j,x in enumerate(row) if x)
source += '  | _, _ => 0\n\n'
source += '''lemma parameter_pos (i : Fin 21) : 0 < parameter i := by
  fin_cases i <;> norm_num [parameter]

lemma mass_nonneg (i : Fin 21) : 0 ≤ mass i := by
  fin_cases i <;> norm_num [mass]

lemma kernel_lower (i : Fin 21) (j : Fin 22) :
    lowerCost i j ≤ kernel (parameter i) (horizon i) (grid j.val) := by
  have hb : 0 < 1 - lowerCost i j := by
    fin_cases i <;> fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost i j) *
      ∑ k ∈ Finset.range 9,
        (parameter i * max (horizon i - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases i <;> fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos i).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma endpoint_check (j : Fin 22) :
    1 - grid j.val ≤ ∑ i : Fin 21, mass i * lowerCost i j := by
  fin_cases j <;>
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [grid, mass, lowerCost]

theorem domination (r : ℝ) (hr : 0 ≤ r) :
    max (1 - r) 0 ≤ combination mass parameter horizon r := by
  apply grid_domination mass parameter horizon mass_nonneg
    (fun i => (parameter_pos i).le) grid 20 _ _ _ _ _ r hr
  · norm_num [grid]
  · norm_num [grid]
  · intro j hj
    interval_cases j <;> norm_num [grid]
  · intro j hj i
    interval_cases j <;> fin_cases i <;> norm_num [horizon, grid]
  · intro j hj
    let k : Fin 22 := ⟨j, by omega⟩
    exact (endpoint_check k).trans (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (kernel_lower i k) (mass_nonneg i))

lemma allowance_log_bound (i : Fin 20) :
    -Real.log (parameter i.castSucc * (1 - horizon i.castSucc)) ≤ allowance i := by
  have hx : 0 ≤ allowance i := by fin_cases i <;> norm_num [allowance]
  have hb : 0 < parameter i.castSucc * (1 - horizon i.castSucc) := by
    fin_cases i <;> norm_num [parameter, horizon, grid]
  have hp : 1 ≤ (parameter i.castSucc * (1 - horizon i.castSucc)) *
      ∑ k ∈ Finset.range 12, allowance i ^ k / (k.factorial : ℝ) := by
    fin_cases i <;>
      norm_num [parameter, horizon, grid, allowance, Finset.sum_range_succ, Nat.factorial]
  have h := (Real.le_log_iff_exp_le hb).2 (exp_neg_le_of_taylor hx hb 12 hp)
  linarith

lemma interior_horizon_bounds (i : Fin 20) :
    0 < horizon i.castSucc ∧ horizon i.castSucc < 1 := by
  fin_cases i <;> norm_num [horizon, grid]

lemma phi_le_price (i : Fin 20) :
    phi (parameter i.castSucc) (1 - horizon i.castSucc) ≤ price i.castSucc := by
  have hs : ¬parameter i.castSucc ≤ 1 := by fin_cases i <;> norm_num [parameter]
  have hm : parameter i.castSucc ≤ 1 / (1 - horizon i.castSucc) := by
    fin_cases i <;> norm_num [parameter, horizon, grid]
  have hu : 0 < 1 - horizon i.castSucc := by fin_cases i <;> norm_num [horizon, grid]
  have hp : price i.castSucc = parameter i.castSucc - 1 + allowance i := by
    fin_cases i <;> norm_num [price, parameter, allowance]
  rw [phi, if_neg hs, if_pos hm, hp]
  have h := allowance_log_bound i
  rw [Real.log_mul (parameter_pos _).ne' hu.ne'] at h
  linarith

lemma log_ten_upper : Real.log 10 ≤ (2302586 / 1000000 : ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10)).2
  have h := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 2302586 / 1000000) 16
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem weighted_price_lt_five : (∑ i : Fin 21, mass i * price i) < 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [mass, price]

/-- The analytic below-five certificate. Its hypotheses are the arrival
inequalities; it is not an unconditional theorem about the PS mechanism. -/
theorem value_lt_five {ι : Type*} [Fintype ι] (D : Data ι)
    (hinterior : ∀ t, 0 < t → t < 1 → ∀ θ, 0 < θ → cost D θ t ≤ phi θ (1 - t))
    (hendpoint : cost D 1600 1 ≤ 1600 + 80 * Real.log 10) :
    value D 1 < 5 := by
  apply lt_of_le_of_lt (value_le_certificate D mass parameter horizon price
    mass_nonneg domination ?_) weighted_price_lt_five
  intro i
  by_cases hi : i.val < 20
  · let j : Fin 20 := ⟨i.val, hi⟩
    have hij : j.castSucc = i := Fin.ext rfl
    have ht := interior_horizon_bounds j
    rw [← hij]
    exact (hinterior _ ht.1 ht.2 _ (parameter_pos _)).trans (phi_le_price j)
  · have hi20 : i = 20 := Fin.ext (by omega)
    subst i
    change cost D 1600 1 ≤ (11151293 / 6250 : ℝ)
    linarith [log_ten_upper]

end ProbabilisticSerial.FiniteFiveCertificate
'''
start = source.index('lemma kernel_lower (i : Fin 21)')
end = source.index('lemma endpoint_check', start)
block = source[start:end]
rows = []
for i in range(21):
    body = block.replace('lemma kernel_lower (i : Fin 21) (j : Fin 22)', f'lemma kernel_lower_{i} (j : Fin 22)')
    body = body.replace('lowerCost i j', f'lowerCost (⟨{i}, by decide⟩ : Fin 21) j')
    body = body.replace('parameter i', f'parameter (⟨{i}, by decide⟩ : Fin 21)')
    body = body.replace('horizon i', f'horizon (⟨{i}, by decide⟩ : Fin 21)')
    body = body.replace('parameter_pos i', f'parameter_pos (⟨{i}, by decide⟩ : Fin 21)')
    body = body.replace('fin_cases i <;> fin_cases j', 'fin_cases j')
    rows.append(body)
assembly = """lemma kernel_lower (i : Fin 21) (j : Fin 22) :
    lowerCost i j ≤ kernel (parameter i) (horizon i) (grid j.val) := by
  fin_cases i
""" + ''.join(f'  · exact kernel_lower_{i} j\n' for i in range(21)) + '\n'
source = source[:start] + ''.join(rows) + assembly + source[end:]
(ROOT / 'FiniteFiveCertificate.lean').write_text(source)
print('Generated FiniteFiveCertificate.lean; Lean must still check it.')
