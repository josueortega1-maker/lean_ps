import FixedQuotaLowerBound

/-!
# Uniform asymptotics for bounded positive quotas

The fixed-quota limit is uniform over every finite set of positive quotas.
Consequently, the same asymptotic holds when the quota varies with the market,
provided it remains bounded and the number of types tends to infinity.
The expectation is the original `ReplicaPS.expectedPS` throughout.
-/

noncomputable section
open Filter
open scoped Topology

namespace ProbabilisticSerial.BoundedQuotaAsymptotics
open StandardLogStar

private theorem eventually_mem_uniform (Q : ℕ) {s : Set ℝ}
    (hs : s ∈ 𝓝 (1 : ℝ)) :
    ∀ᶠ m : ℕ in atTop, ∀ q : ℕ, 0 < q → q ≤ Q →
      ReplicaPS.expectedPS m q / (logStar m : ℝ) ∈ s := by
  induction Q with
  | zero =>
      exact Eventually.of_forall (by intros; omega)
  | succ Q ih =>
      filter_upwards [ih,
        (FixedQuotaLowerBound.expectedPS_div_logStar_tendsto_one (Q + 1)
          (by omega)).eventually hs] with m hm hlast
      intro q hq hQ
      by_cases h : q ≤ Q
      · exact hm q hq h
      · have heq : q = Q + 1 := by omega
        simpa only [heq] using hlast

/-- The normalized expectation approaches one uniformly over positive quotas
bounded by any fixed `Q`. In particular, the threshold in market size can be
chosen independently of the quota in this finite range. -/
theorem eventually_expectedPS_div_logStar_close (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ q : ℕ, 0 < q → q ≤ Q →
      |ReplicaPS.expectedPS m q / (logStar m : ℝ) - 1| < ε := by
  have hnbhd : Set.Ioo (1 - ε) (1 + ε) ∈ 𝓝 (1 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [eventually_mem_uniform Q hnbhd] with m hm
  intro q hq hQ
  obtain ⟨hlower, hupper⟩ := hm q hq hQ
  rw [abs_lt]
  constructor <;> linarith

/-- Bounded positive quotas may vary arbitrarily along a growing family of
markets. The bound `Q` is fixed; no convergence of the quotas is required. -/
theorem expectedPS_div_logStar_tendsto_one
    {α : Type*} {l : Filter α} {m q : α → ℕ}
    (hm : Tendsto m l atTop) (Q : ℕ)
    (hq : ∀ᶠ k in l, 0 < q k ∧ q k ≤ Q) :
    Tendsto (fun k => ReplicaPS.expectedPS (m k) (q k) / (logStar (m k) : ℝ))
      l (𝓝 1) := by
  apply tendsto_def.mpr
  intro s hs
  filter_upwards [hm.eventually (eventually_mem_uniform Q hs), hq] with k hmk hqk
  exact hmk (q k) hqk.1 hqk.2

end ProbabilisticSerial.BoundedQuotaAsymptotics
