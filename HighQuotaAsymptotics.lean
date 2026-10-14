import ReplicaQuotaBound
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# High-quota convergence for the actual PS mechanism

These results concern the existing `ReplicaPS.expectedPS`, not an abstract
rank function. They prove the PS half of the high-quota regime, including
fixed-type replication. No RP convergence or full threshold equivalence is
asserted here.
-/

noncomputable section

open Filter
open scoped Topology

namespace ProbabilisticSerial.HighQuotaAsymptotics

open ReplicaPS ReplicaQuotaBound

/-- Arbitrary market sequences are allowed; positivity is required only
for all sufficiently late terms. -/
theorem expectedPS_tendsto_one_of_log_div_quota_tendsto_zero
    (m q : ℕ → ℕ)
    (hm : ∀ᶠ k in atTop, 0 < m k)
    (hq : ∀ᶠ k in atTop, 0 < q k)
    (ha : Tendsto (fun k => Real.log (m k : ℝ) / (q k : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun k => ReplicaPS.expectedPS (m k) (q k)) atTop (𝓝 1) := by
  have hsqrt : Tendsto
      (fun k => Real.sqrt (2 * (Real.log (m k : ℝ) / (q k : ℝ))))
      atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (2 : ℝ))).mul ha).sqrt
  have hupper : Tendsto
      (fun k => 1 + Real.sqrt (2 * (Real.log (m k : ℝ) / (q k : ℝ))) +
        Real.log (m k : ℝ) / (q k : ℝ)) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hsqrt).add ha
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [hm, hq] with k hmk hqk
    exact (ReplicaPS.expectedPS_bounds (m k) (q k) hmk hqk).1
  · filter_upwards [hm, hq] with k hmk hqk
    exact expectedPS_le_one_add_sqrt_add (m k) (q k) hmk hqk

/-- With a fixed positive number of types, increasing the common integer
quota makes PS's expected type rank converge to one. -/
theorem expectedPS_fixed_types_tendsto_one (m : ℕ) (hm : 0 < m) :
    Tendsto (ReplicaPS.expectedPS m) atTop (𝓝 1) := by
  apply expectedPS_tendsto_one_of_log_div_quota_tendsto_zero
    (fun _ => m) (fun q => q)
  · exact Filter.Eventually.of_forall (fun _ => hm)
  · exact eventually_gt_atTop 0
  · exact tendsto_natCast_atTop_atTop.const_div_atTop (Real.log (m : ℝ))

/-- The PS conclusion holds whenever copies grow faster than the logarithm
of the number of types; a separate assumption that types diverge is unnecessary. -/
theorem expectedPS_tendsto_one_of_quota_div_log_tendsto_atTop
    (m q : ℕ → ℕ)
    (hm : ∀ᶠ k in atTop, 0 < m k)
    (hq : ∀ᶠ k in atTop, 0 < q k)
    (hquota : Tendsto (fun k => (q k : ℝ) / Real.log (m k : ℝ)) atTop atTop) :
    Tendsto (fun k => ReplicaPS.expectedPS (m k) (q k)) atTop (𝓝 1) := by
  apply expectedPS_tendsto_one_of_log_div_quota_tendsto_zero m q hm hq
  simpa only [Function.comp_def, inv_div] using
    (tendsto_inv_atTop_zero.comp hquota)

end ProbabilisticSerial.HighQuotaAsymptotics
