import BoundedQuotaAsymptotics
import HighQuotaAsymptotics
import ReplicaQuotaBound
import FixedQuotaLowerBound
import ReplicaRP

/-!
# Public theorem contracts

These examples check the literal public statements, including positivity and
fixed-quota quantifiers. Unlike an axiom footprint alone, they reject changing
a result into an implication with an additional unproved process premise.
They are regression contracts, not additional mathematical results.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
open ProbabilisticSerial

example (m q : ℕ) :
    ReplicaRP.expectedRP m q =
      𝔼 profile ∈ ReplicaPS.profileSample m q, ReplicaRP.profileAverageRank profile :=
  ReplicaRP.expectedRP_eq_expect_profileAverageRank m q

example (m q : ℕ) (hm : 0 < m) (hq : 0 < q) :
    ReplicaPS.expectedPS m q < (StandardLogStar.logStar m : ℝ) + 17 / 5 :=
  PaperReplicaInterface.expectedPS_lt_logStar_add_three_point_four m q hm hq

example (m q : ℕ) (hm : 0 < m) (hq : 0 < q) (hmax : m ≤ 10 ^ 80) :
    ReplicaPS.expectedPS m q < 5 :=
  PaperReplicaInterface.expectedPS_lt_five m q hm hq hmax

example (q : ℕ) (hq : 0 < q) :
    Tendsto (fun m : ℕ => ReplicaPS.expectedPS m q /
      (StandardLogStar.logStar m : ℝ)) atTop (𝓝 1) :=
  FixedQuotaLowerBound.expectedPS_div_logStar_tendsto_one q hq

example (q : ℕ) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      (1 - ε) * (StandardLogStar.logStar m : ℝ) ≤ ReplicaPS.expectedPS m q :=
  FixedQuotaLowerBound.eventually_expectedPS_ge q hq hε

example {m q : ℕ} [Nonempty (Fin (m * q))] :
    ReplicaPS.expectedPS m q ≤ 1 + (1 - 1 / (m : ℝ)) *
      (FiniteAtomicExposure.value (ReplicaChoiceMachine.actualExposure (m := m) (q := q)) 1 - 1) :=
  ReplicaChoiceMachine.expectedPS_le_actualExposure_affine

example (m q : ℕ) (hm : 0 < m) (hq : 0 < q) :
    ReplicaPS.expectedPS m q ≤ 1 + Real.sqrt (2 * (Real.log (m : ℝ) / (q : ℝ))) +
      Real.log (m : ℝ) / (q : ℝ) :=
  ReplicaQuotaBound.expectedPS_le_one_add_sqrt_add m q hm hq

example (m q : ℕ → ℕ) (hm : ∀ᶠ k in atTop, 0 < m k)
    (hq : ∀ᶠ k in atTop, 0 < q k)
    (ha : Tendsto (fun k => Real.log (m k : ℝ) / (q k : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun k => ReplicaPS.expectedPS (m k) (q k)) atTop (𝓝 1) :=
  HighQuotaAsymptotics.expectedPS_tendsto_one_of_log_div_quota_tendsto_zero m q hm hq ha

example (m q : ℕ → ℕ) (hm : ∀ᶠ k in atTop, 0 < m k)
    (hq : ∀ᶠ k in atTop, 0 < q k)
    (hquota : Tendsto (fun k => (q k : ℝ) / Real.log (m k : ℝ)) atTop atTop) :
    Tendsto (fun k => ReplicaPS.expectedPS (m k) (q k)) atTop (𝓝 1) :=
  HighQuotaAsymptotics.expectedPS_tendsto_one_of_quota_div_log_tendsto_atTop m q hm hq hquota

example {α : Type*} {l : Filter α} {m q : α → ℕ}
    (hm : Tendsto m l atTop) (Q : ℕ)
    (hq : ∀ᶠ k in l, 0 < q k ∧ q k ≤ Q) :
    Tendsto (fun k => ReplicaPS.expectedPS (m k) (q k) /
      (StandardLogStar.logStar (m k) : ℝ)) l (𝓝 1) :=
  BoundedQuotaAsymptotics.expectedPS_div_logStar_tendsto_one hm Q hq
