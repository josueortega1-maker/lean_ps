import ReplicaExpectedRank
import FiniteQuotaEnvelope

/-!
# An unconditional quota-sensitive PS expectation bound

The existing actual replica trace has terminal exponential cost at most
`theta + log(m)/q`. Keeping the factor `1/q`, rather than weakening it to
one, gives a finite bound that approaches rank one under fast replication.
This bound is coarser than the manuscript's supply-identity estimate and
alone does not establish strict separation in the critical regime.
-/

noncomputable section

namespace ProbabilisticSerial.ReplicaQuotaBound

open ReplicaPS ReplicaChoiceMachine FiniteAtomicExposure FiniteQuotaEnvelope

theorem expectedPS_le_exponential (m q : ℕ) (hm : 0 < m) (hq : 0 < q)
    {θ : ℝ} (hθ : 0 < θ) :
    ReplicaPS.expectedPS m q ≤
      (θ + Real.log (m : ℝ) / (q : ℝ)) / (1 - Real.exp (-θ)) := by
  letI : Nonempty (Fin (m * q)) := ⟨⟨0, Nat.mul_pos hm hq⟩⟩
  exact (expectedPS_le_actualExposure (m := m) (q := q)).trans
    (value_one_le_exponential (actualExposure (m := m) (q := q)) hθ
      (actualExposure_cost_endpoint_quota_le θ hθ))

/-- A quota-sensitive bound on the actual expected type rank, with no
probabilistic or exposure hypotheses left to discharge. -/
theorem expectedPS_le_one_add_sqrt_add (m q : ℕ) (hm : 0 < m) (hq : 0 < q) :
    ReplicaPS.expectedPS m q ≤
      1 + Real.sqrt (2 * (Real.log (m : ℝ) / (q : ℝ))) +
        Real.log (m : ℝ) / (q : ℝ) := by
  by_cases hmone : m = 1
  · subst m
    simp [ReplicaPS.expectedPS_one_type q hq]
  · have hmgt : 1 < (m : ℝ) := by
      exact_mod_cast (show 1 < m by omega)
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have ha : 0 < Real.log (m : ℝ) / (q : ℝ) :=
      div_pos (Real.log_pos hmgt) hqR
    have hθ : 0 < Real.sqrt (2 * (Real.log (m : ℝ) / (q : ℝ))) :=
      Real.sqrt_pos.2 (by positivity)
    exact (expectedPS_le_exponential m q hm hq hθ).trans
      (exponential_envelope_le ha)

end ProbabilisticSerial.ReplicaQuotaBound
