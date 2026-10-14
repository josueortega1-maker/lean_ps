# Coverage of the revised manuscript

This status uses the 14 October 2026 revision supplied as
`Paper_JPE_revised(1).tex` (SHA-256
`9a82ff8b4a8ae7d5931775c010ef81e6878357af1cc7e6e3524eb30ecb0cfdd2`). Its Theorem 1 is `thm:main`; its comparison theorem
is Theorem 2, `thm:replica`. Earlier records under `audit/2026-09-28` and
`audit/2026-10-07` refer to earlier manuscript arrangements.

## What the statements mean

All replica results below concern `ReplicaPS.expectedPS m q`: average
original type rank of actual PS allocations under independent uniform type
rankings, with `m*q` agents and `q` ordered copies per type. The lifted copy
rankings are dependent within type blocks. Their law is handled by the
replica revelation proof, not by assuming uniform rankings over all copies.
Quotas in this formalization are positive integers; the paper's extension to
real capacities is not claimed.

## Current coverage

| Revised paper claim | Lean coverage |
| --- | --- |
| Theorem 1: expected PS rank ≤ `log* m + 3.4` | Unconditional for every positive integer `m,q`; `PaperReplicaInterface.expectedPS_le_logStar_add_three_point_four`. The strict version is also proved. |
| Theorem 1: expected PS rank / `log* m` → 1 for each fixed positive quota | `FixedQuotaLowerBound.expectedPS_div_logStar_tendsto_one`, for the original expectation. |
| Theorem 1: tail with absolute constants uniformly over quotas | The one-copy case is proved in `PaperTheoremOne`; the quota-uniform extension remains open. |
| Theorem 2: PS/RP expected-rank ratio → 0 iff `q/log m → 0` | Open for general varying quota. The historical one-copy ratio limit is a special case, not this equivalence. |
| Theorem 2: absolute expected-rank gap → 0 iff `q/log m → ∞` | Open. The new code proves the high-quota PS convergence half, not the RP half or necessity. |
| Critical `q/log m → c ∈ (0,∞)` separation | Open for the actual mechanisms. Scalar implications alone do not establish the required mechanism limits. |
| Sharper quota bound `1+(1−1/m)sqrt(2 log(m)/q)(1+.55/sqrt(q))` | The affine factor is proved. The supply-weighted estimate needed for the sharper quota coefficient is open. |
| Expected rank below five for `m ≤ 10^80` | Unconditional for every positive integer quota, using the existing exact 21-test certificate. |

## Additions established by the review

The exact endpoint bound is now available as
`ReplicaChoiceMachine.actualExposure_cost_endpoint_quota_le`:

```text
cost actualExposure theta 1 ≤ theta + log(m)/q.
```

`FiniteQuotaEnvelope` turns this into a reusable exponential envelope and
optimizes it using `exp(x) ≥ 1+x+x²/2`. The actual mechanism theorem
`ReplicaQuotaBound.expectedPS_le_one_add_sqrt_add` gives

```text
expectedPS m q ≤ 1 + sqrt(2 log(m)/q) + log(m)/q.
```

This is coarser than the sharper manuscript inequality. It is sufficient for
`HighQuotaAsymptotics.expectedPS_tendsto_one_of_log_div_quota_tendsto_zero`.
The companion theorem uses `q/log(m) → ∞` directly, and fixed-type replication
is also exposed. None requires a new process hypothesis.

`ReplicaChoiceMachine.expectedPS_le_actualExposure_affine` retains

```text
expectedPS ≤ 1 + (1−1/m) * (value actualExposure 1−1).
```

Its proof separates the initial rank-one choice from later genuine switches.
At a switch at least one type has disappeared, so the sharper conditional
rank-jump estimate is retained. Earlier weaker APIs remain available.

`BoundedQuotaAsymptotics.expectedPS_div_logStar_tendsto_one` allows arbitrary
varying quotas bounded above by a fixed constant and eventually positive,
along any family of type counts tending to infinity. It follows from uniformity
over a finite set of quotas. It does not extend the fixed-quota lower proof
to unbounded quotas.

## Remaining work that would complete the paper's main claims

1. Derive the replica load and survivor-phase tail estimate with constants
   independent of quota.
2. Prove the supply-weighted identity/estimate needed for the sharper PS quota
   inequality. The endpoint bound alone does not give critical separation.
3. Derive the Gamma-clock representation or an equivalent exact calculation
   from `ReplicaRP.expectedRP`, then prove the RP quota bounds and limits.
4. Combine the low, critical and high regimes, including the subsequence
   arguments for both necessity directions in Theorem 2.

The historical finite proof map remains in
[audit/2026-09-28/Replica_Finite_Bound.md](audit/2026-09-28/Replica_Finite_Bound.md).
The fixed-quota lower chain remains in [LOWER_BOUND_STATUS.md](LOWER_BOUND_STATUS.md).
Use a fresh verification receipt for the reviewed sources; old logs certify
only their recorded hashes.
