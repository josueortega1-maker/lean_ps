# Fixed-quota lower-bound formalization

The manuscript's fixed-quota lower asymptotic is formalized for the unchanged
`ReplicaPS.expectedPS`: the expected rank of actual grouped-copy PS
allocations under independent uniform rankings of types.

The public declarations in `FixedQuotaLowerBound.lean` are:

```lean
theorem expectedPS_div_logStar_tendsto_one (q : ℕ) (hq : 0 < q) :
    Tendsto (fun m : ℕ => ReplicaPS.expectedPS m q / (logStar m : ℝ))
      atTop (𝓝 1)

theorem eventually_expectedPS_ge (q : ℕ) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, (1 - ε) * (logStar m : ℝ) ≤ ReplicaPS.expectedPS m q
```

Here `logStar` is `StandardLogStar.logStar`, with the natural-log convention.
The quota is fixed before `m` tends to infinity. The market-size threshold
may depend on both the quota and the error tolerance; no uniform lower
asymptotic for a growing quota is asserted.

## Proof chain

| Step | Modules |
| --- | --- |
| Exact coupon moments, nonpositive covariance, variance, and lower tail | `CouponLowerBound` |
| Exact mean best rank, second moment, lower exponential estimate, and simultaneous concentration on the original profile sample | `UniformLowerRank`, `ReplicaLowerRank` |
| Uniform raw labels, rejected exhausted types, and the exact original conditional profile law | `ReplicaRawStep`, `ReplicaRawProcess` |
| Predictable clocks, independent raw blocks, subset-count tails, and survivor entries | `ReplicaRawClock`, `UniformRawPrefixes`, `RawSubsetCounts`, `ReplicaSurvivorEntries` |
| Untouched types retain full quota; predictable weighted hits average to raw band cost | `ReplicaUntouched`, `CouponUntouched`, `ReplicaRawBands` |
| Actual consumed capacity, residual supply, and expected cost in each exponential band | `ReplicaConsumptionLower`, `RawSurvivorBound`, `ReplicaBandLower` |
| Raw cost as an actual PS phase sum; rank conversion retaining both exceptional-event costs | `ReplicaRawRankBridge`, `RawPrefixGood`, `ReplicaRawCostRank` |
| Combined finite-market lower inequality with explicit errors | `FiniteLowerBound` |
| Small-set entropy, rounded cutoffs, vanishing errors, and band count equal to log-star up to a fixed additive constant | `LowerBoundEntropy`, `LowerBoundErrors`, `LowerBoundCutoffs`, `LowerBoundBandErrors`, `LowerBoundBands`, `LowerBoundSchedule`, `LowerBoundMarket` |
| Fixed parameters for arbitrary coefficient loss and the final asymptotic | `FixedQuotaParameters`, `FixedQuotaLowerBound` |

`ReplicaRawProcess.raw_prefix_profile_marginal` supplies the original profile
law. `ReplicaConsumptionLower.expected_bandCost_lower` and
`ReplicaRawCostRank.expectedPS_lower_from_rawCost` connect raw draws to
actual PS capacity and rank. The proof does not assume independence between
endogenous active sets and preferences, or assume the desired PS lower bound.

The formal proof uses the second-moment constant `16(1+e)` and a fixed
minimum active-set cutoff depending on the error tolerance. These simplify
the estimates without changing the manuscript's statement. For `0<η<1`,
`eventually_lower_with_loss` proves, for sufficiently large `m`,

```text
((1−η)²/(1+η)) * logStar m − C(q,η) ≤ ReplicaPS.expectedPS m q.
```

Its leading coefficient tends to one as `η` tends to zero. The existing
finite upper bound `logStar m + 17/5` completes the ratio limit.

## Verification and remaining scope

All new modules are roots in `lakefile.toml`. The final theorems and principal
bridges are included in `AxiomAudit.lean`. [PROOF_MAP.md](PROOF_MAP.md) lists
the declarations; [VERIFICATION.md](VERIFICATION.md) records the exact
checked sources, workflow log, and declaration footprints.

This completes the fixed-quota lower-bound clause. The quota-uniform tail
and PS–RP absolute-gap quota-threshold equivalence remain open; see
[THEOREM1_STATUS.md](THEOREM1_STATUS.md). The manuscript and the earlier
Lean upper-bound proof are unchanged by this formalization.
