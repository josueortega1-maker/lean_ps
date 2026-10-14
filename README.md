# Verification of Theorem 1

This repository contains a **Lean 4 formal verification of the expected-rank
parts of Theorem 1's proof** in **Josué Ortega and Geng Zhao,
*The Remarkable Efficiency of the Probabilistic Serial Mechanism***.

[Paper](https://www.josueortega.com/PS_versus_RP_simplified.pdf) 

The finite expected-rank bound and the fixed-quota asymptotic are verified for
positive integer quotas. The high-probability conclusion is verified in the
one-copy case.

This project formalizes expected **type ranks** under probabilistic serial (PS)
with `m` types, positive integer quota `q`, and `m*q` agents with independent
uniform strict rankings. `ReplicaPS.expectedPS` is computed from actual
allocations of grouped copies; it is not defined through an upper bound.

The core results are the unconditional finite bound

```text
expectedPS m q < logStar m + 17/5
```

for every positive integer `m,q`, and

```text
expectedPS m q / logStar m → 1     (m → ∞, each fixed q > 0).
```

The natural-log convention for `logStar` matches the manuscript. The exact
rational `17/5` is 3.4. The separate certificate also proves expected rank
below five when `m ≤ 10^80`, for every positive integer quota.

## Additional verified results

The new quota-sensitive analysis retains `log(m)/q` in the endpoint estimate
and derives, with `a = log(m)/q`,

```text
expectedPS m q ≤ 1 + sqrt(2*a) + a.
```

It proves PS expected rank tends to one along any eventually positive market
sequence with `log(m)/q → 0`, including fixed-type replication. The rank bridge
also retains the finite-market factor `1−1/m`. The fixed-quota log-star limit
is extended uniformly to arbitrary varying quotas in any fixed positive
bounded range.

**The quota-uniform tail and the two general PS–RP threshold equivalences
are not fully formalized.** The latter belong to Theorem 2 of the revised
manuscript. See [THEOREM1_STATUS.md](THEOREM1_STATUS.md) for the exact
coverage of both theorems and the next mathematical obligations.

## Read the public statements

| File | Result |
| --- | --- |
| `PaperReplicaInterface.lean` | Unconditional `+3.4` and below-five bounds |
| `FixedQuotaLowerBound.lean` | Fixed positive quota: expected rank / log-star tends to one |
| `ReplicaQuotaBound.lean` | Exponential endpoint envelope and explicit quota bound |
| `HighQuotaAsymptotics.lean` | High-quota PS convergence to rank one |
| `BoundedQuotaAsymptotics.lean` | Uniform limit over bounded positive quotas |
| `ReplicaExpectedRank.lean` | Actual allocation-to-exposure bridge, including the affine refinement |
| `PaperTheoremOne.lean` | Historical one-copy tail and PS/RP ratio results |
| `TheoremContracts.lean` | Exact public statement and quantifier checks |

[PROOF_MAP.md](PROOF_MAP.md) retains the detailed historical proof map.
[LOWER_BOUND_STATUS.md](LOWER_BOUND_STATUS.md) explains the actual-profile lower
proof. The finite numerical certificate differs from the paper's sharper
1920-step computation; that sharper computation is not kernel verified.

## Reproduce verification

Use the supplied Lean 4.19.0 toolchain and pinned mathlib manifest:

```bash
lake exe cache get
python3 scripts/verify.py --clean
```

Python 3.11 or newer is required. The verification command builds every
project module, checks the exact public contracts and pinned environment,
rejects unbuilt sources, and checks every safe project declaration against the axiom allowlist
`propext`, `Classical.choice`, `Quot.sound`. Missing checks and unexpected
axioms fail the run. Logs and input hashes are written to
`verification-output/verification.json` and companion log files, including on
failure. The same verification gates are used by CI. Omit `--clean` for
incremental builds.

The follow-up audit is recorded in [FULL_AUDIT.md](FULL_AUDIT.md).
`ReplicaRP.profileAverageRank` makes the paper's priority-averaged RP statistic
explicit, with a proved equality to the existing joint expectation.

