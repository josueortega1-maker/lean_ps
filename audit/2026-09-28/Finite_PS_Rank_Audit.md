# Audit of the finite PS rank claims

> Historical baseline audit. Subsequent implementation now proves the
> weighted-arrival process, replica model and type-choice counts, exact Phi
> maximization, the analytic +3.4 phase argument, and a separate 21-test
> analytic certificate below five. See [current coverage](../../THEOREM1_STATUS.md)
> and [verification](../../VERIFICATION.md) for the exact scope. The full
> arbitrary-quota theorem remains open. The new one-copy development supplies
> the actual rank and arrival bridges and the unconditional +3.4/below-five
> statements; see [the one-copy proof chain](One_Copy_Finite_Bound.md).

28 September 2026. Repository: `josueortega1-maker/ProbabilisticSerial`.

## Finding

The September 3 development contains an unexposed finite expectation inequality,
but **neither the additive `log* n + 3.7` bound nor the bound below five follows
from it**. The newer proof requires a weighted-exposure argument absent from the
repository. The gap is mathematical formalization, not just substituting a
constant or checking a table.

The current manuscript read for this audit, `PS_ECMA_finite_clean.tex` version 3,
has sharpened the additive constant further to **3.4**. Its finite certificate
uses 1,920 grid points, 61 rational parameter knots, and terminal parameter
1,600 to bound expected rank below 4.921241 for `1 ≤ n ≤ 10^80`. Proving the
current +3.4 result would imply the requested +3.7 result by rational arithmetic.
This audit does not reinterpret either claim as already formalized.

The numerical computation was reproduced in Python with 70-digit decimal
arithmetic and outward enclosures. All displayed intermediate, terminal, and
partial-allocation bounds matched. This is **numerical reproduction**, not a
Lean certificate or a formal proof of its connection to PS.

## Sources and reproducibility

- Audited source commit: [`11d7b39377d887a200a6f19cbf33e9857db6f5ae`](https://github.com/josueortega1-maker/ProbabilisticSerial/commit/11d7b39377d887a200a6f19cbf33e9857db6f5ae).
- Formalization commit immediately preceding the PDF upload:
  `c64b805f66dd615899fffbf736b3fd3c0fb7751a`.
- All 32 root text files were retrieved at the pinned commit and checked against
  their Git blob hashes. The recursive repository tree contains no `AGENTS.md`.
  All Lean source files were retrieved and searched; dependency-critical
  definitions and proofs, the workflow and checking documentation were read.
- Paper: `PS_ECMA_finite_clean.tex`, version 3, all 1,917 lines read. This is the
  newer supplied manuscript, not the September 3 `PS_ECMA.pdf` in the repository.
  Read-text SHA-256: `50bbcfe2cc53713d74d224e11a621f01e63c074c4886e3aa430045cc89a1cff5`.
- Lean is pinned to 4.19.0; mathlib to
  `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- The September 3 baseline has a successful [repository workflow run](https://github.com/josueortega1-maker/ProbabilisticSerial/actions/runs/33728129955).
  Historical logs are evidence for that baseline only.

The code update is on [`audit/finite-ps-rank-2026-09-28`](https://github.com/josueortega1-maker/ProbabilisticSerial/tree/audit/finite-ps-rank-2026-09-28),
commit `b8a592ce27189dddf04cc8b11693285a541b5e65`. The initial audit left the default
branch unchanged. The subsequent user-requested repository update incorporates
those same verified Lean sources into `main`, with the uploaded manuscript and
`THEOREM1_STATUS.md`. The patch preserves existing theorem statements and adds
four declarations. See that status file for the new theorem's additional quota
equivalence claim, which is outside the September 3 formalization.

## What the existing proof actually gives

Use the repository's one-to-one model, `n` agents and `n` unit-supply goods.
Write

\[
K=\texttt{rankThresholdConstant},\qquad
\delta_n= e^{-n}+e^{-rn}+n^{-3},\qquad
r=\texttt{loadRate}.
\]

The exact source chain is:

| Step | Existing declaration | Role |
|---|---|---|
| Uniform i.i.d. preference profiles | `UniformPermutation.preferenceProfileSample` | Finite uniform product of permutations; the actual sample used by the final theorem. |
| Concrete allocation and rank | `PSProcess.run`, `PSProcess.averageRank` | Defines the PS process and its rank statistic. |
| Rank at most market size | `PSProcess.run_averageRank_le_marketSize` | Bounds the exceptional-event contribution. |
| Good-event rank reduction | `PSProcess.run_rankReduction` | Rank ≤ rank constant × eating integral. |
| Good-event phase integral | `PhaseAdapter.concrete_eatingIntegral_le_logStar` | Eating integral ≤ phase constant × `(1 + psLogStar n)`. |
| Combine deterministic estimates | `ConcreteTheoremOne.rank_le_on_concrete_good` | Rank ≤ `K * (1 + psLogStar n)` on the intersection of good events. |
| Actual profile load law | `PSChoiceMachine.concrete_load_transfer` | Discharges the probability estimate for the concrete process. |
| Assembly-compatible load law | `ConcreteTheoremOne.concrete_load_transfer` in `ConcreteTheoremOneFinal.lean` | Has exactly the premise required by the earlier conditional expectation theorem. |
| Finite expectation split | `ConcreteTheoremOne.expectation_le_of_load_transfer` | Already proves `expectedPS n ≤ K*(1 + psLogStar n) + n*failureError n`. |
| Literal iterated logarithm | `StandardLogStar.psLogStar_le_logStar_add_one` | Pointwise `psLogStar n ≤ logStar n + 1`. |

For `0 < n` and `1 ≤ log n`, these imply

\[
 E[\operatorname{Rank}(PS)]
 \le K(1+\texttt{psLogStar}(n))+n\delta_n
 \le K(2+\log^*n)+n\delta_n.
\]

The second expression avoids the factor-two relaxation used by the old tail
wrapper, which had changed `1 + psLogStar n` to `2*(1 + logStar n)`.
The size bound gives the minimum with `n`. The size bound itself requires only
`0 < n`; it covers the small markets excluded by the concentration hypothesis.

These are pointwise bounds with fixed mathematical constants, not useful
small numerical constants. In the existing source,

\[
 K=2\{\log2+1+\log(1+e)\}(\Lambda_0+130),
 \qquad \eta_0=1/16,
\]

where `phaseLambdaZero = Classical.choose exists_phaseLambdaZero` supplies
`Λ₀`. It is not an evaluated numerical threshold. The rank multiplier alone
is approximately 6.0128, and each old survivor block costs `8/etaZero = 128`
before that multiplier is applied. The new proof's nearly unit phase costs
cannot be obtained by dropping those factors. Likewise, `failureError_cost_tendsto_zero`
only handles an asymptotic error; it does not repair the leading coefficient.

## The interface patch

| New declaration | Statement / proof |
|---|---|
| `ConcreteTheoremOne.expectedPS_le_phase_bound` | Applies `expectation_le_of_load_transfer concrete_load_transfer`. No new probabilistic premise. |
| `ConcreteTheoremOne.expectedPS_le_marketSize` | Averages `run_averageRank_le_marketSize` over the nonempty profile sample. |
| `PaperTheoremOne.expectedPS_le_paperLogStar` | Uses the additive one-step `logStar` comparison, preserving `K` and `n*failureError n`. |
| `PaperTheoremOne.expectedPS_le_finite_min` | Combines the previous estimate and the market-size bound with `le_min`. |

`AxiomAudit.lean` now prints the dependencies of all four new declarations.
`CHECKING.md` and the theorem comments distinguish the September 3 result from
the subsequent finite claims. No `sorry`, new axiom, assumption of either desired
conclusion, or trusted numerical oracle was introduced. The existing theorem
bundles retain their types so downstream code remains compatible.

## What can be reused for the sharper proof

| New paper component | Existing support | Precisely what is still absent |
|---|---|---|
| Exposure `v(t)=1+H(t)` in the one-copy case | `StoppedChoices.displacementPotentialFrom`, `predictableVolumeFrom_eq_card_mul_one_add_potential`, `run_prefix_load_mean` | A real-time exposure function and its time integral/finite weighted-sum representation. Existing identities concern completed phase prefixes. |
| Genuine fresh choices and conditional uniformity | `SequentialRevelation.sequential_revelation_probability`, `sequential_revelation_joint_count`; `PSChoiceMachine.profile_machine_correspondence`, `profileRevealHistory_admissible` | Connect time-weighted fresh entries to this history. Nonfresh singleton queries and terminal fallback labels must contribute zero. |
| Conditional expected rank jump | Concrete ranks and `averageRank_eq_dynamicRank` | The bound `E[Δrank | history] ≤ n/(a+1)`, and its time-weighted summation. This is a substantive new lemma. |
| Weighted exponential one-step estimate | `AdaptiveCategorical.weighted_exp_bool`; `AdaptiveBernoulli.exp_neg_mul_one_add_le_one` | Predictable-weight process with increments `-θ z_h X_h + p_h(1-exp(-θ z_h))`. Existing `lowerProcess_supermartingale` has one fixed coefficient for all steps. |
| Transfer a terminal nonnegative statistic from tree to profiles | `PSChoiceMachine.profileLabelFiber_probability_le_sequenceWeight`, `sequenceWeight_sum_one`, `sequenceWeight_nonneg` | A general expectation transfer lemma. Existing public transfer wrappers bound event probabilities/hitting probabilities. Fiberwise multiplication by a nonnegative terminal statistic supplies the needed extension. |
| Weighted capacity and endpoint identities | `PSProcess.run_consumedByGood`, `run_totalDuration`, phase supplies and durations | Weighted entry mass equals consumed capacity for a survivor; common compensator; existence of a final good and its identity at time 1. |
| Integral inequality for `f_n` | Finite expectation and process machinery | Jensen/log estimate, convolution identity, interior-time and endpoint inequalities below. Neither appears in the repository. |
| Exponential phase count | `PhaseIntegral.iteratedExp`, `chain_length_le_exponentialHeight`; `StandardLogStar.cast_le_iteratedExp_logStar` and least-iteration characterization | The new recurrence with `z_j=(5/6)2^{-j}`, its unit-cost bound, and the exact count `J+1 ≤ logStar n - 1`. The old phase count is for a different recurrence. |
| Numerical finite recursion | No matching declaration or evaluator found | Positive-recursion soundness, terminal remainder, rational input data, sound exponential/log enclosures and checked arithmetic. |

Two tempting shortcuts are invalid. `RandomPriority.activeRank_expectation`
proves `(n+1)/(a+1)` for a fixed available set under an unconditioned uniform
ranking. It does not prove `n/(a+1)` for the increase after a PS agent switches,
conditional on that agent's earlier choices. Also, `PhaseIntegral.PhaseCertificate`
certifies survivor blocks on the old load-good event; it does not encode or
check the newer deterministic recursion.

## Minimal missing mathematical interfaces

The following is a precise decomposition of the missing work, not a claim that
any of these proposed declarations is already proved. Start with `q=1`, which
matches the repository's actual model.

### Shared core for +3.7 and below five

1. **Exposure and rank bridge.** Define event times `τ_h` and remaining choice
   cardinalities `a_h` from the concrete run, recording only fresh choices.
   Define

   \[
   C(t)=t+\sum_{h\text{ post-initial}}\frac{(t-\tau_h)_+}{a_h},
   \qquad f_n(t)=E[C(t)],\quad 0\le t\le1.
   \]

   Show `f_n(0)=0`, nonnegativity, monotonicity and convexity, and

   \[
   \texttt{expectedPS}\ n\le
   1+(1-1/n)(f_n(1)-1)\le f_n(1).
   \]

   The rank-jump proof in the paper uses enriched histories of independent
   uniform scores. The current history stores choice labels, not scores.
   Either formalize that augmentation and its permutation-law equivalence,
   or prove the conditional rank-jump inequality by finite permutation
   counting. Uniformity of the next label alone does not supply it.

2. **Weighted stopped supermartingale and expectation transfer.** For a fixed
   deterministic horizon `t`, put `z_h=(t-τ_h)_+` and stop entries into good `g`
   when it is exhausted. Define

   \[
   M_g=\exp\{-\theta\sum_h z_hX_h^g+
                     \sum_h p_h^g(1-e^{-\theta z_h})\}.
   \]

   Prove `E M_g ≤ 1` on the actual profile sample. At one step, put
   `d=1-exp(-θ z_h)`; the conditional multiplier is
   `exp(p*d)*(1-p*d) ≤ 1`, an instance of the existing exponential inequality.
   New work is the predictable-weight recursion, finite-depth expectation
   induction, and connection to the PS path. Use the existing depth `n*n`;
   make padded/nonfresh/after-horizon steps contribute zero. Generalizing the
   fiber inequality to nonnegative terminal statistics avoids having to prove
   a new full probability-space isomorphism.

3. **Capacity, convolution and Jensen.** For a surviving good, identify the
   weighted entry mass with `1-r_g(t)` and its compensator with

   \[
   F_{\theta,t}=\theta C(t)-\theta^2\int_0^t
                       e^{-\theta(t-s)}C(s)\,ds.
   \]

   Prove the survivor-capacity sum and apply finite Jensen twice to obtain
   `E F_{θ,t} ≤ Φ(θ,1-t)` for `t<1`. At time 1 use at least one good exhausting
   at exactly 1 and sum the potentials over all goods, obtaining the endpoint
   bound. Positivity of the sum makes the logarithm legitimate. Finite profile
   expectations make exchanges with integrals straightforward, but they must
   still be proved.

4. **Analytic interface.** The outputs needed by both downstream proofs are

   \[
   f_n(t)\le\frac{\Phi(\theta,1-t)}\theta+
       \theta\int_0^t e^{-\theta(t-s)}f_n(s)\,ds
       \quad(0\le t<1,\ \theta>0),
   \]
   \[
   f_n(1)\le1+\frac{\log n}\theta+
       \theta\int_0^1 e^{-\theta(1-s)}f_n(s)\,ds.
   \]

   Define `Φ(λ,u)` as the maximum of `-log a + λ*(1-u/a)` on `[u,1]`
   for `0<u≤1`, or use its equivalent piecewise formula in the manuscript.
   The calculation of this maximum is another needed analytic lemma.
   These inequalities cannot be replaced by hypotheses of a theorem called
   the unconditional finite PS result: they must be discharged for `run`.

### Additional obligations for `log* n + 3.7`

After the shared core, the current paper supplies a path to the stronger +3.4.
The missing deterministic lemmas are:

- The envelope
  `f_n(t) ≤ Ψ(t) = t*[t-log(1-t²)]/[1-exp(-t-t²)]` on `0<t<1`.
- Convexity/secant integration yielding
  `f_n(t)-f_n(s) ≤ (t-s)*Φ(θ,1-t)/(1-exp(-θ*(t-s)))`, plus
  `f_n(1)-f_n(1-u) ≤ (θ*u+u*log n)/(1-exp(-θ*u))`.
- For `c(z)=exp z-1-z`, prove positivity and
  `c(z/2)/c(z) ≥ exp(-z/2)/4`. The integral representation
  `c(z)=z²∫₀¹(1-r)exp(z*r)dr` in the paper suffices.
- Set `z_j=(5/6)*2^{-j}`, `c_j=c(z_j)`, `λ₀=e/c₀`,
  `λ_{j+1}=e*z_j*λ_j*exp(c_j*λ_j)`, `x_j=c_j*λ_j`,
  `s_j=1-1/λ_j`. Prove `x_j≥e*2^j`, `x_{j+1}≥exp(x_j)`,
  admissibility of all phase parameters, and phase/terminal cost ≤ `exp z_j`.
- Prove existence of the first `J` with `x_J≥log n`, and
  `J+1≤logStar n-1` for `n≥3`. Reuse the tower lemmas, but prove the index
  shift and `logStar n≥2`; do not use the old loose `+1` comparison here.
- Bound the excess-cost sum by
  `Σ_j(exp((5/6)*2^{-j})-1) ≤ 2*(5/6)+(4/3)*c(5/6)`.
  Finite partial sums with a uniform bound suffice; an infinite series is
  optional.

The remaining numerical inequalities for the current +3.4 proof can be reduced
to the following fixed real inequalities with rational endpoints:

\[
 \frac5{24}e^{19/12}\ge1,\quad
 1<\frac{5e}{6c(5/6)},\quad
 \frac{82796}{100000}<s_0<\frac{82797}{100000},
\]
\[
 \Psi(s_0)<\frac{2108}{1000},\qquad
 \frac53+\frac43c(5/6)<\frac{2291}{1000}.
\]

To enclose `Ψ(s₀)`, use the numerator at `82797/100000` and the positive
denominator at `82796/100000`, with their monotonicity proved on that interval.
Then the additive cost is less than `-1+2.108+2.291=3.399<3.4<3.7`.
For +3.7 alone the smallest final scalar requirement is simply

\[
 \Psi(s_0)+\frac53+\frac43c(5/6)\le\frac{47}{10};
\]

there is no need to certify the sharper decimal cutoffs. The tower and
admissibility inequalities are still required. Markets `n=1,2` can be closed
immediately using the new `expectedPS_le_marketSize` wrapper and nonnegativity
of `logStar`.

### Additional obligations for a bound below five

This route shares the weighted-exposure core but **does not require proving
the iterated-logarithmic phase theorem first**.

1. Prove the positive finite recursion in the paper: bound `f_n` on every earlier
   interval by its right-endpoint bound; on the last interval use `f_n(t_i)`;
   isolate that last term using the strictly positive exponential divisor.
   Prove coefficient nonnegativity so rounding errors can only increase bounds.
2. Prove the tail envelope
   `Ψ(t) ≤ (7/6)*[-log(1-t)+1-log 2]` and its integral. This includes
   `(1-exp(-x))⁻¹ ≤ x⁻¹+1/2+x/12` for `x>0`, the convex elementary bound on
   `[0,1]`, and the logarithmic tail integral.
3. Prove the terminal expression with `ε=1-t_L`:

   \[
   U_n=1+\frac{\log n}{\theta}
    +\sum_{j=1}^{L}b_j
        [e^{-\theta(1-t_j)}-e^{-\theta(1-t_{j-1})}]
    +\frac76\theta\varepsilon[-\log\varepsilon+2-\log2],
   \qquad \texttt{expectedPS}\ n\le f_n(1)\le U_n.
   \]

4. Encode `P=64`, `K=30`, `L=1920`, the exact rational grid, the 61 knots and
   their 32-step linear interpolation. Prove grid ordering and parameter
   positivity. Use a proved upper envelope
   `Φ(θ,1-t) ≤ -log(1-t)+θ-1-log θ`.
5. Supply rational lower/upper enclosures for the relevant exponentials and
   logarithms. A formally proved rational Taylor/range-reduction checker is
   one option. Its output must prove inequalities about `Real.exp`/`Real.log`;
   a table of decimals or a Python assertion alone is insufficient. The
   paper's 70-digit computation need not be mimicked inside Lean: any sound
   rational enclosures tight enough to prove `U<5` suffice. The margin is
   about 0.07876, much larger than the decimal display precision.
6. For rational candidate bounds `B_i`, check every recurrence inequality with
   upward exponential differences. Then check the terminal rational upper
   bound at `log n ≤ 80*log 10`, `θ=1600`, `ε=2^-30`, and prove it is below
   `4921241/1000000<5` (or just below 5). A weaker rational bound would still
   establish the user-requested claim.
7. Transfer from the endpoint `10^80` to the whole range by monotonicity of
   `log n` in the terminal formula. **Do not assume PS expected rank is itself
   monotone in n.** Handle `n=1` separately with the market-size wrapper.

## Numerical reproduction results

The supplied script `reproduce_finite_certificate.py` reads exact rational
knots from `finite-parameters.json`; it performs the full 1,920-step computation
without optimizing or modifying the parameters. Every exponential and logarithm
is surrounded by adjacent 70-digit decimals, and subsequent arithmetic is
rounded upward. Grid, interpolated parameters, and exponential arguments are
terminating decimals with fewer than 70 significant digits.

| Maximum types | Terminal θ | Reproduced upward bound |
|---:|---:|---:|
| 100 | 7 | 3.796592 |
| 1,000 | 12 | 4.047950 |
| 10,000 | 19 | 4.197233 |
| 1,000,000 | 36 | 4.370572 |
| 10^80 | 1,600 | 4.921241 |

The final 70-digit upper computation begins
`4.921240061252361449400361952493438020073226906865873146569988818021537`.
The reproduced checkpoint bounds at indices 64, 128, 320, 640, 1280 and 1920
are respectively `0.716058, 1.409946, 2.804130, 3.694852, 4.223725, 4.422489`.
The partial-allocation bounds at 0.5, 0.75 and 0.9 are
`1.432116, 1.879927, 2.392808`. All agree with the manuscript.

This calculation assumes the correctness of Python Decimal's transcendental
operations and implementation. Its data are useful certificate candidates;
they have no Lean proof terms. `finite-certificate-results.json` and
`grid-upper-bounds.json` retain the full output.

## Scope and verification

The repository fixes `Profile n = Fin n → PreferenceOrder n`, equal numbers of
agents/goods and unit initial capacities. The manuscript's uniformity over
`q≥1` is a further model extension: separate agent and type counts, capacity
`q`, normalized exposure `E C/q`, and the corresponding conservation and law
transfer lemmas must be formalized. Changing the name of `n` to `m` cannot
establish that extension. None of the new interface declarations claims it.

Local source checks found no proof placeholders and `git diff --check` passed.
The original local `lake` commands could not run. Lean 4.19.0 and the pinned
mathlib were then downloaded; this execution runtime returned `failed to
locate application` when launching Lean. No workaround modifying the toolchain
or its trust model was used.

Repository verification status: **PASSED**, on the exact patch commit
`b8a592ce27189dddf04cc8b11693285a541b5e65`. The unchanged repository workflow in
[run 36406816379](https://github.com/josueortega1-maker/ProbabilisticSerial/actions/runs/36406816379)
ran `lake build` successfully with Lean 4.19.0, passed the placeholder scan,
and successfully ran `lake env lean AxiomAudit.lean`. I inspected the job logs,
including the checked-out commit, successful build and actual axiom output.
Each of the four new declarations has exactly the reported dependency set
`[propext, Classical.choice, Quot.sound]`. The original final theorem has that
same set. Full job output is retained in `github-verification.log`.

Thus the four interface additions are kernel-checked by the repository's CI;
this is not a claim that a local build succeeded. The +3.7, +3.4 and below-five
claims remain open formalization obligations. No historical verification log
was overwritten or presented as evidence for this patch.

To apply the standalone patch to a clean checkout of the base commit:

```sh
git apply --check finite-ps-interface.patch
git apply finite-ps-interface.patch
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

Preserve the supplied manifest. Check the four new declarations' axiom lists
alongside the original final theorem. To reproduce the independent numerical
calculation, run `python3 reproduce_finite_certificate.py` beside its JSON inputs.
