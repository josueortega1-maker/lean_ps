# The smaller positive-arrival certificate

This certificate proves a bound for a positive finite exposure trace once
its exponential arrival inequalities have been supplied. The PS application
still needs those probabilistic inequalities and the rank/exposure bridge.
It is a separate certificate from the manuscript's 1920-step recursion; it
does not verify that recursion or its sharper value 4.921241.

Write an exposure as

\[
 f(t)=\sum_a w_a(t-\tau_a)_+,\qquad
 F_{\theta,t}=\sum_a w_a(1-e^{-\theta(t-\tau_a)_+}),
 \quad w_a,\tau_a\ge0.
\]

The certificate uses 21 tests: horizons `1-2^-j` for `j=1,...,20`, and the
endpoint `1`. The first 20 parameters are the even-indexed entries 2 through
40 of the manuscript's compact parameter table; the endpoint parameter is
1600. All masses, parameters, prices and cost enclosures are exact rationals
in [arrival-certificate-21.json](arrival-certificate-21.json).

Let `K_i(r)=1-exp(-theta_i*(t_i-r)_+)`. The nonnegative masses `a_i` satisfy

\[
 (1-r)_+\le\sum_i a_i K_i(r)\qquad(r\ge0).
\]

This is checked at the 22 grid endpoints `0,1-2^-1,...,1-2^-20,1`.
Between successive endpoints no test horizon lies in the open interval.
Each `K_i` is either zero or concave there, so its positive sum lies above
the line joining its endpoint values. Thus the finitely many endpoint checks
imply the inequality for every real `r>=0`, not just the grid.

Multiplication by each `w_a`, summation and interchange of finite sums yield

\[
 f(1)\le\sum_i a_i F_{\theta_i,t_i}.
\]

For interior horizons use `F <= Phi(theta,1-t)`. For the endpoint use
`F_(1600,1) <= 1600+80*log 10`, valid after the market-dependent endpoint
estimate when `m<=10^80`. The real inequalities are enclosed by rational
polynomials: a Taylor lower bound `P(x)<=exp x` implies
`exp(-x)<=1/P(x)` for `x>=0`. This controls both the kernel lower bounds and
the negative logarithms in `Phi`. The final rational sum is

\[
 \frac{124982139465456527}{25000000000000000}
 =4.99928557861826108<5.
\]

`FiniteArrivalCertificate.lean` contains the general soundness proof.
`FiniteFiveCertificate.lean` contains the rational checks, the real
enclosures, the all-real-time domination and `value_lt_five`.
`PaperReplicaInterface.expectedPS_lt_five_of_arrival_bounds` states the PS
application with its remaining rank and arrival hypotheses explicitly.
Use [VERIFICATION.md](../../VERIFICATION.md) for the actual kernel-check
status and commit, rather than inferring verification from this description.

The deterministic generator uses only Python `Fraction` arithmetic:

```sh
python3 audit/2026-09-28/generate_arrival_certificate.py
lake build
lake env lean AxiomAudit.lean
```

The generator's assertions are diagnostics. Only the generated Lean proofs
and the real-analysis soundness lemmas establish the formal certificate.
