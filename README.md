# Stochastic matching: restarted formalization

## Checkpoint 51: optimal competitive ratio in the Poisson model

The public theorem in `Matching/PoissonOptimalRatio.lean` is:

```lean
theorem optimalPoissonCompetitiveRatio_eq :
    optimalPoissonCompetitiveRatio =
      1 - Real.exp 1 / (Real.exp 1) ^ (Real.exp 1)
```

Both directions are proved in one model of randomized online controllers.
`PoissonAchievable r` means that every finite Poisson matching instance has an
online controller achieving expected reward at least `r` times the expected
maximum matching. `optimalPoissonCompetitiveRatio` is the supremum of these
uniform guarantees. The stronger characterization
`poissonAchievable_iff_le` proves that the achievable constants are exactly
those at most `Comparison.ratio`.

The horizon is one, with arbitrary nonnegative intensities for a finite set of
arrival types and a finite set of offline vertices. The offline benchmark is
`poissonOfflineOptimum`, the expectation of the actual finite maximum matching
under independent Poisson type counts. Empty sets and zero intensities are
included in the achievability statement.

### Online model and reward

`PoissonOnlineController` permits an arbitrary measurable history state and a
joint randomized kernel for the routing mark and next state. At every live
state, the kernel's arrival-time/type marginal is the fresh Poisson
next-arrival law for the remaining horizon. Every accepted mark must belong
to the arrival's neighborhood and the current unmatched set; acceptance
removes that vertex. Terminal states retain the unmatched set.

The accepted count is monotone and bounded by the number of offline vertices.
`expectedReward_eq_trajectory` identifies the controller's reward with the
expectation of its limiting accepted count on its actual infinite Markov
trajectory. Thus the reward is not a single-step or finite-truncation proxy.

The constructed coverage algorithm is embedded into this controller model in
`CursorController.lean`. `CursorCardinality.lean` proves exact removal of one
available vertex per acceptance. The projection and payoff lemmas identify
the retained-terminal controller with the already verified routing process.
`coveragePoissonController_lower_bound` imports the established matching
lower bound through this embedding.

### Direct Poisson impossibility proof

For an instance with `m` offline vertices, sample a degree `d >= 2` with
probability `1 / (d * (d - 1))`, then sample `d` uniform neighbors with
replacement. There is one Poisson type per resulting neighborhood, with
rates totaling `m`. The degree probabilities, neighborhood distribution,
normalization, and exact coverage formula are all proved:

\[
  f(A)=|A|\left(1-\log\frac{|A|}{m}\right).
\]

The new finite-instance bounds are:

\[
 \mathbb E[\mathrm{OPT}_m]\ge m-2\sqrt m,
 \qquad
 \mathbb E[\mathrm{ALG}_m]\le m\left(1-e^{1-e}\right)
 \quad\text{for every admissible online controller.}
\]

The offline proof uses the existing exact Poisson--exponential offline
identity. The maximum exponential deficiency is bounded pathwise by the
integrated error of an empirical exponential survival function. Independence,
second moments, and Fubini bound its expectation by `2 * sqrt m`.

The online proof uses the normalized potential

\[
 \Phi(T,u)=1-e^{1-e^T}u^{e^T},
\]

where `u` is the fraction of unmatched vertices. Its terminal value is `1-u`,
and `Phi(1,1)` is the target constant. A finite-jump generator inequality
implies the first-Poisson-arrival inequality, including the no-arrival atom.
The proof then handles every supported randomized routing mark and iterates
the resulting bounded supersolution. Finally, `HardRatioSeparation.lean`
chooses a finite square-sized instance contradicting any proposed ratio
strictly above the target.

The hard neighborhood distribution comes from the impossibility construction
of Chierichetti, Giacchini, Panconesi, and Vattani, *A New Impossibility Result
for Online Bipartite Matching Problems* (https://arxiv.org/abs/2504.14251).
The target theorem is from *Optimal Online Stochastic Matching*
(https://arxiv.org/abs/2610.19866). This checkpoint gives a direct Poisson proof
of the required upper bound using the exponential offline identity and the
potential above.

### Verification and scope

All 289 mathematical modules from checkpoint 50 are retained byte-for-byte.
Twenty-nine new modules complete the unweighted Poisson ratio theorem.
`verification.txt` records the full Lean 4.19.0 build, the audit of every
exported theorem/lemma, and source SHA-256 hashes. The audit permits only
`propext`, `Classical.choice`, and `Quot.sound`; it rejects proof placeholders
and unexpected axioms. The proof is an existence result and uses
noncomputable definitions, as does the preceding formalization.

The weighted extension and the known/unknown-law separation are outside this
checkpoint's scope. The fixed-count transfer is retained as prior work.
Everything below is historical: its remaining-work lists describe the older
checkpoints, not the status of the Poisson ratio theorem above.

## Checkpoint 50: fixed-count transfer lemma

The transfer lemma is now proved for a Poisson mixture of finite causal
matching policies. **Applying it to checkpoint 49's continuous-time routing
process is still unfinished.** In particular, this checkpoint does not assert
an unconditional fixed-count lower bound for that process.

For a finite type distribution `ν`, let `F_k = fixedCountOffline N ν k` be
the expected maximum matching on exactly `k` iid arrivals, and let
`p_n = poissonWeight n n = exp(-n) * n^n / n!`. The new statements prove:

\[
 (1-p_n)F_n \le \sum_k \Pr[\operatorname{Pois}(n)=k] F_k,
 \qquad
 \mathrm{ALG}_n \ge \mathrm{ALG}_{\mathrm{mix}}-p_nF_n.
\]

Here `ALG_mix` is the Poisson-weighted reward of any family `π k` of probability
laws on `FiniteOnlinePolicy N k`. Policy randomness is independent of the iid
type vector. A policy is a decision function with explicit prefix causality,
edge support, and no repeated use of an offline vertex. Its output is an actual
`FiniteMatching`, and its expected reward equals expected matching cardinality.

Consequently, if that policy family has Poisson-mixture ratio `c ≥ 0`, then a
finite causal policy on exactly `n > 0` arrivals achieves

\[
 \left(c-(c+1)p_n\right)F_n
 \;\ge\;
 \left(c-\frac{c+1}{\sqrt{2\pi n}}\right)F_n.
\]

The public exports are `fixed_count_policy_transfer`,
`fixed_count_competitive_transfer`, `fixed_count_competitive_transfer_sqrt`,
`fixed_count_matching_transfer`, and `fixed_count_matching_transfer_sqrt`.
The competitive Poisson-mixture inequality is an explicit input to these
transfer theorems; it has not been silently assumed for the coverage process.

The proof includes the following constructions and identities:

- `FiniteMatching.jobs` converts a matching to indexed routing decisions.
  Restricting an actual maximum matching proves the offline sampling inequality;
  taking iid expectations gives monotonicity and `n F_k ≤ k F_n` for `n ≤ k`.
- `FiniteOnlinePolicy.deleteDummy` inserts a fixed dummy type at a fixed
  position, executes the original policy, and retains real decisions. Its
  prefix causality, support, and uniqueness are proved. Averaging over the
  dummy's iid type and summing over positions retains exactly `k` times the
  original `(k+1)`-arrival reward.
- `appendReject` embeds a policy into one with an extra ignored last arrival.
  Together these operations prove the same monotonicity and sampling inequality
  for the optimum among finite causal policies.
- `poissonWeight_shortfall` and `poissonWeight_excess` prove both exact moments
  `E[(n-K)+] = E[(K-n)+] = n p_n`. The Poisson comparisons use these identities.
- `poissonWeight_diagonal_le` proves `p_n ≤ 1/sqrt(2*pi*n)` from mathlib's
  Stirling sequence monotonicity and limit.

The final policy is `bestFinitePolicy`, a noncomputable maximizer over the
finite set of causal policies. This proves existence and matching validity;
it does not provide an efficient executable implementation of the paper's
random-subset simulator.

### Concrete remaining bridge

For intensities `a s = n * ν.real {s}`, construct probability laws `π k` on
finite causal policies from the existing history-dependent routing kernel,
and prove the two needed identifications:

1. The expected matching reward under `coverageMatchingTrajectory N a` is
   the Poisson average of `randomizedPolicyReward ν (π k)`.
2. Its expected offline optimum is the Poisson average of `fixedCountOffline
   N ν k`.

The first item needs a conditional-count, independent-randomness representation
that preserves prefix causality. The already proved independent Poisson type
counts and matching validity alone do not imply it: those properties would
also hold for a clairvoyant offline policy. The existing one-step routing
type/time marginal, full renewal-input law, and observed-history update are
the starting points for proving the required stronger representation.

After these identifications, `coverage_online_matching_guarantee` supplies
the competitive premise with `c = Comparison.ratio`. No new analytic loss
estimate or finite-policy sampling theorem is then required.

All 280 mathematical modules from checkpoint 49 are retained unchanged. Nine
new modules extend them. `verification.txt` records the full build and axiom
audit. The paper's optimality upper bound, weighted extension, unknown-law
separation, and the historical running conditional-work target remain open.
The notes below describe earlier checkpoints.

## Checkpoint 49: matching cardinality on the policy's actual Poisson input

The lower-bound chain now ends in an actual finite matching on the individual
arrival copies observed by the concrete posterior routing policy. The theorem
`coverage_online_matching_guarantee` proves

\[
  (1-\exp(1-\exp(1)))\,\mathbb E[\mathrm{OPT}(\text{observed arrivals})]
  \;\le\;\mathbb E[|\text{observed routing matching}|].
\]

Both expectations are evaluated under the same probability law,
`coverageMatchingTrajectory`. Both random variables are measurable and
integrable. The input has the independent-Poisson type-count law; the stronger
full typed-input trajectory law from independent renewal streams is also
preserved when routing decisions are recorded. Zero rates and empty finite
vertex/type sets are allowed by the statements.

The new proof chain is:

- `RoutedMemoryValid` records genuine arrivals, supported accepted edges,
  and uniqueness of each accepted job. `routedMemoryMatching` constructs a
  `FiniteMatching` on exactly the arrival copies counted by that memory.
- `PosteriorStage.markedTrajectory_valid` proves this invariant at every
  live step, almost surely. Previously accepted jobs are excluded from the
  available set, and the accepted count equals the cursor's completion depth.
- `observedRoutingMatching` reads the last live memory. It is a total matching
  construction, with an empty-matching fallback on malformed paths; the
  concrete process almost surely uses the valid-memory branch.
- `PosteriorStage.markedTrajectory_matching_payoff_law` identifies its real
  cardinality distribution with the payoff distribution of the stopped
  completion log. `markedTrajectory_expected_matching_size` transfers the
  previously proved scheduling payoff bound without an extra coupling
  assumption.
- `coverageMatchingTrajectory_counts_law` and
  `coverageMatchingTrajectory_expected_offline` identify the offline optimum
  on those same observed arrival copies with the existing Poisson benchmark.
- `coverage_online_matching_guarantee` combines these results with the
  constructed greedy coverage optimizer and the archived comparison theorem.

Online decisions remain the history-dependent marks of the existing routing
kernel. Constructing the finite output only relabels their recorded arrival
indices as type-indexed copies; it makes no new routing decisions. The final
reader does not assume termination: finite termination and a live initial
state are proved for the process before using its last-live-state specification.

The archive's routing support, frozen-job exclusion, append-log length,
Markov trajectory invariant, terminal-payload projection, stopped-output law,
renewal-input law, and expected Poisson benchmark were reused. All 264
mathematical modules from checkpoint 48 remain unchanged; sixteen new modules
extend them. `verification.txt` contains the full build, theorem/lemma axiom
audit, and source hashes.

**Remaining for the whole paper:** the optimality/impossibility upper bound,
the fixed-number-of-arrivals transfer, the weighted extension, and the
unknown-law separation. The stronger running coordinatewise conditional-work
identity discussed in the historical notes remains a separate target. This
checkpoint establishes the concrete Poisson-arrival matching lower bound;
it does not claim a complete formalization of the paper.

All checkpoint notes below are historical. Their statements that the
matching construction or matching-payoff transfer is still missing are
superseded by checkpoint 49.

## Checkpoint 48: observed arrival counts and the offline benchmark

The final arrival log is now identified with the original renewal counts.
The reader `lastArrivalCounts` uses the live state immediately before the
first absorbing state, since the existing stopped process discards live
memory on termination. It depends only on the observed trajectory.

The new proofs establish:

- `loggedStream_live_ledger`: at every live step, the consumed counts,
  residual heads, and all unread tails agree with the once-sampled original
  streams. The total consumed count equals the number of steps.
- `loggedStream_terminal_bound`: regular stream executions terminate by
  one plus the total number of renewal arrivals before the horizon.
- `loggedStream_last_counts_ae`: pathwise, almost surely, the final observed
  counts equal `infiniteRenewalCount` for each original stream.
- `loggedInputTrajectory_counts_law` and
  `PosteriorStage.loggedTrajectory_counts_law`: the counts actually read
  from the input and posterior-policy logs have the independent Poisson
  law with the corresponding horizon-scaled intensities.
- `coverageLoggedTrajectory_expected_offline`: the expected offline optimum
  evaluated on the policy's observed input is exactly the existing Poisson
  benchmark.
- `coverageRoutingOutput_vs_observed_offline`: the existing completion-payoff
  guarantee now compares against that observed-input offline optimum.

Zero arrival rates are allowed. Positivity, valid next-event branches, and
nonexplosion are proved almost surely, including all iterations on the
same sample. No termination, tie exclusion, or endpoint exclusion is added
as an assumption to the final count-law theorems.

The archive's count characterization, nonexplosion theorem, first-event
partition, stream-restart laws, and posterior input projection were reused.
All 255 mathematical modules from checkpoint 47 are unchanged; nine new
modules extend them. `verification.txt` records the full build, theorem
axiom audit, and source hashes.

**Remaining for the online matching lower bound:** construct the matching
on individual observed arrival copies, prove its size equals the recorded
completion reward, and package the resulting online algorithm theorem.
The archive already contains routing support and inactive-job exclusion
(`RoutingSupport`) and completion-label uniqueness (`TraceLabels`) for
this next step. The optimality upper bound, fixed-arrival-count transfer,
weighted extension, and unknown-law separation remain open.

The historical checkpoint notes below are retained as a progress record.
Their references to observed-count identification as open are superseded
by checkpoint 48.

## Checkpoint 47: complete renewal input trajectory

This checkpoint adds a joint law for the next typed arrival and all remaining
renewal streams. It then iterates the deterministic stream-consuming update,
retaining the entire observed history, and identifies its complete infinite
trajectory with the arrival-only Markov trajectory. The concrete posterior
routing process therefore has this independent-renewal-stream input law.

The main new exports are:

- `poisson_stream_next_event_law`: the next event has `poissonNextArrival`
  law and is independent of the entire restarted stream vector. Zero arrival
  rates are allowed.
- `poissonStreamUpdate_iterate_law`: every finite state/remaining-stream law
  factors correctly when the streams are sampled only once initially.
- `deterministicResidual_trajectory_law`: a general full-trajectory theorem;
  its induction invariant includes the complete finite history, not just
  the most recent observed state.
- `independentStreamInputPath_law` and `loggedIndependentStreamPath_law`:
  equality of the full stopped input laws, including the typed arrival log.
- `PosteriorStage.loggedTrajectory_renewal_input_law`: the input projection
  of the concrete posterior routing trajectory has the independent-stream
  execution law.

`RenewalStreamEvolution` also records the physical meaning of the update:
the winning type consumes exactly its first waiting amount; surviving heads
lose exactly the elapsed service; all unread tail values are unchanged.
The proof reuses the existing variable-rate marked completion law, stream
splitting, coordinate splitting, and kernel/trajectory machinery.

The original 248 mathematical modules are unchanged. Seven new modules and
their root imports extend them. The new build and complete theorem axiom
audit are recorded in `verification.txt` when the checkpoint is exported.

**Still required for an end-to-end matching theorem:** formally identify
the terminal type counts read from the consumed arrival history with the
original `renewalTypeCounts` benchmark; assemble a matching on those individual
arrival copies and identify its cardinality with the recorded routing payoff;
then package the online matching lower bound. The optimality upper bound,
fixed-number-of-arrivals transfer, weighted extension, and unknown-law
separation are not proved here. The stronger running conditional-expectation
identity discussed below also remains a separate target.

The historical notes below describe the scope at their respective checkpoints.
In particular, older references to the complete renewal input law as open
are superseded by the statements above.

Checkpoint 46 extends renewal independence to all arrival types jointly:
the current waiting amounts are independent of all future streams. Reading
the next waiting amount from any fixed selected type leaves all remaining
streams independent of that amount. It also includes general finite-product
coordinate splitting and three-component product reordering lemmas.

The full next-arrival restart law for the entire stream vector, its iteration
to identify the complete typed input process, and the optimality upper bound
remain open. The previously proved stopped-output law and routing payoff
bound are retained unchanged.

Checkpoint 45 proves a measurable bounded completion-log payoff and transfers
the scheduling guarantee to the actual stopped routing output. Specializing
to the constructed greedy coverage optimizer, its expected payoff is at least
the comparison ratio times the independent-Poisson expected offline optimum.
Forgetting the retained terminal output recovers the entire original cursor
trajectory law. A new infinite-stream splitting theorem separates its first
exponential waiting amount from its independent complete future.

The benchmark inequality is proved for the concrete routing-kernel process.
Identification of that process's complete typed input with independent
renewal streams, and the optimality upper bound, remain open.

Checkpoint 44 identifies the actual stopped completion-log distribution of
the arrival-driven routing process with the scheduling trace distribution.
The proof uses measurable first-entry stopping, absorption, finite-time
observation invariance, and the geometric termination tail. It is an equality
of full output laws, not only an equality of expectations.

Still open: identify the complete typed arrival-only process with the
independent renewal-stream input model, assemble the matching guarantee
against the original offline benchmark, and prove the optimality upper bound.
Earlier checkpoint notes below describe the gaps as they stood at that time.

Checkpoint 43 adds an absorbing routing state that retains the completed
log. The completion-observation kernel is harmonic under actual routed
arrivals, and its law is invariant through every finite number of transitions.
Initially this is exactly the scheduling trace law; at a terminal state it
is the point mass at the stored log. The output-retaining process terminates
almost surely, with an explicit geometric bound on its remaining live mass.

The passage from these finite observation laws to the actual stopped-output
law is still to be assembled. Independent renewal-stream identification,
the final matching guarantee, and optimality remain open.

Checkpoint 42 retains the complete typed arrival history. The concrete
posterior routing process has the same full logged-input trajectory law as
the arrival-only process; forgetting the log recovers its original cursor
trajectory, and the logged process terminates almost surely.

The completion-prefix reader uses precisely the scheduling trace's labels,
absolute times and revealed demands. A measurable continuation predicts the
full scheduling log from the current cursor and residual vector. It agrees
with tracePlan initially, is unchanged by a rejected arrival, equals the
recorded prefix when the remaining stage is terminal, and takes precisely
the scheduling posterior branch on an accepted job. The full recursive
cursor restart preserves this continuation log almost surely under the
actual joint exponential event/residual law, at every reachable tree depth.

The remaining end-to-end steps are to propagate this continuation identity
through the complete stopped execution, identify the logged arrival-only
process with independent renewal streams, and assemble the final matching
guarantee and its optimality upper bound.

Checkpoint 41 constructs the concrete arrival-driven posterior-policy cursor:
accepted jobs select their posterior child, rejected arrivals advance within
the current service segment, and termination is absorbing. Its curves are
measurable in the history, feasible at every state, and zero on inactive
labels. Every valid arrival decreases the remaining horizon by its waiting
time. The resulting stopped routing trajectory terminates almost surely and
its full remaining-time trajectory has the arrival-only law.

The residual-demand coupling is now instantiated with this concrete cursor:
after every number of arrivals its state law equals the corresponding
marginal of the stopped routing trajectory, jointly with a fresh independent
exponential residual vector. Restoring original labels preserves the first
genuine job event, both pathwise on positive demands and in distribution.

Still required: identify the cursor's completed-job output with the previously
proved scheduling completion log through the entire execution; retain and
identify the complete typed input history with the independent renewal-stream
model; then assemble the matching guarantee and prove optimality. The new
remaining-time law alone does not identify arrival-type histories.

Checkpoint 40 proves the adaptive, repeated residual coupling: after every
finite number of arrivals, the actual surviving-demand simulation has the
same history-state law as routing, with an independent exponential residual
vector conditional on that state. The simulation redraws only its auxiliary
rejection clock; surviving job demands are retained. Rejecting an arrival
preserves the next genuine job completion and its absolute time.

The physical restart invariant preserves reconstructed original demands and
produces a valid cumulative-service/completion state almost surely, including
accepted, rejected, and terminal events. This remains a generic coupling;
instantiation with the concrete posterior scheduling policy and identification
of the full input trajectory with renewal streams are still required. The
matching competitive theorem and optimality upper bound remain open.

Earlier checkpoint notes below record the development at their stated dates.

Checkpoint 39 constructs the complete stopped routing trajectory and proves
its full arrival-only trajectory projection. With a uniformly bounded horizon,
it terminates almost surely; a geometric survival bound includes rejected
arrivals. The general trajectory projection theorem uses uniqueness of the
projective limit, so this is equality of whole trajectory laws.

The fixed-coordinate restart theorem proves the joint law of the next event
and fresh exponential residuals. At an accepted job its now-inactive coordinate
is filled with the residual auxiliary clock; all surviving jobs keep their
actual residual demands. This theorem includes the terminal outcome.

Remaining coupling work: iterate this actual residual update under adaptive
histories, instantiate the history update with the constructed scheduling
policy, and identify the arrival-only trajectory with the renewal-stream input.
The full matching competitive theorem and optimality upper bound remain open.


Checkpoint 38 adds finite routing-history projection laws, a genuine infinite
exponential renewal process, its almost-sure nonexplosion and full Poisson
count distribution, and independent renewal streams whose joint type counts
have exactly the independent Poisson law. The expected offline equality is
transported to these actual renewal samples. The arrival kernel is identified
with the first-event law of independent type clocks, including zero rates.
An infinite Markov trajectory law is constructed with proved finite marginals
and almost-sure invariant propagation. Routing chooses only available
neighbors and has strictly positive event times almost surely.

Still missing for Lemma 2.4: assemble the stopped history-dependent routing
process, identify its complete input law with the renewal streams, and connect
its accepted-job process to the constructed scheduling policy. The general
Markov and renewal results above do not by themselves complete that coupling.


This is a new, independently checked checkpoint created on 2026-10-21.
It does not contain or recover the previously reported 291-theorem archive.
The complete paper is not proved here.

This version continues checkpoint 05 after the user reattached its ZIP. The
reattached archive matched SHA-256
`a09a65c3ca0e495743876414800923b72bc4b5c24e6e1af713f2b3f74eb134b1`,
and all 22 recorded source/configuration hashes matched. All 16 original
mathematical source modules are retained without changes.

Reference: Paul Dütting, Michal Feldman and Mathieu Molina,
*Optimal Online Stochastic Matching*, arXiv:2610.19866v1,
https://arxiv.org/html/2610.19866v1 .

## Current scope

- `Matching/CompletionState.lean`: states indexed by fixed original job labels,
  validity under a single completion, monotone cumulative service, service frozen
  on completed jobs, exact completion counts and a finite bound on run length.
- `Matching/CompletionBound.lean`: a small standalone completion-count bound.
- `Matching/ActiveCoordinates.lean`: restrictions and extensions of active-job
  coordinates, consistent original labels through successive removals, and
  preservation of downward-closed feasibility when completed rates are zeroed.
- `Matching/TimedRun.lean`: additive elapsed times, concatenation, deadline work
  bounds, and positive elapsed time for a genuine completion with valid endpoints.
- `Matching/ExpectedTelescope.lean`: finite telescoping of conditional identities,
  including a bounded random terminal stage with zero cost after termination.
- `Matching/IntegratedSegment.lean`: nonnegative bounded service rates produce
  the actual integral increments required by a valid bounded completion step.
- `Matching/ComparisonPotential.lean`: the explicit continuation function from
  Section 4.2, both derivatives, its PDE, sensitivity bounds and drift factorization.
- `Matching/LossBudget.lean`: the exact integral of the comparison loss kernel,
  tower-property/Fubini reduction of the conditional residual budget, and a
  conditional final guarantee. For a nonnegative residual, joint measurability
  is sufficient for the required product integrability; a uniform residual
  bound is not needed.
- `Matching/ExponentialResidual.lean`: scalar exponential tails and full
  memorylessness as a pushforward identity of restricted probability measures.
- `Matching/ExponentialWork.lean`: integrability and expectation of capped work,
  equality with completion probability, and identification of the comparison
  potential with expected capped exponential work.
- `Matching/VectorResidual.lean`: full finite-product residual law at fixed
  nonnegative thresholds, including normalization by the joint survival
  probability. Independence of the residual coordinates follows from equality
  with the original product measure.
- `Matching/HistoryResidual.lean`: measurable history-dependent thresholds,
  exact factorization after observing survival, and inverse maps recovering
  the original demand sample. The fresh residual vector is independent of the
  prior history as a hypothesis of the product-measure model.
- `Matching/InitialState.lean`: almost-sure positivity of all initial demands
  and validity of the all-unfinished zero-service initial state.
- `Matching/TerminalSegment.lean`: the final segment with no new completion,
  and full finite-execution bounds including paths with no completions.
- `Matching/SurvivalCurve.lean`: the exact probability of no completion along
  nondecreasing service curves and the derivative of its exponential formula.
- `Matching/FirstStepIdentity.lean`: integration-by-parts identity for one
  segment, its finite-job version, and survival/event-mass conservation.
- `Matching/MarkedResidual.lean`: split one candidate completing coordinate
  from the other demands, and factor the residual law for any measurable
  candidate time depending on that coordinate, restricted to other jobs'
  survival at that time.
- `Matching/ExponentialScaling.lean`: the actual completion-time law for a job
  served at a positive constant rate.
- `Matching/ConstantRateRace.lean`: the joint law of a constant-rate winner,
  its completion time and all surviving residual demands; the time density is
  `r j * exp (-(sum r) * t)`, and the winning probability is `r j / sum r`.
- `Matching/RacePartition.lean`: unique first completion almost surely for a
  nonempty finite set of jobs with strictly positive constant rates, and
  positivity of every surviving residual demand.
- `Matching/ZeroRateRace.lean`: extension of the marked law and winning
  probabilities to nonnegative constant rates; idle jobs never win, and the
  winner is almost surely unique whenever the total rate is positive.
- `Matching/CappedHittingTime.lean`: a finite-horizon first-hit clock for
  continuous nondecreasing service, including measurable dependence on history,
  exact service at completion, and the exponential CDF/survival identities.
- `Matching/HittingDensity.lean`: the full scalar density of completion before
  the deadline for continuous nonnegative rates, allowing flat intervals.
  The censored clock value at the deadline is excluded from the completion law.
- `Matching/VariableRateRace.lean`: the joint marked law before a fixed deadline
  for continuous time-varying nonnegative rates. Its density is
  `r j t * exp (-(sum i, a i t))`, multiplied by the product of independent
  exponential survivor-residual laws.

- `Matching/VariableRacePartition.lean`: measurable and disjoint winner events,
  their exact masses, and the almost-sure partition into a unique first
  completion before the deadline or survival of every job to the deadline.
- `Matching/CompletionReconstruction.lean`: reconstruction of the original
  demand vector from the completion time and surviving residual demands,
  almost surely on each winner branch, and the corresponding integral formula.
- `Matching/OneStepLaw.lean`: the complete one-segment measure decomposition
  and expectation formula for any nonnegative measurable function of the
  original demand sample, including the terminal-survival contribution.
- `Matching/HistoryService.lean`: measurable service families selected by
  history, including measurable random deadlines, clocks, winner events,
  observations, and marked densities. Joint measurability follows from path
  continuity and measurability at each fixed time.
- `Matching/HistoryMarkedLaw.lean`: the marked first-completion law integrated
  over incoming histories, with an explicit product-law hypothesis for fresh
  demands. The surviving residuals factor independently of the extended history.
- `Matching/HistoryOneStep.lean`: the terminal branch, almost-sure exhaustive
  partition, measure decomposition, and full nonnegative one-step formula
  integrated over random histories.
- `Matching/HistoryTransport.lean`: transport to an arbitrary sample space
  satisfying the incoming product-law invariant, and its preservation through
  two successive completion observations with history-dependent service curves.
- `Matching/PosteriorMean.lean`: real-valued exponential averaging, bounds,
  and quantitative sensitivity to nonnegative service increments for bounded
  nonnegative measurable allocations.
- `Matching/PosteriorRegularity.lean`: global Lipschitz continuity in active
  service coordinates and joint measurability in history and service, without
  assuming continuity of the underlying allocation.
- `Matching/PosteriorFlow.lean`: existence and uniqueness of the posterior-rate
  ODE on any finite nonnegative horizon, for each fixed history and initial state.
- `Matching/PosteriorTrajectory.lean`: a chosen continuous ODE trajectory,
  its initial condition and its ordinary derivatives through both endpoints.
- `Matching/PosteriorFeasibility.lean`: compact allocation regions provide a
  uniform coordinate bound; closed convex regions preserve feasibility under
  posterior averaging, and downward closure permits masking completed jobs.


- `Matching/MeasurablePosteriorFlow.lean`: joint measurability of the chosen
  posterior trajectory in history and time, using measurable Picard iterations
  and their factorial convergence bound.
- `Matching/PosteriorService.lean`: monotone posterior trajectories and an actual
  measurable history-dependent service family generated by the posterior ODE.
- `Matching/HistoryConditionalExpectation.lean`: conditional expectation given
  the history coordinate under an explicit history/residual product law.
- `Matching/ConditionalTransport.lean`: transport of that conditional identity
  to an arbitrary original sample space and identification of posterior rates.
- `Matching/ServiceExecution.lean`: actual integrated service, demand reached by
  the winner, strict surviving residuals, and valid bounded state transitions
  retaining original job labels.


- `Matching/PosteriorSurvival.lean`: posterior rates equal conditional
  allocations after observing no completion along the constructed trajectory,
  including inspection times selected measurably from the incoming history.
- `Matching/HistoryReconstruction.lean`: reconstruction of original demands
  after a marked completion and conditional expectations of bounded original
  sample functions given the extended history, under the winner-branch measure.
- `Matching/CompletionPosterior.lean`: allocation data after revealing a
  completed demand and the conditional resampling formula on that branch.
- `Matching/RestartPosterior.lean`: measurable survivor initial services and
  allocation data for restarting after a completion; the new posterior rate
  is the conditional original allocation on the observed winner branch.
- `Matching/NonnegativeAllocation.lean`: extend bounded nonnegative allocation
  data from nonnegative demands to all real vectors by coordinatewise clamping,
  with exact agreement on the original domain.


- `Matching/MeasurableBranching.lean`: measurable selection among disjoint
  event branches, with a total fallback on exceptional samples.
- `Matching/AdaptivePlan.lean`: finite adaptive decision trees, one measurable
  execution on the incoming sample space, and exact terminal/winner equations.
- `Matching/AdaptiveLaw.lean`: the full recursively computed outcome law,
  including every terminal branch, and preservation of probability mass.
- `Matching/PosteriorStage.lean`: posterior stage parameters and a measurable
  restart whose deadline is exactly the remaining time on each winner event.
- `Matching/AdaptiveBudget.lean`: every completion removes one label; a recursion
  budget at least the active cardinality cannot cut off with active jobs left.
- `Matching/PosteriorExecution.lean`: a concrete measurable posterior-policy
  completion count, its finite bound, exhaustive budget, and exact distribution.
- `Matching/BranchConditional.lean`: patch conditional identities on observable
  branch events covering the original sample space almost surely.

- `Matching/ConditionalObservation.lean`: transfer conditional expectations from
  a richer observation to a measurable observable quotient when the candidate
  conditional mean depends only on that quotient.
- `Matching/TerminalConditional.lean`: terminal-survival conditional resampling
  of bounded functions of the original sample.
- `Matching/StepObservation.lean`: one complete observation with an explicit
  winner/terminal tag; every branch event is measurable in this observation.
- `Matching/StepConditional.lean`: the combined conditional-resampling identity
  under the full one-step observation, without conditioning on a branch first.
- `Matching/PosteriorTrace.lean`: the measurable execution log records original
  job labels, absolute completion times and revealed demands; its law is exact.
- `Matching/ExponentialMean.lean`: integrability and mean one of fresh demands,
  proved from the exponential tail law, and shifted coordinate means.
- `Matching/ObservationFiltration.lean`: the actual log generates an increasing
  filtration by retaining only completion records visible by each time.
- `Matching/GoodExecution.lean`: almost-sure recursive validity of all selected
  branches, strictly positive completion clocks, demand reconstruction and
  preservation of the absolute deadline through restarts.
- `Matching/TraceValidity.lean`: recorded demands equal the original demands
  almost surely, and every recorded completion lies before the initial deadline.
- `Matching/PosteriorGap.lean`: the gap between conditional demand mean and
  posterior rate equals expected unallocated demand and is nonnegative under
  the allocation cap on nonnegative demand vectors.
- `Matching/ConditionalDemand.lean`: conditional demand means and the actual
  conditional unallocated-demand identity under the history/product law.

- `Matching/ComparisonFlow.lean`: differentiate the comparison potential along
  actual service curves, identify completion jumps, and derive the exact
  first-segment drift identity from the fundamental theorem of calculus.
- `Matching/PosteriorComparison.lean`: instantiate this calculation with the
  constructed posterior ODE; identify the deficit as unallocated demand and
  prove the integrated first-segment loss bound with the paper's loss kernel.
- `Matching/FirstStepReward.lean`: the actual winner-clock pushforward law and
  real-valued expectation formula; the first-step drift identity now uses the
  true terminal and winner events of the exponential demand sample.

- `Matching/ExpectedExecution.lean`: integrability and the exact expected-count
  recurrence of the actual adaptive run, including its terminal and marked branches.
- `Matching/ComparisonOutcome.lean`: a measurable, integrable one-step random
  comparison payoff, bounded by the number of active labels, with its exact
  expected drift and integrated loss bound.
- `Matching/TraceLength.lean`: the completion count equals the number of filled
  log entries, which form a contiguous prefix, on every sample.
- `Matching/TraceLabels.lean`: no original label is recorded twice when the
  initial label map is injective, following the survivor-type recursion.
- `Matching/AdmissibleStage.lean`: admissibility and allocation caps at individual
  reached histories are preserved through valid restarts; local comparison
  estimates do not require admissibility of impossible histories. Service and
  restarted initial services satisfy the uniform allocation-rate bound.

- `Matching/StageRegion.lean`: measurable sets of valid incoming histories,
  elapsed-time and initial-service bounds, and preservation of full measure
  under each actual marked-completion history law.
- `Matching/StagePotential.lean`: jointly measurable comparison payoffs and
  their actual expected decrement, identified with the drift integral and
  proved nonnegative and bounded on valid histories.
- `Matching/StageExpectation.lean`: derive the history-integrated one-step
  potential/defect recurrence with all integrability conditions discharged.
- `Matching/ExecutionDefect.lean`: exact global decomposition of the concrete
  expected completion count as initial expected potential minus recursively
  accumulated defects. The induction uses actual marked-history laws and the
  active-cardinality bound; no local Dynkin identity is assumed.

- `Matching/ResidualBudget.lean`: the actual unallocated-demand budget, its
  integrability and posterior mean, exact allocation reconstruction at a
  completion, and monotone decrease when the completed coordinate is removed.
- `Matching/StoppingClock.lean`: the measurable actual first-segment endpoint;
  survival before the deadline is exactly being before this clock almost surely.
- `Matching/StoppedOccupation.lean`: the weighted stopped-interval identity by
  Fubini, with joint integrability, and the shifted loss-kernel antiderivative.
- `Matching/StoppedBudget.lean`: split a fixed sample's budget between occupation
  before the stopping clock and its remaining comparison weight afterward.
- `Matching/SurvivalBudget.lean`: identify survival-weighted posterior gaps with
  original unallocated demand restricted to survival; derive the exact local
  budget identity and bound the segment defect plus remaining sample budget.

- `Matching/BudgetFunctions.lean`: measurable stopping clocks and sample/history
  budget quantities, with all integrability proved from the valid-history bounds.
- `Matching/BudgetRecurrence.lean`: the original budget dominates a segment's
  defect plus the expected budgets of all actual restart branches.
- `Matching/PolicyGuarantee.lean`: bound the accumulated defect by the initial
  budget and derive the quantitative guarantee for the concrete finite
  posterior-policy completion count.
- `Matching/LabelFeasibility.lean` and `Matching/RatePath.lean`: lift survivor
  coordinates to fixed original labels, construct the actual jointly measurable
  rate path, and prove feasibility at every time under convexity, closedness,
  downward closure, and feasible allocation hypotheses.
- `Matching/RateIntegral.lean` and `Matching/PathRestart.lean`: integrate the rate
  path, prove continuous service in compact feasible regions, identify its first
  segment with the ODE service, and prove exact restart concatenation. A completed
  job receives exactly its demand and no further service.
- `Matching/PathBounds.lean`: prove nonnegative service bounded by each incoming
  demand at every time of the horizon, on every good execution and almost surely.
- `Matching/PathCount.lean`: identify the recursive completion count with the
  number of original coordinates whose integrated service reaches their demand.
- `Matching/ServiceGuarantee.lean`: export the concrete rate, service, and reward
  functions and prove the quantitative bound for fully served jobs themselves.
- `Matching/PathRegularity.lean`: joint measurability of cumulative service,
  nonnegative rates, and monotone service on every original coordinate.
- `Matching/LogRateReader.lean`: a jointly measurable rate evaluator using only
  the initial history and the completion log censored at the query time; its
  fixed-time output is measurable for the completion-observation filtration.
- `Matching/LogRateAgreement.lean`: prove that the observable evaluator and
  analyzed rate path agree simultaneously at every time outside one null set.
- `Matching/AdaptedPolicy.lean`: construct an explicitly observation-adapted
  implementation, prove rate feasibility everywhere, transfer the pathwise
  service bounds, and prove its expected-reward guarantee.
- `Matching/PathLogValidity.lean`: every recorded completion has actually
  received its revealed demand by the recorded time, and its service remains
  frozen thereafter.
- `Matching/AdaptedRegularity.lean`: locally integrable rates, continuous and
  monotone service on every sample, and an integrable completion reward.
- `Matching/SchedulingTheorem.lean`: combine the construction into the public
  existence theorem `exists_observable_service_policy`, directly from a
  measurable feasible offline allocation in a compact nonnegative region.
- `Matching/FirstSegmentWork.lean` and `HistorySegmentWork.lean`: expected work
  on each coordinate before the actual first stop equals its first-completion
  probability, including random incoming histories and all integrability.
- `Matching/WorkRecursion.lean` and `WorkExpectation.lean`: split integrated
  terminal work across actual restart branches and prove its expectation equals
  the completion count for every finite recursion depth.
- `Matching/AdaptedWork.lean`: transfer this identity to the observable policy
  and prove the competitive lower bound for its total integrated work.
- `Matching/CoordinateComparison.lean` and `CoordinateOutcome.lean`: the
  first-segment potential calculation and actual random payoff for one tagged
  job, accounting for every other job's possible completion.
- `Matching/CoordinateBudget.lean` and `CoordinateStage.lean`: an individual
  unallocated-demand budget, its stopped occupation identity and integrability,
  and the resulting one-job comparison certificate.
- `Matching/CoordinatePayoff.lean`: preserve that certificate through the actual
  marked restart laws and drop the nonnegative budget when the tagged job ends.
- `Matching/CoordinateWork.lean` and `CoordinateGuarantee.lean`: exact expected
  service recursion for one job and the full coordinatewise competitive bound
  for the explicitly observable policy.
- `Matching/SupplyRegion.lean`: normalized monotone submodular neighborhood
  coverage, a compact convex downward closed feasible region containing zero,
  coordinate bounds, and supermodular scheduling deficiencies.
- `Matching/SupplyFlow.lean`: supported feasible supply flows satisfy all
  coverage constraints; their normalized assignment probabilities have mass at
  most one and recover the aggregate rates, including zero-supply types.
- `Matching/OfflineValue.lean`: existence of a pointwise offline optimum, its
  demand bound, Lipschitz continuity, measurability, and integrability. This does
  not yet supply a measurable selection of optimal allocations.

## Quantitative theorem now proved

`PosteriorData.posterior_policy_guarantee` states that, for a measurable bounded
nonnegative allocation `Y`, with `Y(h,z)[i] <= z[i]` on nonnegative demand vectors,
and an incoming probability measure on histories independent of the fresh unit
exponential demands,

```
E[initialStage.completionCount] >= (1 - exp(1 - exp(1))) * E[sum_i Y_i].
```

The posterior ODE, actual first-completion laws, restart data, finite execution,
measurability and integrability, potential decomposition, and accumulated
unallocated-demand budget bound used in this theorem are all proved here.
No process-specific Dynkin formula or global loss inequality is assumed in
this theorem. The earlier generic telescope and conditional-loss lemmas retain
their explicit hypotheses; the concrete policy proof supplies its own exact
recursion and quantitative budget argument.

`PosteriorData.posterior_service_guarantee` now transfers this bound to
`policyReward`, the sum of indicators that `policyService(x,1)[i] = x[i]`.
For a compact convex nonnegatively downward closed feasible region containing
zero, and allocations in that region, the exported `policyRate` is jointly
measurable and feasible at every query. Its integral `policyService` is continuous,
stays between zero and demand almost surely throughout `[0,1]`, and its count of
fully served jobs equals the recursive completion count almost surely.

`PosteriorData.posterior_adapted_guarantee` proves the same bound for
`adaptedReward`, computed by integrating `adaptedRate`. For every deterministic
time `t`, `adaptedRate(t, .)` is measurable for the completion-observation
filtration. It is jointly measurable and feasible at every query. Its rate and
service agree with the analyzed construction at all times outside one null set,
so the same simultaneous demand bounds and reward guarantee hold. Finite job
labels are assumed to have measurable singletons, as for the discrete sigma
algebra.

`PosteriorData.expected_adaptedWork_eq_reward` now proves
`E[sum_i adaptedService(x,1)[i]] = E[adaptedReward]` for the actual constructed
policy. `posterior_adapted_work_guarantee` therefore gives the same lower bound
for total expected work. The proof uses the actual stopping-clock occupation
identity and marked restart laws, and includes work on unfinished jobs.

`PosteriorData.posterior_adapted_coordinate_work_guarantee` proves the stronger
coordinatewise statement `E[adaptedService(x,1)[i]] >= ratio * E[Y_i]` for every
job, under the same feasible-region and demand-cap hypotheses. This is the
quantitative assertion of Proposition 4.5, for the constructed policy; its proof
uses finite restart induction and a separate budget per job. It even allows a
finite incoming history measure without normalization.

The combined theorem `StochasticMatching.exists_observable_service_policy`
takes a measurable allocation `Y`, a compact convex nonnegative region `P`
containing zero and closed under coordinatewise reductions, feasibility of `Y`,
and `Y_i <= z_i` on nonnegative demands. For independent unit exponential
demands and any independent incoming probability law on histories, it provides
a measurable completion log and jointly measurable rates that:

- record each job at most once, with no more entries than the number of jobs;
- are measurable for the information in the initial history and the log seen
  up to each deterministic time;
- lie in `P` at every query;
- have terminal integrated service in `P` on every sample;
- integrate to continuous, coordinatewise monotone service on every sample;
- stay between zero and demand almost surely at every time in `[0,1]`;
- realize every logged completion in `[0,1)`, revealing the actual demand and
  remaining frozen at that demand afterward;
- have integrable total terminal work, with its expectation equal to the
  expected fully served job count;
- attain expected work on each individual job at least
  `(1 - exp(1 - exp(1))) * E[Y_i]`;
- attain expected total work at least
  `(1 - exp(1 - exp(1))) * E[sum_i Y_i]`;
- attain expected fully served job count at least
  `(1 - exp(1 - exp(1))) * E[sum_i Y_i]`.

The supermodular maximum chain formula (Proposition 3.3) is now proved by
finite sign cancellation, including its probability version and comparison
of maximum tails from chain laws. `MatchingDeficiency.lean` also proves
the finite bipartite matching deficiency formula from Hall's theorem: an
optimal matching leaves exactly the maximum Hall deficiency unmatched.

The offline scheduling deficiency formula is also proved:
`offlineValue(supplyRegion, z) = sum z - maxSupplyDeficiency z` for
nonnegative demands and supplies. The proof establishes tight-set union
closure and a tight certificate at every optimum. The real-valued matching
deficiency is proved supermodular and its maximum equals the unmatched count
of an optimal finite matching. These deterministic formulas do not yet give
the Poisson/exponential equality in expectation.

The measurable optimizer-selection obligation for coverage regions is now
closed by an explicit continuous greedy construction (`GreedyAllocation`).
`exists_coverage_policy_against_offline_optimum` supplies an observable
scheduling policy directly from neighborhoods and nonnegative capacities,
with the actual expected offline scheduling optimum as benchmark. No input
allocation or unproved measurable-selection hypothesis is needed.

The full coverage-region/supply-flow equivalence (Lemma 2.3) is now proved
in `SupplyFlowConverse.lean`. Compact convex projection gives a supporting
flow; its row optimality yields a coverage cut if positive residual demand
remains. Column scaling then supplies exactly the requested rates. This proves
existence; the continuous selector described below closes measurable choice.

The flow selector is now explicit and continuous jointly in supplies and
requested rates. `ContinuousSupplyFlow.lean` eliminates edges using finite
cut bounds; its correctness uses the proved flow-existence theorem.
`AssignmentSelector.lean` converts the selected flow into measurable
assignment probabilities and finite probability laws, with an explicit reject
outcome, support on allowed neighbors, and exact rate recovery.

Poisson mass convolution, addition of independent Poisson variables, finite
subset-sum laws for the independent type-count model, and integration of
bounded-count Poisson-mixture tails are now checked. The chain formula also
holds at random measurable thresholds. `ExpectedOfflineDeficiency.lean`
proves integrability and the expectation formula for exponential deficiency,
and gives an explicit conditional bridge from a Poisson-mixture tail identity
to offline equality. That bridge is now discharged by the complete chain
duality proved in `PoissonExponentialChainLaw.lean`.

`ArrivalInstance.lean` realizes every finite type-count vector as an actual
bipartite graph of individual arrival copies and identifies its maximum
matching value. `OfflineDualityReduction.lean` proves expected offline equality
conditional on the explicitly named `PoissonExponentialChainLaw`. The law is
now proved, and `ExpectedOfflineEquality.lean` exports unconditional expected
offline equality for every finite instance. `IndependentBlocks.lean` proves mutual independence of all
disjoint groups of coordinates. `NestedPoissonCounts.lean` then proves the
full joint law of nested neighborhood counts as cumulative independent Poisson
increments, including arbitrary overlapping arrival-type neighborhoods.

The exponential side now has the corresponding joint nested-sum law.
`ExponentialPoissonTail.lean` proves the scalar Erlang/Poisson waiting-time
identity from actual sums of independent exponential variables.
`SingleSetChainLaw.lean` proves the one-set deficiency identity for arbitrary
subsets and neighborhoods. `OneJobOfflineEquality.lean` closes the complete
chain law and expected offline equality for instances with at most one job.

The renewal construction now has checked deterministic-time cut probabilities,
a fresh exponential residual law, and preservation of all independent future
variables. These laws are connected to the original exponential vector in
`VectorRenewalCut.lean`. `OrderedRenewalCuts.lean` proves uniqueness and
existence of the active waiting interval. `FiniteRenewalPoisson.lean` proves
that its actual finite arrival count has the truncated Poisson distribution.
The full joint identity for an arbitrary chain of observation times is now
proved by a multi-observation induction.

The two-time step is now proved. `VectorRenewalTotal.lean` transports the
residual waiting vector to its total remaining time. `FiniteRenewalJoint.lean`
proves joint probabilities for an exact count at the first time and survival
of the last waiting time at the second. `TwoTimePoissonLaw.lean` sums these
events and identifies their joint probability with independent Poisson
increments. `TwoTimeWaitingLaw.lean` converts counts into prefix-sum
inequalities, and `NestedPairWaitingLaw.lean` extends the result to arbitrary
nested subsets A of B. For independent unit exponential demands, it proves
P(a < sum_A Z and a+b < sum_B Z) =
P(K_a < |A| and K_a+K_b < |B|), with independent Poisson increments of means
a and b. This is a joint identity, including empty sets and zero times.
`BlockRenewalRestart.lean` restores the full remaining exponential vector after
each renewal cut and proves the translation rule for every later superset sum.
`SubsetRenewalPartition.lean` and `SubsetRenewalRecursion.lean` partition the
first observation and retain all future constraints. The exponential and
Poisson models satisfy the same finite recurrence in
`ExponentialChainRecurrence.lean` and `PoissonChainRecurrence.lean`.
`NestedWaitingCountLaw.lean` proves their joint identity for arbitrary finite
chains, and `PoissonThresholdAugmentation.lean` adds the independent threshold
as an extra arrival type. `ChainEnumeration.lean` enumerates any finite nested
family in inclusion order. The resulting
`poisson_exponential_chain_law` proves Lemma 3.4 without an extra hypothesis.
`expected_offline_equality` proves the general expected offline equality of
Theorem 3.1, for arbitrary finite sets and nonnegative arrival intensities.

The online coupling now has a full one-arrival construction.
`RejectionClockService.lean` adds a fresh independent rejection clock to the
service race, making the total event rate equal to the total arrival intensity.
`RoutingHazards.lean` proves the row and column identities of the type/job
rate matrix, including zero rates and forbidden edges. `MarkedArrivalCoupling.lean`
proves the time/type/job measure identities, while `RoutingRestarts.lean`
retains the full independent exponential residual law: rejection keeps all
jobs, and acceptance removes exactly the matched job.
`ShiftedService.lean` proves that advancing time after survival translates
every future completion clock correctly. `FirstEventDistribution.lean` and
`NextArrivalDistribution.lean` include the no-arrival outcome and prove a
normalized probability law whose type/time marginal is the prescribed Poisson
arrival law and whose job/time marginal is the augmented scheduling race.
`HistoryRoutingKernel.lean` proves measurable dependence on histories and
packages this law as a Markov kernel. Iteration into a complete arrival process,
its non-explosion/count law, and the full policy coupling are still required.

## Exact remaining scope

This is not an end-to-end formalization of the full matching paper. The current
quantitative theorems concern both the constructed completion count and the
actual integrated service path. Global rate feasibility, continuous service,
demand bounds, and equality of the fully served job count and the recursive
count are proved. The original-label log, demand/time correctness, absence of
repeated labels, and equality of count and log length are also proved.

The completion-log-generated time filtration is constructed. A measurable
log evaluator, its simultaneous almost-sure agreement with the original rate
path, and an observation-adapted implementation are now proved. Conditional
resampling is proved for the complete tagged one-step observation. The stronger
identification of the full running rates as conditional expectations at arbitrary
deterministic times remains unfinished; it is not needed as an assumed premise
of the proved adapted implementation's quantitative guarantee.
Deterministic-threshold memorylessness has not been substituted at an arbitrary
demand-dependent random threshold.

The actual online matching/scheduling policy coupling and the optimality upper
bound needed to formalize the complete paper remain outside the proved scope.
The general unweighted offline duality is now proved.
The matching-derived region and both directions of its supply-flow
characterization are proved. A continuous flow decomposition is now proved. The actual Poisson
policy coupling remains open. The offline value
is a continuous integrable function, and a continuous exact optimizer is
constructed for the coverage region. Selection for arbitrary compact downward
closed regions is not claimed.
The checked quantitative guarantee is for both total work and completion count.
The paper's stronger coordinatewise expected-work guarantee (Proposition 4.5)
is now proved for the constructed observable policy. The full constructed policy's work-completion
expectation identity is proved by the actual stopped-segment and restart
calculation, rather than assumed from the earlier clipped-exponential lemma.
All theorem hypotheses are visible in Lean. No proof placeholders or new
axioms are used.

## Concrete continuation point

The main quantitative chain is `StageRegion` -> `StageExpectation` ->
`ExecutionDefect` together with `SurvivalBudget` -> `BudgetRecurrence` ->
`PolicyGuarantee`. The actual count is `PosteriorStage.completionCount`, and its
log is `PosteriorStage.completionLog`. Preserve the incoming product-law
invariant and the measurable valid-history region through each marked restart.

The concrete fixed-label path is `PosteriorStage.ratePath` and its integral is
`cumulativePath`. The initial exports are `PosteriorData.policyRate`,
`policyService`, and `policyReward`. `LogRateAgreement` connects this path to
the observable reader; `adaptedRate`, `adaptedService`, and `adaptedReward` are
the adapted exports, with estimate `posterior_adapted_guarantee`. The public
combined scheduling statement is `exists_observable_service_policy`. The work
identity chain is `FirstSegmentWork` -> `HistorySegmentWork` -> `WorkRecursion`
-> `WorkExpectation` -> `AdaptedWork`. The coordinatewise chain is
`CoordinateComparison` / `CoordinateBudget` -> `CoordinateStage` ->
`CoordinatePayoff`, combined with `CoordinateWork` -> `CoordinateGuarantee`.
The next major work is the actual online policy coupling (Lemma 2.4), followed
by the optimality upper bound. The chain law and general expected offline
equality are now proved. The feasible
region, continuous flow decomposition, and deterministic offline formulas
are already proved. The full-process conditional-expectation identity is an
additional remaining target.

## Reproduce

Lean 4.19.0 and mathlib v4.19.0 are pinned in `lean-toolchain`, `lakefile.toml`
and `lake-manifest.json`. With Lean's normal `elan` installation:

```sh
lake exe cache get Mathlib.Data.Real.Basic Mathlib.Data.Fintype.Card Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus Mathlib.MeasureTheory.Integral.Prod Mathlib.Analysis.SpecialFunctions.ExpDeriv Mathlib.Probability.Distributions.Exponential Mathlib.MeasureTheory.Integral.Layercake Mathlib.MeasureTheory.Constructions.Pi Mathlib.Analysis.ODE.PicardLindelof Mathlib.Analysis.ODE.Gronwall Mathlib.Analysis.Convex.Integral Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator Mathlib.Probability.Process.Filtration Mathlib.Probability.ProductMeasure Mathlib.Probability.Kernel.IonescuTulcea.Traj
lake build
lake env lean Audit.lean
```

`verification.txt` records the actual build, the complete theorem axiom audit,
and source hashes for this checkpoint. No proof placeholders or new axioms are
allowed. Compiler binaries and dependency caches are omitted from the archive.
The audit verifies that each listed name is a theorem in Lean's checked
environment, then uses Lean's standard axiom collector with a shared visited
set to check the union of all theorem dependencies. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed.
The optional `python3 scripts/checkpoint.py /absolute/output.zip` command runs
the build and axiom audit, rejects proof placeholders, records source hashes,
and creates a new source archive. Run it from an environment with `lake` on PATH.

The original restricted workspace required a compatibility shim solely to find
the executable path without `/proc`; it did not alter Lean's proof kernel and
is unnecessary on ordinary machines.

## Checkpoint recovery

Download each ZIP when it is delivered and keep it outside the execution
workspace. Uploading that downloaded ZIP again permits checksum verification.
Saving a file does not by itself prove that a future session can retrieve it.
