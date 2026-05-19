# ByzantineCD — Byzantine-tolerant detection of causality, in Isabelle/HOL

Mechanisation of the impossibility results of

> Anshuman Misra and Ajay D. Kshemkalyani,
> **Byzantine-tolerant detection of causality: There is no holy grail.**
> *Parallel Computing* 124 (2025) 103136.
> https://doi.org/10.1016/j.parco.2025.103136

A local copy of the paper is in
[`paper/`](paper/Misra-Kshemkalyani-2025-Byzantine-tolerant-detection-of-causality.pdf).
The article is open access under CC-BY 4.0; the file is redistributed
here under the same license.

building on the AFP entry [`FLP`](https://www.isa-afp.org/entries/FLP.html)
(Bisping, Brodmann, Jungnickel, Rickmann, Seidler, Stüber,
Wilhelm-Weidner, Peters, Nestmann, 2025-03).

## Status

The session compiles against **Isabelle 2025-2 + AFP snapshot
`afp-2026-05-13`** in **~9 s** wall time, **20 theory files** at
100%, **0** `sorry` / `oops` / `apply` / `sledgehammer` in any proof.

Reproducing:

```sh
isabelle build -d $AFP -D ByzantineCD
```

with `$AFP` pointing at a checkout of the Archive of Formal Proofs
that includes the `FLP` entry.  The development imports only
`FLP.AsynchronousSystem`, `FLP.Execution`, `FLP.FLPTheorem`,
`FLP.FLPSystem`, and the AFP-FLP `Multiset.thy` indirectly.  The
abstract Consensus problem is re-stated locally rather than imported,
so the build is robust to AFP's `FLP` entry not exposing a
`Consensus.thy` of its own.

See [`ROADMAP.md`](ROADMAP.md) for the up-to-date status of every
theorem in the paper and what remains as future work.

## Scope

All 18 of the paper's theorems are fully proven (see
[`ROADMAP.md`](ROADMAP.md) for the per-theorem status table).
Highlights:

Fully proven:

- **Theorems 1, 2** (paper §4.1, `Theorems_1_2.thy`):
  FN and FN-or-FP unavoidable under Byzantine.  Constructive
  adversaries via fresh natural numbers.
- **Theorems 3, 4, 5** (paper §4.2, `Impossibility.thy`):
  CD impossible under unicast / broadcast / multicast.  Conditional
  only on a mild finiteness side condition `fin_cd`.  Proofs route
  *directly* through Theorem 1 (`CD_FN_unavoidable`); the paper's
  `Consensus ⪯ BlackBox ⪯ CD + FLP` chain is bypassed at the
  critical-path level (and preserved as paper-faithful documentation).
- **Theorems 6, 7** (paper §4.3, `CD_B_Algorithm.thy`):
  CD_B solvable under unicast / broadcast.  Mechanised at three
  layers: the abstract `naive_cd_B_alg` is correct under
  `correct_reporting` (Phase 1); the operational `Delivery.thy`
  reduces this to a structural delivery property on the global
  history (Phase 4); the refined `mode_admissible` of Phase 5
  internalises the delivery property; the inductive
  `Execution_Model.thy` exhibits a concrete operational construction
  that produces mode-admissible histories (Phases 6–8: fairness
  implies delivery + wf_history preserved + deadlock freedom).
- **Theorem 8** (paper §4.3, `CD_B_Algorithm.thy`):
  CD_B impossible under multicast.  Mechanised as the impossibility
  of a strengthened `produces_valid_F_B_recv_strong` predicate,
  using a fresh-id adversary at two correct processes.
- **Theorem 15** (paper §5.1, `CD_vs_Consensus.thy`):
  CD harder than Consensus under Byzantine.  Directly from CD
  unsolvability + `exists_consensus_alg`.
- **Theorem 16** (paper §5.1, `CD_vs_Consensus.thy`):
  Consensus harder than CD under crash failures.  Consensus-half
  exported from `flp_consensus_unsolvable`; CD-solvable-half via
  the `cd_alg_with_recv` signature — the naive algorithm
  `F := recv` produces valid F whenever `recv = adv_E adv`, the
  abstract content of the paper's "transitive propagation via
  execution messages".
- **Fair infinite executions** (paper-adjacent, `Liveness.thy`):
  the liveness companion to `Execution_Model.thy`.  Infinite
  executions modelled as `nat ⇒ 'p config`; the headline
  `fair_run_delivers` theorem says every correct-to-correct `Send`
  in a fair infinite run eventually has a matching `Receive`.
  Composes deadlock freedom + fairness assumption into a per-event
  liveness guarantee.
- **BRU and BCB-over-BRB primitives** (paper-adjacent,
  `Primitives.thy`): named abstractions of the two communication
  primitives invoked in paper §4.3 for T6 and T7.  `bru_satisfied`
  is the structural shape of BRU at the event level (every
  correct-to-correct `Send` has a matching `Receive`); the
  existing `fairness_implies_delivery` and `fair_run_delivers` of
  `Execution_Model.thy` / `Liveness.thy` discharge it from the
  inductive run model.  `bcb_causal_order` is the additional
  delivery-order property that BCB (over BRB) guarantees; together
  with BRU it makes `bcb_over_brb_satisfied`.  End-to-end
  composition theorems `bru_solves_CD_B_unicast` and
  `bcb_over_brb_solves_CD_B_broadcast` give operational T6 / T7
  named explicitly via the primitives; `fair_drained_run_solves_CD_B_*`
  ties it all the way back to a concrete fair drained run.
- **Concrete T6 demo** (`T6_Concrete.thy`): a fully-explicit
  worked example.  Two distinct correct processes; a three-step
  `run_step` sequence (`step_send`, `step_recv`, `step_internal`);
  proven to be fair, drained, well-formed, and to produce a
  history at which the naive algorithm solves CD_B for the
  resulting adversary.  Witnesses T6's existential
  non-vacuously: there is an actual adversary, an actual run, and
  an actual algorithm output.
- **Theorems 9–14** (paper §4.4 + §4.5, `CD_with_Crypto.thy`):
  CD impossibility under unicast / broadcast / multicast even
  with cryptography (T9, T10, T11) — direct corollaries of
  T3/T4/T5 since the Theorem-1 FN attack is crypto-independent.
  CD_B possibility under unicast / broadcast / multicast with
  cryptography (T12, T13, T14) — T12/T13 are corollaries of
  T6/T7 (crypto does not change the conclusion), while T14 is
  the genuinely new content: with crypto, multicast becomes
  solvable under BHB (whereas T8 said it was impossible without).
  At our abstraction level, crypto plays the same role as
  BRU/BCB-over-BRB do for T6/T7: it discharges
  `correct_reporting` under multicast.  The cryptographic
  primitive layer itself is below our abstraction.
- **Theorems 17, 18** (paper §5.2, `CO.thy`):
  CD ↔ CO interreducibility in the Byzantine model (T17), and CO
  subject to FN and FN-or-FP for internal-event witnesses (T18).
  T17's forward direction (`CD_solvable_imp_CO_solvable`) is
  proven outside any locale.  T18 is proven directly via a two-
  message fresh-id construction with a receive-event target.  T17's
  reverse direction is proven under the standard Byzantine premises
  by routing through `CD_impossible_*` + `CO_impossible_*` (both
  sides impossible, hence interreducible).

Out of scope (paper-adjacent, would deepen the mechanisation):

- **Concrete cryptographic primitive layer.**  `CD_with_Crypto.thy`
  discharges T9–T14 as corollaries treating crypto as an
  off-the-shelf primitive (the same way the paper cites Bracha
  1987 for BRB).  A faithful mechanisation of digital signatures,
  collision-resistant hashes, and recursive hash histories would
  let us state the paper's quantitative FP-prevention qualifier
  (FP prevented for `t < n/3` under Bracha's BRB).
- **Operational realisation of BCB causal order.**  `Primitives.thy`
  states `bcb_causal_order` and connects it to the broadcast-mode
  CD_B solvability theorem, but the underlying `run_step`
  scheduler does not enforce causal order on `step_recv`.  A
  scheduler-level refinement of the model would discharge that
  property operationally; we leave it out of scope at the same
  abstraction as crypto.

## File structure

| File                       | Purpose                                                                                                              |
|----------------------------|----------------------------------------------------------------------------------------------------------------------|
| `ROOT`                     | Session declaration; depends on AFP `FLP`.                                                                           |
| `ByzantineSystem.thy`      | Process partition (correct ⊎ byzantine), Consensus solver signature, `byzantineSystem` locale (no extra axioms).     |
| `Events.thy`               | Event datatype, per-process and global histories, program-order, message-order, happened-before relation, `hb_eval`. |
| `CD.thy`                   | `valid(F)`, false positives/negatives, adversary model, CD-solver signature, `produces_valid_F`, `CD_solvable`.      |
| `BlackBox.thy`             | `w_value`, BB output record, `solves_BlackBox`, `BlackBox_solvable`.                                                 |
| `Reductions.thy`           | The two reductions of §4.2 (R1 constructive in `byzantineSystem`; R2 in sub-locale `byzantineSystem_with_identification` with the paper's named meta-level step `cd_can_identify_correct`).  Preserved as paper-faithful documentation; not on the critical path of Theorems 3/4/5. |
| `Impossibility.thy`        | Theorems 3, 4, 5 plus a summary corollary.  Lives in `byzantineSystem` (not `_with_identification`) and routes directly through Theorem 1.                                                                           |
| `Theorems_1_2.thy`         | Theorems 1 and 2 (FN-unavoidable, FN-or-FP-unavoidable for internal events).  Constructive adversaries via fresh ids.|
| `BlackBox_Unsolvable.thy`  | *Proves* `¬ BlackBox_solvable procs correct` by direct reduction to Theorem 1 via the BB→CD projection.  This discharges what was previously the `bb_unsolv` hypothesis on Theorems 3/4/5. |
| `FLP_Consensus.thy`        | FLP-style consensus predicate and *proven* impossibility (no axiom) via AFP's `ConsensusFails`.  Retained as the AFP-FLP citation that motivates the paper's chain; not used in the headline impossibility proof. |
| `Foundation_Vacuity.thy`   | Regression diagnostic: retains the witness showing the abstract `solves_Consensus` predicate alone admits a trivial HOL solver. |
| `CD_vs_Consensus.thy`      | Theorem 15 (Byzantine: CD harder than Consensus) — fully proven from the existing CD impossibility and the abstract Consensus witness.  Theorem 16 (crash failures: Consensus harder than CD) — fully proven: Consensus half exported from `flp_consensus_unsolvable`; CD-solvable-half via the `cd_alg_with_recv` signature with `F := recv` under the abstract crash-faithfulness assumption `recv = adv_E adv`. |
| `BHB.thy`                  | The Byzantine happened-before relation (paper Definition 3) and the CD_B problem (paper Definition 6).  Definitional foundation for paper §4.3: `bhb`, `bhb_eval`, `valid_B`, `produces_valid_F_B`, `CD_B_solvable`, and structural lemmas (`bhb` is a sub-relation of `hb` against the same history). |
| `CD_B_Algorithm.thy`       | Theorems 6/7/8 (paper §4.3).  Abstract algorithm with `recv` input; `naive_cd_B_alg` proven correct under `correct_reporting`; T6/T7 as mode-tagged corollaries; T8 as `produces_valid_F_B_recv_strong_unsolvable`. |
| `Delivery.thy`             | Operational delivery layer: `messages_delivered_among` as the structural correct-to-correct delivery property; `mode_admissible` refined to bundle this with `wf_history`; operational versions of T6/T7. |
| `Execution_Model.thy`      | Inductive `run_step` (internal/send/recv/byzantine) with in-flight buffer.  Proves: `fairness_implies_delivery`, `wf_history_run`, `run_completes_to_mode_admissible_unicast`/`_broadcast` (closes the Phase 5 gap), `buffer_correct_inv`, `not_drained_can_step` (deadlock freedom). |
| `Liveness.thy`             | Real-world fairness on infinite executions: `infinite_run` (a `nat ⇒ 'p config` with adjacent `run_step`), `fair_run` (every buffered triple eventually leaves), and the liveness theorem `fair_run_delivers` (every correct-to-correct `Send` in some `E i` has a matching `Receive` in some `E j`).  Key technical lemma: `step_removes_triple_is_recv` — case analysis showing only `step_recv` can remove a buffer triple, and it adds the matching `Receive`. |
| `Primitives.thy`           | Byzantine Reliable Unicast (BRU) and Byzantine Causal Broadcast over Byzantine Reliable Broadcast (BCB-over-BRB) named explicitly at the event-level abstraction.  `bru_satisfied`, `bcb_causal_order`, `bcb_over_brb_satisfied` predicates; operational discharge of BRU from the run model (`drained_run_satisfies_bru`, `fair_run_satisfies_bru_pointwise`); end-to-end composition theorems `T6_unicast_via_bru`, `T7_broadcast_via_bcb_over_brb`, `bru_solves_CD_B_unicast`, `bcb_over_brb_solves_CD_B_broadcast`, `fair_drained_run_solves_CD_B_unicast`/`_broadcast`. |
| `T6_Concrete.thy`          | Fully-concrete worked example of T6.  Two distinct correct processes `p_a`, `p_b`; explicit three-step `run_step` sequence (`step_send`, `step_recv`, `step_internal`); proofs that the run is fair, drained, well-formed; composition with `fair_drained_run_solves_CD_B_unicast` to demonstrate the naive algorithm solving CD_B at the resulting adversary.  Witnesses that T6's existential statement is non-vacuously satisfiable. |
| `CD_with_Crypto.thy`       | Theorems 9–14 (paper §4.4 + §4.5).  CD impossibility with crypto (T9, T10, T11) as corollaries of T3/T4/T5; CD_B possibility with crypto (T12, T13) as corollaries of T6/T7; T14 (the genuinely new multicast-with-crypto possibility) via the naive algorithm under `correct_reporting`.  Crypto is treated at the same abstraction as BRU/BCB-over-BRB: it discharges `correct_reporting` operationally, and the primitive layer is below our abstraction. |
| `CO.thy`                   | Theorems 17 and 18 (paper §5.2).  Causal Ordering problem: `co_admissible` (CD admissibility restricted to receive-event targets), `produces_valid_F_CO`, `CO_solvable`.  Forward T17 (`CD_solvable_imp_CO_solvable`) constructive.  T18a (`CO_FN_unavoidable`) and T18b (`CO_FN_or_FP_unavoidable_internal`) by fresh-id constructions adapted to receive-event targets.  `CO_impossible_unicast`/`broadcast`/`multicast` plus `T17_CO_interreducible_with_CD` under Byzantine premises. |
| `document/root.tex`        | AFP-style cover-page LaTeX (title, abstract, table of contents, reading-order guide).                                |
| `document/root.bib`        | Bibliography (source paper, AFP-FLP entry, Lamport 1978).                                                            |

A pre-built copy of the session document is committed at
[`dist/ByzantineCD.pdf`](dist/ByzantineCD.pdf) (134 pages, A4) for
direct reading; regenerate it any time with
`isabelle build -d $AFP -o document=pdf -D ByzantineCD`.

See [`AFP_SUBMISSION.md`](AFP_SUBMISSION.md) at the repo root for
notes on AFP submission preparation.

## Proof strategy

We mirror the paper exactly:

```
Consensus  ⪯  BlackBox  ⪯  CD
   ↑ FLP        ↑ R1        ↑ R2  (meta-level)
```

- **R1 — `consensus_reduces_to_blackbox`.** Constructive.  Given a BB
  solver, build a Consensus algorithm that at process `i` outputs
  `bb_w (bb_alg procs V e_default p_star)`, where `p_star ∈ correct`
  is hard-wired.  Agreement is by constancy in `i`; Validity is by
  instantiating BB-correctness at the trivial adversary; Termination is
  by totality of `'p consensus_alg`.

- **R2 — `blackbox_reduces_to_cd`.** The paper's argument is meta-level:
  > *"To solve CD, it is necessary to identify Byzantine processes…"*

  We capture this faithfully as a single named locale assumption,
  `cd_can_identify_correct`, in the sub-locale
  `byzantineSystem_with_identification`.  The assumption states:

  > Every CD solver `cd_alg` that `produces_valid_F` can be augmented to a
  > solver `cd_alg'` that **(i)** produces the same valid F, **(ii)**
  > returns the decision `True`, and **(iii)** also reports the set of
  > correct processes.

  This is the positive form of Misra–Kshemkalyani's meta-level
  contrapositive ("producing valid F is impossible without identifying
  the correct set").  From this assumption the reduction is fully
  constructive (`bb_from_cd_with_L`) and the three sub-claims of
  `bb_correct_output` are discharged one by one, matching the paper's
  enumeration ("Managing false positives" / "Managing false negatives").

- **Composition (the direct route, used by Theorems 3/4/5).**
  `Impossibility.thy` chains `CD_solvable mode correct` (which
  existentially extracts a `produces_valid_F` witness) with Theorem 1
  (`CD_FN_unavoidable`).  Theorem 1 immediately yields an admissible
  adversary that defeats the witness — contradiction.  No BlackBox
  detour is needed; the paper's `Consensus ⪯ BlackBox ⪯ CD + FLP`
  chain is bypassed at the headline-theorem level.

- **Paper's chain (preserved as documentation, not on the critical
  path).**  `Reductions.thy` retains both reductions of §4.2:
  R1 constructive (BB ⪯ Consensus) and R2 conditional on
  `cd_can_identify_correct` (CD ⪯ BB).  `BlackBox_Unsolvable.thy`
  proves `¬ BlackBox_solvable procs correct` directly by the same
  Theorem-1 reduction, applied to the BB-to-CD projection.
  `FLP_Consensus.thy` proves the FLP-style consensus impossibility
  (`flp_consensus_unsolvable`) against the AFP entry's
  `ConsensusFails`.  These three together reproduce the paper's
  chain as a fully proven alternative derivation of Theorems 3/4/5
  — but the headline theorems no longer need any of it.

## Assumptions introduced beyond the paper

The headline impossibility theorems (Theorems 3/4/5 in
`Impossibility.thy`) take exactly one mild side hypothesis,
`fin_cd`.  No HOL axioms, no locale axioms on the impossibility
chain.

1. **`fin_cd`** *(side hypothesis of Theorems 3/4/5)*.
   Statement: every candidate CD-solver `cd_alg` that produces a
   valid `F` for `correct` has finite `events_of` output, at the
   adversary's local target event of the form `Internal p_i_in 2`:

   ```
   ∀cd_alg. produces_valid_F correct cd_alg ⟶
       ∀p_i_in. finite (events_of
                          (fst (cd_alg p_i_in (Internal p_i_in 2))))
   ```

   Faithfulness: any algorithm whose output `F` is supported on
   `procs` (the finite process set) trivially satisfies this.  The
   condition exposes the requirement that a candidate CD-solver's
   collected history is "implementable" in the sense of producing
   only finitely many events at any given query.  It is identical
   in shape to the `fin_F` side hypothesis of Theorem 1
   (`CD_FN_unavoidable` in `Theorems_1_2.thy`), where it is needed
   to ensure a fresh natural number exists.

   *History — the discharge of two previous hypotheses.*

   - Earlier revisions of Theorems 3/4/5 took an unconditional
     meta-level hypothesis `¬ BlackBox_solvable procs correct`
     (named `bb_unsolv`).  That hypothesis was *discharged*:
     `BlackBox_unsolvable` is now a proven theorem in
     `BlackBox_Unsolvable.thy`, derived from Theorem 1 via the
     BB-to-CD projection
     `(λi e. (bb_F (bb_alg procs (λ_. False) e i), True))`.

   - Theorems 3/4/5 previously lived in
     `byzantineSystem_with_identification`, which adds the locale
     axiom `cd_can_identify_correct` (R2's meta-level step:
     "any CD-solver that produces valid F can be augmented to
     report L = correct").  After the above discharge, the
     impossibility chain no longer needs to go through BlackBox at
     all — Theorem 1 contradicts CD-solvability directly — so
     Theorems 3/4/5 now live in plain `byzantineSystem`, and
     `cd_can_identify_correct` is no longer on the critical path.
     R2 itself is preserved in `Reductions.thy` as paper-faithful
     documentation of the §4.2 chain (it provides an alternative
     derivation of `¬ BlackBox_solvable`, which composes with
     `BlackBox_unsolvable` for an alternative — but redundant —
     route to the headline theorems).

   - Even earlier revisions packaged `bb_unsolv` as an elaborate
     "bridge" predicate `bb_realizes_flp_consensus`.  Logically
     equivalent to `¬ BlackBox_solvable` (because
     `flp_consensus_unsolvable` makes its inner existential always
     False); fully retired now.

   - The formerly-vacuous locale axiom
     `byzantineSystem.flp_consensus_impossibility` (unsatisfiable
     at the abstract-function level) was retired in an even
     earlier round; `Foundation_Vacuity.thy` retains the
     machine-checked counter-example as a regression test.

   The proven theorem `flp_consensus_unsolvable` (in
   `FLP_Consensus.thy`, discharged against the AFP entry's
   `ConsensusFails`) is retained as the AFP-FLP citation that
   motivates the paper's chosen chain.  It is not on the
   impossibility chain.

2. **`byzantineSystem_with_identification.cd_can_identify_correct`** *(in
   `Reductions.thy`)*.
   Statement: any CD solver that produces a valid F can be augmented to
   also report `L = correct` and decision `True`.
   Faithfulness: this is the positive form of the meta-level
   contrapositive that Misra–Kshemkalyani argue in §4.2:
   > *"If there were an algorithm to make F match E, it requires
   > identifying whether each of the processes that input their execution
   > histories is correct or Byzantine, and tracing and dealing with /
   > resolving the impact of contamination via message passing by the
   > Byzantine processes from and through those Byzantine processes on
   > the execution histories of processes at other processes."*

   We chose this formulation because the paper's argument is informal
   and meta-level; it argues that any algorithm with the
   `produces_valid_F` property *internally* has the data required to
   identify correct processes.  Our locale assumption says: extracting
   that data into an explicit output yields the augmented solver.  No
   constructive recipe for the extraction is committed to.

## Gaps from the paper that we had to fill

These are points where the paper's prose underspecifies what is meant; we
made the conservative choice (the one that yields the weakest
formalisation faithful to the prose) in each case.

1. **Universally-quantified `e_h^x` in `valid(F)`.**  Definition 5 says
   "∀ e_h^x" without bounding the variable.  We range it over
   `events_of E ∪ events_of F`, matching the paper's later clarification
   that *"we have to evaluate … even if e_h^x ∈ (T(E) ∪ T(F)) ∖ T(E)"*.

2. **The interpretation of `F` in `w_value`.**  In §4.2 the Black_Box
   problem's "else" branch is `CD(E, F, e*_i)`.  We make explicit that
   the `F` here is the algorithm's own collected `F'` (which is what
   CD outputs), not an externally-supplied history.  The
   `bb_correct_output` predicate evaluates `w_value` at the BB output's
   `bb_F` field accordingly.

3. **The `b` field of the augmented CD solver.**  Definition 5's "1 is
   returned" is the algorithm's claim of validity.  Our
   `produces_valid_F_with_L` requires `b = True` alongside validity of
   `F`, matching the paper's reading.

4. **Mode tag on `CD_solvable`.**  Definition 5 is mode-agnostic at its
   surface; the mode only matters in the reduction (and in the
   Byzantine-happened-before refinements that we do not formalise).  Our
   `CD_solvable Unicast` ⟺ `CD_solvable Broadcast` ⟺ `CD_solvable
   Multicast` at the abstraction level of Definition 5; the three
   impossibility theorems are nevertheless stated separately so that
   downstream developments which refine the mode (e.g., for the
   B-happened-before results) can pick the right specialisation.

5. **`correct ≠ {}` as a side condition.**  The paper does not state
   this explicitly but FLP needs at least one correct process.  All three
   impossibility theorems take both `byzantine ≠ {}` and
   `correct ≠ {}` as hypotheses.

## Mismatches with FLP's model (if any)

The AFP `FLP` entry models *crash-stop* failures with a record-shaped
distributed-system locale.  Our development is parametric in the process
type only, intentionally abstracted away from the AFP entry's record
shapes.  The single touch-point is `flp_consensus_unsolvable` in
`FLP_Consensus.thy` — a *proven* theorem (not an axiom), discharged
against the AFP entry's `flpPseudoConsensus.ConsensusFails`.  An earlier
revision of this development used a `flp_consensus_impossibility` locale
axiom in place of the proven theorem; that axiom turned out to be
unsatisfiable at the abstract-function level (see
`Foundation_Vacuity.thy`) and was retired.  The headline impossibility
theorems (3/4/5) no longer rely on any FLP axiom — they route directly
through Theorem 1 (`CD_FN_unavoidable`); `flp_consensus_unsolvable` is
retained as the AFP-FLP citation that motivates the paper's chosen
chain.

## The B-happened-before extension (paper §4.3)

The B-happened-before extension is now implemented end-to-end:

- `BHB.thy` defines `bhb`, `bhb_eval`, `valid_B`, `produces_valid_F_B`,
  `CD_B_solvable`, plus structural lemmas (`bhb` is a sub-relation of
  `hb` against the same history; bhb's endpoints are at correct
  processes).
- `CD_B_Algorithm.thy` introduces a richer algorithm signature
  `'p cd_alg_with_recv` that takes a per-peer reported history, and
  proves the abstract correctness of the trivial `naive_cd_B_alg`
  under `correct_reporting`.  T6, T7 fall out as mode-tagged
  corollaries; T8 is mechanised as the impossibility of a
  strengthened `produces_valid_F_B_recv_strong` predicate.
- `Delivery.thy` connects `correct_reporting` to a structural
  delivery property on the global history.
- `Execution_Model.thy` exhibits a concrete operational construction
  (inductive `run_step` with explicit in-flight buffer) and proves
  `run_completes_to_mode_admissible_unicast`/`_broadcast` plus
  deadlock freedom.

`Events.thy`'s `Send`/`Receive` events carry peer fields exactly to
support this stack.

## How to read the proofs

The proofs are written in **declarative Isar**, no `apply`-style.  Each
named step (`have …`) in the proof body should correspond to a named
claim in the paper's prose.  For instance, in
`bb_from_cd_with_L_correct`:

- `claim_valid` matches the paper's "Managing false negatives — the
  collected F must match E";
- `claim_w` matches the explicit piecewise definition of `w` in §4.2;
- `claim_L` matches "and locally returns L, a list of ids of correct
  processes".

If you find a step closed by `by auto` or `by simp` whose argument is
not transparent at a glance, please open an issue — that violates the
project's no-silent-gaps policy.

## Licence

Same as the FLP AFP entry: BSD-3-Clause.
