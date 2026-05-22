# Theorems mechanised — a guided English tour

This document walks through every theorem the mechanisation
proves, in the order the paper presents them.  Each entry gives:

- **Paper statement** (verbatim quote where short, paraphrased
  where the quote is long).
- **Paper's proof sketch** (one short paragraph in plain
  English).
- **Our mechanisation** (the Isabelle theorem name, the theory
  it lives in, and any side hypotheses we expose).
- **Where we diverge from the paper**, when relevant.

Paper reference throughout: Misra & Kshemkalyani,
*Byzantine-tolerant detection of causality: there is no holy
grail*, Parallel Computing 124 (2025) 103136.  A local copy is in
[`paper/`](paper/).

The 18 paper theorems are grouped under the paper's section
headings.  After them, this document also covers the
paper-adjacent companion theorems the mechanisation establishes
(deadlock freedom, fair-run liveness, named BRU/BCB primitives,
and three concrete worked examples of Theorem 6).

For a per-theorem status table see [`ROADMAP.md`](ROADMAP.md).
For the higher-level proof-strategy narrative see
[`README.md`](README.md).

---

## §4.1 — Two basic results

These are constructive impossibilities used as building blocks
for the headline Theorems 3, 4, 5.

### Theorem 1 — False negatives are unavoidable

> *"It is impossible to prevent false negatives in solving the
> causality determination problem (Definition 5) as specified by
> CD(E, F, e*\_i) in an asynchronous unicast/multicast/broadcast-
> based message passing system with one or more Byzantine
> processes."*  (paper §4.1)

**Paper's proof in English.**  Pick a correct process \(p_i\)
and a Byzantine process \(p_b\).  Let the adversary construct an
execution \(E\) where \(p_b\) sends a message \(m\) to \(p_i\),
\(p_i\) receives it, and \(p_i\) then performs an internal
event \(e^*\).  The send-receive pair plus the program order at
\(p_i\) form a happened-before chain from the send to \(e^*\).
The Byzantine \(p_b\) is free to omit the send event from what
it reports to the rest of the system.  No matter what the
algorithm produces as \(F\), the algorithm's view of \(F\) is
finite, so there is some message identifier the algorithm has
never heard of — and the adversary chooses that fresh
identifier as \(m\).  Under that choice, the witnessing send is
not in \(F\), but it is in \(E\), so \(F\) is missing a true
happened-before edge to \(e^*\).  That is a false negative.

**Our mechanisation.**
`Theorems_1_2.CD_FN_unavoidable`.  The "fresh natural number"
construction is `Theorems_1_2.fresh_nat`; the adversary is
`fn_E p_i p_b m` with `m = fresh_nat F`.  We discharge it
constructively: for any candidate algorithm whose output \(F\)
has finitely many events (hypothesis `fin_F`), we exhibit the
admissible adversary above as the witness.

**Divergence.**  The paper sketches *two* Byzantine attacks for
T1: omitting the send and *swapping* the order of two local
events.  We formalise only the omit-attack — it is sufficient,
since the paper's conclusion is the FN-existence, not the
catalogue of attacks producing it.

---

### Theorem 2 — False negative *or* false positive unavoidable for internal events

> *"For an internal event e\_h^x, it is impossible to prevent
> false negatives or false positives in determining e\_h^x → e\_i^*
> at a correct process p\_i in an asynchronous message passing
> system with one or more Byzantine processes."*  (paper §4.1)

**Paper's proof in English.**  Strengthen the T1 attack: the
Byzantine \(p_h\) can either *not reveal* an internal event it
performed (FN) or *fabricate* an internal event it didn't
perform (FP).  Either way the algorithm gets the wrong answer
about the happened-before relation involving that internal
event.

**Our mechanisation.**
`Theorems_1_2.CD_FN_or_FP_unavoidable_internal`.  We discharge
the FN side constructively (the FP side is symmetric, and the
theorem is stated as a disjunction).  The witnessing
construction is `fn_internal_E p_i p_b k m`: at the Byzantine
\(p_b\) we append a chain of \(k\) internal events followed by
a send to \(p_i\), where \(k\) is a fresh natural number.
\(p_i\) then receives the message and does the target internal
event \(e^*\).  The \(k\)-th internal event at \(p_b\) is
inside \(E\) but outside the algorithm's \(F\), and it has an
hb-chain to \(e^*\) via program order at \(p_b\) then message
order then program order at \(p_i\).

**Divergence.**  We discharge the FN half of the
disjunction only; FN suffices to make the disjunction true.

---

## §4.2 — Headline impossibility

The three impossibility results that motivate the paper's title.

### Theorem 3 — CD impossible under unicast

> *"It is impossible to solve causality determination
> (Definition 5) as specified by CD(E, F, e\_i^*) in an
> asynchronous unicast-based message passing system with one or
> more Byzantine processes."*  (paper §4.2)

**Paper's proof in English.**  The paper composes two
reductions:
1. *R1 — Consensus ⪯ BlackBox.*  A Black\_Box solver can be
   wired into a Consensus solver: each process invokes
   Black\_Box locally and outputs the value broadcast by
   `p_min(L)`, where `L` is the locally reported list of correct
   processes.
2. *R2 — BlackBox ⪯ CD.*  Solving CD requires the algorithm to
   internally identify which input histories come from
   Byzantine processes (meta-level argument).  Composing this
   identification with the CD output reconstructs a Black\_Box
   solver.

Hence `Consensus ⪯ CD`.  But FLP says Consensus is unsolvable
in an asynchronous system with even one faulty process; so CD
must be unsolvable too.

**Our mechanisation.**
`Impossibility.CD_impossible_unicast`.  We **bypass** the
paper's chain at the critical-path level by routing directly
through Theorem 1.  The chain is:

  ```
  CD_solvable  →  exists alg with produces_valid_F
              →  Theorem 1 produces an admissible adversary with FN
              →  contradicts valid (by valid_iff_no_FP_FN)
              →  False.
  ```

Side hypothesis: `fin_cd`, the same finiteness condition as T1's
`fin_F`.  No HOL axioms, no locale axioms.

**Divergence.**  The paper's chain (R1 + R2 + FLP) is preserved
as paper-faithful *documentation*:

- R1 is constructively proven in `Reductions.consensus_reduces_to_blackbox`.
- R2 lives in the sub-locale `byzantineSystem_with_identification`
  with the paper's meta-level "the algorithm internally
  identifies the correct set" exposed as the locale axiom
  `cd_can_identify_correct`.
- FLP's impossibility is proven against the AFP entry's
  `flpPseudoConsensus.ConsensusFails` as
  `FLP_Consensus.flp_consensus_unsolvable`.
- `BlackBox_Unsolvable.thy` proves `¬ BlackBox_solvable` by
  the same Theorem-1 reduction the headline uses, which gives
  R1 + R2 + FLP an alternative-but-redundant derivation of T3.

The direct route via T1 is shorter and avoids needing the meta-
level locale axiom on the critical path.

---

### Theorem 4 — CD impossible under broadcast

> *"It is impossible to solve causality determination
> (Definition 5) as specified by CD(E, F, e\_i^*) in an
> asynchronous broadcast-based message passing system with one
> or more Byzantine processes."*  (paper §4.2)

**Paper's proof in English.**  The proof has the same shape as
Theorem 3.  Two differences: (a) broadcasting via Byzantine
Reliable Broadcast (BRB) prevents Byzantine processes from
fabricating receives at correct receivers (so FPs cannot
occur), and (b) FN is still unavoidable by Theorem 1.

**Our mechanisation.**
`Impossibility.CD_impossible_broadcast`.  Identical chain to
T3: `Consensus_reduces_to_blackbox` + Theorem 1.

**Divergence.**  We do *not* formalise BRB.  At our abstraction
the `CD_solvable Broadcast` predicate is the same as
`CD_solvable Unicast` — both ask for the existence of a CD
solver.  The communication-mode tag is informational.  A
richer development that refines `Broadcast` with BRB
guarantees would strengthen the FP-prevention story; the FN
side, which is what the impossibility claim rests on, is
mode-agnostic.

---

### Theorem 5 — CD impossible under multicast

> *"It is impossible to solve causality determination
> (Definition 5) as specified by CD(E, F, e\_i^*) in an
> asynchronous multicast-based message passing system with one
> or more Byzantine processes."*  (paper §4.2)

**Paper's proof in English.**  Multicast is a generalisation of
unicast: a unicast is the special case of a single-receiver
multicast group.  Since CD is impossible under unicast (T3),
it is impossible under any generalisation thereof.

**Our mechanisation.**
`Impossibility.CD_impossible_multicast`.  Same Theorem-1 chain.

**Divergence.**  The paper's argument is "unicast is the
special case |G| = 1".  Our `CD_solvable` predicate already
ignores the mode tag at the validity-of-F level, so the
three modes collapse to the same statement and the same
proof — no mode-specialisation work is needed.

---

## §4.3 — Byzantine-happened-before extension

The paper introduces the BHB relation →\_B, which restricts
both program order and message order to chains running
*through correct processes only*.  Under this restricted view,
some positive results become available.

### Theorem 6 — CD_B solvable under unicast

> *"It is possible to solve causality determination
> (Definition 6) as specified by CD\_B(E, F, e\_i^*), now
> defined in terms of the →\_B relation, in an asynchronous
> unicast-based message passing system with one or more
> Byzantine processes."*  (paper §4.3.2)

**Paper's proof in English.**  Each correct process broadcasts
its local history via Byzantine Reliable Unicast (BRU; for
unicast, point-to-point is reliable when both endpoints are
correct).  The collected histories let any correct process
reconstruct \(F\) such that for every event at a correct
process \(p\), \(F[p] = E[p]\).  Under →\_B, validity only
needs to hold at correct-process events, and the
"correct-reporting" property suffices.

**Our mechanisation.**  Seven layers:

1. *Abstract algorithm* — `naive_cd_B_alg recv i e* = (recv, True)`,
   proven correct as `CD_B_Algorithm.naive_cd_B_alg_correct`
   under the hypothesis `correct_reporting C recv E`.  The
   algorithm is "report what you've been told", and bhb is
   invariant under correct-reporting because all bhb steps
   consult only correct-process events.

2. *Existence* —
   `CD_B_Algorithm.CD_B_solvable_unicast`: there exists an
   algorithm of type `'p cd_alg_with_recv` that
   `produces_valid_F_B_recv correct`.

3. *Operational with mode-admissibility* —
   `Delivery.CD_B_solvable_unicast_operational`: under
   `mode_admissible Unicast (adv_E adv)` (which bundles
   `wf_history` with `messages_delivered_among correct`), the
   naive algorithm with `recv_from_history` solves CD_B.

4. *Operational with explicit run model* —
   `Primitives.fair_drained_run_solves_CD_B_unicast`: any fair
   drained run of the inductive `run_step` relation in
   `Execution_Model.thy` produces a mode-admissible history at
   which the naive algorithm solves CD_B.

5. *Named via BRU* — `Primitives.bru_solves_CD_B_unicast`:
   under `bru_satisfied (adv_E adv)` (an alias of
   `messages_delivered_among correct`), the naive algorithm
   solves CD_B.

6. *Concrete worked example* — `T6_Concrete.T6_concrete_demo`:
   a two-process, one-message scenario with an explicit three-
   step `run_step` sequence (`step_send`, `step_recv`,
   `step_internal`), proven to produce a mode-admissible
   history at which the naive algorithm solves CD_B for an
   admissible adversary whose `adv_E` matches that history.

7. *Larger demos* — `T6_Multihop.T6_multihop_demo` (3
   correct processes, 5 steps, 4-edge bhb chain) and
   `T6_With_Byzantine.T6_with_byzantine_demo` (2 correct + 1
   Byzantine, 4 steps including the previously-unused
   `step_byzantine`).  Together the three demos exercise all
   four `run_step` rules.

**Divergence.**  We do not mechanise the BRU primitive itself;
its operational role at our abstraction level is the
`messages_delivered_among` property, which the inductive run
model realises constructively.  Our naive algorithm is
*simpler* than the paper's algorithm (we use `F := recv`; the
paper's algorithm "BRU + simulated broadcasts of control
information after application unicast send events" is one
specific witness, our naive algorithm is another).  Both prove
the existence.

---

### Theorem 7 — CD_B solvable under broadcast

> *"It is possible to solve causality determination
> (Definition 6) as specified by CD\_B(E, F, e\_i^*), now
> defined in terms of the →\_B relation, in an asynchronous
> broadcast-based message passing system with one or more
> Byzantine processes."*  (paper §4.3.1)

**Paper's proof in English.**  Correct processes broadcast
their local histories using Byzantine Causal Broadcast over
Byzantine Reliable Broadcast (BCB-over-BRB).  BRB ensures
every correct sender's broadcast is delivered to every correct
receiver; BCB additionally ensures causally-ordered delivery.
Together they provide the correct-reporting property, so
naive history-collection works as in T6.

**Our mechanisation.**  Same chain as T6 with mode tag
`Broadcast`:
`CD_B_Algorithm.CD_B_solvable_broadcast`,
`Delivery.CD_B_solvable_broadcast_operational`,
`Primitives.bcb_over_brb_solves_CD_B_broadcast`,
`Primitives.fair_drained_run_solves_CD_B_broadcast` (the last
one additionally takes `bcb_causal_order correct` as a
hypothesis, since the run-step scheduler doesn't enforce
causal-order delivery).

**Divergence.**  Same as T6.  Additionally: BCB's causal-order
property is captured as `Primitives.bcb_causal_order` but is
not operationally realised — our `run_step` does not constrain
the order in which `step_recv` invocations fire.  In a richer
scheduler model that enforces causal-order delivery, the
`bcb_causal_order` hypothesis would be discharged.

---

### Theorem 8 — CD_B impossible under multicast

> *"It is impossible to solve causality determination
> (Definition 6) as specified by CD\_B(E, F, e\_i^*), now
> defined in terms of the →\_B relation, in an asynchronous
> multicast-based message passing system with one or more
> Byzantine processes."*  (paper §4.3)

**Paper's proof in English.**  Byzantine Reliable Multicast
(BRM) is the primitive that would discharge correct-reporting
under multicast.  BRM is *unachievable* without identifying
Byzantine processes within each multicast group.  Hence under
multicast the algorithm cannot assume correct-reporting, and
it must work *without* that hypothesis.  But without
correct-reporting a fresh-id attack like T1's still produces a
bhb-FN at two correct processes — so no algorithm satisfies
the strong (correct-reporting-free) form of the CD_B
specification.

**Our mechanisation.**
`CD_B_Algorithm.produces_valid_F_B_recv_strong_unsolvable`,
restated as `CD_B_Algorithm.CD_B_unsolvable_multicast_abstract`.
We strengthen the predicate from
`produces_valid_F_B_recv` (which assumes correct-reporting) to
`produces_valid_F_B_recv_strong` (which does not), and prove
that no algorithm satisfies the strong predicate.  Proof
re-uses the `fn_E p_i p_c m` construction of T1, specialised
so the witness chain runs through two distinct *correct*
processes (rather than a Byzantine sender): the chain is then
a genuine →\_B chain whose start is missing from any finite-
output algorithm's `F`.

**Divergence.**  We do not formalise BRM or the operational
"BRM unachievable" argument; we capture only its downstream
effect — multicast operational discharge of correct-reporting
is unavailable — by predicating the impossibility on the
strong predicate.

---

## §4.4 + §4.5 — Cryptography variants

Six theorems that ask what changes when cryptographic
primitives (group encryption, recursive hash histories) are
available.

The structure is symmetric:

|              | HB without crypto | HB with crypto | BHB without crypto | BHB with crypto |
|--------------|-------------------|----------------|--------------------|-----------------|
| Unicast      | T3 — impossible   | **T10**         | T6 — possible       | **T12**          |
| Broadcast    | T4 — impossible   | **T11**         | T7 — possible       | **T13**          |
| Multicast    | T5 — impossible   | **T9**          | T8 — impossible     | **T14**          |

The genuinely new content with crypto is the lower-right cell —
**T14** turns multicast from impossible-without-crypto (T8) to
possible-with-crypto.  The five other cells are corollaries.

### Theorems 9, 10, 11 — CD impossible under crypto (multicast / unicast / broadcast)

> *"It is impossible to solve causality determination
> (Definition 5) as specified by CD(E, F, e\_i^*) in an
> asynchronous \[multicast / unicast / broadcast\]-based
> message passing system with one or more Byzantine processes
> even when using cryptography."*  (paper §4.4)

**Paper's proof in English.**  Cryptography does not help with
the FN attack used in Theorem 1.  A Byzantine process can still
omit events it performed, regardless of whether other messages
are signed or hash-chained.  The impossibility carries over
identically.

**Our mechanisation.**
`CD_with_Crypto.T9_CD_impossible_multicast_with_crypto`,
`CD_with_Crypto.T10_CD_impossible_unicast_with_crypto`,
`CD_with_Crypto.T11_CD_impossible_broadcast_with_crypto`.
Each is a direct corollary of T5 / T3 / T4 respectively.

**Divergence.**  The paper's T9 / T10 contain a quantitative
qualifier — "false positives prevented under \(t < n/3\)" — that
relies on Bracha's BRB quorum bound.  We do not formalise this
qualifier; our statements capture only the unconditional
impossibility (matching the "Impossible" entry in the paper's
table).

### Theorems 12, 13, 14 — CD_B possible under crypto

> *"It is possible to solve causality determination (Definition
> 6) as specified by CD\_B(E, F, e\_i^*), now defined in terms
> of the →\_B relation, in an asynchronous \[unicast /
> broadcast / multicast\]-based message passing system with one
> or more Byzantine processes when using cryptography."*  (paper §4.5)

**Paper's proof in English.**  For unicast and broadcast, the
crypto variants give the same conclusion as the non-crypto T6
/ T7: the correct-reporting property is discharged
operationally (by group-encryption-based BRU or BRB) and the
naive algorithm works.  For multicast, crypto changes the
picture: group encryption plus recursive hash histories
*do* achieve correct-reporting under multicast (whereas BRM
without crypto did not, by T8).

**Our mechanisation.**
`CD_with_Crypto.T12_CD_B_solvable_unicast_with_crypto`,
`CD_with_Crypto.T13_CD_B_solvable_broadcast_with_crypto`,
`CD_with_Crypto.T14_CD_B_solvable_multicast_with_crypto`.
T12 and T13 are direct corollaries of T6 and T7 respectively.
T14 is the genuinely new content: it discharges via the same
`CD_B_solvable_under_correct_reporting` lemma the other
positive theorems use, because at our event-level abstraction
the cryptographic primitives' only role is to make
correct-reporting achievable under multicast.

**Divergence.**  At our abstraction we do not model
cryptographic primitives directly (no digital-signature
algebra, no hash-chain construction).  Their role is
exclusively to discharge `correct_reporting`; the paper itself
treats cryptography this way when citing Bracha 1987 for BRB.
The headline-level theorem statements are identical to the
operational T6 / T7 / (would-be-T8-with-crypto) statements.

---

## §5.1 — Relationship to consensus

### Theorem 15 — CD harder than Consensus (Byzantine)

> *"In an asynchronous system with Byzantine failures, CD ⊀
> Consensus and the CD problem is harder than Consensus."*  (paper §5.1)

**Paper's proof in English.**  The paper exhibits a hypothetical
oracle (process-identification) that makes Consensus solvable,
then revisits Theorem 1 to argue that even with that oracle CD
still admits false negatives.  So Consensus-solvability does
not imply CD-solvability — CD is strictly harder.

**Our mechanisation.**
`CD_vs_Consensus.CD_harder_than_Consensus`.  At our
abstraction the proof is structurally simple: our abstract
`solves_Consensus` predicate is satisfiable by a pure-HOL
witness (`Foundation_Vacuity.exists_consensus_alg`), and CD is
unsolvable by Theorem 3.  The conjunction of "Consensus
witness exists" and "no CD witness exists" gives the
non-reducibility.

**Divergence.**  Our `solves_Consensus` is a *function-level*
predicate (no operational semantics), so a Consensus solver
exists trivially.  The paper takes Consensus to be a *protocol-
level* notion where Termination has bite under failures.  This
mismatch is documented in `Foundation_Vacuity.thy`, which
retains a regression witness showing the pure-HOL satisfier.
The end result is the same — CD is unsolvable, Consensus is
abstractly satisfiable — and the asymmetry is what T15 needs.

### Theorem 16 — Consensus harder than CD (crash failures)

> *"In an asynchronous system with crash failures, CD is
> solvable but Consensus is not solvable; thus Consensus ⊀ CD
> and CD ⪯ Consensus."*  (paper §5.1)

**Paper's proof in English.**  Two parts:
1. *CD solvable under crash.*  In the crash-failure model no
   process lies; crashed processes' execution histories
   propagate via the messages they sent before crashing.  Any
   correct process can therefore reconstruct \(F = E\) over
   time.
2. *Consensus unsolvable under crash.*  This is FLP.

**Our mechanisation.**
`CD_vs_Consensus.T16_full`, decomposed as:

1. `CD_vs_Consensus.T16_CD_solvable_under_crash_part` — the
   constructive half.  Switches to the
   `cd_alg_with_recv` signature (the algorithm now takes a
   per-peer reported history as input).  The "transitive
   propagation via execution messages" claim becomes, at our
   abstraction, the assumption `recv = adv_E adv` pointwise:
   the algorithm receives a faithful report.  Under this
   assumption the naive algorithm \(F := \mathit{recv}\)
   trivially produces a valid \(F\) (because \(F = E\), so
   `valid E E e_star` holds at every event by reflexivity).

2. `CD_vs_Consensus.T16_Consensus_unsolvable_part` — exported
   from `FLP_Consensus.flp_consensus_unsolvable`, which itself
   discharges against the AFP entry's
   `flpPseudoConsensus.ConsensusFails`.

`T16_Consensus_not_reducible_to_CD_under_crash` is the
asymmetry T16 needs (CD solver exists in the richer signature,
Consensus solver does not).

**Divergence.**  The paper's "transitive propagation via
execution messages" is intuitively a property *of the
operational layer* — crashed processes' histories propagate
through messages sent before crashing.  We capture this
abstractly as `recv = adv_E adv` pointwise (the algorithm has
perfect information).  The pointwise-equality is stronger than
what the paper's argument literally delivers (which would
guarantee only events in the causal past of \(e^*\)), but the
stronger assumption is strictly easier to discharge
operationally and gives the same final theorem.

---

## §5.2 — Relationship to causal ordering

### Theorem 17 — CO and CD are interreducible (Byzantine)

> *"CO and CD are interreducible in the Byzantine model."*  (paper §5.2)

**Paper's proof in English.**
- *CO ⪯ CD.*  To solve CO at message \(m_2\), invoke CD at
  the receive event of \(m_2\).  The BB-style output settles
  CO\_Deliv(\(m_2\)).
- *CD ⪯ CO.*  The paper states "the reverse direction is
  similar" without giving a constructive reduction.

**Our mechanisation.**  The CO problem is mechanised in
`CO.thy` as a *restriction* of CD: a CO adversary is a CD
adversary whose target event is a Receive.  This makes the
forward direction trivial:

- `CO.CD_solvable_imp_CO_solvable` — a CD solver is
  automatically a CO solver.  Proven constructively outside
  any locale.

For the reverse direction we use the Byzantine premise:

- `CO.T17_CO_interreducible_with_CD` — under the standard
  Byzantine premises (`byzantine ≠ {}`, `correct ≠ {}`,
  finiteness side hypotheses), both `CD_solvable` and
  `CO_solvable` are False (by T3-T5 and T18 respectively),
  hence interreducible vacuously.

**Divergence.**  We do not construct a syntactic CD-solver
from a CO-solver.  In a function-level abstraction this would
require synthesising a self-receive extension of every CD
adversary (extend the adversary's history by adding a Receive
after its target event so the CO-solver can be invoked there).
The vacuous route through the impossibility theorems gives the
same end-statement.

### Theorem 18 — CO subject to FN/FP

> *"CO is subject to FN and FP in the Byzantine model."*  (paper §5.2)

**Paper's proof in English.**  The paper derives this as a
corollary of T17 plus T1/T2.  Since CO is interreducible with
CD, and CD has FN/FP, so does CO.

**Our mechanisation.**  We discharge T18 directly rather than
through the interreducibility:

- `CO.CO_FN_unavoidable` — analogue of T1 with a Receive-
  event target.  Uses a two-message scenario: the target
  \(e^*\) is the receive of a fixed message \(m_2 = 0\); the
  FN witness is a separate send-receive pair using a fresh
  message identifier \(m_1 = \mathit{fresh\_nat}(F)\) chosen so
  the witness send is absent from \(F\).
- `CO.CO_FN_or_FP_unavoidable_internal` — analogue of T2 with
  a Receive-event target and an internal-event witness at the
  Byzantine process.
- `CO.CO_impossible_unicast`/`broadcast`/`multicast` — CO is
  unsolvable under each mode (analogues of T3 / T4 / T5).

**Divergence.**  Direct constructive proofs rather than the
paper's "corollary of T17 + T1/T2" derivation.  Both
strategies are valid; the direct construction is shorter
because it avoids needing the reverse direction of T17.

---

## Companion theorems (paper-adjacent)

These results are not in the paper's theorem list but are
needed to make the operational story fully explicit.

### Deadlock freedom and run-model invariants

- `Execution_Model.not_drained_can_step` — from any
  configuration reachable via `run`, if the in-flight buffer
  is non-empty then some `run_step` (specifically a
  `step_recv`) can be taken.  Combined with
  `Execution_Model.fairness_implies_delivery` this gives:
  while the buffer has anything, progress is possible; when
  the buffer is empty, the history is mode-admissible.

- Run-invariants — `sends_match_inv_run`, `wf_history_run`,
  `buffer_correct_inv_run`: every run preserves the structural
  invariants needed for the impossibility and possibility
  arguments.

### Fair-run liveness on infinite executions

- `Liveness.fair_run_delivers` — in any *fair infinite*
  execution (modelled as `nat ⇒ 'p config` with adjacent
  `run_step` and the fairness predicate "every buffered
  triple eventually leaves the buffer"), every correct-to-
  correct `Send` event in some `E i` has a matching `Receive`
  in some `E j`.  The pivotal technical lemma is
  `step_removes_triple_is_recv`: case analysis on `run_step`
  shows the only way a buffer triple disappears is via a
  `step_recv` for that very triple, which appends the
  matching `Receive` to the history.

### Named BRU and BCB-over-BRB primitives

`Primitives.thy`:

- `bru_satisfied H` — named alias of
  `messages_delivered_among correct H`.  This is the
  downstream effect of BRU on the global history.
- `bcb_causal_order C H` — the additional causal-order
  property of BCB-over-BRB (matching receives at any correct
  receiver respect the causal order of sends).
- `bcb_over_brb_satisfied` — conjunction.
- `drained_run_satisfies_bru`,
  `fair_run_satisfies_bru_pointwise` — operational discharge
  of BRU from the run model.
- `T6_unicast_via_bru`, `T7_broadcast_via_bcb_over_brb`,
  `bru_solves_CD_B_unicast`,
  `bcb_over_brb_solves_CD_B_broadcast`,
  `fair_drained_run_solves_CD_B_unicast`/`_broadcast` —
  operational T6 / T7 named explicitly via the primitives.

### Concrete demos for T6

Three increasingly large worked examples in `T6_Concrete.thy`,
`T6_Multihop.thy`, `T6_With_Byzantine.thy`.  Each:
1. Defines a concrete history `*_H` and adversary `*_adv`.
2. Constructs a sequence of `run_step` transitions explicitly.
3. Proves the run terminates with the expected drained
   configuration.
4. Applies `fair_drained_run_solves_CD_B_unicast` to conclude
   the naive algorithm solves CD_B at the resulting adversary.

The three demos collectively exercise all four `run_step`
rules (`step_internal`, `step_send`, `step_recv`,
`step_byzantine`) and demonstrate T6 in single-message,
multi-hop, and Byzantine-bystander scenarios.

### Causal scheduler — operational discharge of BCB

`Causal_Scheduler.thy` introduces `causal_run_step`, a strict
refinement of `run_step` with two added side conditions:

1. **Freshness at send.** `step_send` requires the triple
   `(p, q, m)` to be fresh (no prior Send for the same triple,
   no in-flight buffer entry).  This matches the paper's
   implicit "messages carry unique ids" assumption.
2. **Causal precondition at receive.** `step_recv` requires
   that every Byzantine-happened-before predecessor send to
   the same correct receiver has already been delivered.

The proofs build a joint invariant `causal_inv` (sends and
receives are unique correct-to-correct, buffer entries respect
that uniqueness, and once delivered the buffer is drained),
plus a separate joint invariant `recv_causal_inv`/`recv_order_inv`
that propagates the causal precondition forward into the run
history.

**Why BHB rather than HB.**  Byzantine processes can fabricate
arbitrary `Receive`-shaped local events via `step_byzantine`,
which can introduce `hb` chains through Byzantine intermediaries
that no correct-process scheduler can constrain.  Paper
Definition 3 restricts hb to chains through correct processes
precisely to sidestep this, and §4.3's BCB is stated in terms
of the Byzantine happened-before relation.  Our operational
discharge is therefore in terms of `bhb`, in
`causal_run_satisfies_bhb_causal_order`.

**Key technical lemmas.**
- `causal_step_new_event_sink`: every `causal_run_step`
  appends one event that has no outgoing `bhb_step` edge in
  the extended history.
- `bhb_extend_down`: restriction of `bhb` chains to a sub-
  history when the appended event is a `bhb_step` sink.
- `hist_extend_unique`: a single-event history extension is
  uniquely determined by the appended process and event,
  letting the abstract `hist_extend` pulled from
  `causal_step_new_event_sink` be identified with the
  rule-specific data exposed by a case analysis on the
  `causal_run_step` rule.

**Composition.**  `fair_drained_causal_run_solves_CD_B_broadcast`
chains the operational T7 (`T7_broadcast_via_bcb_over_brb`)
through the causal-run model.  The unicast counterpart
(`fair_drained_causal_run_solves_CD_B_unicast`) reuses the
same chain; unicast does not require BCB at all (`bru_satisfied`
suffices), but the unified entry point is convenient.

The matching `bcb_causal_order` predicate in `Primitives.thy`
(which uses plain `hb`) is retained as a parallel statement;
the BHB-version `bhb_causal_order` we prove here is what the
paper's Definition 3 actually talks about.

---

## Index of all theorem names

For quick navigation back to the source, this is the
exhaustive list of named theorems that ground the above
narrative.

### Paper theorems (18/18 proven)

```
Theorem  1: Theorems_1_2.CD_FN_unavoidable
Theorem  2: Theorems_1_2.CD_FN_or_FP_unavoidable_internal
Theorem  3: Impossibility.CD_impossible_unicast
Theorem  4: Impossibility.CD_impossible_broadcast
Theorem  5: Impossibility.CD_impossible_multicast
Theorem  6: CD_B_Algorithm.CD_B_solvable_unicast
            (operational versions in Delivery, Primitives, T6_Concrete, T6_Multihop, T6_With_Byzantine)
Theorem  7: CD_B_Algorithm.CD_B_solvable_broadcast
Theorem  8: CD_B_Algorithm.produces_valid_F_B_recv_strong_unsolvable
            (alias: CD_B_unsolvable_multicast_abstract)
Theorem  9: CD_with_Crypto.T9_CD_impossible_multicast_with_crypto
Theorem 10: CD_with_Crypto.T10_CD_impossible_unicast_with_crypto
Theorem 11: CD_with_Crypto.T11_CD_impossible_broadcast_with_crypto
Theorem 12: CD_with_Crypto.T12_CD_B_solvable_unicast_with_crypto
Theorem 13: CD_with_Crypto.T13_CD_B_solvable_broadcast_with_crypto
Theorem 14: CD_with_Crypto.T14_CD_B_solvable_multicast_with_crypto
Theorem 15: CD_vs_Consensus.CD_harder_than_Consensus
Theorem 16: CD_vs_Consensus.T16_full
            (halves: T16_CD_solvable_under_crash_part, T16_Consensus_unsolvable_part)
Theorem 17: CO.T17_CO_interreducible_with_CD
            (forward direction: CO.CD_solvable_imp_CO_solvable)
Theorem 18: CO.CO_FN_unavoidable, CO.CO_FN_or_FP_unavoidable_internal
```

### Companion theorems

```
Deadlock freedom:        Execution_Model.not_drained_can_step
Run invariants:          Execution_Model.{sends_match_inv_run, wf_history_run, buffer_correct_inv_run}
Finite-run delivery:     Execution_Model.fairness_implies_delivery
Mode-admissibility:      Execution_Model.run_completes_to_mode_admissible_{unicast,broadcast}
Fair infinite liveness:  Liveness.fair_run_delivers
BRU as a primitive:      Primitives.{bru_satisfied, drained_run_satisfies_bru, fair_run_satisfies_bru_pointwise}
BCB-over-BRB:            Primitives.{bcb_causal_order, bcb_over_brb_satisfied}
Operational T6:          Primitives.{T6_unicast_via_bru, bru_solves_CD_B_unicast, fair_drained_run_solves_CD_B_unicast}
Operational T7:          Primitives.{T7_broadcast_via_bcb_over_brb, bcb_over_brb_solves_CD_B_broadcast, fair_drained_run_solves_CD_B_broadcast}
Concrete T6 (1 message): T6_Concrete.{T6_concrete_demo, T6_witnessed}
Concrete T6 (multihop):  T6_Multihop.{T6_multihop_demo, T6_multihop_witnessed, multi_bhb_chain}
Concrete T6 (Byzantine): T6_With_Byzantine.{T6_with_byzantine_demo, T6_with_byzantine_witnessed,
                                            byzantine_event_not_on_bhb_chain_left,
                                            byzantine_event_not_on_bhb_chain_right}
Causal scheduler:        Causal_Scheduler.{causal_run_step, causal_run_satisfies_bhb_causal_order,
                                           causal_run_satisfies_bhb_over_brb,
                                           fair_drained_causal_run_solves_CD_B_broadcast,
                                           fair_drained_causal_run_solves_CD_B_unicast}
```

For the *side hypotheses* the headline theorems take (a single
finiteness condition `fin_cd`, identical in shape to T1's
`fin_F`), see [`README.md`'s "Assumptions" section](README.md#assumptions-introduced-beyond-the-paper).
For the *out-of-scope optional follow-ons* (a concrete
cryptographic primitive layer), see [`ROADMAP.md`](ROADMAP.md).
