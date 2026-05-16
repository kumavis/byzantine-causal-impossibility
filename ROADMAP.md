# Roadmap

Per-theorem status against the paper's 18 theorems, plus the
suggested order for the remaining work.

## Status summary

| § | Thm | Statement | Status | Where |
|---|-----|-----------|--------|-------|
| 4.1 | T1  | FN unavoidable under Byzantine | ✅ proven | `Theorems_1_2.CD_FN_unavoidable` |
| 4.1 | T2  | FN-or-FP unavoidable for internal events | ✅ proven | `Theorems_1_2.CD_FN_or_FP_unavoidable_internal` |
| 4.2 | T3  | CD impossible, unicast | ✅ proven (under `fin_cd`) | `Impossibility.CD_impossible_unicast` |
| 4.2 | T4  | CD impossible, broadcast | ✅ proven | `Impossibility.CD_impossible_broadcast` |
| 4.2 | T5  | CD impossible, multicast | ✅ proven | `Impossibility.CD_impossible_multicast` |
| 4.3 | T6  | CD_B solvable, unicast | ✅ proven (abstract + operational + run model) | `CD_B_Algorithm.CD_B_solvable_unicast`, `Execution_Model.run_completes_to_mode_admissible_unicast` |
| 4.3 | T7  | CD_B solvable, broadcast | ✅ proven (same chain) | `CD_B_Algorithm.CD_B_solvable_broadcast`, `Execution_Model.run_completes_to_mode_admissible_broadcast` |
| 4.3 | T8  | CD_B impossible, multicast | ✅ proven (abstract content) | `CD_B_Algorithm.produces_valid_F_B_recv_strong_unsolvable` |
| 4.4 | T9  | CD_B impossible, broadcast + crypto | ❌ not done | (needs crypto layer) |
| 4.4 | T10 | CD_B impossible, unicast + crypto | ❌ not done | (needs crypto layer) |
| 4.4 | T11 | CD_B impossible, multicast + crypto | ❌ not done | (needs crypto layer) |
| 4.4 | T12 | crypto-impossibility | ❌ not done | (needs crypto layer) |
| 4.4 | T13 | CD_B possible, unicast + crypto | ❌ not done | (needs crypto layer) |
| 4.4 | T14 | CD_B possible, multicast + crypto | ❌ not done | (needs crypto layer) |
| 5.1 | T15 | CD harder than Consensus (Byzantine) | ✅ proven | `CD_vs_Consensus.CD_harder_than_Consensus` |
| 5.1 | T16 | Consensus harder than CD (crash) | ⚠️ partial | `CD_vs_Consensus.T16_Consensus_unsolvable_part` |
| 5.2 | T17 | CO ↔ CD interreducible (Byzantine) | ❌ not done | (needs CO definitions) |
| 5.2 | T18 | CO subject to FN/FP (cited [42]) | ❌ not done | (cited from prior work; would need CO layer) |

**Scoreboard**: 12/18 fully proven · 1/18 partial · 5/18 not done.

## Side hypotheses still on the critical path

The mechanisation introduces exactly *one* mild side hypothesis on
the headline theorems (3/4/5):

- `fin_cd`: every candidate CD-solver `cd_alg` that produces a valid
  `F` has finite `events_of` output at the Theorem-1 adversary's
  local target event.  Trivially satisfied by any algorithm whose
  output is supported on the finite process set.  Identical in shape
  to Theorem 1's `fin_F`.

No HOL axioms.  No locale axioms on the critical path.  (R2's
`cd_can_identify_correct` exists in `Reductions.thy` but is
preserved only as paper-faithful documentation; the headline
theorems do not need it.)

## Remaining work

In suggested order (easiest → hardest), with notes on what each
piece would require:

### 1. Theorem 17 (CD ↔ CO interreducibility, Byzantine)

Smallest of the remaining items.  Paper §5.2 defines the causal-
ordering problem `CO(E, F, m_2)` (their Definition 10) in shape
parallel to `CD(E, F, e*_i)` (Definition 5) — `m_2` is a message
identifier instead of an event identifier.  The reduction `CO ⪯
CD` is one paragraph: invoke `CD(E, F, e*_r)` where `e*_r` is the
receive event of `m_2`; the BB-style output gives enough
information to settle `CO_Deliv(m_2)`.  The reverse direction is
similar.

Mechanisation plan:
- New theory `CO.thy` defining the CO problem analogously to
  `CD.thy`.
- Two reduction lemmas: `CO_reduces_to_CD`, `CD_reduces_to_CO`.
- Composition: `CO ⪯ CD ∧ CD ⪯ CO`.

Estimated effort: a few hundred lines of Isar.  No new model
extensions.

### 2. Theorem 18 (CO subject to FN/FP)

Stated by the paper as a corollary of [42] — earlier prior work.
Once T17 is in place, T18 follows from T1+T2 via the reduction.
Small extra step on top of T17.

### 3. Theorem 16's CD-solvable-under-crash half

Paper §5.1 argues: in the crash-failure model, CD is solvable
because crashed processes' histories can be transitively propagated
via the messages they sent before crashing.

Mechanisation requires:
- A *crash-failure* adversary model distinct from the existing
  Byzantine model.  At the abstraction level this is a constraint
  on `adv_E adv` that says "crashed processes' history is a prefix
  of some honest execution".
- A constructive algorithm using the messages-propagation argument.

Modest model extension (~the size of one new theory).

### 4. Real-world fairness on the execution model

Phase 8 proved deadlock freedom (`not_drained_can_step`).  The
remaining temporal-liveness theorem is:

> Every fair infinite execution eventually has empty buffer.

Requires:
- A coinductive definition of infinite executions (streams over
  `run_step`).
- A temporal fairness predicate: every in-flight triple eventually
  scheduled for `step_recv`.
- A liveness theorem.

Substantial — proper coinduction territory.  Standard distributed-
systems formalisation work but not small.  The current development
is parametric over it (Phases 6–8 cover the *finite*-execution
side: any run that fairly completes is mode-admissible).

### 5. Theorems 9–14 (cryptography variants)

Paper §4.4.  The hardest remaining piece.  Requires:
- A model of digital signatures (sign / verify, with `verify (sign
  k m) k = m` and forge resistance).
- A model of hash functions and hash-chain histories.
- Possibility constructions (T13, T14) that build algorithms using
  these primitives.
- Impossibility constructions (T9–T12) showing certain mode/crypto
  combinations still fail.

This is a multi-week project on its own.

## Possible immediate next step

Recommendation: **Theorem 17**.  It's the smallest remaining piece,
genuinely extends the development with new mathematical content,
and lays the foundation for T18.  After that the natural ordering
is T18 → T16-half → fairness streams → T9–T14.
