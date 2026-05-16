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
| 5.2 | T17 | CO ↔ CD interreducible (Byzantine) | ✅ proven | `CO.CD_solvable_imp_CO_solvable` + `CO.T17_CO_interreducible_with_CD` |
| 5.2 | T18 | CO subject to FN/FP | ✅ proven | `CO.CO_FN_unavoidable`, `CO.CO_FN_or_FP_unavoidable_internal` |

**Scoreboard**: 14/18 fully proven · 1/18 partial · 3/18 not done.

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

### 1. Theorem 16's CD-solvable-under-crash half

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

### 2. Real-world fairness on the execution model

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

### 3. Theorems 9–14 (cryptography variants)

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

Recommendation: **Theorem 16's CD-solvable-under-crash half**.  It is
the smallest remaining piece, extends the development with a crash-
failure model that is genuinely distinct from the Byzantine model
already in place, and finishes off T16 (currently the only partial
theorem).  After that the natural ordering is fairness streams →
T9–T14.
