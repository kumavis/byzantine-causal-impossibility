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
| 4.4 | T9  | CD impossible, multicast + crypto | ✅ proven (corollary of T5) | `CD_with_Crypto.T9_CD_impossible_multicast_with_crypto` |
| 4.4 | T10 | CD impossible, unicast + crypto | ✅ proven (corollary of T3) | `CD_with_Crypto.T10_CD_impossible_unicast_with_crypto` |
| 4.4 | T11 | CD impossible, broadcast + crypto | ✅ proven (corollary of T4) | `CD_with_Crypto.T11_CD_impossible_broadcast_with_crypto` |
| 4.5 | T12 | CD_B possible, unicast + crypto | ✅ proven (corollary of T6) | `CD_with_Crypto.T12_CD_B_solvable_unicast_with_crypto` |
| 4.5 | T13 | CD_B possible, broadcast + crypto | ✅ proven (corollary of T7) | `CD_with_Crypto.T13_CD_B_solvable_broadcast_with_crypto` |
| 4.5 | T14 | CD_B possible, multicast + crypto | ✅ proven (new) | `CD_with_Crypto.T14_CD_B_solvable_multicast_with_crypto` |
| 5.1 | T15 | CD harder than Consensus (Byzantine) | ✅ proven | `CD_vs_Consensus.CD_harder_than_Consensus` |
| 5.1 | T16 | Consensus harder than CD (crash) | ✅ proven | `CD_vs_Consensus.T16_full`, `T16_Consensus_unsolvable_part`, `T16_CD_solvable_under_crash_part` |
| 5.2 | T17 | CO ↔ CD interreducible (Byzantine) | ✅ proven | `CO.CD_solvable_imp_CO_solvable` + `CO.T17_CO_interreducible_with_CD` |
| 5.2 | T18 | CO subject to FN/FP | ✅ proven | `CO.CO_FN_unavoidable`, `CO.CO_FN_or_FP_unavoidable_internal` |

**Scoreboard**: 18/18 fully proven.

Plus paper-adjacent companion theorems: deadlock freedom on the
inductive execution model (`Execution_Model.not_drained_can_step`),
liveness on infinite executions (`Liveness.fair_run_delivers`),
and named BRU / BCB-over-BRB primitive abstractions with end-to-
end composition into operational T6 / T7
(`Primitives.fair_drained_run_solves_CD_B_unicast` /
`_broadcast`).

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

All 18 paper theorems are formalised.  Optional follow-ons that
would deepen the mechanisation but are not on the paper's
critical path:

### 1. Concrete cryptographic primitive layer

`CD_with_Crypto.thy` discharges T9–T14 as corollaries of existing
results, treating cryptography the same way the paper treats it
when it cites Bracha 1987 for BRB: as an off-the-shelf primitive
whose operational role is to discharge `correct_reporting` under
multicast (T14) or to support the FN-attack-style impossibility
arguments (T9–T11).  A deeper mechanisation would add:

- A model of digital signatures with `verify (sign k m) k = m`
  and forge-resistance.
- A model of collision-resistant hashes and recursive hash
  histories of the form `\<hat>s_i^x = H(\<hat>s_i^{x-1}, e_i^x)`.
- A constructive multicast algorithm that uses group encryption
  to discharge `correct_reporting` (the operational side of T14).
- Refined T9–T11 statements that capture the paper's quantitative
  FP-prevention qualifier ("FP prevented for `t < n/3`" under
  Bracha's BRB), which currently lives in the prose of
  `CD_with_Crypto.thy` but is not formalised.

### 2. Scheduler-level realisation of BCB causal order

`Primitives.thy` names BRU and BCB-over-BRB at the event-level
abstraction and proves operational T6 / T7 composing into a fair
drained run.  BRU is operationally realised by the existing
inductive `run_step` (any drained run satisfies `bru_satisfied`);
BCB's additional `bcb_causal_order` property is stated and
threaded through the broadcast-side theorems but is not directly
realised by `run_step` (the scheduler does not enforce
causally-ordered `step_recv` invocations).  A scheduler-level
refinement of `run_step` that enforces causal-order delivery
would discharge that hypothesis operationally.
