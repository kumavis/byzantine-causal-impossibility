# Mission

This document captures the original request that initiated this project,
preserved verbatim for traceability, plus a short status section
recording what was delivered against that request and what remains open.

## Original request (verbatim)

> Formalize "Byzantine-tolerant detection of causality" impossibility
> results in Isabelle/HOL
>
> You are a formal-methods engineer working in Isabelle/HOL. Your task is
> to mechanize the impossibility results from Misra & Kshemkalyani,
> *"Byzantine-tolerant detection of causality: There is no holy grail"*
> (Parallel Computing 124, 2025, article 103136), building on the
> existing FLP formalization in the Archive of Formal Proofs.
>
> ## Scope (what to prove)
>
> The minimum viable result is **Theorem 3**: in an asynchronous unicast
> message-passing system with one or more Byzantine processes, the
> Causality Determination problem `CD(E, F, e*_i)` (Definition 5 of the
> paper) is unsolvable. Then extend to **Theorem 4** (broadcast) and
> **Theorem 5** (multicast).
>
> Out of scope for this first pass:
> - The `B`-happened-before positive results (Theorems 6, 7, 8) and their
>   algorithms
> - The cryptography-allowing variants (Theorems 9–14)
> - The auxiliary results in Section 5 (CD vs Consensus vs CO
>   relationships)
> - Theorems 1 and 2 (trivial corollaries that you can include if cheap,
>   but they aren't the goal)
>
> Keep the model and proofs reusable so the later extensions don't
> require reworking the foundation.
>
> ## Foundation to build on
>
> Use the AFP entry **`FLP`** by Bisping, Brodmann, Jungnickel, Rickmann,
> Seidler, Stüber, Wilhelm-Weidner, Peters, Nestmann (last updated March
> 2025), available at <https://www.isa-afp.org/entries/FLP.html>. Read it
> before writing anything. Key items you will reuse or adapt:
>
> - `AsynchronousSystem.thy` — messages, configurations, the
>   asynchronous step relation, the `system` locale
> - `Execution.thy` — executions, fairness
> - `Consensus.thy` — the Consensus problem statement
>   (Agreement / Validity / Termination)
> - `FLPTheorem.thy` — the FLP impossibility result itself, which you
>   will *invoke*, not reprove
>
> The AFP entry models crash failures. You will need to extend the model
> to **Byzantine** behavior. Do this by adding a new locale that extends
> `system` rather than editing AFP files.
>
> ## Proof strategy (follow the paper)
>
> The paper's argument is a two-step reduction:
>
> 1. `Consensus ⪯ Black_Box` — given a solver for the `Black_Box` problem
>    (Definition in §4.2), build a Consensus solver
> 2. `Black_Box ⪯ CD` — given a CD solver, build a `Black_Box` solver
>
> Composing: `Consensus ⪯ CD`. By FLP, `Consensus` is unsolvable in an
> async system with one faulty process. Therefore `CD` is unsolvable in
> an async system with one Byzantine process (Byzantine is strictly more
> powerful than crash, so unsolvability transfers).
>
> Your formalization should mirror this structure exactly — three
> separate lemmas plus a composition theorem — rather than a monolithic
> proof.
>
> ## Concrete deliverables
>
> Produce an Isabelle session `ByzantineCD` with these theories, in
> roughly this order:
>
> 1. **`ByzantineSystem.thy`** — locale extending `system` with a
>    partition `correct ⊎ byzantine` of processes, where Byzantine
>    processes have arbitrary (under-specified) step behavior. State and
>    prove a few sanity lemmas (e.g., the projection onto correct
>    processes is still a valid asynchronous system; Byzantine ⊆ crash
>    in the sense that any Byzantine execution can simulate any crash
>    execution).
>
> 2. **`Events.thy`** — events (`internal`, `send`, `receive`), the
>    happened-before relation `→` (Definition 1), execution histories
>    `E_i` and the global `E`, and the collected history `F` (the
>    algorithm's view, which may differ from `E` at Byzantine
>    processes). Define `e →|E` and `e →|F` as Boolean evaluations.
>
> 3. **`CD.thy`** — the `valid(F)` predicate (Definition 5), false
>    positives `FP` and false negatives `FN`, and the `CD(E, F, e*_i)`
>    problem. A "solver" is a function from observable inputs to `F`
>    plus a decision; "solves CD" means `valid(F) = 1` for every
>    admissible adversary strategy. Make the adversary model explicit.
>
> 4. **`BlackBox.thy`** — the `Black_Box(V, E, F, e*_i)` problem from
>    §4.2, parameterized on the vector `V` of initial values and the
>    local correctness list `L` returned.
>
> 5. **`Reductions.thy`** — two lemmas:
>    - `consensus_reduces_to_blackbox`: a `Black_Box` solver yields a
>      Consensus solver (paper's argument: each `p_i` broadcasts `w`,
>      then outputs the value from `p_{min(L)}`; Agreement, Validity,
>      Termination all follow).
>    - `blackbox_reduces_to_cd`: a `CD` solver yields a `Black_Box`
>      solver (paper's argument: solving CD forces identification of
>      Byzantine processes and reconstruction of their execution
>      histories).
>
>    The second is the subtler one and is where the paper's prose is
>    least mechanical. Be prepared to make implicit assumptions
>    explicit. State precisely what "identifying Byzantine processes"
>    means as a predicate on the solver's output.
>
> 6. **`Impossibility.thy`** — the headline theorems:
>    - `theorem CD_impossible_unicast` (Theorem 3): by composing the two
>      reductions and invoking `FLPTheorem.flp` from the AFP.
>    - `theorem CD_impossible_broadcast` (Theorem 4): same reduction
>      skeleton, with a Byzantine Reliable Broadcast layer modeled as an
>      additional assumption that *strengthens* the system (still
>      doesn't suffice).
>    - `theorem CD_impossible_multicast` (Theorem 5): trivial corollary
>      — unicast is the special case `|G| = 1`.
>
> 7. **`ROOT`** — session declaration listing the theories and
>    depending on `FLP` from AFP.
>
> ## Working method
>
> Approach the project incrementally and verify each layer compiles
> before moving on. Specifically:
>
> - Set up the toolchain first: install Isabelle2025 (or current
>   stable), clone AFP, register the `FLP` entry, confirm
>   `isabelle build -d $AFP FLP` succeeds. Don't write any new theory
>   until this passes.
> - For each new theory, write definitions first, get them through the
>   parser, then state the lemmas (admit them with `sorry`), confirm
>   the overall structure typechecks, then discharge the `sorry`s one
>   at a time.
> - Lean on `sledgehammer`, `auto`, `blast`, `metis`, and `force`
>   aggressively. For inductive arguments on executions, `induct` on
>   the execution relation or use the AFP's existing induction
>   principles where available.
> - Prefer **locales** over **type classes** for the system model —
>   this matches AFP `FLP` and makes extension cleaner.
> - When the paper's prose has a gap (e.g., the meta-level claim "this
>   requires identifying all Byzantine processes"), pause and either
>   find a precise formulation or flag it as an assumption you need to
>   add. Do not paper over informal steps with `sorry`.
>
> ## Definitions of done
>
> The project is complete when:
>
> - `isabelle build -D .` succeeds with zero `sorry` and zero `oops`
> - All three impossibility theorems (3, 4, 5) are statements directly
>   invokable by future developments
> - The Byzantine system locale and event/history layer are documented
>   well enough to extend to the `B`-happened-before results
> - A short `README.md` explains the file structure, the proof
>   strategy, the gaps you had to fill from the paper's informal prose,
>   and any axioms or assumptions you introduced beyond what the paper
>   states
>
> ## Risk and escalation
>
> If after focused effort you cannot discharge `blackbox_reduces_to_cd`
> — the meta-level reduction is the trickiest piece — stop and write up
> *precisely* what additional assumption would close it, with a short
> argument for why that assumption is faithful to the paper's intent.
> A partial formalization with a clearly-stated open lemma is more
> valuable than a hand-wave.
>
> If the AFP `FLP` entry's model turns out to be too restrictive for
> the paper's notion of asynchrony (e.g., message ordering assumptions
> differ), document the mismatch rather than working around it
> silently.
>
> Report progress after each theory compiles.

## Subsequent style directive

A follow-up message refined the style requirements:

> ## Proof style: declarative Isar
>
> Write all proofs in structured Isar, not apply-style. Use
> `proof ... qed` blocks with `fix`, `assume`, `have`, `show`,
> `obtain`, `hence`, `thus`. Tactics (`auto`, `blast`, `metis`,
> `force`, `induct`, `simp`) appear only at the leaves via `by ...` or
> `by (...)`. Avoid sequences of `apply` commands; if you find yourself
> reaching for them, restructure as an Isar block instead.
>
> Three concrete rules:
>
> 1. **Mirror the paper's structure.** Each named claim in the prose
>    ("Managing false positives", "Managing false negatives",
>    "therefore Black_Box ⪯ CD") becomes a `have` with a stated
>    proposition. A reviewer should be able to read the theory file
>    next to the paper and match them line by line.
>
> 2. **No silent gaps.** When the paper's argument has an implicit step
>    (especially in `blackbox_reduces_to_cd`), make it an explicit
>    `have` with a proposition you actually prove — or flag it as an
>    `assumes` on the surrounding lemma with a comment explaining why.
>    Never close a gap with a broad `by auto` that hides what's
>    happening.
>
> 3. **Use sledgehammer at the leaves, then minimize.** Run
>    sledgehammer to find a proof, then replace its suggestion with
>    the smallest tactic that works (`by simp`, `by blast`,
>    `by (metis ...)`). Don't ship `try0` or `sledgehammer`
>    invocations in the committed source.
>
> Match the style of the AFP `FLP` entry's existing theories — that's
> the reference for naming, indentation, locale usage, and
> lemma-statement conventions.
>
> install any necessary dependencies to test locally, if you can't try
> other means, if you can't: stop and report

## Status (current)

The original mission (Theorems 3, 4, 5) is fully delivered.  The
project has since grown to cover **all 18 paper theorems** plus
paper-adjacent companion theorems (deadlock freedom, fair-
infinite-execution liveness).  See [`ROADMAP.md`](ROADMAP.md) for
the per-theorem status table.

| Component                                                       | Status |
|-----------------------------------------------------------------|--------|
| `ByzantineSystem.thy`                                           | Done.  Locale `process_partition` + `byzantineSystem`; FLP impossibility now imported as a proven theorem (not an axiom). |
| `Events.thy`                                                    | Done.  Datatype `'p event`, per-process and global histories, program-order, message-order, transitive closure `hb`, Boolean `hb_eval`. |
| `CD.thy`                                                        | Done.  `valid`, `false_negative`, `false_positive`, adversary record, `produces_valid_F`, `CD_solvable`. |
| `BlackBox.thy`                                                  | Done.  `w_value`, `bb_output` record, `solves_BlackBox`, `BlackBox_solvable`. |
| `Reductions.thy` — `consensus_reduces_to_blackbox` (R1)         | Done, constructive.  Preserved as paper-faithful documentation. |
| `Reductions.thy` — `blackbox_reduces_to_cd` (R2)                | Done, modulo locale axiom `cd_can_identify_correct`.  *Off the critical path* of Theorems 3/4/5. |
| `Theorems_1_2.thy` — Theorems 1, 2                              | Done. |
| `BlackBox_Unsolvable.thy` — `¬ BlackBox_solvable`              | *Proven* (no longer a hypothesis); via projection to Theorem 1. |
| `FLP_Consensus.thy` — FLP impossibility                         | *Proven* (no longer an axiom); via AFP's `ConsensusFails`. |
| `Impossibility.thy` — Theorems 3, 4, 5                          | Done, in plain `byzantineSystem`, routed through Theorem 1, under `fin_cd`. |
| `CD_vs_Consensus.thy` — Theorem 15 (full), Theorem 16 (full)    | Both halves of T15 and T16 done. |
| `BHB.thy` — Byzantine happened-before                           | Done.  bhb relation, valid_B, CD_B problem, structural lemmas. |
| `CD_B_Algorithm.thy` — Theorems 6, 7, 8                         | Done.  Abstract `naive_cd_B_alg` correct under `correct_reporting`; T6, T7, T8 as mode-tagged corollaries / impossibilities. |
| `Delivery.thy` — operational delivery layer                     | Done.  `messages_delivered_among`, refined `mode_admissible`, operational T6/T7. |
| `Execution_Model.thy` — inductive `run_step` + invariants       | Done.  `fairness_implies_delivery`, `wf_history_run`, `run_completes_to_mode_admissible_*`, `buffer_correct_inv`, `not_drained_can_step` (deadlock freedom). |
| `Liveness.thy` — fair infinite executions                       | Done.  `infinite_run`, `fair_run`, `step_removes_triple_is_recv`, `fair_run_delivers` (liveness theorem). |
| `Primitives.thy` — BRU / BCB-over-BRB                           | Done.  Named primitive abstractions `bru_satisfied`, `bcb_causal_order`, `bcb_over_brb_satisfied`; operational discharge of BRU from the run model; end-to-end composition into operational T6 / T7 (`bru_solves_CD_B_unicast`, `bcb_over_brb_solves_CD_B_broadcast`, `fair_drained_run_solves_CD_B_*`). |
| `T6_Concrete.thy` — concrete T6 demo                            | Done.  A fully-explicit two-process worked example: `demo_H`, `demo_adv`, `demo_cfg1/2/3`, three `run_step` transitions, composition with `fair_drained_run_solves_CD_B_unicast` into `T6_concrete_demo` and the existential witness `T6_witnessed`. |
| `T6_Multihop.thy` — multihop T6 demo                            | Done.  Three-process two-hop scenario; five `run_step` transitions; `multi_bhb_chain` proves the four-edge bhb path; `T6_multihop_demo` / `T6_multihop_witnessed` mirror the 1-message demo at the bigger scale. |
| `T6_With_Byzantine.thy` — Byzantine-bystander T6 demo           | Done.  Two correct processes + one Byzantine; four `run_step` transitions including `step_byzantine`; `byzantine_event_not_on_bhb_chain_*` proves the Byzantine's local event is excluded from every bhb chain; `T6_with_byzantine_demo` / `T6_with_byzantine_witnessed` demonstrate T6's robustness to live Byzantine activity. |
| `CO.thy` — Theorems 17, 18                                      | Done.  CO problem as receive-event-target restriction of CD; T17 forward; T18 FN-unavoidable + FN-or-FP-unavoidable; CO impossibility + T17 interreducibility. |
| `CD_with_Crypto.thy` — Theorems 9–14                            | Done.  T9/T10/T11 corollaries of T3/T4/T5; T12/T13 corollaries of T6/T7; T14 new (multicast + crypto possible). |
| `Foundation_Vacuity.thy`                                        | Regression diagnostic. |
| `ROOT`, `document/root.tex`, `document/root.bib`                | Done. |
| Declarative Isar, no apply-style, no silent gaps                | Audited.  `grep` for `apply\|sorry\|oops\|sledgehammer\|try0` in `ByzantineCD/*.thy` returns nothing. |
| `isabelle build -D .` succeeds                                  | **Verified** on Isabelle 2025-2 + AFP snapshot `afp-2026-05-13`.  Wall time ~11s, 22 theory files at 100%, 0 `sorry`/`oops`. |
| `isabelle build -o document=pdf -D .` succeeds                  | **Verified** on the same toolchain.  Produces `document.pdf` (155 pages, A4).  A committed snapshot is at `dist/ByzantineCD.pdf`. |

### Build verification (post-hoc)

The original sandbox in which the development was produced could not
reach `isabelle.in.tum.de` or `www.isa-afp.org`, so `isabelle build`
was deferred.  A subsequent session in a different sandbox could reach
both, installed Isabelle2025-2 and the AFP snapshot `afp-2026-05-13`,
and ran the build.  The initial run surfaced a small number of issues
that the deferred verification had hidden; these were fixed in place:

- `ByzantineSystem.thy` imported `FLP.Consensus`, which does not exist
  (Consensus is defined inside `FLPTheorem.thy`, not in a dedicated
  theory).  Import line corrected.
- Several `text \<open>...\<close>` antiquotations referenced terms or thms
  that did not parse / did not yet exist at that program point
  (`@{const Consensus_solvability}`, forward `@{thm ...}` references
  across locale boundaries, `@{term "|G| = 1"}`, `@{term "e \<rightarrow> e'"}`).
  Re-cast as plain Isar inline markup (\<open>...\<close>).
- One `define alg' :: "'p cd_solver"` introduced a fresh type variable
  that did not unify with the surrounding lemma's polymorphism.  Type
  ascription dropped; inference does the right thing.
- `simp` could not always cross an `if`-`then`-`else` whose conditions
  were named hypotheses of the surrounding context.  Reformulated those
  steps as explicit `if_not_P` rewrites composed via `also`/`finally`.
- Three constructor-side proofs (`wf_history_trivial`,
  `adversary_admissible_trivial`, the augmented-CD-to-BB
  `uniform_true` case) were re-expressed declaratively, naming each
  rewrite step rather than asking `simp` to unfold a record/`if`
  chain in one shot.

None of these affected the proof structure or any mathematical content.

Build command, reproducible from any environment that has the deps:

```sh
isabelle build -d $AFP -D ByzantineCD
```

On JVM-on-NixOS environments specifically, the bundled JDK's
`libfontmanager.so` calls `dlopen("libfontconfig.so.1")` at startup.
If no system `libfontconfig.so.1` is on the loader path the JVM
emits `Fontconfig head is null` to stderr and silently exits with
rc=2.  Adding a `libfontconfig` to `LD_LIBRARY_PATH` (e.g. via
`~/.isabelle/Isabelle2025-2/etc/settings`) restores the build.

### Open assumptions (current state)

The vacuity discovered post-build has been fixed.  The development now
takes two meta-level *hypotheses* (not internal HOL axioms), both
satisfiable and faithful to the paper:

1. `fin_cd` *(side hypothesis of Theorems 3, 4, 5 in
   `Impossibility.thy`)*.
   Statement: every candidate CD-solver `cd_alg` that produces a
   valid `F` for `correct` has finite `events_of` output at the
   Theorem 1 adversary's local target event of the form
   `Internal p_i_in 2`.  Identical in shape to the `fin_F`
   hypothesis of Theorem 1 (`CD_FN_unavoidable`); trivially
   satisfied by any "implementable" algorithm whose output is
   supported on the finite process set.

   *History.*  Earlier revisions of this development took two
   additional load-bearing hypotheses on Theorems 3/4/5:

   - An unconditional `bb_unsolv: ¬ BlackBox_solvable procs correct`,
     since *discharged* by `BlackBox_unsolvable` in
     `BlackBox_Unsolvable.thy` (a proven theorem derived directly
     from Theorem 1 via the BB-to-CD projection).

   - The locale axiom `cd_can_identify_correct` in
     `byzantineSystem_with_identification` (R2's meta-level step,
     in `Reductions.thy`).  This *no longer feeds the
     impossibility chain*: Theorems 3/4/5 now route directly
     through Theorem 1 in `byzantineSystem` (no `_with_identification`
     extension needed).  R2 itself is preserved as paper-faithful
     documentation of the §4.2 chain.

   Even earlier revisions packaged `bb_unsolv` as a "bridge"
   predicate `bb_realizes_flp_consensus`, since fully retired.

   The formerly-vacuous locale axiom
   `byzantineSystem.flp_consensus_impossibility` was retired earlier;
   `Foundation_Vacuity.thy` retains the machine-checked
   counter-example as a regression test.

   The FLP impossibility is *proven* (no axiom) as
   `flp_consensus_unsolvable` in `FLP_Consensus.thy`, against the
   AFP entry's `ConsensusFails`.  It is retained as the AFP-FLP
   citation that motivates the paper's chain
   `Consensus ⪯ BlackBox ⪯ CD` but is not on the impossibility
   path of this development; the headline theorems route through
   Theorem 1 instead.

2. `byzantineSystem_with_identification.cd_can_identify_correct` —
   the positive form of the paper's meta-level argument that any CD
   solver internally identifies the correct set.  This is the
   `blackbox_reduces_to_cd` reduction's only non-constructive step;
   the paper's prose is informal here, and we deliberately chose the
   smallest assumption that closes the gap rather than papering over
   it with `sorry`.

Both are documented at length in `README.md`.

## Out-of-scope items (preserved for future work)

For the full, up-to-date breakdown see [`ROADMAP.md`](ROADMAP.md).
All 18 paper theorems are now proven; the remaining work is
paper-adjacent deepening rather than paper-required content:

- **Concrete cryptographic primitive layer.**  `CD_with_Crypto.thy`
  treats crypto the same way the paper itself does when citing
  Bracha 1987 for BRB (as an off-the-shelf primitive whose role
  is to discharge `correct_reporting`).  A faithful mechanisation
  of digital signatures, collision-resistant hashes, and
  recursive hash histories would let the development capture the
  paper's quantitative FP-prevention qualifier ("FP prevented
  for `t < n/3`" under Bracha's BRB).
- **Scheduler-level realisation of BCB causal order.**
  `Primitives.thy` names BRU and BCB-over-BRB at the event level
  and threads `bcb_causal_order` through the broadcast-side
  composition theorems.  BRU is operationally realised by the
  existing inductive `run_step`; BCB's causal-order half is not
  enforced by the run scheduler and is left as a hypothesis.  A
  scheduler-level refinement of `run_step` that enforces causal-
  order delivery would discharge it.

Earlier out-of-scope items that have since been completed:

- **Theorems 1, 2** — proven constructively (`Theorems_1_2.thy`).
- **Theorems 6, 7, 8** — proven at the abstract + operational +
  run-model layers (`BHB.thy`, `CD_B_Algorithm.thy`, `Delivery.thy`,
  `Execution_Model.thy`).
- **Theorem 15** — proven fully (`CD_vs_Consensus.thy`).
- **Theorem 16** (both halves) — Consensus-impossibility half via
  `T16_Consensus_unsolvable_part`; CD-solvable-under-crash half
  via `T16_CD_solvable_under_crash_part`.
- **Theorems 17, 18** — proven in `CO.thy`.
- **Theorems 9–14** — proven in `CD_with_Crypto.thy` (T9/T10/T11
  as crypto-independent corollaries of T3/T4/T5; T12/T13 as
  corollaries of T6/T7; T14 as the genuinely new
  multicast-with-crypto possibility).
- **Real-world fairness on the execution model** — `Liveness.thy`
  proves `fair_run_delivers` over infinite executions modelled as
  `nat ⇒ 'p config`.
- **BRU / BCB-over-BRB operational primitives behind T6/T7** —
  `Primitives.thy` names the two primitives and composes them
  end-to-end with the run model into operational T6 / T7.
