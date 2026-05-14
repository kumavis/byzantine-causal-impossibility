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

## Status (initial commit `524a4d2`)

Delivered against the original request:

| Item                                                          | Status                                                                                                                                                         |
|---------------------------------------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `ByzantineSystem.thy`                                         | Done.  Locale `process_partition` + `byzantineSystem`; FLP impossibility imported as a locale axiom.  See `README.md` for the discharge sketch.                |
| `Events.thy`                                                  | Done.  Datatype `'p event`, per-process and global histories, program-order, message-order, transitive closure `hb`, Boolean `hb_eval`.                        |
| `CD.thy`                                                      | Done.  `valid`, `false_negative`, `false_positive`, adversary record, `produces_valid_F`, `CD_solvable`.                                                       |
| `BlackBox.thy`                                                | Done.  `w_value`, `bb_output` record, `solves_BlackBox`, `BlackBox_solvable`.                                                                                  |
| `Reductions.thy` — `consensus_reduces_to_blackbox`            | Done, fully constructive, declarative Isar.                                                                                                                    |
| `Reductions.thy` — `blackbox_reduces_to_cd`                   | Done, *modulo* one named locale assumption `cd_can_identify_correct` in sub-locale `byzantineSystem_with_identification`.  Paper-faithfulness justified in `README.md`. |
| `Impossibility.thy` — Theorems 3, 4, 5                        | Done.                                                                                                                                                          |
| `ROOT`                                                        | Done.                                                                                                                                                          |
| `README.md` — structure, strategy, gaps, assumptions          | Done.                                                                                                                                                          |
| Declarative Isar throughout, no apply-style, no silent gaps   | Audited.  `grep` for `apply\|sorry\|oops\|sledgehammer\|try0` in `ByzantineCD/*.thy` returns nothing.                                                          |
| `isabelle build -D .` succeeds with zero `sorry` / zero `oops`| **Verified** on Isabelle2025-2 + AFP snapshot 2026-05-13 (rebuild log: `0:00:02` ByzantineCD wall-time, all six theories at 100%).                              |

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

### Open assumptions

Two named assumptions are introduced beyond plain HOL:

1. `byzantineSystem.flp_consensus_impossibility` — the FLP
   impossibility transferred from the AFP `FLP` entry through the
   "Byzantine subsumes crash" embedding.  **Caveat surfaced after
   build verification:** at the present abstraction level this axiom
   is not just hard to discharge against AFP — it is logically
   *inconsistent* with `byzantine ≠ {}` in HOL.  The diagnostic
   theory `Foundation_Vacuity.thy` exhibits a pure-HOL function
   `simple_alg C V p \<equiv> \<exists>q\<in>C. V q` satisfying
   `solves_Consensus C (simple_alg C)`, so `\<exists>alg. solves_Consensus
   correct alg` is provably True, the axiom's right-hand side is
   provably False, and the impossibility theorems are vacuous in
   exactly the case the paper is about.  Fixing this requires
   strengthening `solves_Consensus` so it demands realisability by an
   asynchronous distributed protocol (e.g.\ by quantifying over
   `flpSystem` instances of the AFP entry) — at which point the FLP
   discharge becomes mechanisable but the rest of the development
   (CD, BlackBox, Reductions) must be re-checked against the new
   predicate.  Recorded as a load-bearing open item; see `README.md`.
2. `byzantineSystem_with_identification.cd_can_identify_correct` —
   the positive form of the paper's meta-level argument that any CD
   solver internally identifies the correct set.  This is the
   `blackbox_reduces_to_cd` reduction's only non-constructive step;
   the paper's prose is informal here, and we deliberately chose the
   smallest assumption that closes the gap rather than papering over
   it with `sorry`.

Both are documented at length in `README.md`.

## Out-of-scope items (preserved for future work)

- Theorems 6, 7, 8 — `B`-happened-before positive results.  The
  `Events.thy` foundation is built with `Send` and `Receive` peer
  fields exactly so that `bhb` can be defined inductively over
  correct-process paths without reworking the event datatype.
- Theorems 9 – 14 — cryptography-allowing variants.
- Theorems 15, 16 — CD vs Consensus relationship results.
- Theorems 1, 2 — corollaries; provable in the existing setup if
  desired.
