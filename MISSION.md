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

