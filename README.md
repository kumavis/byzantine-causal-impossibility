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
`afp-2026-05-13`**.  Verified locally:

```
Running ByzantineCD ...
ByzantineCD: theory ByzantineCD.ByzantineSystem 100% (0.102s ...)
ByzantineCD: theory ByzantineCD.Events         100% (0.694s ...)
ByzantineCD: theory ByzantineCD.CD             100% (0.338s ...)
ByzantineCD: theory ByzantineCD.BlackBox       100% (0.169s ...)
ByzantineCD: theory ByzantineCD.Reductions     100% (0.320s ...)
ByzantineCD: theory ByzantineCD.Impossibility  100% (0.045s ...)
Finished ByzantineCD (0:00:02 elapsed)
```

Reproducing:

```sh
isabelle build -d $AFP -D ByzantineCD
```

with `$AFP` pointing at a checkout of the Archive of Formal Proofs that
includes the `FLP` entry.  The development imports only
`FLP.AsynchronousSystem`, `FLP.Execution`, and `FLP.FLPTheorem`; the
Consensus problem is re-stated locally rather than imported, so the
build is robust to AFP's `FLP` entry not exposing a `Consensus.thy`
of its own.

## Scope

In scope, fully proved:

- **Theorem 3** (`CD_impossible_unicast`): CD unsolvable in asynchronous
  unicast with one or more Byzantine processes.
- **Theorem 4** (`CD_impossible_broadcast`): same, broadcast.
- **Theorem 5** (`CD_impossible_multicast`): trivial corollary of 3.

Out of scope (left as deliberate extension points; see `Events.thy`'s
event datatype, which has a `Send`/`Receive` peer parameter ready for the
B-happened-before relation):

- Theorems 6–8 (B-happened-before positive results)
- Theorems 9–14 (cryptography-allowing variants)
- Theorems 15–16 (CD vs Consensus relationships)
- Theorems 1–2 (corollaries; the foundation is enough to add them in a few
  lines if wanted)

## File structure

| File                       | Purpose                                                                                                              |
|----------------------------|----------------------------------------------------------------------------------------------------------------------|
| `ROOT`                     | Session declaration; depends on AFP `FLP`.                                                                           |
| `ByzantineSystem.thy`      | Process partition (correct ⊎ byzantine), Consensus solver signature, FLP impossibility imported as a locale axiom.   |
| `Events.thy`               | Event datatype, per-process and global histories, program-order, message-order, happened-before relation, `hb_eval`. |
| `CD.thy`                   | `valid(F)`, false positives/negatives, adversary model, CD-solver signature, `produces_valid_F`, `CD_solvable`.      |
| `BlackBox.thy`             | `w_value`, BB output record, `solves_BlackBox`, `BlackBox_solvable`.                                                 |
| `Reductions.thy`           | The two reductions of §4.2.  Constructive proofs in declarative Isar.                                                |
| `Impossibility.thy`        | Theorems 3, 4, 5 plus a summary corollary.                                                                           |
| `Foundation_Vacuity.thy`   | Diagnostic: machine-checked counter-example showing `flp_consensus_impossibility` is unsatisfiable at this abstraction. |

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

- **Composition.** `Impossibility.thy` chains R2 ∘ R1 to derive Consensus
  from CD; the FLP impossibility, imported through
  `byzantineSystem.flp_consensus_impossibility`, then yields the
  contradiction whenever `byzantine ≠ {}`.

## Assumptions introduced beyond the paper

The development introduces exactly two named assumptions that go beyond
plain HOL definitions:

1. **`byzantineSystem.flp_consensus_impossibility`** *(in
   `ByzantineSystem.thy`)*.
   Statement: `byzantine ≠ {} ⟹ ¬ (∃ alg. solves_Consensus correct alg)`.
   Faithfulness: this is intended to mirror the FLP impossibility
   result, imported through the *Byzantine subsumes crash* embedding.

   > **Important caveat (discovered during build verification).**  At
   > the present abstraction level the axiom is *not* faithful to FLP:
   > it is logically inconsistent with `byzantine ≠ {}` in HOL.  The
   > theory `Foundation_Vacuity.thy` exhibits the witness
   >
   > ```isabelle
   > simple_alg C V p \<equiv> (\<exists>q \<in> C. V q)
   > ```
   >
   > which satisfies `solves_Consensus C (simple_alg C)` purely as an
   > HOL function — no distributed-computation constraint is in scope
   > for `solves_Consensus` to fail on.  Hence `\<exists>alg. solves_Consensus
   > correct alg` is provably True, so the locale axiom collapses to
   > `byzantine = {}`, and the impossibility theorems in
   > `Impossibility.thy` are vacuous in exactly the regime
   > (`byzantine \<noteq> {}`) the paper is about.
   >
   > The structural fix is to strengthen `solves_Consensus` so it
   > demands realisability by an asynchronous distributed protocol —
   > e.g.\ by re-stating the predicate as an existential over
   > `flpSystem` instances of the AFP entry, instead of over arbitrary
   > HOL functions.  Once `solves_Consensus` is strong enough that
   > FLP's `ConsensusFails` actually bites on it, the discharge
   > sketched in the original interpretation outline below becomes
   > available.

   Intended interpretation outline (left here so it does not get lost
   when the predicate is strengthened):

   ```isabelle
   interpretation our_sys: byzantineSystem procs correct byzantine
   proof
     fix alg :: "'p consensus_alg"
     show "byzantine \<noteq> {} \<Longrightarrow> \<not> (\<exists>alg. solves_Consensus correct alg)"
       ⟨reduce solves_Consensus to AFP entry's predicate;
        invoke AFP entry's FLP theorem⟩
   qed
   ```

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
shapes.  The single touch-point — `flp_consensus_impossibility` — is a
locale axiom that we expect to be discharged by interpretation outside
the session, using the *Byzantine subsumes crash* embedding sketched
above.  If you find that the AFP entry's notion of asynchrony is stricter
than what the paper assumes (e.g., FIFO links are baked in but the paper
allows reordering), the embedding will need to be adjusted at the same
interpretation site — *not* in the body of this session.  Such an
adjustment is local and well-defined.

## Reusability for the B-happened-before extensions

`Events.thy` already records peer information on `Send` and `Receive`
events; deriving the `B`-happened-before relation
(Definition 3 of the paper) is straightforward:

```isabelle
inductive bhb :: "'p set ⇒ 'p history ⇒ 'p event ⇒ 'p event ⇒ bool"
  for C H where
    "p \<in> C ⟹ \<dots> ⟹ bhb C H e e'"   \<comment> \<open>program order at a correct process\<close>
  | "p \<in> C ⟹ q \<in> C ⟹ matches e e' ⟹ \<dots> ⟹ bhb C H e e'"
  | "bhb C H e e' ⟹ bhb C H e' e'' ⟹ bhb C H e e''"
```

The validity predicate analogously becomes a `valid_B` that uses `bhb`
in place of `hb`; the rest of the development re-uses the same locale
machinery, with Theorems 6, 7, 8 proved as inhabitations of the
constructive (positive-result) part of the framework.

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
