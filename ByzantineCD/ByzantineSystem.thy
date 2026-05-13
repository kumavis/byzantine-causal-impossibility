(*
  Title:   ByzantineSystem.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  The Byzantine system locale.  We extend the asynchronous-system layer of the
  AFP entry FLP (Bisping, Brodmann, Jungnickel, Rickmann, Seidler, Stueber,
  Wilhelm-Weidner, Peters, Nestmann, 2025) with a partition of processes into
  correct and Byzantine.  Byzantine processes are under-specified: their local
  behaviour is arbitrary.

  This theory exposes:
   * the process partition itself, with sanity lemmas;
   * an abstract Consensus solver-type and a solvesConsensus predicate;
   * the FLP impossibility for our Consensus signature, as a locale axiom
     that is intended to be discharged by lifting the AFP entry's
     impossibility theorem through the standard "Byzantine subsumes crash"
     embedding (sketched in the README).
*)

theory ByzantineSystem
  imports
    FLP.AsynchronousSystem
    FLP.Execution
    FLP.Consensus
    FLP.FLPTheorem
begin

section \<open>Process identifiers, correct vs. Byzantine partition\<close>

text \<open>We work with an arbitrary process-identifier type @{typ 'p} and
require only that the set of processes be finite, non-empty, and
partitioned into a set of correct and a set of Byzantine processes.\<close>

locale process_partition =
  fixes
    procs     :: "'p set" and
    correct   :: "'p set" and
    byzantine :: "'p set"
  assumes
    finite_procs:     "finite procs" and
    nonempty_procs:   "procs \<noteq> {}" and
    partition_union:  "procs = correct \<union> byzantine" and
    partition_disj:   "correct \<inter> byzantine = {}" and
    correct_subset:   "correct \<subseteq> procs" and
    byzantine_subset: "byzantine \<subseteq> procs"

context process_partition
begin

lemma correct_finite [simp]: "finite correct"
  using finite_procs correct_subset by (rule rev_finite_subset)

lemma byzantine_finite [simp]: "finite byzantine"
  using finite_procs byzantine_subset by (rule rev_finite_subset)

lemma correct_byzantine_disjoint:
  assumes "p \<in> correct" shows "p \<notin> byzantine"
  using assms partition_disj by blast

lemma proc_correct_or_byz:
  assumes "p \<in> procs" shows "p \<in> correct \<or> p \<in> byzantine"
  using assms partition_union by blast

end \<comment> \<open>context @{locale process_partition}\<close>

section \<open>Abstract Consensus solver signature\<close>

text \<open>We model a deterministic distributed Consensus algorithm at the level
of its observable input/output behaviour.  Each correct process @{term p}
starts with an initial boolean value @{term "V p"}; the algorithm produces
a decision value for each process.  This abstraction does not in itself
constrain communication patterns or schedules; the FLP impossibility we
import below applies to algorithms in the asynchronous message-passing
model and is faithful to the AFP entry's distributed semantics.\<close>

type_synonym 'p consensus_alg = "('p \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> bool"

text \<open>Three properties demanded of a Consensus algorithm:
  Agreement: all correct processes decide the same value.
  Validity:  if every correct process starts with @{term v}, they all decide @{term v}.
  Termination: each correct process decides.  At our abstraction level a
  decision is always returned, so Termination is implicit in the totality
  of @{typ "'p consensus_alg"}.\<close>

definition consensus_agreement ::
  "'p set \<Rightarrow> 'p consensus_alg \<Rightarrow> ('p \<Rightarrow> bool) \<Rightarrow> bool" where
  "consensus_agreement C alg V \<longleftrightarrow> (\<forall>p \<in> C. \<forall>q \<in> C. alg V p = alg V q)"

definition consensus_validity ::
  "'p set \<Rightarrow> 'p consensus_alg \<Rightarrow> ('p \<Rightarrow> bool) \<Rightarrow> bool" where
  "consensus_validity C alg V \<longleftrightarrow>
     ((\<forall>p \<in> C. V p) \<longrightarrow> (\<forall>p \<in> C. alg V p)) \<and>
     ((\<forall>p \<in> C. \<not> V p) \<longrightarrow> (\<forall>p \<in> C. \<not> alg V p))"

definition solves_Consensus ::
  "'p set \<Rightarrow> 'p consensus_alg \<Rightarrow> bool" where
  "solves_Consensus C alg \<longleftrightarrow>
     (\<forall>V. consensus_agreement C alg V \<and> consensus_validity C alg V)"

section \<open>The Byzantine system locale\<close>

text \<open>We bundle the process partition together with the FLP impossibility
fact, stated for our abstract Consensus signature.

\emph{Faithfulness note.}  We do \emph{not} re-prove FLP.  We re-use the AFP
entry's theorem.  In the intended interpretation against the AFP entry, the
axiom below is discharged as follows.  Take any putative @{term "alg ::
'p consensus_alg"} that satisfies @{const solves_Consensus}.  Show that it
also satisfies the FLP entry's @{const Consensus_solvability} predicate
(under the embedding of the abstract signature into FLP's record-shaped
distributed-system model: an asynchronous schedule and arbitrarily one
failing process induces an input vector @{term V} and a decision per
correct process).  Since Byzantine failures subsume crash failures (a
Byzantine process can simulate a crash by halting after a chosen prefix),
the FLP impossibility theorem yields a contradiction whenever
@{term "byzantine \<noteq> {}"}.\<close>

locale byzantineSystem = process_partition procs correct byzantine
  for procs correct byzantine :: "'p set" +
  assumes
    flp_consensus_impossibility:
      "byzantine \<noteq> {} \<Longrightarrow> \<not> (\<exists>alg. solves_Consensus correct alg)"

context byzantineSystem
begin

lemma no_consensus_solver:
  assumes "byzantine \<noteq> {}"
  shows "\<nexists>alg. solves_Consensus correct alg"
  using assms flp_consensus_impossibility by blast

text \<open>Sanity lemma: ``Byzantine subsumes crash''.  Any algorithm that
solves Consensus tolerating Byzantine failures also solves Consensus
tolerating crash failures; conversely, the impossibility of Consensus
under crash failures (FLP) implies the impossibility of Consensus under
Byzantine failures.  In our locale this is a one-line consequence of
@{thm flp_consensus_impossibility}.\<close>

lemma byzantine_subsumes_crash:
  assumes "byzantine \<noteq> {}"
  shows "\<not> (\<exists>alg. solves_Consensus correct alg)"
  using assms flp_consensus_impossibility .

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
