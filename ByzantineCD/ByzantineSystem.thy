(*
  Title:   ByzantineSystem.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  Paper coverage:
    - Section 2 ("System model"): the partition of processes into
      correct and Byzantine.
    - Section 4.2: the abstract Consensus problem (used in the
      reduction Consensus \<preceq> BlackBox).

  This theory exposes:
    * the process partition with sanity lemmas;
    * an abstract Consensus solver-type and the solves_Consensus
      predicate;
    * the byzantineSystem locale (a thin extension of
      process_partition; the formerly-bundled FLP-impossibility
      axiom was retired -- see Foundation_Vacuity.thy and
      FLP_Consensus.thy).

  Deviations from the paper:

    1. The paper writes "G = (P, C)" with C the set of FIFO links.
       We only track P (here split into "procs"); the FIFO
       constraint is not enforced because none of T1-T5 need it.

    2. The paper does not name "correct" / "Byzantine" sets in the
       formal model; it refers to "a Byzantine process p_b" in
       prose.  We make the partition explicit as locale parameters
       so theorems can quantify "for every admissible adversary"
       with respect to a chosen partition.

    3. We do not formalise digital signatures / cryptography (paper
       Section 4.4); that is the difference between Theorems 3-5
       (no crypto) and 9-14 (with crypto).
*)

theory ByzantineSystem
  imports
    FLP.AsynchronousSystem
    FLP.Execution
    FLP.FLPTheorem
begin

section \<open>Process identifiers, correct vs. Byzantine partition\<close>

text \<open>Paper, Section 2:
\begin{quote}
``The distributed system is modeled as an undirected graph
\<open>G = (P, C)\<close>.  Here \<open>P\<close> is the set of processes communicating
asynchronously in the distributed system.  Let \<open>|P| = n\<close>.''
\end{quote}

The paper does not formalise the correct/Byzantine partition in
the model itself; it talks about ``a correct process \<open>p_c\<close>'' and
``a Byzantine process \<open>p_b\<close>'' in prose.  We make the partition
explicit: \<open>procs\<close> is the set \<open>P\<close>, \<open>correct\<close> is the set of
non-Byzantine processes, \<open>byzantine\<close> is the rest.  Finiteness and
non-emptiness of \<open>P\<close> are taken from the paper's tacit assumptions.\<close>

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

text \<open>Paper, Section 4.2:
\begin{quote}
``In the Consensus problem, each process has an initial value and
all correct processes must agree on a single value.  The solution
needs to satisfy the following three conditions.

\begin{itemize}
  \item Agreement: All non-faulty processes must agree on the same
        single value.
  \item Validity: If all non-faulty processes have the same initial
        value, then the agreed-on value by all the non-faulty
        processes must be that same value.
  \item Termination: Each non-faulty process must eventually decide
        on a value.
\end{itemize}''
\end{quote}

We model a Consensus algorithm at the level of its observable
input/output behaviour: it takes an initial-value vector \<open>V\<close>
(boolean per process) and produces a decision (boolean per process).

\textit{Major deviation (load-bearing).}  At this level of
abstraction the predicate \<open>solves_Consensus\<close> below only enforces
Agreement and Validity, with Termination trivially holding by
totality of the function type.  The FLP impossibility result relies
crucially on Termination-under-failure in an asynchronous distributed
\emph{protocol}, which a pure HOL function does not model; this
makes \<open>solves_Consensus\<close> too weak for FLP to bite on, and is the
reason the impossibility chain in @{theory_text \<open>Impossibility.thy\<close>}
routes through the FLP-style predicate in
@{theory_text \<open>FLP_Consensus.thy\<close>} instead.  See
\<open>Foundation_Vacuity.thy\<close> for a machine-checked counter-example to
the naive ``no abstract consensus solver exists'' claim.\<close>

type_synonym 'p consensus_alg = "('p \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> bool"

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

text \<open>We bundle the process partition into a locale named
\<open>byzantineSystem\<close>.  The locale has no extra assumptions beyond
those of @{locale process_partition}: it merely fixes the partition
\<open>procs = correct \<union> byzantine\<close>.

\textit{Historical note.}  Earlier versions of this development
added a locale axiom \<open>flp_consensus_impossibility\<close> that claimed the
FLP impossibility directly on @{const solves_Consensus}, but that
axiom turned out to be unsatisfiable in HOL (the pure-HOL function
\<open>simple_alg C V p \<equiv> \<exists>q\<in>C. V q\<close> satisfies @{const solves_Consensus},
so denying it collapses to \<open>byzantine = {}\<close>).  See
\<open>Foundation_Vacuity.thy\<close> for the machine-checked counter-example.
The impossibility is now imported from the AFP entry's
\<open>ConsensusFails\<close> theorem via the FLP-style predicate in
\<open>FLP_Consensus.thy\<close>, and the chain from CD-solvability to a
contradiction is closed in \<open>Impossibility.thy\<close> through the
\<open>bb_realizes_flp_consensus\<close> bridge.\<close>

locale byzantineSystem = process_partition procs correct byzantine
  for procs correct byzantine :: "'p set"

end
