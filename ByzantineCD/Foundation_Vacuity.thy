(*
  Title:   Foundation_Vacuity.thy
  Purpose: Machine-checked diagnostic that the locale axiom
           byzantineSystem.flp_consensus_impossibility is logically
           inconsistent with byzantine \<noteq> {}.  Therefore the locale
           byzantineSystem itself is satisfiable only when
           byzantine = {}, and the impossibility theorems in
           Impossibility.thy hold vacuously in the very case
           (byzantine \<noteq> {}) the paper is about.

           This theory contains no proof of impossibility; it contains
           the counter-example showing why the present abstraction
           needs to be strengthened before the FLP discharge attempted
           in the README is mechanisable.  See README.md for
           discussion.
*)

theory Foundation_Vacuity
  imports ByzantineSystem
begin

section \<open>A pure-HOL ``consensus solver'' satisfying \<open>solves_Consensus\<close>\<close>

text \<open>The abstract predicate \<open>solves_Consensus C alg\<close> in
\<open>ByzantineSystem.thy\<close> demands of @{term alg} only Agreement (all
correct processes decide the same value) and Validity (if every
correct process proposes the same value, they decide it).  In
particular, it places \emph{no} constraint making @{term alg}
implementable by an asynchronous distributed protocol.  At this
abstraction level the function below already satisfies the
predicate.\<close>

definition simple_alg :: "'p set \<Rightarrow> 'p consensus_alg" where
  "simple_alg C V p \<equiv> (\<exists>q \<in> C. V q)"

lemma simple_alg_solves_Consensus:
  "solves_Consensus C (simple_alg C)"
proof -
  have AGR: "\<forall>V. consensus_agreement C (simple_alg C) V"
    by (auto simp: consensus_agreement_def simple_alg_def)
  have VAL: "\<forall>V. consensus_validity C (simple_alg C) V"
    by (auto simp: consensus_validity_def simple_alg_def)
  show ?thesis
    using AGR VAL by (simp add: solves_Consensus_def)
qed

lemma exists_consensus_alg:
  "\<exists>alg. solves_Consensus (C::'p set) alg"
  using simple_alg_solves_Consensus by blast

section \<open>Vacuity of the \<open>byzantineSystem\<close> locale\<close>

text \<open>From @{thm exists_consensus_alg} we obtain a witness for the
existential which \<open>byzantineSystem.flp_consensus_impossibility\<close>
denies.  Inside the locale this yields @{term False} whenever
@{term "byzantine \<noteq> {}"} \<open>---\<close> i.e.\ exactly the regime where the
paper's impossibility result is meant to bite.\<close>

lemma (in byzantineSystem) locale_inconsistent_when_byzantine_nonempty:
  assumes "byzantine \<noteq> {}"
  shows   "False"
  using assms flp_consensus_impossibility exists_consensus_alg
  by blast

text \<open>Consequence: any \<open>interpretation\<close> of \<open>byzantineSystem\<close> that
picks a non-empty @{term byzantine} must \emph{also} discharge an
unprovable goal.  The impossibility theorems in \<open>Impossibility.thy\<close>
are therefore vacuous in the non-empty Byzantine case until
\<open>solves_Consensus\<close> is strengthened to require, for example,
realisability by an asynchronous distributed protocol \<open>--\<close> at which
point the FLP-discharge sketch in \<open>README.md\<close> becomes
mechanisable.\<close>

end
