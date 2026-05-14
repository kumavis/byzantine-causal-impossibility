(*
  Title:   Foundation_Vacuity.thy
  Purpose: Historical / regression diagnostic.  Earlier versions of
           ByzantineSystem.thy declared a locale axiom

             flp_consensus_impossibility:
               "byzantine \<noteq> {} \<Longrightarrow> \<not> (\<exists>alg. solves_Consensus correct alg)"

           which turned out to be unsatisfiable in HOL: the pure-HOL
           function simple_alg below already satisfies the right-hand
           side, so the axiom collapsed to byzantine = {}.

           That axiom has now been retired.  The FLP impossibility is
           imported instead through the AFP entry's ConsensusFails
           theorem in FLP_Consensus.thy, and the chain from CD
           solvability to a contradiction is closed in Impossibility.thy
           via an explicit BlackBox-to-FLP bridge predicate.

           The witness lemmas in this file are kept as a regression
           test: they continue to prove that the abstract predicate
           solves_Consensus alone is too weak to express
           ``asynchronous-distributed consensus''.  Any future attempt
           to re-state the impossibility purely on solves_Consensus
           will re-introduce the vacuity these lemmas witness.
*)

theory Foundation_Vacuity
  imports ByzantineSystem
begin

section \<open>A pure-HOL ``consensus solver'' satisfying \<open>solves_Consensus\<close>\<close>

text \<open>The abstract predicate @{const solves_Consensus} demands only
Agreement and Validity on a HOL function; it places \emph{no} constraint
making the function implementable by an asynchronous distributed
protocol.  At this abstraction level the function below already
satisfies the predicate, so any axiom of the shape ``no abstract
@{term alg} satisfies @{const solves_Consensus}'' is unsatisfiable.\<close>

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

section \<open>The natural-looking ``abstract-consensus is unsolvable'' claim is false\<close>

text \<open>This is what the retired axiom denied.  The negation is a HOL
theorem, hence the original axiom was unsatisfiable.\<close>

lemma exists_abstract_consensus_solver:
  shows "\<not> (\<not> (\<exists>alg. solves_Consensus (C::'p set) alg))"
  using exists_consensus_alg by blast

end
