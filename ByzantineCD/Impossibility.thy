(*
  Title:   Impossibility.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  The headline impossibility theorems for the Causality Determination
  problem CD(E, F, e*_i):

    Theorem 3:  CD is impossible in async unicasts with one or more
                Byzantine processes.
    Theorem 4:  CD is impossible in async broadcasts (even with a
                Byzantine Reliable Broadcast layer beneath).
    Theorem 5:  CD is impossible in async multicasts (trivial corollary
                of Theorem 3: unicast is the special case |G| = 1).

  Chain:

    CD_solvable
       |  R2 (blackbox_reduces_to_cd) -- in Reductions.thy, conditional
       |     on locale assumption cd_can_identify_correct.
       v
    BlackBox_solvable
       |  bb_realizes_flp_consensus -- in FLP_Consensus.thy, conditional
       |     on the meta-level bridge predicate of the same name.
       v
    \<exists> flp_consensus_solvable instance
       |  flp_consensus_unsolvable -- in FLP_Consensus.thy, *proven*
       |     against the AFP entry's ConsensusFails theorem.
       v
    False

  Theorems 3/4/5 below take both the cd_can_identify_correct
  assumption (via the surrounding locale byzantineSystem_with_identification)
  and the bb_realizes_flp_consensus assumption (as an explicit hypothesis
  with two type-witness parameters).  The FLP impossibility itself is
  no longer an axiom - it is proved in FLP_Consensus.thy.
*)

theory Impossibility
  imports Reductions FLP_Consensus
begin

section \<open>Theorem 3: CD impossible under unicast\<close>

text \<open>Paper, Theorem 3 (Section 4.2):
\begin{quote}
``It is impossible to solve causality determination (Definition 5)
as specified by CD(\<open>E, F, e_i^*\<close>) in an asynchronous unicast-based
message passing system with one or more Byzantine processes.''
\end{quote>

The paper's proof composes the two reductions of Section 4.2 with
FLP's impossibility:
\begin{quote}
``Transitivity of reductions implies that if the CD problem is
solvable, then Consensus is also solvable.  However, that contradicts
the FLP impossibility result [35] when applied to a Byzantine system,
hence CD cannot be solvable.''
\end{quote>

\textit{Deviation -- non-vacuous chain.}  At our abstraction level the
pure-HOL @{const solves_Consensus} predicate is too weak to express
FLP (Foundation\_Vacuity.thy makes this machine-checked).  We
therefore route the chain through the FLP-style
@{const flp_consensus_solvable} predicate of FLP\_Consensus.thy
instead, using the meta-level bridge @{const bb_realizes_flp_consensus}
to cross from BB-solvability to ``some asynchronous distributed
protocol flp-solves consensus''.  The chain is then:
\begin{quote}
   \<open>CD_solvable\<close>
      \<open>\<longrightarrow>\<close> \<open>BlackBox_solvable\<close> (by R2 +
                                 \<open>cd_can_identify_correct\<close>)
      \<open>\<longrightarrow>\<close> \<open>\<exists>\<close> FLP-style consensus solver (by the bridge)
      \<open>\<longrightarrow>\<close> @{term False} (by \<open>flp_consensus_unsolvable\<close>, proven
                                 against the AFP entry's
                                 \<open>ConsensusFails\<close>).
\end{quote>

The two type witnesses @{typ 's} (state) and @{typ 'v} (message-value)
are parameters of the bridge predicate.\<close>

context byzantineSystem_with_identification
begin

theorem CD_impossible_unicast:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and bridge: "bb_realizes_flp_consensus
                     procs correct TYPE('s) TYPE('v)"
  shows "\<not> CD_solvable Unicast correct"
proof
  assume CD_solv: "CD_solvable Unicast correct"

  \<comment> \<open>Step 1: CD solvable \<Longrightarrow> BlackBox solvable.\<close>
  have BB_solv: "BlackBox_solvable procs correct"
    by (rule CD_solvable_imp_BlackBox_solvable[OF CD_solv])

  \<comment> \<open>Step 2: BlackBox solvable \<Longrightarrow> False, via the bridge and FLP.\<close>
  have BB_unsolv:
    "\<not> BlackBox_solvable procs correct"
    by (rule BlackBox_unsolvable_via_bridge[OF bridge])

  from BB_solv BB_unsolv show False by contradiction
qed

section \<open>Theorem 4: CD impossible under broadcast\<close>

text \<open>Paper, Theorem 4 (Section 4.2):
\begin{quote}
``It is impossible to solve causality determination (Definition 5) as
specified by CD(\<open>E, F, e_i^*\<close>) in an asynchronous broadcast-based
message passing system with one or more Byzantine processes.''
\end{quote>

The paper's proof of Theorem 4 ``has the overall structure along the
lines of that for Theorem 3''.  Its two differences:
\begin{enumerate}
  \item ``By doing broadcasts using the Byzantine Reliable Broadcast
        (BRB) [\dots] layer, false positives can be prevented by
        ensuring no fake events/causal dependencies are added to
        \<open>F\<close>.''
  \item ``False negatives still cannot be prevented (Theorem 1
        carries over).''
\end{enumerate>

\textit{Deviation:} we do not formalise BRB.  We use the same
chain as Theorem 3, exploiting the mode-agnosticism of @{const
CD_solvable} -- the reduction-to-FLP works mode-independently.
A richer development that adds BRB would refine our \<open>Broadcast\<close>
predicate and re-state Theorem 4 with BRB as a hypothesis, but the
\emph{conclusion} -- ``CD is unsolvable'' -- is identical.\<close>

theorem CD_impossible_broadcast:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and bridge: "bb_realizes_flp_consensus
                     procs correct TYPE('s) TYPE('v)"
  shows "\<not> CD_solvable Broadcast correct"
proof
  assume CD_solv: "CD_solvable Broadcast correct"
  have BB_solv: "BlackBox_solvable procs correct"
    by (rule CD_solvable_imp_BlackBox_solvable[OF CD_solv])
  have BB_unsolv: "\<not> BlackBox_solvable procs correct"
    by (rule BlackBox_unsolvable_via_bridge[OF bridge])
  from BB_solv BB_unsolv show False by contradiction
qed

section \<open>Theorem 5: CD impossible under multicast\<close>

text \<open>Paper, Theorem 5 (Section 4.2):
\begin{quote}
``It is impossible to solve causality determination (Definition 5) as
specified by CD(\<open>E, F, e_i^*\<close>) in an asynchronous multicast-based
message passing system with one or more Byzantine processes.

Proof.  Unicast mode of communication is a special case of multicast
where each group is of size 1 (or 2 if the sender is included in the
multicast group).  Theorem 3 proved that causality determination in
the presence of even a single Byzantine process under unicast
communication is impossible to solve.  As the special case of group
size 1 (or 2) is not solvable, the general case of multicast is also
not solvable.''
\end{quote>

\textit{Faithfulness:} our \<open>CD_solvable\<close> predicate is mode-agnostic
at the level of Definition 5 (see comment in \<open>CD.thy\<close>); a multicast
algorithm could in particular be used as a unicast algorithm by
specialising to a group of size 1.  We reduce Theorem 5 to Theorem 3
explicitly via the function-level argument: if some
@{const produces_valid_F} algorithm exists for Multicast, the same
algorithm witnesses \<open>CD_solvable Unicast\<close>.\<close>

theorem CD_impossible_multicast:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and bridge: "bb_realizes_flp_consensus
                     procs correct TYPE('s) TYPE('v)"
  shows "\<not> CD_solvable Multicast correct"
proof
  assume CD_solv: "CD_solvable Multicast correct"

  \<comment> \<open>Specialise the multicast solver to the unicast mode.  At the
      abstraction level of Definition 5 this is trivial: any algorithm that
      produces a valid F under multicasting also produces a valid F under
      unicasting (the validity predicate is mode-agnostic).  Hence
      @{const CD_solvable} of @{term Multicast} entails the same for
      @{term Unicast}.\<close>
  have unicast_solv: "CD_solvable Unicast correct"
  proof -
    obtain alg where "produces_valid_F correct alg"
      using CD_solv by (auto simp: CD_solvable_def)
    thus ?thesis by (auto simp: CD_solvable_def)
  qed

  show False
    using CD_impossible_unicast[OF byz_ne cor_ne bridge] unicast_solv
    by contradiction
qed

section \<open>Summary corollary\<close>

text \<open>One statement, all three modes.\<close>

theorem CD_impossible_all_modes:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and bridge: "bb_realizes_flp_consensus
                     procs correct TYPE('s) TYPE('v)"
  shows "\<not> CD_solvable Unicast   correct"
    and "\<not> CD_solvable Broadcast correct"
    and "\<not> CD_solvable Multicast correct"
proof -
  show "\<not> CD_solvable Unicast correct"
    by (rule CD_impossible_unicast[OF byz_ne cor_ne bridge])
  show "\<not> CD_solvable Broadcast correct"
    by (rule CD_impossible_broadcast[OF byz_ne cor_ne bridge])
  show "\<not> CD_solvable Multicast correct"
    by (rule CD_impossible_multicast[OF byz_ne cor_ne bridge])
qed

end \<comment> \<open>context @{locale byzantineSystem_with_identification}\<close>

end
