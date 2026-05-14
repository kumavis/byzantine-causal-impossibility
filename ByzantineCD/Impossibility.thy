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

text \<open>Paper:
\begin{quote}
   It is impossible to solve causality determination (Definition 5) as
   specified by CD($E, F, e_i^*$) in an asynchronous unicast-based
   message-passing system with one or more Byzantine processes.
\end{quote}

Strategy: compose
\<open>blackbox_reduces_to_cd\<close> with the BlackBox-to-FLP bridge predicate
@{const bb_realizes_flp_consensus} and conclude by
@{thm flp_consensus_unsolvable}.\<close>

context byzantineSystem_with_identification
begin

theorem CD_impossible_unicast:
  assumes cor_ne: "correct \<noteq> {}"
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

text \<open>Paper:
\begin{quote}
   It is impossible to solve causality determination (Definition 5) as
   specified by CD($E, F, e_i^*$) in an asynchronous broadcast-based
   message-passing system with one or more Byzantine processes.
\end{quote}

The paper's proof of Theorem 4 ``has the overall structure along the
lines of that for Theorem 3''.  The differences are:
\begin{enumerate}
  \item False positives can now be prevented by running broadcasts over a
        Byzantine Reliable Broadcast (BRB) layer beneath.
  \item False negatives still cannot be prevented (Theorem 1 carries over).
\end{enumerate}
Both are within-mode strengthenings; the reduction structure is identical.
Since our abstract Black\_Box-reduces-to-CD argument does not depend on the
mode (it relies only on @{thm cd_can_identify_correct}), Theorem 4 is the
same theorem as Theorem 3 specialised to the broadcast mode.\<close>

theorem CD_impossible_broadcast:
  assumes cor_ne: "correct \<noteq> {}"
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

text \<open>Paper:
\begin{quote}
   It is impossible to solve causality determination (Definition 5) as
   specified by CD($E, F, e_i^*$) in an asynchronous multicast-based
   message-passing system with one or more Byzantine processes.

   Proof. Unicast mode of communication is a special case of multicast
   where each group is of size 1 (or 2 if the sender is included in the
   multicast group).  Theorem 3 proved that causality determination in the
   presence of even a single Byzantine process under unicast communication
   is impossible to solve.  As the special case of group size 1 (or 2) is
   not solvable, the general case of multicast is also not solvable.
\end{quote}

In our abstraction the @{const CD_solvable} predicate does not actually
depend on the mode tag (see comment in \<open>CD.thy\<close>); a multicast
algorithm could in particular be used as a unicast algorithm by
specialising to \<open>|G| = 1\<close>.  We therefore reduce Theorem 5 to
Theorem 3 explicitly.\<close>

theorem CD_impossible_multicast:
  assumes cor_ne: "correct \<noteq> {}"
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
    using CD_impossible_unicast[OF cor_ne bridge] unicast_solv by contradiction
qed

section \<open>Summary corollary\<close>

text \<open>One statement, all three modes.\<close>

theorem CD_impossible_all_modes:
  assumes cor_ne: "correct \<noteq> {}"
      and bridge: "bb_realizes_flp_consensus
                     procs correct TYPE('s) TYPE('v)"
  shows "\<not> CD_solvable Unicast   correct"
    and "\<not> CD_solvable Broadcast correct"
    and "\<not> CD_solvable Multicast correct"
proof -
  show "\<not> CD_solvable Unicast correct"
    by (rule CD_impossible_unicast[OF cor_ne bridge])
  show "\<not> CD_solvable Broadcast correct"
    by (rule CD_impossible_broadcast[OF cor_ne bridge])
  show "\<not> CD_solvable Multicast correct"
    by (rule CD_impossible_multicast[OF cor_ne bridge])
qed

end \<comment> \<open>context @{locale byzantineSystem_with_identification}\<close>

end
