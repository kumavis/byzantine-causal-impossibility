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

  All three follow from the composition  Consensus \<preceq> BlackBox \<preceq> CD
  proved in Reductions.thy plus the FLP impossibility imported through
  byzantineSystem.flp_consensus_impossibility.
*)

theory Impossibility
  imports Reductions
begin

section \<open>Theorem 3: CD impossible under unicast\<close>

text \<open>Paper:
\begin{quote}
   It is impossible to solve causality determination (Definition 5) as
   specified by CD($E, F, e_i^*$) in an asynchronous unicast-based
   message-passing system with one or more Byzantine processes.
\end{quote}

Strategy: we have \<open>consensus_reduces_to_blackbox\<close> and
\<open>blackbox_reduces_to_cd\<close>; their composition gives
Consensus $\preceq$ BlackBox $\preceq$ CD.  The FLP impossibility, imported
through \<open>byzantineSystem.flp_consensus_impossibility\<close>, then yields the
contradiction whenever @{term "byzantine \<noteq> {}"}.\<close>

context byzantineSystem_with_identification
begin

theorem CD_impossible_unicast:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
  shows "\<not> CD_solvable Unicast correct"
proof
  assume CD_solv: "CD_solvable Unicast correct"

  \<comment> \<open>Step 1: CD solvable \<Longrightarrow> BlackBox solvable.\<close>
  have BB_solv: "BlackBox_solvable procs correct"
    by (rule CD_solvable_imp_BlackBox_solvable[OF CD_solv])

  \<comment> \<open>Step 2: BlackBox solvable \<Longrightarrow> Consensus solvable.\<close>
  have Cons_solv: "\<exists>alg. solves_Consensus correct alg"
    by (rule BlackBox_solvable_imp_Consensus_solvable[OF cor_ne BB_solv])

  \<comment> \<open>Step 3: FLP applies (we are in @{locale byzantineSystem}, and
      @{term "byzantine \<noteq> {}"}).\<close>
  have Cons_unsolv: "\<not> (\<exists>alg. solves_Consensus correct alg)"
    by (rule flp_consensus_impossibility[OF byz_ne])

  from Cons_solv Cons_unsolv show False by contradiction
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
same theorem as Theorem 3 specialised to the broadcast mode.  We record it
explicitly for downstream reuse.\<close>

theorem CD_impossible_broadcast:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
  shows "\<not> CD_solvable Broadcast correct"
proof
  assume CD_solv: "CD_solvable Broadcast correct"
  have BB_solv: "BlackBox_solvable procs correct"
    by (rule CD_solvable_imp_BlackBox_solvable[OF CD_solv])
  have Cons_solv: "\<exists>alg. solves_Consensus correct alg"
    by (rule BlackBox_solvable_imp_Consensus_solvable[OF cor_ne BB_solv])
  have Cons_unsolv: "\<not> (\<exists>alg. solves_Consensus correct alg)"
    by (rule flp_consensus_impossibility[OF byz_ne])
  from Cons_solv Cons_unsolv show False by contradiction
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
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
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
    using CD_impossible_unicast[OF byz_ne cor_ne] unicast_solv by contradiction
qed

section \<open>Summary corollary\<close>

text \<open>One statement, all three modes.\<close>

theorem CD_impossible_all_modes:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
  shows "\<not> CD_solvable Unicast   correct"
    and "\<not> CD_solvable Broadcast correct"
    and "\<not> CD_solvable Multicast correct"
proof -
  show "\<not> CD_solvable Unicast correct"
    by (rule CD_impossible_unicast[OF byz_ne cor_ne])
  show "\<not> CD_solvable Broadcast correct"
    by (rule CD_impossible_broadcast[OF byz_ne cor_ne])
  show "\<not> CD_solvable Multicast correct"
    by (rule CD_impossible_multicast[OF byz_ne cor_ne])
qed

end \<comment> \<open>context @{locale byzantineSystem_with_identification}\<close>

end
