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

  Chain (the direct route, used here):

    CD_solvable
       |  CD_solvable extracts a witness produces_valid_F cd_alg.
       v
    produces_valid_F correct cd_alg
       |  Theorem 1 (CD_FN_unavoidable, Theorems_1_2.thy) yields an
       |     admissible adversary at which cd_alg has a false negative.
       v
    False  (false negative contradicts valid -- valid_iff_no_FP_FN).

  Theorems 3/4/5 below take only a mild finiteness side hypothesis
  (fin_cd, identical in shape to Theorem 1's fin_F).  They do not use
  the paper's "Consensus \<preceq> BlackBox \<preceq> CD + FLP" chain at all; that
  chain is preserved in Reductions.thy + BlackBox_Unsolvable.thy +
  FLP_Consensus.thy as paper-faithful documentation but is not on the
  critical path.

  In particular, Theorems 3/4/5 live in the byzantineSystem locale
  (not in byzantineSystem_with_identification), so the
  cd_can_identify_correct meta-level locale axiom of Reductions.thy
  no longer feeds the headline impossibility chain.
*)

theory Impossibility
  imports Reductions BlackBox_Unsolvable FLP_Consensus
begin

context byzantineSystem
begin

section \<open>The direct Theorem-1 chain\<close>

text \<open>Helper: \<open>byzantine \<noteq> {}\<close> and \<open>correct \<noteq> {}\<close> together yield
the distinct-pair witness Theorem 1 wants (the locale's
\<open>partition_disj\<close> separates the two sets).\<close>

lemma byz_cor_distinct_of_ne:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
  shows "\<exists>p_i p_b. p_i \<in> correct \<and> p_b \<in> byzantine \<and> p_b \<noteq> p_i"
proof -
  obtain p_i where pi: "p_i \<in> correct" using cor_ne by blast
  obtain p_b where pb: "p_b \<in> byzantine" using byz_ne by blast
  have "p_i \<noteq> p_b" using pi pb partition_disj by blast
  thus ?thesis using pi pb by blast
qed

text \<open>The direct CD-impossibility lemma: given a finiteness side
condition on every candidate solver's output history, Theorem 1
directly contradicts the existence of a \<open>produces_valid_F\<close>
algorithm.\<close>

lemma no_produces_valid_F:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "\<not> (\<exists>cd_alg. produces_valid_F correct cd_alg)"
proof
  assume "\<exists>cd_alg. produces_valid_F correct cd_alg"
  then obtain cd_alg where val_F: "produces_valid_F correct cd_alg" by blast

  have byz_cor_distinct:
    "\<exists>p_i p_b. p_i \<in> correct \<and> p_b \<in> byzantine \<and> p_b \<noteq> p_i"
    by (rule byz_cor_distinct_of_ne[OF byz_ne cor_ne])

  have fin_F:
    "\<forall>p_i_in. finite (events_of (fst (cd_alg p_i_in (Internal p_i_in 2))))"
    using fin_cd val_F by blast

  obtain adv where
    adm: "adversary_admissible correct adv"
    and FN: "false_negative (adv_E adv)
                            (fst (cd_alg (adv_i adv) (adv_e_star adv)))
                            (adv_e_star adv)"
    using CD_FN_unavoidable[where alg = cd_alg,
                            OF byz_cor_distinct fin_F]
    by blast

  have valid_at:
    "valid (adv_E adv)
           (fst (cd_alg (adv_i adv) (adv_e_star adv)))
           (adv_e_star adv)"
    using val_F adm
    by (auto simp: produces_valid_F_def Let_def split: prod.split)
  hence "\<not> false_negative (adv_E adv)
                          (fst (cd_alg (adv_i adv) (adv_e_star adv)))
                          (adv_e_star adv)"
    using valid_iff_no_FP_FN by blast
  with FN show False by contradiction
qed

section \<open>Theorem 3: CD impossible under unicast\<close>

text \<open>Paper, Theorem 3 (Section 4.2):
\begin{quote}
``It is impossible to solve causality determination (Definition 5)
as specified by CD(\<open>E, F, e_i^*\<close>) in an asynchronous unicast-based
message passing system with one or more Byzantine processes.''
\end{quote}

The paper's proof composes the two reductions of Section 4.2 with
FLP's impossibility:
\begin{quote}
``Transitivity of reductions implies that if the CD problem is
solvable, then Consensus is also solvable.  However, that contradicts
the FLP impossibility result [35] when applied to a Byzantine system,
hence CD cannot be solvable.''
\end{quote}

\textit{Deviation -- the paper's chain is bypassed.}  Theorem 1
(\<open>CD_FN_unavoidable\<close>) already gives the impossibility directly: it
exhibits, for any candidate CD-solver with finite output histories,
an admissible adversary that defeats it.  Composing that with the
definition of @{const CD_solvable} (which existentially quantifies
the solver) immediately yields the impossibility, without needing
to route through the BlackBox-and-FLP detour the paper uses.

The chain in this theory is therefore:
\begin{quote}
   \<open>CD_solvable\<close>
      \<open>\<longrightarrow>\<close> @{term "\<exists> cd_alg. produces_valid_F correct cd_alg"}
      \<open>\<longrightarrow>\<close> @{term False} (by Theorem 1, under \<open>fin_cd\<close>).
\end{quote}

The paper's chain is preserved as paper-faithful documentation in
\<open>Reductions.thy\<close> (R1, R2) and \<open>BlackBox_Unsolvable.thy\<close> (the
discharge of \<open>\<not> BlackBox_solvable\<close> via Theorem 1), but is not on
the critical path of the headline impossibility theorems below.\<close>

theorem CD_impossible_unicast:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "\<not> CD_solvable Unicast correct"
  using no_produces_valid_F[OF byz_ne cor_ne fin_cd]
  by (auto simp: CD_solvable_def)

section \<open>Theorem 4: CD impossible under broadcast\<close>

text \<open>Paper, Theorem 4 (Section 4.2):
\begin{quote}
``It is impossible to solve causality determination (Definition 5) as
specified by CD(\<open>E, F, e_i^*\<close>) in an asynchronous broadcast-based
message passing system with one or more Byzantine processes.''
\end{quote}

The paper's proof of Theorem 4 ``has the overall structure along the
lines of that for Theorem 3''.  Its two differences:
\begin{enumerate}
  \item ``By doing broadcasts using the Byzantine Reliable Broadcast
        (BRB) [\dots] layer, false positives can be prevented by
        ensuring no fake events/causal dependencies are added to
        \<open>F\<close>.''
  \item ``False negatives still cannot be prevented (Theorem 1
        carries over).''
\end{enumerate}

\textit{Deviation:} we do not formalise BRB.  Theorem 4 collapses to
Theorem 3 at this abstraction level because @{const CD_solvable} is
mode-agnostic.  A richer development that adds BRB would refine our
\<open>Broadcast\<close> predicate and re-state Theorem 4 with BRB as a
hypothesis, but the conclusion -- ``CD is unsolvable'' -- is
identical.\<close>

theorem CD_impossible_broadcast:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "\<not> CD_solvable Broadcast correct"
  using no_produces_valid_F[OF byz_ne cor_ne fin_cd]
  by (auto simp: CD_solvable_def)

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
\end{quote}\<close>

theorem CD_impossible_multicast:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "\<not> CD_solvable Multicast correct"
  using no_produces_valid_F[OF byz_ne cor_ne fin_cd]
  by (auto simp: CD_solvable_def)

section \<open>Summary corollary\<close>

text \<open>One statement, all three modes.\<close>

theorem CD_impossible_all_modes:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "\<not> CD_solvable Unicast   correct"
    and "\<not> CD_solvable Broadcast correct"
    and "\<not> CD_solvable Multicast correct"
proof -
  show "\<not> CD_solvable Unicast correct"
    by (rule CD_impossible_unicast[OF byz_ne cor_ne fin_cd])
  show "\<not> CD_solvable Broadcast correct"
    by (rule CD_impossible_broadcast[OF byz_ne cor_ne fin_cd])
  show "\<not> CD_solvable Multicast correct"
    by (rule CD_impossible_multicast[OF byz_ne cor_ne fin_cd])
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
