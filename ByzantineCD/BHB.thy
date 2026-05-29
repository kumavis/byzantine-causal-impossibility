(*
  Title:   BHB.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  The Byzantine happened-before relation \<rightarrow>_B (paper Definition 3) and
  the CD_B problem (paper Definition 6), the prerequisites for paper
  Section 4.3 (Theorems 6, 7, 8).

  ----------------------------------------------------------------
  Theorems 6, 7, 8 -- scope

    Theorem 6 (paper, Section 4.3.2, "possible"):
      CD_B is solvable in an asynchronous unicast-based system with
      one or more Byzantine processes.
      Proof: explicit algorithm using BRU (Byzantine Reliable Unicast,
      i.e., point-to-point) plus locally-simulated broadcasts of
      causal-dependency control information.

    Theorem 7 (paper, Section 4.3.1, "possible"):
      CD_B is solvable in an asynchronous broadcast-based system with
      one or more Byzantine processes.
      Proof: explicit algorithm using BCB (Byzantine Causal Broadcast)
      over BRB (Byzantine Reliable Broadcast).

    Theorem 8 (paper, Section 4.3, "impossible"):
      CD_B is unsolvable in an asynchronous multicast-based system
      with one or more Byzantine processes.
      Proof: BRM (Byzantine Reliable Multicast) is unachievable
      without identifying Byzantine processes; hence CD_B over
      multicast is unachievable.

  ----------------------------------------------------------------
  What we formalise here

  We provide the definitional layer that paper Section 4.3 needs:

    - The Byzantine happened-before relation \<rightarrow>_B (bhb below), with
      its boolean evaluation form bhb_eval.

    - valid_B (paper, Definition 6's correctness criterion) and the
      false negative/positive variants under \<rightarrow>_B (FN_B, FP_B).

    - A small library of structural lemmas (bhb is a sub-relation of
      hb against the same history, etc.) used downstream.

  Theorems 6, 7, 8 are proven in CD_B_Algorithm.thy on top of this
  foundation; the algorithm signature used there is the richer
  cd_alg_with_recv from CD_B_Algorithm.thy (which takes a per-peer
  reported history as input), not the bare cd_solver type below.

  The bare produces_valid_F_B / CD_B_solvable predicates near the
  end of this file are retained as the paper-faithful definitional
  surface that mirrors Definition 6 against the bare cd_solver
  type; the downstream development uses the cd_alg_with_recv
  versions exclusively.
*)

theory BHB
  imports Events CD
begin

section \<open>Byzantine happened-before relation (paper Definition 3)\<close>

text \<open>Paper, Section 3:
\begin{quote}
``Definition 3. The Byzantine happened before relation \<open>\<rightarrow>_B\<close> on
events at correct processes consists of the following rules:
[program order at correct processes, message order between correct
processes, transitive closure].''
\end{quote}

We mechanise \<open>\<rightarrow>_B\<close> as the transitive closure of a one-step relation
that requires both endpoints of each step to be at correct processes
(in the parameter \<open>C\<close>) and that the underlying step is either a
program-order step or a message-order step.  Restricting endpoints to
@{term C} at each step suffices: by transitivity, any \<open>bhb\<close> chain has
all its events at correct processes.\<close>

definition bhb_step ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "bhb_step C H e e' \<longleftrightarrow>
     proc_of e \<in> C \<and> proc_of e' \<in> C \<and>
     (program_order H e e' \<or> message_order H e e')"

definition bhb ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "bhb C H e e' \<longleftrightarrow> (bhb_step C H)\<^sup>+\<^sup>+ e e'"

text \<open>Paper, Section 3:
\begin{quote}
``\<open>e \<rightarrow>_B e' |_E\<close> is defined as (\<open>e \<rightarrow> e' |_E\<close> \<open>\<and>\<close> there is a causal
path from \<open>e\<close> to \<open>e'\<close> going through correct processes in the
execution).''
\end{quote}
The paper's evaluation operator \<open>\<rightarrow>_B|_H\<close> behaves analogously to
@{const hb_eval}: an event pair satisfies it only if both endpoints
are recorded in @{term H}.\<close>

definition bhb_eval ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "bhb_eval C H e e' \<longleftrightarrow>
     e \<in> events_of H \<and> e' \<in> events_of H \<and> bhb C H e e'"

subsection \<open>Structural lemmas: bhb is a sub-relation of hb\<close>

text \<open>A single \<open>bhb_step\<close> is, by definition, also an \<open>hb_step\<close>;
the converse fails because @{const hb_step} accepts steps through
Byzantine processes.\<close>

lemma bhb_step_imp_hb_step:
  assumes "bhb_step C H e e'"
  shows "hb_step H e e'"
  using assms unfolding bhb_step_def hb_step_def by blast

lemma bhb_imp_hb:
  assumes "bhb C H e e'"
  shows "hb H e e'"
proof -
  from assms have "(bhb_step C H)\<^sup>+\<^sup>+ e e'" unfolding bhb_def .
  hence "(hb_step H)\<^sup>+\<^sup>+ e e'"
  proof (induction rule: tranclp_induct)
    case (base y)
    from bhb_step_imp_hb_step[OF base]
    show ?case by (rule tranclp.r_into_trancl)
  next
    case (step y z)
    have step_hb: "hb_step H y z"
      by (rule bhb_step_imp_hb_step[OF step.hyps(2)])
    from step.IH step_hb
    show ?case by (rule tranclp.trancl_into_trancl)
  qed
  thus "hb H e e'" by (simp add: hb_def)
qed

lemma bhb_eval_imp_hb_eval:
  assumes "bhb_eval C H e e'"
  shows "hb_eval H e e'"
  using assms bhb_imp_hb
  by (auto simp: bhb_eval_def hb_eval_def)

text \<open>Domain restriction: a \<open>bhb\<close> chain begins and ends at
correct processes (any intermediate node is at a correct process
too, by the same step-wise restriction).\<close>

lemma bhb_proc_of_endpoints:
  assumes "bhb C H e e'"
  shows "proc_of e \<in> C \<and> proc_of e' \<in> C"
proof -
  from assms have "(bhb_step C H)\<^sup>+\<^sup>+ e e'" unfolding bhb_def .
  thus ?thesis
  proof (induction rule: tranclp_induct)
    case (base y)
    thus ?case unfolding bhb_step_def by blast
  next
    case (step y z)
    from step.hyps(2) have "proc_of z \<in> C" unfolding bhb_step_def by blast
    with step.IH show ?case by blast
  qed
qed

section \<open>The \<open>CD_B\<close> problem (paper Definition 6)\<close>

text \<open>Paper, Section 4.3:
\begin{quote}
``Definition 6. The causality determination problem
\<open>CD_B(E, F, e_i^*)\<close> for any event \<open>e_i^* \<in> T(E)\<close> at a correct
process \<open>p_i\<close> is to devise an algorithm to collect the execution
history \<open>E\<close> as \<open>F\<close> at \<open>p_i\<close> such that \<open>valid_B(F) = 1\<close>, where
\[
\mathit{valid}_B(F) =
  \begin{cases}
    1 & \text{if } \forall e_h^x,\ e_h^x \rightarrow_B e_i^* |_E
                    = e_h^x \rightarrow_B e_i^* |_F \\
    0 & \text{otherwise}
  \end{cases}
\]''
\end{quote}

The paper also identifies the analogues of FN and FP under \<open>\<rightarrow>_B\<close>:
\<open>FN_B\<close> is a witness of \<open>e \<rightarrow>_B e_i^* |_E = 1 \<and> e \<rightarrow>_B e_i^* |_F = 0\<close>
on a causal path going through correct processes (Section 4.3,
``denoting a false negative under \<open>\<rightarrow>_B\<close>''), and analogously \<open>FP_B\<close>
on the other side.  Paper Section 4.3 notes that the second case
``cannot occur as the first and third terms cannot both be true'' --
i.e., \<open>FP_B\<close> is vacuous in the paper's reading.  We formalise both
\<open>FN_B\<close> and \<open>FP_B\<close> uniformly here; the vacuity of \<open>FP_B\<close> is a
lemma we leave to whoever proves Theorems 6/7 to bring out
explicitly if needed.\<close>

definition valid_B ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> bool" where
  "valid_B C E F e_star \<longleftrightarrow>
     (\<forall>e \<in> events_of E \<union> events_of F.
        bhb_eval C E e e_star = bhb_eval C F e e_star)"

definition false_negative_B ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> bool" where
  "false_negative_B C E F e_star \<longleftrightarrow>
     (\<exists>e \<in> events_of E \<union> events_of F.
        bhb_eval C E e e_star \<and> \<not> bhb_eval C F e e_star)"

definition false_positive_B ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> bool" where
  "false_positive_B C E F e_star \<longleftrightarrow>
     (\<exists>e \<in> events_of E \<union> events_of F.
        \<not> bhb_eval C E e e_star \<and> bhb_eval C F e e_star)"

lemma valid_B_iff_no_FP_FN:
  shows "valid_B C E F e_star
           \<longleftrightarrow> \<not> false_negative_B C E F e_star
              \<and> \<not> false_positive_B C E F e_star"
proof -
  have "valid_B C E F e_star
          \<longleftrightarrow> (\<forall>e \<in> events_of E \<union> events_of F.
                 bhb_eval C E e e_star = bhb_eval C F e e_star)"
    by (simp add: valid_B_def)
  also have "\<dots> \<longleftrightarrow> \<not> false_negative_B C E F e_star
                  \<and> \<not> false_positive_B C E F e_star"
    by (auto simp: false_negative_B_def false_positive_B_def)
  finally show ?thesis .
qed

text \<open>\<open>CD_B\<close> solver signature and the \<open>produces_valid_F_B\<close> /
\<open>CD_B_solvable\<close> predicates, parallel to those of @{theory_text \<open>CD.thy\<close>}.\<close>

definition produces_valid_F_B ::
  "'p set \<Rightarrow> 'p cd_solver \<Rightarrow> bool" where
  "produces_valid_F_B C alg \<longleftrightarrow>
     (\<forall>adv. adversary_admissible C adv \<longrightarrow>
        (let (F', _) = alg (adv_i adv) (adv_e_star adv) in
           valid_B C (adv_E adv) F' (adv_e_star adv)))"

definition CD_B_solvable :: "comm_mode \<Rightarrow> 'p set \<Rightarrow> bool" where
  "CD_B_solvable m C \<longleftrightarrow> (\<exists>alg. produces_valid_F_B C alg)"

section \<open>Forward pointer: Theorems 6, 7, 8 are proven downstream\<close>

text \<open>Paper Section 4.3's Theorems 6 (unicast, solvable), 7
(broadcast, solvable), and 8 (multicast, unsolvable) are proven in
@{theory_text \<open>CD_B_Algorithm.thy\<close>} on top of this foundation.
They use a richer algorithm signature, @{text cd_alg_with_recv}, that
takes a per-peer reported history as input (where the bare
@{type cd_solver} type used in @{const produces_valid_F_B} above sees
only the query indices); the operational layer is in
@{theory_text \<open>Delivery.thy\<close>} (structural delivery property) and
@{theory_text \<open>Execution_Model.thy\<close>} (inductive \<open>run_step\<close>
with explicit in-flight buffer).

The bare @{const produces_valid_F_B} and @{const CD_B_solvable}
definitions above mirror paper Definition 6 against the original
@{type cd_solver} type and are retained as paper-faithful
definitional surface; the downstream development uses the
@{text cd_alg_with_recv} versions in @{theory_text \<open>CD_B_Algorithm.thy\<close>}
exclusively.\<close>

end
