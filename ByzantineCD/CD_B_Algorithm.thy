(*
  Title:   CD_B_Algorithm.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  An abstract communication-model layer for paper Section 4.3.

  The algorithm signature 'p cd_solver in CD.thy is too weak to talk
  about Theorems 6 and 7: it has no input channel by which an
  algorithm could receive messages from other processes.  This theory
  adds a richer signature in which the algorithm at p_i takes a
  per-peer reported history as input -- the abstract content of
  "p_i has received q's broadcast/unicast view".

  Under the operational assumption that correct processes report
  truthfully (i.e., recv p = E p for every correct p), the naive
  CD_B-algorithm "F = recv, decision = True" already solves CD_B for
  any query e_star at a correct process.  This is the abstract core
  of Theorems 6 and 7: the bhb relation is restricted to chains
  through correct processes, so making F agree with E at correct
  processes suffices.

  T6 and T7 are then each just an instance of the abstract result --
  modulo the operational fact that their respective communication
  modes (unicast with simulated broadcasts via BRU, broadcast via
  BCB-over-BRB) actually achieve correct_reporting.  That operational
  fact is not formalised here.

  The type synonym 'p cd_alg_with_recv is declared at the theory
  level (outside the byzantineSystem locale context) so that the
  locale's locally-fixed type variable does not interfere; the rest
  of the development lives inside the locale.
*)

theory CD_B_Algorithm
  imports BHB
begin

section \<open>Algorithm signature with a received-view input\<close>

text \<open>An algorithm of this richer type takes, in addition to its
local query \<open>(i, e_star)\<close>, a per-peer reported history @{term recv}
-- "what \<open>p_i\<close> has been told about each other process's execution".
For correct peers, the paper assumes \<open>recv p = E p\<close> via the
communication primitive (BRU for unicast in T6, BCB/BRB for
broadcast in T7); for Byzantine peers, \<open>recv p\<close> can be anything the
Byzantine sent.\<close>

type_synonym 'p cd_alg_with_recv =
  "('p \<Rightarrow> 'p history_local) \<Rightarrow> 'p \<Rightarrow> 'p event \<Rightarrow> 'p history \<times> bool"

context byzantineSystem
begin

text \<open>The operational fidelity property the paper relies on: correct
processes report their actual local history truthfully.\<close>

definition correct_reporting ::
  "'p set \<Rightarrow> ('p \<Rightarrow> 'p history_local) \<Rightarrow> 'p history \<Rightarrow> bool" where
  "correct_reporting C recv E \<longleftrightarrow> (\<forall>p \<in> C. recv p = E p)"

text \<open>The CD_B correctness predicate for algorithms of the richer
type: the algorithm must produce a valid F (in the bhb sense) for
every admissible adversary AND every received-view that respects
correct reporting from correct processes.\<close>

definition produces_valid_F_B_recv ::
  "'p set \<Rightarrow> 'p cd_alg_with_recv \<Rightarrow> bool" where
  "produces_valid_F_B_recv C alg \<longleftrightarrow>
     (\<forall>adv recv.
        adversary_admissible C adv \<longrightarrow>
        wf_history recv \<longrightarrow>
        correct_reporting C recv (adv_E adv) \<longrightarrow>
          (let (F', _) = alg recv (adv_i adv) (adv_e_star adv) in
             valid_B C (adv_E adv) F' (adv_e_star adv)))"

text \<open>The naive algorithm: at \<open>p_i\<close>, just output the received view
as \<open>F\<close>.  Decision is always \<open>True\<close>.\<close>

definition naive_cd_B_alg :: "'p cd_alg_with_recv" where
  "naive_cd_B_alg recv _ _ = (recv, True)"

section \<open>Structural lemmas: under correct\<open>_reporting\<close>, bhb is invariant\<close>

text \<open>The key technical observation: bhb's definition consults events
only at correct processes (\<open>bhb_step\<close> requires both endpoints to be
in @{term C}), and the underlying program-order / message-order
relations consult @{term "H p"} only for the process @{term p} that
owns the event.  Under @{const correct_reporting}, those owners are
correct and \<open>recv p = E p\<close>, so the entire bhb relation is invariant
across the two histories.

\textit{Engineering note:} the \<open>by blast\<close> tactic does not apply
equality rewrites; in proofs below, where an equality \<open>F p = E p\<close>
needs to be substituted into a goal, we use \<open>by (simp add: \<dots>)\<close>
instead.  An earlier version of this theory used \<open>blast\<close> for those
substitutions and timed out (>10 min wall time).\<close>

subsection \<open>events\<open>_of\<close> at correct processes\<close>

text \<open>Helper: in a well-formed history, an event's owner is the
process whose list it appears in.\<close>

lemma proc_of_in_wf_history:
  assumes "wf_history H" and "e \<in> set (H p)"
  shows "proc_of e = p"
proof -
  from assms(1) have "wf_history_local p (H p)"
    unfolding wf_history_def by blast
  with assms(2) show ?thesis
    unfolding wf_history_local_def by blast
qed

lemma events_at_correct_eq:
  assumes wfE: "wf_history E"
      and wfF: "wf_history F"
      and rep: "correct_reporting C F E"
      and pC:  "proc_of e \<in> C"
  shows "e \<in> events_of E \<longleftrightarrow> e \<in> events_of F"
proof
  assume "e \<in> events_of E"
  then obtain p where p_E: "e \<in> set (E p)"
    by (auto simp: events_of_def)
  from wfE p_E have "proc_of e = p"
    by (rule proc_of_in_wf_history)
  with pC have pC': "p \<in> C" by simp
  from rep pC' have "F p = E p"
    unfolding correct_reporting_def by blast
  with p_E have "e \<in> set (F p)" by simp
  thus "e \<in> events_of F" by (auto simp: events_of_def)
next
  assume "e \<in> events_of F"
  then obtain p where p_F: "e \<in> set (F p)"
    by (auto simp: events_of_def)
  from wfF p_F have "proc_of e = p"
    by (rule proc_of_in_wf_history)
  with pC have pC': "p \<in> C" by simp
  from rep pC' have "F p = E p"
    unfolding correct_reporting_def by blast
  with p_F have "e \<in> set (E p)" by simp
  thus "e \<in> events_of E" by (auto simp: events_of_def)
qed

lemma program_order_at_correct:
  assumes wfE: "wf_history E"
      and wfF: "wf_history F"
      and rep: "correct_reporting C F E"
      and pC:  "proc_of e \<in> C"
  shows "program_order E e e' = program_order F e e'"
proof
  assume "program_order E e e'"
  then obtain p i j where
    ij: "i < j" "j < length (E p)"
    and ei: "(E p) ! i = e"
    and ej: "(E p) ! j = e'"
    unfolding program_order_def by blast
  have proc_e: "proc_of e = p"
  proof -
    from ij have "i < length (E p)" by simp
    hence "(E p) ! i \<in> set (E p)" by (rule nth_mem)
    with ei have "e \<in> set (E p)" by simp
    with wfE show ?thesis by (rule proc_of_in_wf_history)
  qed
  with pC have pC': "p \<in> C" by simp
  from rep pC' have eq: "F p = E p"
    unfolding correct_reporting_def by blast
  have "i < j \<and> j < length (F p) \<and> F p ! i = e \<and> F p ! j = e'"
    using ij ei ej by (simp add: eq)
  thus "program_order F e e'"
    unfolding program_order_def by blast
next
  assume "program_order F e e'"
  then obtain p i j where
    ij: "i < j" "j < length (F p)"
    and ei: "(F p) ! i = e"
    and ej: "(F p) ! j = e'"
    unfolding program_order_def by blast
  have proc_e: "proc_of e = p"
  proof -
    from ij have "i < length (F p)" by simp
    hence "(F p) ! i \<in> set (F p)" by (rule nth_mem)
    with ei have "e \<in> set (F p)" by simp
    with wfF show ?thesis by (rule proc_of_in_wf_history)
  qed
  with pC have pC': "p \<in> C" by simp
  from rep pC' have eq: "F p = E p"
    unfolding correct_reporting_def by blast
  have "i < j \<and> j < length (E p) \<and> E p ! i = e \<and> E p ! j = e'"
    using ij ei ej by (simp add: eq[symmetric])
  thus "program_order E e e'"
    unfolding program_order_def by blast
qed

lemma message_order_at_correct:
  assumes wfE: "wf_history E"
      and wfF: "wf_history F"
      and rep: "correct_reporting C F E"
      and pC:  "proc_of e \<in> C"
      and pC': "proc_of e' \<in> C"
  shows "message_order E e e' = message_order F e e'"
proof -
  have eqE: "e \<in> events_of E \<longleftrightarrow> e \<in> events_of F"
    by (rule events_at_correct_eq[OF wfE wfF rep pC])
  have eqE': "e' \<in> events_of E \<longleftrightarrow> e' \<in> events_of F"
    by (rule events_at_correct_eq[OF wfE wfF rep pC'])
  show ?thesis
    unfolding message_order_def by (simp add: eqE eqE')
qed

subsection \<open>One bhb step is invariant under correct\<open>_reporting\<close>\<close>

lemma bhb_step_eq:
  assumes wfE: "wf_history E"
      and wfF: "wf_history F"
      and rep: "correct_reporting C F E"
  shows "bhb_step C E e e' = bhb_step C F e e'"
proof
  assume H: "bhb_step C E e e'"
  hence pC: "proc_of e \<in> C" and pC': "proc_of e' \<in> C"
    unfolding bhb_step_def by blast+
  from H have step_in_E:
    "program_order E e e' \<or> message_order E e e'"
    unfolding bhb_step_def by blast
  have po_eq: "program_order E e e' = program_order F e e'"
    by (rule program_order_at_correct[OF wfE wfF rep pC])
  have mo_eq: "message_order E e e' = message_order F e e'"
    by (rule message_order_at_correct[OF wfE wfF rep pC pC'])
  from step_in_E po_eq mo_eq
  have step_in_F: "program_order F e e' \<or> message_order F e e'" by simp
  show "bhb_step C F e e'"
    unfolding bhb_step_def using pC pC' step_in_F by blast
next
  assume H: "bhb_step C F e e'"
  hence pC: "proc_of e \<in> C" and pC': "proc_of e' \<in> C"
    unfolding bhb_step_def by blast+
  from H have step_in_F:
    "program_order F e e' \<or> message_order F e e'"
    unfolding bhb_step_def by blast
  have po_eq: "program_order E e e' = program_order F e e'"
    by (rule program_order_at_correct[OF wfE wfF rep pC])
  have mo_eq: "message_order E e e' = message_order F e e'"
    by (rule message_order_at_correct[OF wfE wfF rep pC pC'])
  from step_in_F po_eq mo_eq
  have step_in_E: "program_order E e e' \<or> message_order E e e'" by simp
  show "bhb_step C E e e'"
    unfolding bhb_step_def using pC pC' step_in_E by blast
qed

subsection \<open>bhb itself is invariant under correct\<open>_reporting\<close>\<close>

lemma bhb_eq_under_correct_reporting:
  assumes wfE: "wf_history E"
      and wfF: "wf_history F"
      and rep: "correct_reporting C F E"
  shows "bhb C E e e' = bhb C F e e'"
proof
  assume "bhb C E e e'"
  hence "(bhb_step C E)\<^sup>+\<^sup>+ e e'" unfolding bhb_def .
  hence "(bhb_step C F)\<^sup>+\<^sup>+ e e'"
  proof (induction rule: tranclp_induct)
    case (base y)
    have "bhb_step C F e y"
      using base bhb_step_eq[OF wfE wfF rep] by simp
    thus ?case by (rule tranclp.r_into_trancl)
  next
    case (step y z)
    have step_F: "bhb_step C F y z"
      using step.hyps(2) bhb_step_eq[OF wfE wfF rep] by simp
    from step.IH step_F show ?case by (rule tranclp.trancl_into_trancl)
  qed
  thus "bhb C F e e'" unfolding bhb_def .
next
  assume "bhb C F e e'"
  hence "(bhb_step C F)\<^sup>+\<^sup>+ e e'" unfolding bhb_def .
  hence "(bhb_step C E)\<^sup>+\<^sup>+ e e'"
  proof (induction rule: tranclp_induct)
    case (base y)
    have "bhb_step C E e y"
      using base bhb_step_eq[OF wfE wfF rep] by simp
    thus ?case by (rule tranclp.r_into_trancl)
  next
    case (step y z)
    have step_E: "bhb_step C E y z"
      using step.hyps(2) bhb_step_eq[OF wfE wfF rep] by simp
    from step.IH step_E show ?case by (rule tranclp.trancl_into_trancl)
  qed
  thus "bhb C E e e'" unfolding bhb_def .
qed

subsection \<open>bhb\<open>_eval\<close> agrees on relevant events\<close>

text \<open>Both bhb endpoints must be at correct processes for the
relation to hold (by @{thm bhb_proc_of_endpoints}), so it suffices to
check @{term events_of} at correct processes; under correct reporting
those agree.\<close>

lemma bhb_eval_eq_under_correct_reporting:
  assumes wfE: "wf_history E"
      and wfF: "wf_history F"
      and rep: "correct_reporting C F E"
      and pC_star: "proc_of e_star \<in> C"
  shows "bhb_eval C E e e_star = bhb_eval C F e e_star"
proof (cases "proc_of e \<in> C")
  case True
  have e_eq: "e \<in> events_of E \<longleftrightarrow> e \<in> events_of F"
    by (rule events_at_correct_eq[OF wfE wfF rep True])
  have es_eq: "e_star \<in> events_of E \<longleftrightarrow> e_star \<in> events_of F"
    by (rule events_at_correct_eq[OF wfE wfF rep pC_star])
  have bhb_eq: "bhb C E e e_star = bhb C F e e_star"
    by (rule bhb_eq_under_correct_reporting[OF wfE wfF rep])
  show ?thesis
    unfolding bhb_eval_def by (simp add: e_eq es_eq bhb_eq)
next
  case False
  hence noE: "\<not> bhb C E e e_star"
    using bhb_proc_of_endpoints by blast
  from False have noF: "\<not> bhb C F e e_star"
    using bhb_proc_of_endpoints by blast
  show ?thesis
    unfolding bhb_eval_def using noE noF by blast
qed

section \<open>The naive CD_B algorithm and its correctness\<close>

text \<open>The abstract correctness theorem: under correct reporting from
correct processes, the naive algorithm \<open>F = recv\<close> satisfies CD_B (in
the bhb sense).  This is the algorithmic core of paper Theorems 6
and 7.\<close>

theorem naive_cd_B_alg_correct:
  shows "produces_valid_F_B_recv correct naive_cd_B_alg"
proof (unfold produces_valid_F_B_recv_def, intro allI impI)
  fix adv recv
  assume adm: "adversary_admissible correct adv"
     and wfR: "wf_history recv"
     and rep: "correct_reporting correct recv (adv_E adv)"

  have wfE: "wf_history (adv_E adv)"
    using adm by (auto simp: adversary_admissible_def)

  have pC_star: "proc_of (adv_e_star adv) \<in> correct"
  proof -
    have "proc_of (adv_e_star adv) = adv_i adv"
      using adm by (auto simp: adversary_admissible_def)
    moreover have "adv_i adv \<in> correct"
      using adm by (auto simp: adversary_admissible_def)
    ultimately show ?thesis by simp
  qed

  have "valid_B correct (adv_E adv) recv (adv_e_star adv)"
  proof (unfold valid_B_def, intro ballI)
    fix e
    assume e_in: "e \<in> events_of (adv_E adv) \<union> events_of recv"
    show "bhb_eval correct (adv_E adv) e (adv_e_star adv)
            = bhb_eval correct recv e (adv_e_star adv)"
      by (rule bhb_eval_eq_under_correct_reporting[OF wfE wfR rep pC_star])
  qed
  thus "let (F', _) = naive_cd_B_alg recv (adv_i adv) (adv_e_star adv) in
          valid_B correct (adv_E adv) F' (adv_e_star adv)"
    by (simp add: naive_cd_B_alg_def Let_def)
qed

corollary CD_B_solvable_under_correct_reporting:
  shows "\<exists>alg. produces_valid_F_B_recv correct alg"
  using naive_cd_B_alg_correct by blast

section \<open>Theorems 6 and 7: CD_B solvable under unicast and broadcast\<close>

text \<open>Paper, Theorem 6 (Section 4.3.2, "possible"):
\begin{quote}
``It is possible to solve causality determination (Definition 6) as
specified by \<open>CD_B(E, F, e_i^*)\<close>, now defined in terms of the
\<open>\<rightarrow>_B\<close> relation, in an asynchronous unicast-based message passing
system with one or more Byzantine processes.''
\end{quote}

Paper, Theorem 7 (Section 4.3.1, "possible"):
\begin{quote}
``It is possible to solve causality determination (Definition 6) as
specified by \<open>CD_B(E, F, e_i^*)\<close>, now defined in terms of the
\<open>\<rightarrow>_B\<close> relation, in an asynchronous broadcast-based message passing
system with one or more Byzantine processes.''
\end{quote}

At the abstraction level of this theory, Theorems 6 and 7 are the
same statement: ``in mode \<open>m\<close>, some algorithm of type
@{type cd_alg_with_recv} satisfies @{const produces_valid_F_B_recv}''.
Both are direct corollaries of @{thm naive_cd_B_alg_correct} since
the abstract correctness of the naive algorithm does not depend on
the mode.

\textit{Where the paper's two theorems differ.}  The paper's
distinction between T6 and T7 lies in which communication primitive
discharges @{const correct_reporting}:

\begin{itemize}
  \item T6 (unicast): correct processes report their local
        histories via point-to-point messages
        (Byzantine Reliable Unicast, trivially achievable since
        point-to-point is already reliable in the absence of
        Byzantine senders along the path), supplemented by
        simulated broadcasts of control information after
        application unicast send events.
  \item T7 (broadcast): correct processes report via Byzantine
        Causal Broadcast over Byzantine Reliable Broadcast
        (BCB-over-BRB), which guarantees that any message a correct
        process delivers was previously delivered by all other
        correct processes in the causal order required to
        reconstruct the history.
\end{itemize}

Both primitives are operational and require a communication-level
model -- explicit messages, channels, fairness -- not present in
this development.  We therefore state Theorems 6 and 7 as
mode-tagged existential statements about
@{const produces_valid_F_B_recv}, leaving the operational discharge
of @{const correct_reporting} to whoever extends the development
with a communication model.\<close>

definition CD_B_solvable_with_recv ::
  "comm_mode \<Rightarrow> 'p set \<Rightarrow> bool" where
  "CD_B_solvable_with_recv m C \<longleftrightarrow>
     (\<exists>alg. produces_valid_F_B_recv C alg)"

theorem CD_B_solvable_unicast:
  shows "CD_B_solvable_with_recv Unicast correct"
  unfolding CD_B_solvable_with_recv_def
  by (rule CD_B_solvable_under_correct_reporting)

theorem CD_B_solvable_broadcast:
  shows "CD_B_solvable_with_recv Broadcast correct"
  unfolding CD_B_solvable_with_recv_def
  by (rule CD_B_solvable_under_correct_reporting)

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
