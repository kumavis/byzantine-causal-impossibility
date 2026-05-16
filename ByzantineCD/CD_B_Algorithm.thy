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
  imports BHB Theorems_1_2
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

text \<open>The \<open>CD_B\<close> correctness predicate for algorithms of the richer
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

section \<open>The naive \<open>CD_B\<close> algorithm and its correctness\<close>

text \<open>The abstract correctness theorem: under correct reporting from
correct processes, the naive algorithm \<open>F = recv\<close> satisfies \<open>CD_B\<close> (in
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

section \<open>Theorems 6 and 7: \<open>CD_B\<close> solvable under unicast and broadcast\<close>

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

section \<open>Theorem 8: \<open>CD_B\<close> impossible under multicast\<close>

text \<open>Paper, Theorem 8 (Section 4.3, "impossible"):
\begin{quote}
``It is impossible to solve causality determination (Definition 6)
as specified by \<open>CD_B(E, F, e_i^*)\<close>, now defined in terms of the
\<open>\<rightarrow>_B\<close> relation, in an asynchronous multicast-based message passing
system with one or more Byzantine processes.''
\end{quote}

The paper's proof is operational: BRM (Byzantine Reliable Multicast)
is the primitive that would discharge @{const correct_reporting}
under multicast, but BRM is unachievable without first identifying
the Byzantine processes within each multicast group.  Hence under
multicast, @{const correct_reporting} cannot be assumed, and an
algorithm must be correct without it -- which we capture as the
``strong'' predicate below.

\textit{Our formalisation.}  We give T8 a concrete formal content by
showing that no algorithm satisfies @{term produces_valid_F_B_recv_strong}
-- the strengthened correctness predicate that drops the
@{const correct_reporting} hypothesis.  The proof reuses the
fresh-id adversary construction of @{theory_text \<open>Theorems_1_2.thy\<close>},
specialised so the witness chain runs through two distinct
\emph{correct} processes \<open>p_c\<close> and \<open>p_i\<close> (rather than a Byzantine
sender).  The chain becomes a genuine \<open>\<rightarrow>_B\<close> chain in \<open>E\<close>; if the
algorithm's output \<open>F\<close> has finite \<open>events_of\<close>, a fresh message id
exists outside \<open>F\<close>, and the bhb chain in \<open>E\<close> is missing in \<open>F\<close> --
a bhb-false-negative.

The operational "BRM is unachievable" argument is not formalised
(same out-of-scope band as T6/T7's BRU and BCB/BRB primitives); we
state it as the meta-level fact that translates ``under multicast''
into ``without @{const correct_reporting}'' into the strong
predicate.\<close>

definition produces_valid_F_B_recv_strong ::
  "'p set \<Rightarrow> 'p cd_alg_with_recv \<Rightarrow> bool" where
  "produces_valid_F_B_recv_strong C alg \<longleftrightarrow>
     (\<forall>adv recv.
        adversary_admissible C adv \<longrightarrow>
        wf_history recv \<longrightarrow>
          (let (F', _) = alg recv (adv_i adv) (adv_e_star adv) in
             valid_B C (adv_E adv) F' (adv_e_star adv)))"

subsection \<open>The bhb chain in \<open>fn_E\<close> when both endpoints are correct\<close>

text \<open>The fresh-id history @{term "fn_E p_i p_c m"} from
@{theory_text \<open>Theorems_1_2.thy\<close>}, when \<open>p_c\<close> and \<open>p_i\<close> are both
correct and distinct, exhibits a genuine \<open>\<rightarrow>_B\<close> chain from the
@{term "Send p_c 1 p_i m"} event to the @{term "Internal p_i 2"}
event.  Both endpoints and the intermediate @{term "Receive p_i 1 p_c m"}
are at correct processes, so every step is a @{const bhb_step}.\<close>

lemma bhb_send_to_estar_in_fn_E:
  assumes pi_cor: "p_i \<in> correct"
      and pc_cor: "p_c \<in> correct"
      and dist:   "p_c \<noteq> p_i"
  shows "bhb correct (fn_E p_i p_c m) (Send p_c 1 p_i m) (Internal p_i 2)"
proof -
  let ?H = "fn_E p_i p_c m"
  let ?s = "Send p_c 1 p_i m"
  let ?r = "Receive p_i 1 p_c m"
  let ?es = "Internal p_i 2"

  have step_sr_under: "program_order ?H ?s ?r \<or> message_order ?H ?s ?r"
    using message_order_fn_E_send_receive[OF dist] by blast
  have proc_s: "proc_of ?s = p_c" by simp
  have proc_r: "proc_of ?r = p_i" by simp
  have proc_es: "proc_of ?es = p_i" by simp

  have step_sr: "bhb_step correct ?H ?s ?r"
    using step_sr_under pc_cor pi_cor proc_s proc_r
    unfolding bhb_step_def by simp

  have step_re_under: "program_order ?H ?r ?es \<or> message_order ?H ?r ?es"
    using program_order_fn_E_at_pi[OF dist] by blast
  have step_re: "bhb_step correct ?H ?r ?es"
    using step_re_under pi_cor proc_r proc_es
    unfolding bhb_step_def by simp

  have base: "(bhb_step correct ?H)\<^sup>+\<^sup>+ ?s ?r"
    using step_sr by blast
  have extend: "(bhb_step correct ?H)\<^sup>+\<^sup>+ ?r ?es"
    using step_re by blast
  have "(bhb_step correct ?H)\<^sup>+\<^sup>+ ?s ?es"
    using base extend by (rule tranclp_trans)
  thus ?thesis unfolding bhb_def .
qed

lemma bhb_eval_send_to_estar_in_fn_E:
  assumes pi_cor: "p_i \<in> correct"
      and pc_cor: "p_c \<in> correct"
      and dist:   "p_c \<noteq> p_i"
  shows "bhb_eval correct (fn_E p_i p_c m)
           (Send p_c 1 p_i m) (Internal p_i 2)"
proof -
  have e1: "Send p_c 1 p_i m \<in> events_of (fn_E p_i p_c m)"
    using dist by (simp add: fn_E_events)
  have e2: "Internal p_i 2 \<in> events_of (fn_E p_i p_c m)"
    using dist by (simp add: fn_E_events)
  have h: "bhb correct (fn_E p_i p_c m)
             (Send p_c 1 p_i m) (Internal p_i 2)"
    by (rule bhb_send_to_estar_in_fn_E[OF pi_cor pc_cor dist])
  show ?thesis using e1 e2 h by (simp add: bhb_eval_def)
qed

subsection \<open>The impossibility\<close>

text \<open>Following the same shape as @{thm CD_FN_unavoidable}: any
purported strong-correct algorithm has finite output, fresh ids
exist, the adversary places a bhb chain through two correct
processes using a fresh id, the algorithm's @{term F} misses the
chain start, and a bhb-false-negative results.\<close>

theorem produces_valid_F_B_recv_strong_unsolvable:
  assumes cor_two:
        "\<exists>p_i p_c. p_i \<in> correct \<and> p_c \<in> correct \<and> p_c \<noteq> p_i"
      and fin_F:
        "\<forall>alg. produces_valid_F_B_recv_strong correct alg \<longrightarrow>
           (\<forall>recv p_i_in.
              finite (events_of
                        (fst (alg recv p_i_in (Internal p_i_in 2)))))"
  shows "\<not> (\<exists>alg. produces_valid_F_B_recv_strong correct alg)"
proof
  assume "\<exists>alg. produces_valid_F_B_recv_strong correct alg"
  then obtain alg where solver:
    "produces_valid_F_B_recv_strong correct alg" by blast

  obtain p_i p_c where
      pi_cor: "p_i \<in> correct"
      and pc_cor: "p_c \<in> correct"
      and dist:   "p_c \<noteq> p_i"
    using cor_two by blast

  define recv :: "'p \<Rightarrow> 'p history_local" where
    "recv \<equiv> (\<lambda>_. [])"

  have wfR: "wf_history recv"
    unfolding recv_def wf_history_def wf_history_local_def by simp

  let ?e_star = "Internal p_i 2"
  let ?F = "fst (alg recv p_i ?e_star)"
  let ?m = "fresh_nat ?F"
  let ?adv = "fn_adv p_i p_c ?m"
  let ?s = "Send p_c 1 p_i ?m"

  have finF: "finite (events_of ?F)"
    using fin_F solver by blast

  have adm: "adversary_admissible correct ?adv"
    using pi_cor dist by (rule adv_admissible_fn_adv)

  have adv_eq:
    "adv_E ?adv = fn_E p_i p_c ?m \<and>
     adv_i ?adv = p_i \<and>
     adv_e_star ?adv = ?e_star"
    by (simp add: fn_adv_def)

  have witness_in_E: "?s \<in> events_of (adv_E ?adv)"
    using dist adv_eq by (simp add: fn_E_events)
  have bhb_E_chain:
    "bhb_eval correct (adv_E ?adv) ?s (adv_e_star ?adv)"
    using bhb_eval_send_to_estar_in_fn_E[OF pi_cor pc_cor dist]
          adv_eq by simp
  have witness_not_in_F: "?s \<notin> events_of ?F"
    using finF Send_at_fresh_nat_not_in_F[of ?F] by blast
  have not_bhb_F:
    "\<not> bhb_eval correct ?F ?s (adv_e_star ?adv)"
    using witness_not_in_F by (simp add: bhb_eval_def)

  \<comment> \<open>The adversary establishes a bhb-FN: chain in E, not in F.\<close>
  have FN_witness:
    "?s \<in> events_of (adv_E ?adv) \<union> events_of ?F \<and>
     bhb_eval correct (adv_E ?adv) ?s (adv_e_star ?adv) \<and>
     \<not> bhb_eval correct ?F ?s (adv_e_star ?adv)"
    using witness_in_E bhb_E_chain not_bhb_F by blast

  hence FN: "false_negative_B correct (adv_E ?adv) ?F (adv_e_star ?adv)"
    unfolding false_negative_B_def by blast

  \<comment> \<open>But the alleged solver claims \<open>valid_B\<close> on this very adversary.\<close>
  have F_eq:
    "?F = fst (alg recv (adv_i ?adv) (adv_e_star ?adv))"
    using adv_eq by simp
  have "valid_B correct (adv_E ?adv) ?F (adv_e_star ?adv)"
  proof -
    from solver adm wfR have
      "let (F', _) = alg recv (adv_i ?adv) (adv_e_star ?adv) in
         valid_B correct (adv_E ?adv) F' (adv_e_star ?adv)"
      by (simp add: produces_valid_F_B_recv_strong_def)
    thus ?thesis using F_eq by (simp add: Let_def split: prod.split_asm)
  qed
  hence "\<not> false_negative_B correct (adv_E ?adv) ?F (adv_e_star ?adv)"
    using valid_B_iff_no_FP_FN by blast
  with FN show False by contradiction
qed

text \<open>Mapping to paper Theorem 8.  The paper says: under multicast,
@{const correct_reporting} cannot be guaranteed (BRM is
unachievable), so an algorithm would have to work without it -- but
the previous theorem says no algorithm does.  Hence \<open>CD_B\<close> is
unsolvable under multicast.

The operational ``BRM is unachievable'' claim itself is out of
scope (it requires modelling multicast groups, the BRM primitive,
and the unachievability of BRM without Byzantine identification).
We state the impossibility conditionally on the operational claim:
``if BRM-style \<open>correct_reporting\<close> is not guaranteed under
multicast, then \<open>CD_B\<close> is unsolvable under multicast in the
\<open>recv\<close>-augmented signature''.

In our predicate vocabulary:
\begin{itemize}
  \item ``\<open>correct_reporting\<close> guaranteed'' corresponds to using
        the \emph{conditional} predicate @{const produces_valid_F_B_recv}
        -- which is satisfiable (T6/T7).
  \item ``\<open>correct_reporting\<close> not guaranteed'' corresponds to
        using the \emph{strong} predicate
        @{const produces_valid_F_B_recv_strong} -- which is
        \emph{not} satisfiable
        (@{thm produces_valid_F_B_recv_strong_unsolvable}).
\end{itemize}\<close>

theorem CD_B_unsolvable_multicast_abstract:
  assumes cor_two:
        "\<exists>p_i p_c. p_i \<in> correct \<and> p_c \<in> correct \<and> p_c \<noteq> p_i"
      and fin_F:
        "\<forall>alg. produces_valid_F_B_recv_strong correct alg \<longrightarrow>
           (\<forall>recv p_i_in.
              finite (events_of
                        (fst (alg recv p_i_in (Internal p_i_in 2)))))"
  shows "\<not> (\<exists>alg. produces_valid_F_B_recv_strong correct alg)"
  by (rule produces_valid_F_B_recv_strong_unsolvable[OF cor_two fin_F])

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
