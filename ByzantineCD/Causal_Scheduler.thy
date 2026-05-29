(*
  Title:   Causal_Scheduler.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  An independently-proven, paper-faithful BCB causal-order theorem
  at the scheduler level (paper Section 4.3, Definition 3).

  --------------------------------------------------------------------
  Scope and honest framing.  @{theory_text \<open>Primitives.thy\<close>}'s
  @{thm fair_drained_run_solves_CD_B_broadcast} takes
  @{const bcb_causal_order} as a hypothesis, but the chain wired
  through @{thm bcb_over_brb_realises_mode_admissible_broadcast}
  discards the causal-order half and consumes only
  @{const bru_satisfied}.  At the abstraction the development
  chooses for the recv view (@{const recv_from_history} ignores
  per-process receive order), causal-order delivery cannot have
  material content on the chain.

  So this theory is \<^emph>\<open>not\<close> closing a load-bearing operational
  hypothesis: both
  @{thm fair_drained_run_solves_CD_B_broadcast} (Primitives.thy)
  and our @{const fair_drained_causal_run_solves_CD_B_broadcast}
  bottom out at @{const T7_broadcast_via_bcb_over_brb}, which only
  asks for @{const mode_admissible} \<open>Broadcast\<close>.  What this theory
  contributes instead:

  (1) An independent, paper-faithful statement of BCB causal-order
      delivery at the Byzantine-happened-before layer
      (paper Definition 3), realised by a strict scheduler-level
      refinement of @{const run_step}.

  (2) A demonstration that the refinement is consistent: it embeds
      into @{const run_step} (so inherits all run invariants), and
      at every reachable configuration the BHB causal-order
      property holds.

  In a future development where the recv view is built from per-q
  receive sequences (so the order of receives at @{term q} becomes
  load-bearing), this theory would provide the operational
  discharge.

  --------------------------------------------------------------------
  Refinement.  @{const causal_run_step} adds two side conditions to
  @{const run_step}:

    (a) freshness at @{const run_step.step_send}: a correct sender's
        triple @{term \<open>(p, q, m)\<close>} is fresh, i.e., no Send event with
        the same triple has been recorded and no in-flight entry
        with this triple exists.  This matches the paper's implicit
        assumption that messages carry unique ids.
    (b) causal precondition at @{const run_step.step_recv}: a
        correct receiver @{term q} delivers @{term \<open>(p, q, m)\<close>}
        only after every Byzantine-happened-before predecessor
        send-to-@{term q} (in the current history) has already been
        delivered at @{term q}.

  --------------------------------------------------------------------
  What we prove

  -- @{const causal_run_step} is a sub-relation of @{const run_step};
     hence every @{const causal_run} inherits the @{const run}
     invariants (@{const wf_history}, @{const sends_match_inv},
     @{const buffer_correct_inv}, @{thm fairness_implies_delivery},
     and so on).
  -- Uniqueness of correct-to-correct sends and receives along any
     @{const causal_run}.
  -- The Byzantine-happened-before BCB causal-order property
     (@{term bhb_causal_order}, paper Definition 3 + Section 4.3)
     holds at every reachable @{const causal_run} configuration.
     This is the BHB version of @{const bcb_causal_order} from
     Primitives.thy (which uses plain @{const hb}); it is what the
     paper's text actually calls for, since Byzantine processes can
     fabricate hb chains through themselves that no correct-process
     scheduler can constrain.
  -- A drained @{const causal_run} satisfies
     @{const bhb_over_brb_satisfied} (BRU + BHB causal-order).
  -- End-to-end composition into operational T7 over the
     @{const causal_run} model
     (@{const fair_drained_causal_run_solves_CD_B_broadcast}),
     parallel to the plain-@{const run} chain in Primitives.thy.
     The same caveat applies: the broadcast chain's recv view
     ignores per-q receive order, so this composition does not
     materially use the BHB causal-order theorem.

  --------------------------------------------------------------------
  Why @{const bhb} rather than @{const hb}.  Byzantine processes can
  fabricate arbitrary local events (including @{const Receive}-shaped
  ones at themselves) via @{const run_step.step_byzantine}, which can
  introduce hb-chains through Byzantine intermediaries that no
  correct-process scheduler can constrain.  Paper Definition 3
  restricts hb to chains through correct processes precisely to
  sidestep this, and Section 4.3's BCB is stated in terms of the
  Byzantine happened-before relation.  Our statement of BCB
  causal-order is therefore in terms of @{const bhb}, and matches
  the paper.
*)

theory Causal_Scheduler
  imports Primitives
begin

context byzantineSystem
begin

section \<open>Definitions: freshness, causal precondition, refined relation\<close>

text \<open>A correct-to-correct triple @{term \<open>(p, q, m)\<close>} is \<^emph>\<open>fresh\<close> at
configuration @{term cfg} if no Send event with the same triple has
been recorded and no in-flight buffer entry for the triple exists.\<close>

definition send_fresh :: "'p config \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> bool" where
  "send_fresh cfg p q m \<longleftrightarrow>
     (\<forall>n. Send p n q m \<notin> events_of (cfg_hist cfg)) \<and>
     \<not> (p, q, m) \<in># cfg_inflight cfg"

text \<open>The \<^emph>\<open>causal precondition\<close> at a receive step says: there exists
a matching Send event for @{term \<open>(p, q, m)\<close>} in
@{term \<open>cfg_hist cfg\<close>}, and for that Send event every
Byzantine-happened-before predecessor send-to-@{term q} has already
been received at @{term q}.\<close>

definition causal_recv_ok ::
  "'p config \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> bool" where
  "causal_recv_ok cfg q p m \<longleftrightarrow>
     (\<exists>ns. Send p ns q m \<in> events_of (cfg_hist cfg) \<and>
           (\<forall>p' ns' m'. p' \<in> correct \<longrightarrow>
              Send p' ns' q m' \<in> events_of (cfg_hist cfg) \<longrightarrow>
              bhb correct (cfg_hist cfg)
                  (Send p' ns' q m') (Send p ns q m) \<longrightarrow>
              (\<exists>nr. Receive q nr p' m' \<in> events_of (cfg_hist cfg))))"

text \<open>The refined single-step relation.\<close>

inductive causal_run_step :: "'p config \<Rightarrow> 'p config \<Rightarrow> bool" where
  causal_step_internal:
    "p \<in> correct
       \<Longrightarrow> n = Suc (length (cfg_hist cfg p))
       \<Longrightarrow> cfg' = cfg
              \<lparr> cfg_hist := (cfg_hist cfg)
                              (p := cfg_hist cfg p @ [Internal p n]) \<rparr>
       \<Longrightarrow> causal_run_step cfg cfg'"
| causal_step_send:
    "p \<in> correct
       \<Longrightarrow> q \<in> correct
       \<Longrightarrow> n = Suc (length (cfg_hist cfg p))
       \<Longrightarrow> send_fresh cfg p q m
       \<Longrightarrow> cfg' = cfg
              \<lparr> cfg_hist := (cfg_hist cfg)
                              (p := cfg_hist cfg p @ [Send p n q m]),
                cfg_inflight := cfg_inflight cfg \<union># {# (p, q, m) } \<rparr>
       \<Longrightarrow> causal_run_step cfg cfg'"
| causal_step_recv:
    "q \<in> correct
       \<Longrightarrow> p \<in> correct
       \<Longrightarrow> (p, q, m) \<in># cfg_inflight cfg
       \<Longrightarrow> causal_recv_ok cfg q p m
       \<Longrightarrow> n = Suc (length (cfg_hist cfg q))
       \<Longrightarrow> cfg' = cfg
              \<lparr> cfg_hist := (cfg_hist cfg)
                              (q := cfg_hist cfg q @ [Receive q n p m]),
                cfg_inflight := cfg_inflight cfg -# (p, q, m) \<rparr>
       \<Longrightarrow> causal_run_step cfg cfg'"
| causal_step_byzantine:
    "p \<in> byzantine
       \<Longrightarrow> proc_of new_event = p
       \<Longrightarrow> seq_of new_event = Suc (length (cfg_hist cfg p))
       \<Longrightarrow> cfg' = cfg
              \<lparr> cfg_hist := (cfg_hist cfg)
                              (p := cfg_hist cfg p @ [new_event]) \<rparr>
       \<Longrightarrow> causal_run_step cfg cfg'"

definition causal_run :: "'p config \<Rightarrow> bool" where
  "causal_run cfg \<longleftrightarrow> causal_run_step\<^sup>*\<^sup>* init_config cfg"

lemma causal_run_init [simp]: "causal_run init_config"
  by (simp add: causal_run_def)

lemma causal_run_extend:
  "causal_run cfg \<Longrightarrow> causal_run_step cfg cfg' \<Longrightarrow> causal_run cfg'"
  unfolding causal_run_def by simp

section \<open>causal\<open>_run_step\<close> is a sub-relation of @{const run_step}\<close>

text \<open>Every @{const causal_run_step} can be matched by a
@{const run_step}: the rules drop the extra side conditions and
otherwise coincide.  All existing @{const run}-level invariants
(@{const wf_history}, @{const sends_match_inv}, deadlock freedom,
@{thm fairness_implies_delivery}, etc.) therefore apply to
@{const causal_run}.\<close>

lemma causal_run_step_imp_run_step:
  assumes "causal_run_step cfg cfg'"
  shows "run_step cfg cfg'"
  using assms
proof induction
  case (causal_step_internal p n cfg cfg')
  show ?case by (rule run_step.step_internal[OF causal_step_internal.hyps(1-3)])
next
  case (causal_step_send p q n cfg m cfg')
  show ?case by (rule run_step.step_send[OF causal_step_send.hyps(1-3,5)])
next
  case (causal_step_recv q p m cfg n cfg')
  show ?case
    by (rule run_step.step_recv[OF causal_step_recv.hyps(1-3,5-6)])
next
  case (causal_step_byzantine p new_event cfg cfg')
  show ?case
    by (rule run_step.step_byzantine[OF causal_step_byzantine.hyps(1-4)])
qed

lemma causal_run_imp_run:
  assumes "causal_run cfg"
  shows "run cfg"
  using assms unfolding causal_run_def run_def
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have "run_step y z" by (rule causal_run_step_imp_run_step[OF step.hyps(2)])
  with step.IH show ?case by simp
qed

section \<open>Structural invariants: sends, receives, and the buffer\<close>

text \<open>Five invariants jointly pin down uniqueness of
correct-to-correct sends/receives and the relationship between
sends, receives, and the buffer along @{const causal_run}.\<close>

definition send_unique_inv :: "'p config \<Rightarrow> bool" where
  "send_unique_inv cfg \<longleftrightarrow>
     (\<forall>p q m n1 n2.
        p \<in> correct \<longrightarrow> q \<in> correct \<longrightarrow>
        Send p n1 q m \<in> events_of (cfg_hist cfg) \<longrightarrow>
        Send p n2 q m \<in> events_of (cfg_hist cfg) \<longrightarrow>
        n1 = n2)"

definition recv_unique_inv :: "'p config \<Rightarrow> bool" where
  "recv_unique_inv cfg \<longleftrightarrow>
     (\<forall>p q m n1 n2.
        p \<in> correct \<longrightarrow> q \<in> correct \<longrightarrow>
        Receive q n1 p m \<in> events_of (cfg_hist cfg) \<longrightarrow>
        Receive q n2 p m \<in> events_of (cfg_hist cfg) \<longrightarrow>
        n1 = n2)"

definition buffer_count_inv :: "'p config \<Rightarrow> bool" where
  "buffer_count_inv cfg \<longleftrightarrow>
     (\<forall>p q m. p \<in> correct \<longrightarrow> q \<in> correct \<longrightarrow>
              cfg_inflight cfg (p, q, m) \<le> 1)"

text \<open>Once delivered, the buffer is drained -- and freshness
prevents reintroduction.\<close>

definition delivered_drained_inv :: "'p config \<Rightarrow> bool" where
  "delivered_drained_inv cfg \<longleftrightarrow>
     (\<forall>p q m. p \<in> correct \<longrightarrow> q \<in> correct \<longrightarrow>
              (\<exists>n. Receive q n p m \<in> events_of (cfg_hist cfg)) \<longrightarrow>
              \<not> (p, q, m) \<in># cfg_inflight cfg)"

text \<open>Every correct receive at @{term q} from correct @{term p} has
a matching correct-to-correct Send in the history.\<close>

definition recv_implies_send_inv :: "'p config \<Rightarrow> bool" where
  "recv_implies_send_inv cfg \<longleftrightarrow>
     (\<forall>p q m. p \<in> correct \<longrightarrow> q \<in> correct \<longrightarrow>
              (\<exists>n. Receive q n p m \<in> events_of (cfg_hist cfg)) \<longrightarrow>
              (\<exists>ns. Send p ns q m \<in> events_of (cfg_hist cfg)))"

definition causal_inv :: "'p config \<Rightarrow> bool" where
  "causal_inv cfg \<longleftrightarrow>
     wf_history (cfg_hist cfg) \<and>
     sends_match_inv cfg \<and>
     buffer_correct_inv cfg \<and>
     send_unique_inv cfg \<and>
     recv_unique_inv cfg \<and>
     buffer_count_inv cfg \<and>
     delivered_drained_inv cfg \<and>
     recv_implies_send_inv cfg"

lemma causal_inv_init [simp]: "causal_inv init_config"
proof -
  have su: "send_unique_inv init_config"
    by (simp add: send_unique_inv_def init_config_def events_of_def)
  have ru: "recv_unique_inv init_config"
    by (simp add: recv_unique_inv_def init_config_def events_of_def)
  have bcnt: "buffer_count_inv init_config"
    by (simp add: buffer_count_inv_def init_config_def empty_inflight_def)
  have dd: "delivered_drained_inv init_config"
    by (simp add: delivered_drained_inv_def init_config_def events_of_def)
  have ris: "recv_implies_send_inv init_config"
    by (simp add: recv_implies_send_inv_def init_config_def events_of_def)
  show ?thesis
    unfolding causal_inv_def
    using su ru bcnt dd ris by simp
qed

subsection \<open>Step-wise preservation of the structural invariants\<close>

lemma send_unique_step:
  assumes inv:  "send_unique_inv cfg"
      and step: "causal_run_step cfg cfg'"
  shows "send_unique_inv cfg'"
  using step inv
proof induction
  case (causal_step_internal p n cfg cfg')
  have ev:
    "events_of (cfg_hist cfg') = events_of (cfg_hist cfg) \<union> {Internal p n}"
    using causal_step_internal.hyps(3) events_of_extend by simp
  show ?case
    using causal_step_internal.prems ev
    by (auto simp: send_unique_inv_def)
next
  case (causal_step_send p q n cfg m cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {Send p n q m}"
    using causal_step_send.hyps(5) events_of_extend by simp
  have fresh: "send_fresh cfg p q m" by (rule causal_step_send.hyps(4))
  hence no_old_send: "Send p k q m \<notin> events_of (cfg_hist cfg)" for k
    by (simp add: send_fresh_def)
  show ?case
  proof (unfold send_unique_inv_def, intro allI impI)
    fix p' q' m' n1 n2
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and s1: "Send p' n1 q' m' \<in> events_of (cfg_hist cfg')"
       and s2: "Send p' n2 q' m' \<in> events_of (cfg_hist cfg')"
    show "n1 = n2"
    proof (cases "(p', q', m') = (p, q, m)")
      case match: True
      have no_old: "Send p k q m \<notin> events_of (cfg_hist cfg)" for k
        using no_old_send by simp
      from s1 ev have s1': "Send p' n1 q' m' = Send p n q m
                            \<or> Send p' n1 q' m' \<in> events_of (cfg_hist cfg)"
        by auto
      from s2 ev have s2': "Send p' n2 q' m' = Send p n q m
                            \<or> Send p' n2 q' m' \<in> events_of (cfg_hist cfg)"
        by auto
      from s1' no_old match have n1_eq: "n1 = n"
        by (cases "Send p' n1 q' m' = Send p n q m") auto
      from s2' no_old match have n2_eq: "n2 = n"
        by (cases "Send p' n2 q' m' = Send p n q m") auto
      from n1_eq n2_eq show ?thesis by simp
    next
      case neq: False
      have neq_event: "Send p' k q' m' \<noteq> Send p n q m" for k
        using neq by auto
      from s1 ev have s1_in: "Send p' n1 q' m' \<in> events_of (cfg_hist cfg)"
        using neq_event by auto
      from s2 ev have s2_in: "Send p' n2 q' m' \<in> events_of (cfg_hist cfg)"
        using neq_event by auto
      show ?thesis
        using causal_step_send.prems pc qc s1_in s2_in
        by (auto simp: send_unique_inv_def)
    qed
  qed
next
  case (causal_step_recv q p m cfg n cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {Receive q n p m}"
    using causal_step_recv.hyps(6) events_of_extend by simp
  show ?case
    using causal_step_recv.prems ev
    by (auto simp: send_unique_inv_def)
next
  case (causal_step_byzantine pb new_event cfg cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {new_event}"
    using causal_step_byzantine.hyps(4) events_of_extend by simp
  have pby: "pb \<in> byzantine" by (rule causal_step_byzantine.hyps(1))
  have proc_new: "proc_of new_event = pb"
    by (rule causal_step_byzantine.hyps(2))
  show ?case
  proof (unfold send_unique_inv_def, intro allI impI)
    fix p' q' m' n1 n2
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and s1: "Send p' n1 q' m' \<in> events_of (cfg_hist cfg')"
       and s2: "Send p' n2 q' m' \<in> events_of (cfg_hist cfg')"
    have p_ne: "p' \<noteq> pb" using pc pby partition_disj by blast
    have proc_send1: "proc_of (Send p' n1 q' m') = p'" by simp
    have proc_send2: "proc_of (Send p' n2 q' m') = p'" by simp
    have not_new1: "Send p' n1 q' m' \<noteq> new_event"
      using p_ne proc_new proc_send1 by metis
    have not_new2: "Send p' n2 q' m' \<noteq> new_event"
      using p_ne proc_new proc_send2 by metis
    from s1 ev not_new1
    have s1_in: "Send p' n1 q' m' \<in> events_of (cfg_hist cfg)" by auto
    from s2 ev not_new2
    have s2_in: "Send p' n2 q' m' \<in> events_of (cfg_hist cfg)" by auto
    show "n1 = n2"
      using causal_step_byzantine.prems pc qc s1_in s2_in
      by (auto simp: send_unique_inv_def)
  qed
qed

lemma buffer_count_step:
  assumes inv:  "buffer_count_inv cfg"
      and step: "causal_run_step cfg cfg'"
  shows "buffer_count_inv cfg'"
  using step inv
proof induction
  case (causal_step_internal p n cfg cfg')
  have buf: "cfg_inflight cfg' = cfg_inflight cfg"
    using causal_step_internal.hyps(3) by simp
  show ?case
    using causal_step_internal.prems buf
    by (simp add: buffer_count_inv_def)
next
  case (causal_step_send p q n cfg m cfg')
  have buf: "cfg_inflight cfg' = cfg_inflight cfg \<union># {# (p, q, m) }"
    using causal_step_send.hyps(5) by simp
  have fresh: "send_fresh cfg p q m" by (rule causal_step_send.hyps(4))
  hence buf0: "cfg_inflight cfg (p, q, m) = 0"
    by (simp add: send_fresh_def)
  show ?case
  proof (unfold buffer_count_inv_def, intro allI impI)
    fix p' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
    show "cfg_inflight cfg' (p', q', m') \<le> 1"
    proof (cases "(p', q', m') = (p, q, m)")
      case True
      have "cfg_inflight cfg' (p, q, m) = cfg_inflight cfg (p, q, m) + 1"
        using buf by simp
      also have "\<dots> = 1" using buf0 by simp
      finally show ?thesis using True by simp
    next
      case False
      have neq: "(p, q, m) \<noteq> (p', q', m')" using False by auto
      have eq_count:
        "cfg_inflight cfg' (p', q', m') = cfg_inflight cfg (p', q', m')"
        using buf neq by simp
      show ?thesis
        using causal_step_send.prems pc qc eq_count
        by (auto simp: buffer_count_inv_def)
    qed
  qed
next
  case (causal_step_recv q p m cfg n cfg')
  have buf: "cfg_inflight cfg' = cfg_inflight cfg -# (p, q, m)"
    using causal_step_recv.hyps(6) by simp
  show ?case
  proof (unfold buffer_count_inv_def, intro allI impI)
    fix p' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
    have old: "cfg_inflight cfg (p', q', m') \<le> 1"
      using causal_step_recv.prems pc qc
      by (auto simp: buffer_count_inv_def)
    show "cfg_inflight cfg' (p', q', m') \<le> 1"
      using buf old by (auto split: if_split_asm)
  qed
next
  case (causal_step_byzantine pb new_event cfg cfg')
  have buf: "cfg_inflight cfg' = cfg_inflight cfg"
    using causal_step_byzantine.hyps(4) by simp
  show ?case
    using causal_step_byzantine.prems buf
    by (simp add: buffer_count_inv_def)
qed

lemma recv_implies_send_step:
  assumes inv:  "recv_implies_send_inv cfg"
      and step: "causal_run_step cfg cfg'"
  shows "recv_implies_send_inv cfg'"
  using step inv
proof induction
  case (causal_step_internal p n cfg cfg')
  have ev:
    "events_of (cfg_hist cfg') = events_of (cfg_hist cfg) \<union> {Internal p n}"
    using causal_step_internal.hyps(3) events_of_extend by simp
  show ?case
  proof (unfold recv_implies_send_inv_def, intro allI impI)
    fix p' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and ex_rev: "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg')"
    from ex_rev ev have
      "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg)" by auto
    with causal_step_internal.prems pc qc
    have "\<exists>ns. Send p' ns q' m' \<in> events_of (cfg_hist cfg)"
      by (auto simp: recv_implies_send_inv_def)
    thus "\<exists>ns. Send p' ns q' m' \<in> events_of (cfg_hist cfg')"
      using ev by auto
  qed
next
  case (causal_step_send p q n cfg m cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {Send p n q m}"
    using causal_step_send.hyps(5) events_of_extend by simp
  show ?case
  proof (unfold recv_implies_send_inv_def, intro allI impI)
    fix p' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and ex_rev: "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg')"
    have neq_send: "Receive q' k p' m' \<noteq> Send p n q m" for k by auto
    from ex_rev ev neq_send have
      "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg)" by auto
    with causal_step_send.prems pc qc
    have "\<exists>ns. Send p' ns q' m' \<in> events_of (cfg_hist cfg)"
      by (auto simp: recv_implies_send_inv_def)
    thus "\<exists>ns. Send p' ns q' m' \<in> events_of (cfg_hist cfg')"
      using ev by auto
  qed
next
  case (causal_step_recv q p m cfg n cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {Receive q n p m}"
    using causal_step_recv.hyps(6) events_of_extend by simp
  have causal_ok: "causal_recv_ok cfg q p m"
    by (rule causal_step_recv.hyps(4))
  then obtain ns0 where
    send0: "Send p ns0 q m \<in> events_of (cfg_hist cfg)"
    by (auto simp: causal_recv_ok_def)
  show ?case
  proof (unfold recv_implies_send_inv_def, intro allI impI)
    fix p' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and ex_rev: "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg')"
    show "\<exists>ns. Send p' ns q' m' \<in> events_of (cfg_hist cfg')"
    proof (cases "(p', q', m') = (p, q, m)")
      case match: True
      have "Send p ns0 q m \<in> events_of (cfg_hist cfg')"
        using send0 ev by auto
      with match show ?thesis by auto
    next
      case neq: False
      have neq_event: "Receive q' k p' m' \<noteq> Receive q n p m" for k
        using neq by auto
      from ex_rev ev neq_event have
        ex_rev_old: "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg)"
        by auto
      with causal_step_recv.prems pc qc
      have "\<exists>ns. Send p' ns q' m' \<in> events_of (cfg_hist cfg)"
        by (auto simp: recv_implies_send_inv_def)
      thus ?thesis using ev by auto
    qed
  qed
next
  case (causal_step_byzantine pb new_event cfg cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {new_event}"
    using causal_step_byzantine.hyps(4) events_of_extend by simp
  have pby: "pb \<in> byzantine" by (rule causal_step_byzantine.hyps(1))
  have proc_new: "proc_of new_event = pb"
    by (rule causal_step_byzantine.hyps(2))
  show ?case
  proof (unfold recv_implies_send_inv_def, intro allI impI)
    fix p' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and ex_rev: "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg')"
    have q_ne: "q' \<noteq> pb" using qc pby partition_disj by blast
    have not_new: "Receive q' k p' m' \<noteq> new_event" for k
    proof -
      have "proc_of (Receive q' k p' m') = q'" by simp
      thus "Receive q' k p' m' \<noteq> new_event"
        using q_ne proc_new by metis
    qed
    from ex_rev ev not_new have
      "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg)" by auto
    with causal_step_byzantine.prems pc qc
    have "\<exists>ns. Send p' ns q' m' \<in> events_of (cfg_hist cfg)"
      by (auto simp: recv_implies_send_inv_def)
    thus "\<exists>ns. Send p' ns q' m' \<in> events_of (cfg_hist cfg')"
      using ev by auto
  qed
qed

lemma delivered_drained_step:
  assumes dd:  "delivered_drained_inv cfg"
      and ris: "recv_implies_send_inv cfg"
      and bcnt: "buffer_count_inv cfg"
      and step: "causal_run_step cfg cfg'"
  shows "delivered_drained_inv cfg'"
  using step dd ris bcnt
proof induction
  case (causal_step_internal p n cfg cfg')
  have ev:
    "events_of (cfg_hist cfg') = events_of (cfg_hist cfg) \<union> {Internal p n}"
    using causal_step_internal.hyps(3) events_of_extend by simp
  have buf: "cfg_inflight cfg' = cfg_inflight cfg"
    using causal_step_internal.hyps(3) by simp
  show ?case
  proof (unfold delivered_drained_inv_def, intro allI impI)
    fix p' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and ex_rev: "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg')"
    from ex_rev ev have
      "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg)" by auto
    with causal_step_internal.prems(1) pc qc
    have "\<not> (p', q', m') \<in># cfg_inflight cfg"
      by (auto simp: delivered_drained_inv_def)
    thus "\<not> (p', q', m') \<in># cfg_inflight cfg'"
      using buf by simp
  qed
next
  case (causal_step_send p q n cfg m cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {Send p n q m}"
    using causal_step_send.hyps(5) events_of_extend by simp
  have buf: "cfg_inflight cfg' = cfg_inflight cfg \<union># {# (p, q, m) }"
    using causal_step_send.hyps(5) by simp
  have fresh: "send_fresh cfg p q m" by (rule causal_step_send.hyps(4))
  have pc': "p \<in> correct" by (rule causal_step_send.hyps(1))
  have qc': "q \<in> correct" by (rule causal_step_send.hyps(2))
  show ?case
  proof (unfold delivered_drained_inv_def, intro allI impI)
    fix p' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and ex_rev: "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg')"
    have neq_send: "Receive q' k p' m' \<noteq> Send p n q m" for k by auto
    from ex_rev ev neq_send have ex_rev_old:
      "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg)" by auto
    with causal_step_send.prems(1) pc qc
    have not_buf: "\<not> (p', q', m') \<in># cfg_inflight cfg"
      by (auto simp: delivered_drained_inv_def)
    show "\<not> (p', q', m') \<in># cfg_inflight cfg'"
    proof (cases "(p', q', m') = (p, q, m)")
      case True
      \<comment> \<open>The existing receive at @{term q} from @{term p} on @{term m}
          would, via @{const recv_implies_send_inv}, force a matching
          Send in @{term cfg}'s events -- but freshness forbids any.\<close>
      from True ex_rev_old have ex_rev_pqm:
        "\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist cfg)" by simp
      from causal_step_send.prems(2) pc' qc' ex_rev_pqm
      have ex_send: "\<exists>ns. Send p ns q m \<in> events_of (cfg_hist cfg)"
        by (auto simp: recv_implies_send_inv_def)
      from fresh have "\<forall>k. Send p k q m \<notin> events_of (cfg_hist cfg)"
        by (simp add: send_fresh_def)
      with ex_send have False by blast
      thus ?thesis by simp
    next
      case False
      have neq: "(p, q, m) \<noteq> (p', q', m')" using False by auto
      have eq_count:
        "cfg_inflight cfg' (p', q', m') = cfg_inflight cfg (p', q', m')"
        using buf neq by simp
      thus ?thesis using not_buf by simp
    qed
  qed
next
  case (causal_step_recv q p m cfg n cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {Receive q n p m}"
    using causal_step_recv.hyps(6) events_of_extend by simp
  have buf: "cfg_inflight cfg' = cfg_inflight cfg -# (p, q, m)"
    using causal_step_recv.hyps(6) by simp
  have buf_in_cfg: "(p, q, m) \<in># cfg_inflight cfg"
    by (rule causal_step_recv.hyps(3))
  have qc_thm: "q \<in> correct" by (rule causal_step_recv.hyps(1))
  have pc_thm: "p \<in> correct" by (rule causal_step_recv.hyps(2))
  have buf_eq1: "cfg_inflight cfg (p, q, m) = 1"
  proof -
    have "cfg_inflight cfg (p, q, m) \<le> 1"
      using causal_step_recv.prems(3) pc_thm qc_thm
      by (auto simp: buffer_count_inv_def)
    moreover have "cfg_inflight cfg (p, q, m) \<ge> 1"
      using buf_in_cfg by simp
    ultimately show ?thesis by simp
  qed
  show ?case
  proof (unfold delivered_drained_inv_def, intro allI impI)
    fix p' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and ex_rev: "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg')"
    show "\<not> (p', q', m') \<in># cfg_inflight cfg'"
    proof (cases "(p', q', m') = (p, q, m)")
      case True
      have "cfg_inflight cfg' (p, q, m) = cfg_inflight cfg (p, q, m) - 1"
        using buf by simp
      also have "\<dots> = 0" using buf_eq1 by simp
      finally have "cfg_inflight cfg' (p, q, m) = 0" .
      thus ?thesis using True by simp
    next
      case neq: False
      have neq_event: "Receive q' k p' m' \<noteq> Receive q n p m" for k
        using neq by auto
      from ex_rev ev neq_event have ex_rev_old:
        "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg)" by auto
      with causal_step_recv.prems(1) pc qc
      have not_buf: "\<not> (p', q', m') \<in># cfg_inflight cfg"
        by (auto simp: delivered_drained_inv_def)
      have eq_count:
        "cfg_inflight cfg' (p', q', m') = cfg_inflight cfg (p', q', m')"
        using buf neq by auto
      thus ?thesis using not_buf by simp
    qed
  qed
next
  case (causal_step_byzantine pb new_event cfg cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {new_event}"
    using causal_step_byzantine.hyps(4) events_of_extend by simp
  have buf: "cfg_inflight cfg' = cfg_inflight cfg"
    using causal_step_byzantine.hyps(4) by simp
  have pby: "pb \<in> byzantine" by (rule causal_step_byzantine.hyps(1))
  have proc_new: "proc_of new_event = pb"
    by (rule causal_step_byzantine.hyps(2))
  show ?case
  proof (unfold delivered_drained_inv_def, intro allI impI)
    fix p' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and ex_rev: "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg')"
    have q_ne: "q' \<noteq> pb" using qc pby partition_disj by blast
    have not_new: "Receive q' k p' m' \<noteq> new_event" for k
    proof -
      have "proc_of (Receive q' k p' m') = q'" by simp
      thus "Receive q' k p' m' \<noteq> new_event"
        using q_ne proc_new by metis
    qed
    from ex_rev ev not_new have
      "\<exists>n'. Receive q' n' p' m' \<in> events_of (cfg_hist cfg)" by auto
    with causal_step_byzantine.prems(1) pc qc
    have "\<not> (p', q', m') \<in># cfg_inflight cfg"
      by (auto simp: delivered_drained_inv_def)
    thus "\<not> (p', q', m') \<in># cfg_inflight cfg'"
      using buf by simp
  qed
qed

lemma recv_unique_step:
  assumes ru:  "recv_unique_inv cfg"
      and dd:  "delivered_drained_inv cfg"
      and step: "causal_run_step cfg cfg'"
  shows "recv_unique_inv cfg'"
  using step ru dd
proof induction
  case (causal_step_internal p n cfg cfg')
  have ev:
    "events_of (cfg_hist cfg') = events_of (cfg_hist cfg) \<union> {Internal p n}"
    using causal_step_internal.hyps(3) events_of_extend by simp
  show ?case
    using causal_step_internal.prems(1) ev
    by (auto simp: recv_unique_inv_def)
next
  case (causal_step_send p q n cfg m cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {Send p n q m}"
    using causal_step_send.hyps(5) events_of_extend by simp
  show ?case
    using causal_step_send.prems(1) ev
    by (auto simp: recv_unique_inv_def)
next
  case (causal_step_recv q p m cfg n cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {Receive q n p m}"
    using causal_step_recv.hyps(6) events_of_extend by simp
  have buf_in: "(p, q, m) \<in># cfg_inflight cfg"
    by (rule causal_step_recv.hyps(3))
  have qc_thm: "q \<in> correct" by (rule causal_step_recv.hyps(1))
  have pc_thm: "p \<in> correct" by (rule causal_step_recv.hyps(2))
  have dd_cfg: "delivered_drained_inv cfg" by (rule causal_step_recv.prems(2))
  have no_old_recv:
    "Receive q k p m \<notin> events_of (cfg_hist cfg)" for k
  proof (rule notI)
    assume "Receive q k p m \<in> events_of (cfg_hist cfg)"
    hence ex: "\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist cfg)" by blast
    with dd_cfg pc_thm qc_thm
    have not_buf: "\<not> (p, q, m) \<in># cfg_inflight cfg"
      by (auto simp: delivered_drained_inv_def)
    from not_buf buf_in show False by simp
  qed
  show ?case
  proof (unfold recv_unique_inv_def, intro allI impI)
    fix p' q' m' n1 n2
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and r1: "Receive q' n1 p' m' \<in> events_of (cfg_hist cfg')"
       and r2: "Receive q' n2 p' m' \<in> events_of (cfg_hist cfg')"
    show "n1 = n2"
    proof (cases "(p', q', m') = (p, q, m)")
      case match: True
      have no_old: "Receive q' k p' m' \<notin> events_of (cfg_hist cfg)" for k
        using no_old_recv match by auto
      from r1 ev have r1': "Receive q' n1 p' m' = Receive q n p m
                            \<or> Receive q' n1 p' m' \<in> events_of (cfg_hist cfg)"
        by auto
      from r2 ev have r2': "Receive q' n2 p' m' = Receive q n p m
                            \<or> Receive q' n2 p' m' \<in> events_of (cfg_hist cfg)"
        by auto
      from r1' no_old match have n1_eq: "n1 = n"
        by (cases "Receive q' n1 p' m' = Receive q n p m") auto
      from r2' no_old match have n2_eq: "n2 = n"
        by (cases "Receive q' n2 p' m' = Receive q n p m") auto
      from n1_eq n2_eq show ?thesis by simp
    next
      case neq: False
      have neq_event: "Receive q' k p' m' \<noteq> Receive q n p m" for k
        using neq by auto
      from r1 ev neq_event
      have r1_in: "Receive q' n1 p' m' \<in> events_of (cfg_hist cfg)" by auto
      from r2 ev neq_event
      have r2_in: "Receive q' n2 p' m' \<in> events_of (cfg_hist cfg)" by auto
      show ?thesis
        using causal_step_recv.prems(1) pc qc r1_in r2_in
        by (auto simp: recv_unique_inv_def)
    qed
  qed
next
  case (causal_step_byzantine pb new_event cfg cfg')
  have ev: "events_of (cfg_hist cfg')
              = events_of (cfg_hist cfg) \<union> {new_event}"
    using causal_step_byzantine.hyps(4) events_of_extend by simp
  have pby: "pb \<in> byzantine" by (rule causal_step_byzantine.hyps(1))
  have proc_new: "proc_of new_event = pb"
    by (rule causal_step_byzantine.hyps(2))
  show ?case
  proof (unfold recv_unique_inv_def, intro allI impI)
    fix p' q' m' n1 n2
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and r1: "Receive q' n1 p' m' \<in> events_of (cfg_hist cfg')"
       and r2: "Receive q' n2 p' m' \<in> events_of (cfg_hist cfg')"
    have q_ne: "q' \<noteq> pb" using qc pby partition_disj by blast
    have proc_recv1: "proc_of (Receive q' n1 p' m') = q'" by simp
    have proc_recv2: "proc_of (Receive q' n2 p' m') = q'" by simp
    have not_new1: "Receive q' n1 p' m' \<noteq> new_event"
      using q_ne proc_new proc_recv1 by metis
    have not_new2: "Receive q' n2 p' m' \<noteq> new_event"
      using q_ne proc_new proc_recv2 by metis
    from r1 ev not_new1
    have r1_in: "Receive q' n1 p' m' \<in> events_of (cfg_hist cfg)" by auto
    from r2 ev not_new2
    have r2_in: "Receive q' n2 p' m' \<in> events_of (cfg_hist cfg)" by auto
    show "n1 = n2"
      using causal_step_byzantine.prems(1) pc qc r1_in r2_in
      by (auto simp: recv_unique_inv_def)
  qed
qed

lemma causal_inv_step:
  assumes inv:  "causal_inv cfg"
      and step: "causal_run_step cfg cfg'"
  shows "causal_inv cfg'"
proof -
  have wf:   "wf_history (cfg_hist cfg)"
       and sm:   "sends_match_inv cfg"
       and bc:   "buffer_correct_inv cfg"
       and su:   "send_unique_inv cfg"
       and ru:   "recv_unique_inv cfg"
       and bcnt: "buffer_count_inv cfg"
       and dd:   "delivered_drained_inv cfg"
       and ris:  "recv_implies_send_inv cfg"
    using inv unfolding causal_inv_def by auto
  have run_step_cfg: "run_step cfg cfg'"
    by (rule causal_run_step_imp_run_step[OF step])
  have wf':   "wf_history (cfg_hist cfg')"
    by (rule wf_history_step[OF wf run_step_cfg])
  have sm':   "sends_match_inv cfg'"
    by (rule sends_match_inv_step[OF sm run_step_cfg])
  have bc':   "buffer_correct_inv cfg'"
    by (rule buffer_correct_inv_step[OF bc run_step_cfg])
  have su':   "send_unique_inv cfg'"
    by (rule send_unique_step[OF su step])
  have bcnt': "buffer_count_inv cfg'"
    by (rule buffer_count_step[OF bcnt step])
  have ris':  "recv_implies_send_inv cfg'"
    by (rule recv_implies_send_step[OF ris step])
  have dd':   "delivered_drained_inv cfg'"
    by (rule delivered_drained_step[OF dd ris bcnt step])
  have ru':   "recv_unique_inv cfg'"
    by (rule recv_unique_step[OF ru dd step])
  show ?thesis
    unfolding causal_inv_def
    using wf' sm' bc' su' ru' bcnt' dd' ris' by simp
qed

lemma causal_inv_run:
  assumes "causal_run cfg"
  shows "causal_inv cfg"
  using assms unfolding causal_run_def
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from causal_inv_step[OF step.IH step.hyps(2)]
  show ?case .
qed

text \<open>Extract individual invariants as named theorems for downstream
use.\<close>

lemma send_unique_run:
  assumes "causal_run cfg"
  shows "send_unique_inv cfg"
  using causal_inv_run[OF assms] by (simp add: causal_inv_def)

lemma recv_unique_run:
  assumes "causal_run cfg"
  shows "recv_unique_inv cfg"
  using causal_inv_run[OF assms] by (simp add: causal_inv_def)

lemma buffer_count_run:
  assumes "causal_run cfg"
  shows "buffer_count_inv cfg"
  using causal_inv_run[OF assms] by (simp add: causal_inv_def)

lemma delivered_drained_run:
  assumes "causal_run cfg"
  shows "delivered_drained_inv cfg"
  using causal_inv_run[OF assms] by (simp add: causal_inv_def)

lemma recv_implies_send_run:
  assumes "causal_run cfg"
  shows "recv_implies_send_inv cfg"
  using causal_inv_run[OF assms] by (simp add: causal_inv_def)

section \<open>Structural lemmas: hb under single-event history extensions\<close>

text \<open>Each @{const causal_run_step} extends the global history by
exactly one event at one process.  We abstract this as a predicate
@{term \<open>hist_extend p ev H H'\<close>} and prove two consequences:
program-order and message-order are monotone-up under extension, and
-- crucially -- if the appended event is a @{const bhb_step} sink
(has no outgoing @{const bhb_step} edges in the extended history),
then @{const bhb} between events of the smaller history coincides
in the two histories.  This is what lets us push the invariant
quantifier between the pre-state and post-state of a step.\<close>

definition hist_extend ::
  "'p \<Rightarrow> 'p event \<Rightarrow> 'p history \<Rightarrow> 'p history \<Rightarrow> bool" where
  "hist_extend p ev H H' \<longleftrightarrow> H' = H (p := H p @ [ev])"

lemma events_of_extend_iff:
  assumes "hist_extend p ev H H'"
  shows "events_of H' = events_of H \<union> {ev}"
  using assms unfolding hist_extend_def
  by (simp add: events_of_extend)

lemma events_of_extend_mono:
  assumes "hist_extend p ev H H'"
  shows "events_of H \<subseteq> events_of H'"
  using events_of_extend_iff[OF assms] by auto

subsection \<open>Program order is monotone under extension\<close>

lemma program_order_extend_up:
  assumes ext: "hist_extend p_new ev H H'"
      and po:  "program_order H e e'"
  shows "program_order H' e e'"
proof -
  from po obtain p' i j where
    ij: "i < j" and j: "j < length (H p')"
    and ei: "H p' ! i = e" and ej: "H p' ! j = e'"
    unfolding program_order_def by blast
  have H'p': "H' p' = H p' \<or> H' p' = H p' @ [ev]"
    using ext unfolding hist_extend_def by auto
  show ?thesis
  proof (cases "p' = p_new")
    case True
    have H'_eq: "H' p_new = H p_new @ [ev]"
      using ext unfolding hist_extend_def by simp
    have len_ge: "length (H' p_new) = length (H p_new) + 1"
      using H'_eq by simp
    have j': "j < length (H' p_new)" using j True len_ge by simp
    have ei': "H' p' ! i = e"
      using True H'_eq ei j ij by (simp add: nth_append)
    have ej': "H' p' ! j = e'"
      using True H'_eq ej j by (simp add: nth_append)
    have conj: "i < j \<and> j < length (H' p') \<and> H' p' ! i = e \<and> H' p' ! j = e'"
      using ij j' ei' ej' True by simp
    hence "\<exists>p i j. i < j \<and> j < length (H' p) \<and> H' p ! i = e \<and> H' p ! j = e'"
      by blast
    thus ?thesis unfolding program_order_def by simp
  next
    case False
    hence H'_eq: "H' p' = H p'"
      using ext unfolding hist_extend_def by simp
    have ei2: "H' p' ! i = e" using ei H'_eq by simp
    have ej2: "H' p' ! j = e'" using ej H'_eq by simp
    have len2: "j < length (H' p')" using j H'_eq by simp
    have conj: "i < j \<and> j < length (H' p') \<and> H' p' ! i = e \<and> H' p' ! j = e'"
      using ij len2 ei2 ej2 by simp
    hence "\<exists>p i j. i < j \<and> j < length (H' p) \<and> H' p ! i = e \<and> H' p ! j = e'"
      by blast
    thus ?thesis unfolding program_order_def by simp
  qed
qed

lemma message_order_extend_up:
  assumes ext: "hist_extend p_new ev H H'"
      and mo:  "message_order H e e'"
  shows "message_order H' e e'"
  using mo events_of_extend_mono[OF ext]
  unfolding message_order_def by blast

lemma hb_step_extend_up:
  assumes "hist_extend p_new ev H H'"
      and "hb_step H e e'"
  shows "hb_step H' e e'"
  using assms program_order_extend_up message_order_extend_up
  unfolding hb_step_def by blast

lemma bhb_step_extend_up:
  assumes ext:  "hist_extend p_new ev H H'"
      and bhbs: "bhb_step C H e e'"
  shows "bhb_step C H' e e'"
  using bhbs hb_step_extend_up[OF ext]
  unfolding bhb_step_def hb_step_def by blast

lemma bhb_extend_up:
  assumes ext: "hist_extend p_new ev H H'"
      and bb:  "bhb C H e e'"
  shows "bhb C H' e e'"
proof -
  from bb have "(bhb_step C H)\<^sup>+\<^sup>+ e e'" unfolding bhb_def .
  hence "(bhb_step C H')\<^sup>+\<^sup>+ e e'"
  proof (induction rule: tranclp_induct)
    case (base y)
    from bhb_step_extend_up[OF ext base]
    show ?case by (rule tranclp.r_into_trancl)
  next
    case (step y z)
    have st: "bhb_step C H' y z"
      by (rule bhb_step_extend_up[OF ext step.hyps(2)])
    from step.IH st show ?case by (rule tranclp.trancl_into_trancl)
  qed
  thus "bhb C H' e e'" unfolding bhb_def .
qed

subsection \<open>Restriction down: removing the new event from chains\<close>

text \<open>If the appended event is a @{const bhb_step} sink in the
extended history (no outgoing @{const bhb_step}), and both endpoints
of a @{const bhb_step} in @{term H'} are events of the smaller
history @{term H} other than the appended event, then the
@{const bhb_step} also holds in @{term H}.\<close>

lemma program_order_extend_down:
  assumes ext: "hist_extend p_new ev H H'"
      and po:  "program_order H' e e'"
      and e_old:  "e \<noteq> ev"
      and e'_old: "e' \<noteq> ev"
  shows "program_order H e e'"
proof -
  from po obtain p' i j where
    ij: "i < j" and j: "j < length (H' p')"
    and ei: "H' p' ! i = e" and ej: "H' p' ! j = e'"
    unfolding program_order_def by blast
  show ?thesis
  proof (cases "p' = p_new")
    case True
    have H'_eq: "H' p_new = H p_new @ [ev]"
      using ext unfolding hist_extend_def by simp
    have len_eq: "length (H' p_new) = length (H p_new) + 1"
      using H'_eq by simp
    have j_lt: "j < length (H p_new) + 1" using j True len_eq by simp
    have j_le: "j < length (H p_new)"
    proof (rule ccontr)
      assume "\<not> j < length (H p_new)"
      with j_lt have "j = length (H p_new)" by simp
      hence "H' p_new ! j = ev" using H'_eq by simp
      with True ej have "e' = ev" by simp
      with e'_old show False by simp
    qed
    have i_le: "i < length (H p_new)" using ij j_le by simp
    have ei': "H p' ! i = e"
      using True H'_eq ei i_le by (simp add: nth_append)
    have ej': "H p' ! j = e'"
      using True H'_eq ej j_le by (simp add: nth_append)
    have conj: "i < j \<and> j < length (H p') \<and> H p' ! i = e \<and> H p' ! j = e'"
      using ij j_le ei' ej' True by simp
    hence "\<exists>p i j. i < j \<and> j < length (H p) \<and> H p ! i = e \<and> H p ! j = e'"
      by blast
    thus ?thesis unfolding program_order_def by simp
  next
    case False
    hence H'_eq: "H' p' = H p'"
      using ext unfolding hist_extend_def by simp
    have ei2: "H p' ! i = e" using ei H'_eq by simp
    have ej2: "H p' ! j = e'" using ej H'_eq by simp
    have len2: "j < length (H p')" using j H'_eq by simp
    have conj: "i < j \<and> j < length (H p') \<and> H p' ! i = e \<and> H p' ! j = e'"
      using ij len2 ei2 ej2 by simp
    hence "\<exists>p i j. i < j \<and> j < length (H p) \<and> H p ! i = e \<and> H p ! j = e'"
      by blast
    thus ?thesis unfolding program_order_def by simp
  qed
qed

lemma message_order_extend_down:
  assumes ext: "hist_extend p_new ev H H'"
      and mo:  "message_order H' e e'"
      and e_in:  "e \<in> events_of H"
      and e'_in: "e' \<in> events_of H"
  shows "message_order H e e'"
  using mo e_in e'_in
  unfolding message_order_def by blast

text \<open>A @{const bhb_step} sink in @{term H'}: an event that has no
outgoing @{const bhb_step} edge.  Sink events cannot be intermediate
in any chain, so chains between old events do not pass through them.\<close>

definition bhb_step_sink ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> bool" where
  "bhb_step_sink C H ev \<longleftrightarrow> (\<forall>e'. \<not> bhb_step C H ev e')"

lemma bhb_step_extend_down:
  assumes ext:   "hist_extend p_new ev H H'"
      and sink:  "bhb_step_sink C H' ev"
      and bhbs:  "bhb_step C H' e e'"
      and e_in:  "e \<in> events_of H"
      and e'_in: "e' \<in> events_of H"
      and ev_new: "ev \<notin> events_of H"
  shows "bhb_step C H e e'"
proof -
  have e_old:  "e \<noteq> ev"  using e_in ev_new by auto
  have e'_old: "e' \<noteq> ev" using e'_in ev_new by auto
  from bhbs have proc_e:  "proc_of e \<in> C"
            and proc_e': "proc_of e' \<in> C"
            and step:    "program_order H' e e' \<or> message_order H' e e'"
    unfolding bhb_step_def hb_step_def by auto
  from step have "program_order H e e' \<or> message_order H e e'"
  proof
    assume "program_order H' e e'"
    from program_order_extend_down[OF ext this e_old e'_old]
    show ?thesis by simp
  next
    assume "message_order H' e e'"
    from message_order_extend_down[OF ext this e_in e'_in]
    show ?thesis by simp
  qed
  with proc_e proc_e' show ?thesis
    unfolding bhb_step_def hb_step_def by auto
qed

lemma bhb_step_source_in_history:
  assumes "bhb_step C H e e'"
  shows "e \<in> events_of H"
proof -
  from assms have "program_order H e e' \<or> message_order H e e'"
    unfolding bhb_step_def hb_step_def by simp
  thus ?thesis
  proof
    assume "program_order H e e'"
    then obtain p i j where j: "j < length (H p)" and ei: "H p ! i = e"
      and ij: "i < j" unfolding program_order_def by blast
    have "i < length (H p)" using ij j by simp
    hence "e \<in> set (H p)" using ei nth_mem by metis
    thus ?thesis by (auto simp: events_of_def)
  next
    assume "message_order H e e'"
    thus ?thesis unfolding message_order_def by simp
  qed
qed

lemma bhb_extend_down:
  assumes ext:   "hist_extend p_new ev H H'"
      and sink:  "bhb_step_sink C H' ev"
      and bb:    "bhb C H' e e'"
      and e_in:  "e \<in> events_of H"
      and e'_in: "e' \<in> events_of H"
      and ev_new: "ev \<notin> events_of H"
  shows "bhb C H e e'"
proof -
  from bb have tc: "(bhb_step C H')\<^sup>+\<^sup>+ e e'" unfolding bhb_def .
  have "(bhb_step C H)\<^sup>+\<^sup>+ e e' \<and> e \<in> events_of H"
  using tc e'_in
  proof (induction rule: tranclp_induct)
    case (base y)
    have st: "bhb_step C H' e y" by (rule base.hyps)
    have y_in: "y \<in> events_of H" using base.prems by simp
    have e_in_loc: "e \<in> events_of H"
    proof (rule ccontr)
      assume "e \<notin> events_of H"
      have e_in_H': "e \<in> events_of H'"
        by (rule bhb_step_source_in_history[OF st])
      with \<open>e \<notin> events_of H\<close> events_of_extend_iff[OF ext]
      have "e = ev" by auto
      with sink st show False
        unfolding bhb_step_sink_def by blast
    qed
    have ev_step: "bhb_step C H e y"
      by (rule bhb_step_extend_down[OF ext sink st e_in_loc y_in ev_new])
    from ev_step have "(bhb_step C H)\<^sup>+\<^sup>+ e y"
      by (rule tranclp.r_into_trancl)
    with e_in_loc show ?case by simp
  next
    case (step y z)
    have st: "bhb_step C H' y z" by (rule step.hyps(2))
    have z_in: "z \<in> events_of H" using step.prems by simp
    have y_in_loc: "y \<in> events_of H"
    proof (rule ccontr)
      assume "y \<notin> events_of H"
      have y_in_H': "y \<in> events_of H'"
        by (rule bhb_step_source_in_history[OF st])
      with \<open>y \<notin> events_of H\<close> events_of_extend_iff[OF ext]
      have "y = ev" by auto
      with sink st show False
        unfolding bhb_step_sink_def by blast
    qed
    from step.IH y_in_loc obtain tc_y where
      tc_y: "(bhb_step C H)\<^sup>+\<^sup>+ e y" and
      e_in_loc: "e \<in> events_of H" by blast
    have new_st: "bhb_step C H y z"
      by (rule bhb_step_extend_down[OF ext sink st y_in_loc z_in ev_new])
    from tc_y new_st have "(bhb_step C H)\<^sup>+\<^sup>+ e z"
      by (rule tranclp.trancl_into_trancl)
    with e_in_loc show ?case by simp
  qed
  thus ?thesis unfolding bhb_def by simp
qed

section \<open>The new event of each rule is a @{const bhb_step} sink\<close>

text \<open>For each of the four @{const causal_run_step} rules, the
appended event has no outgoing @{const bhb_step} edge in the extended
history.\<close>

text \<open>Auxiliary: under @{const wf_history}, an event whose sequence
number is one past the local list's length is fresh.  This is exactly
the freshness gadget that @{const causal_run_step}'s rules invoke
implicitly when setting up @{term \<open>n = Suc (length (H p))\<close>}, lifted
to a structural property of histories.\<close>

lemma fresh_event_not_in_history:
  assumes wf:    "wf_history H"
      and proc_e: "proc_of ev = p"
      and seq_e:  "seq_of ev = Suc (length (H p))"
  shows "ev \<notin> events_of H"
proof
  assume "ev \<in> events_of H"
  then obtain p' where in_p': "ev \<in> set (H p')"
    by (auto simp: events_of_def)
  have wfp': "wf_history_local p' (H p')"
    using wf unfolding wf_history_def by blast
  hence "proc_of ev = p'"
    using in_p' unfolding wf_history_local_def by blast
  with proc_e have p'_eq: "p' = p" by simp
  from in_p' p'_eq obtain k where
    k_lt: "k < length (H p)" and
    nth_eq: "H p ! k = ev" by (auto simp: in_set_conv_nth)
  have wfp: "wf_history_local p (H p)"
    using wf unfolding wf_history_def by blast
  hence "seq_of (H p ! k) = Suc k"
    using k_lt unfolding wf_history_local_def by blast
  with nth_eq seq_e have "Suc k = Suc (length (H p))" by simp
  with k_lt show False by simp
qed

text \<open>Sink lemma per rule.  Each takes @{term \<open>wf_history H\<close>} so
the freshness consequence of the appended event's sequence number
can be used to rule out @{const program_order} chains via the new
event.\<close>

lemma append_event_no_outgoing_po:
  assumes wf:    "wf_history H"
      and ext:   "hist_extend p ev H H'"
      and proc_e: "proc_of ev = p"
      and seq_e:  "seq_of ev = Suc (length (H p))"
  shows "\<not> program_order H' ev e'"
proof
  assume po: "program_order H' ev e'"
  then obtain p'' i j where
    ij: "i < j" and j: "j < length (H' p'')"
    and ei: "H' p'' ! i = ev"
    unfolding program_order_def by blast
  have ev_fresh: "ev \<notin> events_of H"
    by (rule fresh_event_not_in_history[OF wf proc_e seq_e])
  have H'_eq: "H' p = H p @ [ev]" using ext unfolding hist_extend_def by simp
  have len_H'p: "length (H' p) = length (H p) + 1" using H'_eq by simp
  have p''_eq: "p'' = p"
  proof (rule ccontr)
    assume "p'' \<noteq> p"
    hence H_eq: "H' p'' = H p''"
      using ext unfolding hist_extend_def by simp
    have i_lt: "i < length (H p'')"
      using ij j H_eq by simp
    have "H p'' ! i = ev" using ei H_eq by simp
    hence "ev \<in> set (H p'')" using i_lt nth_mem by metis
    hence "ev \<in> events_of H" by (auto simp: events_of_def)
    with ev_fresh show False by simp
  qed
  have i_eq: "i = length (H p)"
  proof (rule ccontr)
    assume neq: "i \<noteq> length (H p)"
    have i_lt: "i < length (H p)"
    proof -
      from ij j p''_eq len_H'p have "i < length (H p) + 1" by simp
      with neq show ?thesis by simp
    qed
    have "H' p ! i = H p ! i" using H'_eq i_lt by (simp add: nth_append)
    with ei p''_eq have "H p ! i = ev" by simp
    hence "ev \<in> set (H p)" using i_lt nth_mem by metis
    hence "ev \<in> events_of H" by (auto simp: events_of_def)
    with ev_fresh show False by simp
  qed
  from ij j p''_eq len_H'p i_eq
  have "length (H p) < j \<and> j < length (H p) + 1" by simp
  thus False by linarith
qed

text \<open>Sink lemmas: for each rule's new event, no outgoing
@{const bhb_step}.\<close>

lemma internal_event_is_sink:
  assumes wf:    "wf_history H"
      and ext:   "hist_extend p (Internal p n) H H'"
      and n_def: "n = Suc (length (H p))"
  shows "bhb_step_sink C H' (Internal p n)"
proof (unfold bhb_step_sink_def, intro allI notI)
  fix e'
  assume bhbs: "bhb_step C H' (Internal p n) e'"
  from bhbs have step: "program_order H' (Internal p n) e' \<or>
                        message_order H' (Internal p n) e'"
    unfolding bhb_step_def hb_step_def by simp
  have proc_e: "proc_of (Internal p n) = p" by simp
  have seq_e:  "seq_of (Internal p n) = Suc (length (H p))" using n_def by simp
  have no_po: "\<not> program_order H' (Internal p n) e'"
    by (rule append_event_no_outgoing_po[OF wf ext proc_e seq_e])
  have no_mo: "\<not> message_order H' (Internal p n) e'"
    unfolding message_order_def by simp
  from step no_po no_mo show False by simp
qed

lemma send_event_is_sink:
  assumes wf:    "wf_history H"
      and ext:   "hist_extend p (Send p n q m) H H'"
      and n_def: "n = Suc (length (H p))"
      and no_recv:
        "\<not> (\<exists>n'. Receive q n' p m \<in> events_of H')"
  shows "bhb_step_sink C H' (Send p n q m)"
proof (unfold bhb_step_sink_def, intro allI notI)
  fix e'
  assume bhbs: "bhb_step C H' (Send p n q m) e'"
  from bhbs have step: "program_order H' (Send p n q m) e' \<or>
                        message_order H' (Send p n q m) e'"
    unfolding bhb_step_def hb_step_def by simp
  have proc_e: "proc_of (Send p n q m) = p" by simp
  have seq_e:  "seq_of (Send p n q m) = Suc (length (H p))" using n_def by simp
  have no_po: "\<not> program_order H' (Send p n q m) e'"
    by (rule append_event_no_outgoing_po[OF wf ext proc_e seq_e])
  have no_mo: "\<not> message_order H' (Send p n q m) e'"
  proof
    assume "message_order H' (Send p n q m) e'"
    then obtain q' n' p' m' where
      e'_eq: "e' = Receive q' n' p' m'"
      and matches: "p = p' \<and> q = q' \<and> m = m'"
      and e'_in: "e' \<in> events_of H'"
      unfolding message_order_def
      by (cases e') auto
    from e'_eq matches e'_in
    have "Receive q n' p m \<in> events_of H'" by simp
    with no_recv show False by blast
  qed
  from step no_po no_mo show False by simp
qed

lemma recv_event_is_sink:
  assumes wf:    "wf_history H"
      and ext:   "hist_extend q (Receive q n p m) H H'"
      and n_def: "n = Suc (length (H q))"
  shows "bhb_step_sink C H' (Receive q n p m)"
proof (unfold bhb_step_sink_def, intro allI notI)
  fix e'
  assume bhbs: "bhb_step C H' (Receive q n p m) e'"
  from bhbs have step: "program_order H' (Receive q n p m) e' \<or>
                        message_order H' (Receive q n p m) e'"
    unfolding bhb_step_def hb_step_def by simp
  have proc_e: "proc_of (Receive q n p m) = q" by simp
  have seq_e:  "seq_of (Receive q n p m) = Suc (length (H q))" using n_def by simp
  have no_po: "\<not> program_order H' (Receive q n p m) e'"
    by (rule append_event_no_outgoing_po[OF wf ext proc_e seq_e])
  have no_mo: "\<not> message_order H' (Receive q n p m) e'"
    unfolding message_order_def by simp
  from step no_po no_mo show False by simp
qed

lemma byzantine_event_is_sink_correct:
  assumes pby: "pb \<in> byzantine"
      and proc_e: "proc_of new_event = pb"
  shows "bhb_step_sink correct H' new_event"
proof (unfold bhb_step_sink_def, intro allI notI)
  fix e'
  assume bhbs: "bhb_step correct H' new_event e'"
  hence "proc_of new_event \<in> correct"
    unfolding bhb_step_def by simp
  with proc_e have "pb \<in> correct" by simp
  with pby show False using partition_disj by blast
qed

text \<open>Combining sink-ness with the run dynamics: every step's new
event is a @{const bhb_step} sink under @{term correct}.\<close>

lemma causal_step_new_event_sink:
  assumes step: "causal_run_step cfg cfg'"
      and inv:  "causal_inv cfg"
  shows "\<exists>p_new ev. hist_extend p_new ev (cfg_hist cfg) (cfg_hist cfg') \<and>
                    bhb_step_sink correct (cfg_hist cfg') ev \<and>
                    ev \<notin> events_of (cfg_hist cfg)"
  using step inv
proof induction
  case (causal_step_internal p n cfg cfg')
  have wf: "wf_history (cfg_hist cfg)"
    using causal_step_internal.prems unfolding causal_inv_def by simp
  let ?ev = "Internal p n"
  have ext: "hist_extend p ?ev (cfg_hist cfg) (cfg_hist cfg')"
    unfolding hist_extend_def using causal_step_internal.hyps(3) by simp
  have sink: "bhb_step_sink correct (cfg_hist cfg') ?ev"
    by (rule internal_event_is_sink[OF wf ext causal_step_internal.hyps(2)])
  have proc_e: "proc_of ?ev = p" by simp
  have seq_e: "seq_of ?ev = Suc (length (cfg_hist cfg p))"
    using causal_step_internal.hyps(2) by simp
  have ev_fresh: "?ev \<notin> events_of (cfg_hist cfg)"
    by (rule fresh_event_not_in_history[OF wf proc_e seq_e])
  show ?case using ext sink ev_fresh by blast
next
  case (causal_step_send p q n cfg m cfg')
  have wf: "wf_history (cfg_hist cfg)"
    using causal_step_send.prems unfolding causal_inv_def by simp
  have ris: "recv_implies_send_inv cfg"
    using causal_step_send.prems unfolding causal_inv_def by simp
  let ?ev = "Send p n q m"
  have ext: "hist_extend p ?ev (cfg_hist cfg) (cfg_hist cfg')"
    unfolding hist_extend_def using causal_step_send.hyps(5) by simp
  have fresh: "send_fresh cfg p q m" by (rule causal_step_send.hyps(4))
  have no_old_send: "Send p k q m \<notin> events_of (cfg_hist cfg)" for k
    using fresh by (simp add: send_fresh_def)
  \<comment> \<open>By @{const recv_implies_send_inv}, no Receive at @{term q} for
      the new triple in @{term \<open>cfg_hist cfg\<close>}; freshness ensures
      none gets added in this step either.\<close>
  have pc': "p \<in> correct" by (rule causal_step_send.hyps(1))
  have qc': "q \<in> correct" by (rule causal_step_send.hyps(2))
  have no_recv_cfg: "\<not> (\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist cfg))"
  proof
    assume "\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist cfg)"
    with ris pc' qc'
    have "\<exists>ns. Send p ns q m \<in> events_of (cfg_hist cfg)"
      by (auto simp: recv_implies_send_inv_def)
    with no_old_send show False by blast
  qed
  have ev_iff: "events_of (cfg_hist cfg')
                  = events_of (cfg_hist cfg) \<union> {?ev}"
    using events_of_extend_iff[OF ext] .
  have no_recv_cfg': "\<not> (\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist cfg'))"
  proof
    assume "\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist cfg')"
    then obtain n' where
      "Receive q n' p m \<in> events_of (cfg_hist cfg')" by blast
    with ev_iff have "Receive q n' p m \<in> events_of (cfg_hist cfg)
                      \<or> Receive q n' p m = ?ev" by auto
    hence "Receive q n' p m \<in> events_of (cfg_hist cfg)" by auto
    with no_recv_cfg show False by blast
  qed
  have sink: "bhb_step_sink correct (cfg_hist cfg') ?ev"
    by (rule send_event_is_sink[OF wf ext causal_step_send.hyps(3) no_recv_cfg'])
  have proc_e: "proc_of ?ev = p" by simp
  have seq_e: "seq_of ?ev = Suc (length (cfg_hist cfg p))"
    using causal_step_send.hyps(3) by simp
  have ev_fresh: "?ev \<notin> events_of (cfg_hist cfg)"
    by (rule fresh_event_not_in_history[OF wf proc_e seq_e])
  show ?case using ext sink ev_fresh by blast
next
  case (causal_step_recv q p m cfg n cfg')
  have wf: "wf_history (cfg_hist cfg)"
    using causal_step_recv.prems unfolding causal_inv_def by simp
  let ?ev = "Receive q n p m"
  have ext: "hist_extend q ?ev (cfg_hist cfg) (cfg_hist cfg')"
    unfolding hist_extend_def using causal_step_recv.hyps(6) by simp
  have sink: "bhb_step_sink correct (cfg_hist cfg') ?ev"
    by (rule recv_event_is_sink[OF wf ext causal_step_recv.hyps(5)])
  have proc_e: "proc_of ?ev = q" by simp
  have seq_e: "seq_of ?ev = Suc (length (cfg_hist cfg q))"
    using causal_step_recv.hyps(5) by simp
  have ev_fresh: "?ev \<notin> events_of (cfg_hist cfg)"
    by (rule fresh_event_not_in_history[OF wf proc_e seq_e])
  show ?case using ext sink ev_fresh by blast
next
  case (causal_step_byzantine pb new_event cfg cfg')
  have wf: "wf_history (cfg_hist cfg)"
    using causal_step_byzantine.prems unfolding causal_inv_def by simp
  have ext: "hist_extend pb new_event (cfg_hist cfg) (cfg_hist cfg')"
    unfolding hist_extend_def using causal_step_byzantine.hyps(4) by simp
  have sink: "bhb_step_sink correct (cfg_hist cfg') new_event"
    by (rule byzantine_event_is_sink_correct[OF
                  causal_step_byzantine.hyps(1) causal_step_byzantine.hyps(2)])
  have ev_fresh: "new_event \<notin> events_of (cfg_hist cfg)"
    by (rule fresh_event_not_in_history[OF wf
                  causal_step_byzantine.hyps(2) causal_step_byzantine.hyps(3)])
  show ?case using ext sink ev_fresh by blast
qed

text \<open>Direct consequence: @{const bhb} between events of
@{term \<open>cfg_hist cfg\<close>} agrees in the pre- and post-states of a
@{const causal_run_step}.\<close>

lemma bhb_step_preserved_old_endpoints:
  assumes step: "causal_run_step cfg cfg'"
      and inv:  "causal_inv cfg"
      and bbe:  "bhb correct (cfg_hist cfg') e e'"
      and e_in: "e \<in> events_of (cfg_hist cfg)"
      and e'_in: "e' \<in> events_of (cfg_hist cfg)"
  shows "bhb correct (cfg_hist cfg) e e'"
proof -
  obtain p_new ev where
    ext: "hist_extend p_new ev (cfg_hist cfg) (cfg_hist cfg')" and
    sink: "bhb_step_sink correct (cfg_hist cfg') ev" and
    ev_fresh: "ev \<notin> events_of (cfg_hist cfg)"
    using causal_step_new_event_sink[OF step inv] by blast
  show ?thesis
    by (rule bhb_extend_down[OF ext sink bbe e_in e'_in ev_fresh])
qed

section \<open>BCB causal order under @{const bhb}\<close>

text \<open>The Byzantine-happened-before version of the BCB causal-order
property: for any two correct-to-correct Sends to the same correct
receiver @{term q}, if the sends are BHB-ordered then the matching
Receives at @{term q} are BHB-ordered, and indeed appear in @{term q}'s
local history at strictly increasing sequence numbers.\<close>

definition bhb_causal_order :: "'p set \<Rightarrow> 'p history \<Rightarrow> bool" where
  "bhb_causal_order C H \<longleftrightarrow>
     (\<forall>p1 n1 q m1 p2 n2 m2 nr1 nr2.
        p1 \<in> C \<and> p2 \<in> C \<and> q \<in> C \<and>
        Send p1 n1 q m1 \<in> events_of H \<and>
        Send p2 n2 q m2 \<in> events_of H \<and>
        Receive q nr1 p1 m1 \<in> events_of H \<and>
        Receive q nr2 p2 m2 \<in> events_of H \<and>
        bhb C H (Send p1 n1 q m1) (Send p2 n2 q m2)
        \<longrightarrow> bhb C H (Receive q nr1 p1 m1) (Receive q nr2 p2 m2))"

subsection \<open>Auxiliary: uniqueness of @{const hist_extend}\<close>

text \<open>If a history extends to another via two appended-event
descriptions, the appended @{term p_new} and @{term ev} must agree.
This lets us identify the abstract @{term p_new}/@{term ev} pulled
from @{thm causal_step_new_event_sink} with the rule-specific data
exposed by a case analysis on @{const causal_run_step}.\<close>

lemma hist_extend_unique:
  assumes ext1: "hist_extend p1 ev1 H H'"
      and ext2: "hist_extend p2 ev2 H H'"
  shows "p1 = p2 \<and> ev1 = ev2"
proof -
  have eq: "H(p1 := H p1 @ [ev1]) = H(p2 := H p2 @ [ev2])"
    using ext1 ext2 unfolding hist_extend_def by simp
  have p_eq: "p1 = p2"
  proof (rule ccontr)
    assume "p1 \<noteq> p2"
    have lhs: "(H(p1 := H p1 @ [ev1])) p2 = H p2"
      using \<open>p1 \<noteq> p2\<close> by simp
    have rhs: "(H(p2 := H p2 @ [ev2])) p2 = H p2 @ [ev2]"
      by simp
    from eq lhs rhs have "H p2 = H p2 @ [ev2]" by metis
    thus False by simp
  qed
  have ev_eq: "ev1 = ev2"
  proof -
    have step1: "(H(p1 := H p1 @ [ev1])) p1 = (H(p2 := H p2 @ [ev2])) p1"
      using eq by metis
    have lhs_eq: "(H(p1 := H p1 @ [ev1])) p1 = H p1 @ [ev1]" by simp
    have rhs_eq: "(H(p2 := H p2 @ [ev2])) p1 = H p2 @ [ev2]"
      using p_eq by simp
    from step1 lhs_eq rhs_eq have "H p1 @ [ev1] = H p2 @ [ev2]" by simp
    with p_eq show ?thesis by simp
  qed
  show ?thesis using p_eq ev_eq by simp
qed

text \<open>The recv-rule inversion helper.  Given a @{const causal_run_step}
whose @{const hist_extend} witness is a @{const Receive} at a correct
process, the step must have come from the \<open>causal_step_recv\<close>
rule with matching parameters.  This packages the four-case analysis
on the rule (used in \<open>recv_causal_step\<close> and \<open>recv_order_step\<close>
below) into a single lemma.\<close>

lemma causal_step_recv_inversion:
  assumes step: "causal_run_step cfg cfg'"
      and ext: "hist_extend p_new ev (cfg_hist cfg) (cfg_hist cfg')"
      and is_recv: "ev = Receive q n p m"
      and qc: "q \<in> correct"
  shows "p \<in> correct \<and> (p, q, m) \<in># cfg_inflight cfg \<and>
         causal_recv_ok cfg q p m \<and>
         n = Suc (length (cfg_hist cfg q)) \<and>
         p_new = q"
  using step
proof (cases rule: causal_run_step.cases)
  case (causal_step_internal p0 n0)
  have ext_int: "hist_extend p0 (Internal p0 n0)
                  (cfg_hist cfg) (cfg_hist cfg')"
    unfolding hist_extend_def using causal_step_internal by simp
  from hist_extend_unique[OF ext ext_int] is_recv
  show ?thesis by simp
next
  case (causal_step_send p1 q1 n1 m1)
  have ext_send: "hist_extend p1 (Send p1 n1 q1 m1)
                    (cfg_hist cfg) (cfg_hist cfg')"
    unfolding hist_extend_def using causal_step_send by simp
  from hist_extend_unique[OF ext ext_send] is_recv
  show ?thesis by simp
next
  case (causal_step_recv q0 p0 m0 n0)
  have ext_recv: "hist_extend q0 (Receive q0 n0 p0 m0)
                    (cfg_hist cfg) (cfg_hist cfg')"
    unfolding hist_extend_def using causal_step_recv by simp
  from hist_extend_unique[OF ext ext_recv]
  have pn_eq: "p_new = q0" and ev_eq: "ev = Receive q0 n0 p0 m0" by auto
  have q_match: "q = q0" and n_match: "n = n0"
    and p_match: "p = p0" and m_match: "m = m0"
    using ev_eq is_recv by auto
  show ?thesis
    using causal_step_recv pn_eq q_match n_match p_match m_match by simp
next
  case (causal_step_byzantine pb new_event)
  have ext_byz: "hist_extend pb new_event
                    (cfg_hist cfg) (cfg_hist cfg')"
    unfolding hist_extend_def using causal_step_byzantine by simp
  from hist_extend_unique[OF ext ext_byz]
  have ev_eq: "ev = new_event" by simp
  have proc_new: "proc_of new_event = pb"
    using causal_step_byzantine by simp
  have proc_ev: "proc_of ev = q" using is_recv by simp
  have q_eq_pb: "q = pb" using ev_eq proc_new proc_ev by simp
  have pby: "pb \<in> byzantine" using causal_step_byzantine by simp
  with qc q_eq_pb partition_disj show ?thesis by blast
qed

subsection \<open>Inductive invariants: @{text recv_causal_inv} and
@{text recv_order_inv}\<close>

text \<open>``If a correct-to-correct send has been received at
@{term q}, then every BHB-predecessor correct send to @{term q} has
also been received at @{term q}.''  This invariant is the inductive
counterpart of the causal precondition; it propagates the precondition
into the run history.\<close>

definition recv_causal_inv :: "'p config \<Rightarrow> bool" where
  "recv_causal_inv cfg \<longleftrightarrow>
     (\<forall>p ns q m. p \<in> correct \<longrightarrow> q \<in> correct \<longrightarrow>
        Send p ns q m \<in> events_of (cfg_hist cfg) \<longrightarrow>
        (\<exists>n. Receive q n p m \<in> events_of (cfg_hist cfg)) \<longrightarrow>
        (\<forall>p' ns' m'. p' \<in> correct \<longrightarrow>
           Send p' ns' q m' \<in> events_of (cfg_hist cfg) \<longrightarrow>
           bhb correct (cfg_hist cfg)
               (Send p' ns' q m') (Send p ns q m) \<longrightarrow>
           (\<exists>nr. Receive q nr p' m' \<in> events_of (cfg_hist cfg))))"

text \<open>``The Receive-at-correct-q sequence numbers respect the BHB
order of corresponding correct sends.''  This is the strong form of
BCB causal-order: BHB on sends $\Longrightarrow$ strict ordering of
matching Receives' local sequence numbers at @{term q}.\<close>

definition recv_order_inv :: "'p config \<Rightarrow> bool" where
  "recv_order_inv cfg \<longleftrightarrow>
     (\<forall>p1 n1 q m1 p2 n2 m2 nr1 nr2.
        p1 \<in> correct \<longrightarrow> p2 \<in> correct \<longrightarrow> q \<in> correct \<longrightarrow>
        Send p1 n1 q m1 \<in> events_of (cfg_hist cfg) \<longrightarrow>
        Send p2 n2 q m2 \<in> events_of (cfg_hist cfg) \<longrightarrow>
        Receive q nr1 p1 m1 \<in> events_of (cfg_hist cfg) \<longrightarrow>
        Receive q nr2 p2 m2 \<in> events_of (cfg_hist cfg) \<longrightarrow>
        bhb correct (cfg_hist cfg)
            (Send p1 n1 q m1) (Send p2 n2 q m2)
        \<longrightarrow> nr1 < nr2)"

text \<open>Helper: the local sequence number of a Receive event is
bounded by the length of @{term q}'s local list when the event is
recorded.  This is the wf-history packing of ``the seq number of an
event at position $k$ is @{term \<open>Suc k\<close>}''.\<close>

lemma recv_seq_bounded:
  assumes wf:  "wf_history H"
      and qc:  "q \<in> correct"
      and rev: "Receive q n p m \<in> events_of H"
  shows "n \<le> length (H q)"
proof -
  let ?ev = "Receive q n p m"
  have proc_ev: "proc_of ?ev = q" by simp
  from rev obtain p' where in_p': "?ev \<in> set (H p')"
    by (auto simp: events_of_def)
  have wfp': "wf_history_local p' (H p')"
    using wf unfolding wf_history_def by blast
  hence "proc_of ?ev = p'" using in_p' unfolding wf_history_local_def by blast
  with proc_ev have p'_eq: "p' = q" by simp
  from in_p' p'_eq obtain k where
    k_lt: "k < length (H q)" and nth_eq: "H q ! k = ?ev"
    by (auto simp: in_set_conv_nth)
  have wfp: "wf_history_local q (H q)"
    using wf unfolding wf_history_def by blast
  hence "seq_of (H q ! k) = Suc k"
    using k_lt unfolding wf_history_local_def by blast
  with nth_eq have "n = Suc k" by simp
  thus ?thesis using k_lt by simp
qed

subsection \<open>Preservation of @{const recv_causal_inv}\<close>

lemma recv_causal_step:
  assumes inv:  "recv_causal_inv cfg"
      and ji:   "causal_inv cfg"
      and step: "causal_run_step cfg cfg'"
  shows "recv_causal_inv cfg'"
proof -
  have wf: "wf_history (cfg_hist cfg)"
    using ji unfolding causal_inv_def by simp
  obtain p_new ev where
    ext: "hist_extend p_new ev (cfg_hist cfg) (cfg_hist cfg')" and
    sink: "bhb_step_sink correct (cfg_hist cfg') ev" and
    ev_fresh: "ev \<notin> events_of (cfg_hist cfg)"
    using causal_step_new_event_sink[OF step ji] by blast
  have ev_iff: "events_of (cfg_hist cfg')
                  = events_of (cfg_hist cfg) \<union> {ev}"
    using events_of_extend_iff[OF ext] .
  have su: "send_unique_inv cfg" using ji unfolding causal_inv_def by simp
  show ?thesis
  proof (unfold recv_causal_inv_def, intro allI impI)
    fix p ns q m p' ns' m'
    assume pc: "p \<in> correct" and qc: "q \<in> correct"
       and pc': "p' \<in> correct"
       and send_pq: "Send p ns q m \<in> events_of (cfg_hist cfg')"
       and ex_rev: "\<exists>n. Receive q n p m \<in> events_of (cfg_hist cfg')"
       and send_xq: "Send p' ns' q m' \<in> events_of (cfg_hist cfg')"
       and bhbs: "bhb correct (cfg_hist cfg')
                      (Send p' ns' q m') (Send p ns q m)"
    show "\<exists>nr. Receive q nr p' m' \<in> events_of (cfg_hist cfg')"
    proof -
      \<comment> \<open>Both Sends are in @{term \<open>cfg_hist cfg\<close>}: the only step
          that adds a Send to a correct-process history is
          \<open>causal_step_send\<close>, in which case the new event @{term ev}
          is a Send; and @{term \<open>send_pq\<close>}, @{term \<open>send_xq\<close>} cannot
          both equal @{term ev}'s @{term \<open>p_new\<close>}-Send unless they
          coincide -- but @{term bhbs} forbids reflexivity in @{const bhb}.
          We carefully treat the cases.\<close>
      have send_pq_old: "Send p ns q m \<in> events_of (cfg_hist cfg)"
      proof -
        from send_pq ev_iff have "Send p ns q m \<in> events_of (cfg_hist cfg)
                                 \<or> Send p ns q m = ev" by auto
        thus ?thesis
        proof
          assume "Send p ns q m = ev"
          \<comment> \<open>Then the matching Receive @{term \<open>ex_rev\<close>} would, by
              freshness of the just-added Send (since
              @{term \<open>ev = Send p ns q m\<close>} and no prior such send),
              not exist in @{term cfg}; and adding @{term ev} as a
              Send does not introduce any Receive into @{term cfg'}.\<close>
          from \<open>Send p ns q m = ev\<close> ex_rev
          obtain n where rev_in: "Receive q n p m \<in> events_of (cfg_hist cfg')" by blast
          have neq_send_recv: "Receive q n p m \<noteq> ev"
            using \<open>Send p ns q m = ev\<close> by auto
          from rev_in ev_iff neq_send_recv
          have "Receive q n p m \<in> events_of (cfg_hist cfg)" by auto
          \<comment> \<open>By @{const recv_implies_send_inv}, this forces a Send for
              @{term \<open>(p, m)\<close>} in @{term \<open>cfg_hist cfg\<close>}, but the new
              Send is exactly @{term \<open>Send p ns q m\<close>}, and freshness
              of \<open>causal_step_send\<close> forbids any prior such Send.
              Hence contradiction.\<close>
          have ris: "recv_implies_send_inv cfg"
            using ji unfolding causal_inv_def by simp
          have ex_rev_in: "\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist cfg)"
            using \<open>Receive q n p m \<in> events_of (cfg_hist cfg)\<close> by blast
          from ris pc qc ex_rev_in
          have "\<exists>k. Send p k q m \<in> events_of (cfg_hist cfg)"
            by (auto simp: recv_implies_send_inv_def)
          then obtain k where "Send p k q m \<in> events_of (cfg_hist cfg)" by blast
          \<comment> \<open>This Send is also in @{term \<open>cfg_hist cfg'\<close>}, hence by
              @{const send_unique_inv} on @{term \<open>cfg'\<close>} (which holds
              by step-level preservation), @{term k} equals @{term ns}.
              But then @{term \<open>Send p ns q m \<in> events_of (cfg_hist cfg)\<close>},
              contradicting freshness via @{term \<open>ev_fresh\<close>}.\<close>
          have "Send p k q m = ev"
          proof -
            \<comment> \<open>By send-uniqueness on @{term cfg'}, only one Send for
                @{term \<open>(p, m)\<close>} exists.  The new one is @{term ev};
                if @{term \<open>Send p k q m\<close>} is different, we'd have two
                in @{term \<open>cfg'\<close>}.\<close>
            have "Send p k q m \<in> events_of (cfg_hist cfg')"
              using \<open>Send p k q m \<in> events_of (cfg_hist cfg)\<close> ev_iff by auto
            \<comment> \<open>Apply send-unique to deduce @{term \<open>k = ns\<close>}.\<close>
            have su': "send_unique_inv cfg'"
              by (rule send_unique_step[OF su step])
            from su' pc qc
              \<open>Send p k q m \<in> events_of (cfg_hist cfg')\<close>
              \<open>Send p ns q m \<in> events_of (cfg_hist cfg')\<close>
            have "k = ns" by (auto simp: send_unique_inv_def)
            with \<open>Send p ns q m = ev\<close> show ?thesis by simp
          qed
          with \<open>Send p k q m \<in> events_of (cfg_hist cfg)\<close> ev_fresh
          show ?thesis by simp
        qed
      qed
      have send_xq_old: "Send p' ns' q m' \<in> events_of (cfg_hist cfg)"
      proof -
        from send_xq ev_iff have "Send p' ns' q m' \<in> events_of (cfg_hist cfg)
                                 \<or> Send p' ns' q m' = ev" by auto
        thus ?thesis
        proof
          assume eq: "Send p' ns' q m' = ev"
          \<comment> \<open>@{term \<open>Send p' ns' q m'\<close>} is the just-added event.  It
              must be a @{const bhb} sink in @{term \<open>cfg_hist cfg'\<close>}
              (by @{thm sink}), but @{term bhbs} has it as a source.
              Contradiction.\<close>
          \<comment> \<open>Strictly speaking, @{thm sink} forbids @{const bhb_step},
              but @{const bhb} starts with a @{const bhb_step}, so the
              first step of any chain from @{term ev} would be a
              @{const bhb_step} from @{term ev}, which is forbidden.\<close>
          from bhbs have "(bhb_step correct (cfg_hist cfg'))\<^sup>+\<^sup>+
                            (Send p' ns' q m') (Send p ns q m)"
            unfolding bhb_def by simp
          then obtain z where
            first_step: "bhb_step correct (cfg_hist cfg') (Send p' ns' q m') z"
            by (induction rule: tranclp_induct) auto
          from eq first_step sink show ?thesis
            unfolding bhb_step_sink_def by blast
        qed
      qed
      \<comment> \<open>Apply restriction-down to bring the @{const bhb} chain into
          @{term \<open>cfg_hist cfg\<close>}, then apply the IH or the precondition.\<close>
      have bhb_old: "bhb correct (cfg_hist cfg)
                        (Send p' ns' q m') (Send p ns q m)"
        by (rule bhb_step_preserved_old_endpoints[OF step ji bhbs send_xq_old send_pq_old])
      \<comment> \<open>The existential receive: either the @{term ex_rev} witness
          is the new event @{term ev} (only possible if @{term ev}
          is a Receive for @{term \<open>(p, m)\<close>}) or it is in
          @{term \<open>cfg_hist cfg\<close>}.\<close>
      from ex_rev obtain n where rev_n: "Receive q n p m \<in> events_of (cfg_hist cfg')"
        by blast
      have rev_n_old: "\<exists>n. Receive q n p m \<in> events_of (cfg_hist cfg)
                          \<or> ev = Receive q n p m"
      proof -
        from rev_n ev_iff have "Receive q n p m \<in> events_of (cfg_hist cfg)
                                \<or> Receive q n p m = ev" by auto
        thus ?thesis by auto
      qed
      show "\<exists>nr. Receive q nr p' m' \<in> events_of (cfg_hist cfg')"
      proof (cases "\<exists>n. Receive q n p m \<in> events_of (cfg_hist cfg)")
        case True
        \<comment> \<open>Apply IH @{thm inv}.\<close>
        from inv have
          "p \<in> correct \<longrightarrow> q \<in> correct \<longrightarrow>
            Send p ns q m \<in> events_of (cfg_hist cfg) \<longrightarrow>
            (\<exists>n. Receive q n p m \<in> events_of (cfg_hist cfg)) \<longrightarrow>
            (\<forall>p'' ns'' m''. p'' \<in> correct \<longrightarrow>
               Send p'' ns'' q m'' \<in> events_of (cfg_hist cfg) \<longrightarrow>
               bhb correct (cfg_hist cfg)
                   (Send p'' ns'' q m'') (Send p ns q m) \<longrightarrow>
               (\<exists>nr. Receive q nr p'' m'' \<in> events_of (cfg_hist cfg)))"
          unfolding recv_causal_inv_def by blast
        with pc qc send_pq_old True
        have univ: "\<forall>p'' ns'' m''. p'' \<in> correct \<longrightarrow>
                      Send p'' ns'' q m'' \<in> events_of (cfg_hist cfg) \<longrightarrow>
                      bhb correct (cfg_hist cfg)
                          (Send p'' ns'' q m'') (Send p ns q m) \<longrightarrow>
                      (\<exists>nr. Receive q nr p'' m'' \<in> events_of (cfg_hist cfg))"
          by blast
        from univ pc' send_xq_old bhb_old
        have "\<exists>nr. Receive q nr p' m' \<in> events_of (cfg_hist cfg)"
          by blast
        then obtain nr where
          "Receive q nr p' m' \<in> events_of (cfg_hist cfg)" by blast
        hence "Receive q nr p' m' \<in> events_of (cfg_hist cfg')"
          using ev_iff by auto
        thus ?thesis by blast
      next
        case False
        \<comment> \<open>Then the only matching Receive for @{term \<open>(p, m)\<close>} is
            @{term ev}, hence @{term ev} = @{term \<open>Receive q n p m\<close>}.
            We invoke the @{const causal_recv_ok} premise of the
            \<open>causal_step_recv\<close> rule for the conclusion.\<close>
        from rev_n_old False have ev_is_recv: "ev = Receive q n p m"
          using rev_n ev_iff by auto
        \<comment> \<open>We need to invert @{thm step} to be a \<open>causal_step_recv\<close>
            with the matching triple, and pull out the @{const causal_recv_ok}
            premise.\<close>
        from causal_step_recv_inversion[OF step ext ev_is_recv qc]
        have ok: "causal_recv_ok cfg q p m" by simp
        hence "\<exists>ns0. Send p ns0 q m \<in> events_of (cfg_hist cfg) \<and>
              (\<forall>p'' ns'' m''. p'' \<in> correct \<longrightarrow>
                 Send p'' ns'' q m'' \<in> events_of (cfg_hist cfg) \<longrightarrow>
                 bhb correct (cfg_hist cfg)
                     (Send p'' ns'' q m'') (Send p ns0 q m) \<longrightarrow>
                 (\<exists>nr. Receive q nr p'' m'' \<in> events_of (cfg_hist cfg)))"
          unfolding causal_recv_ok_def by simp
        then obtain ns0 where
          send_pns0: "Send p ns0 q m \<in> events_of (cfg_hist cfg)" and
          univ: "\<forall>p'' ns'' m''. p'' \<in> correct \<longrightarrow>
                   Send p'' ns'' q m'' \<in> events_of (cfg_hist cfg) \<longrightarrow>
                   bhb correct (cfg_hist cfg)
                       (Send p'' ns'' q m'') (Send p ns0 q m) \<longrightarrow>
                   (\<exists>nr. Receive q nr p'' m'' \<in> events_of (cfg_hist cfg))"
          by blast
        \<comment> \<open>By send-uniqueness on @{term cfg}, @{term ns0} equals @{term ns}.\<close>
        from su pc qc send_pns0 send_pq_old
        have ns_eq: "ns0 = ns" by (auto simp: send_unique_inv_def)
        from univ pc' send_xq_old bhb_old ns_eq
        have "\<exists>nr. Receive q nr p' m' \<in> events_of (cfg_hist cfg)"
          by metis
        then obtain nr where
          "Receive q nr p' m' \<in> events_of (cfg_hist cfg)" by blast
        hence "Receive q nr p' m' \<in> events_of (cfg_hist cfg')"
          using ev_iff by auto
        thus ?thesis by blast
      qed
    qed
  qed
qed

subsection \<open>Preservation of @{const recv_order_inv}\<close>

lemma recv_order_step:
  assumes inv:  "recv_order_inv cfg"
      and rci:  "recv_causal_inv cfg"
      and ji:   "causal_inv cfg"
      and step: "causal_run_step cfg cfg'"
  shows "recv_order_inv cfg'"
proof -
  have wf: "wf_history (cfg_hist cfg)"
    using ji unfolding causal_inv_def by simp
  obtain p_new ev where
    ext: "hist_extend p_new ev (cfg_hist cfg) (cfg_hist cfg')" and
    sink: "bhb_step_sink correct (cfg_hist cfg') ev" and
    ev_fresh: "ev \<notin> events_of (cfg_hist cfg)"
    using causal_step_new_event_sink[OF step ji] by blast
  have ev_iff: "events_of (cfg_hist cfg')
                  = events_of (cfg_hist cfg) \<union> {ev}"
    using events_of_extend_iff[OF ext] .
  show ?thesis
  proof (unfold recv_order_inv_def, intro allI impI)
    fix p1 n1 q m1 p2 n2 m2 nr1 nr2
    assume p1c: "p1 \<in> correct" and p2c: "p2 \<in> correct" and qc: "q \<in> correct"
       and s1: "Send p1 n1 q m1 \<in> events_of (cfg_hist cfg')"
       and s2: "Send p2 n2 q m2 \<in> events_of (cfg_hist cfg')"
       and r1: "Receive q nr1 p1 m1 \<in> events_of (cfg_hist cfg')"
       and r2: "Receive q nr2 p2 m2 \<in> events_of (cfg_hist cfg')"
       and bhbs: "bhb correct (cfg_hist cfg')
                       (Send p1 n1 q m1) (Send p2 n2 q m2)"
    show "nr1 < nr2"
    proof -
      \<comment> \<open>Both Sends are in @{term \<open>cfg_hist cfg\<close>} (analogue of
          the @{text send_pq_old}, @{text send_xq_old} arguments above).\<close>
      have s1_old: "Send p1 n1 q m1 \<in> events_of (cfg_hist cfg)"
      proof -
        from s1 ev_iff have or_cases: "Send p1 n1 q m1 \<in> events_of (cfg_hist cfg)
                                       \<or> Send p1 n1 q m1 = ev" by auto
        thus ?thesis
        proof
          assume eq: "Send p1 n1 q m1 = ev"
          from bhbs have "(bhb_step correct (cfg_hist cfg'))\<^sup>+\<^sup>+
                            (Send p1 n1 q m1) (Send p2 n2 q m2)"
            unfolding bhb_def by simp
          then obtain z where
            first_step: "bhb_step correct (cfg_hist cfg') (Send p1 n1 q m1) z"
            by (induction rule: tranclp_induct) auto
          from eq first_step sink show ?thesis
            unfolding bhb_step_sink_def by blast
        qed
      qed
      \<comment> \<open>@{term \<open>Send p2 n2 q m2\<close>} also old: it has the new Receive
          @{term \<open>Receive q nr2 p2 m2\<close>} as a Receive at @{term q}.
          If @{term \<open>Send p2 n2 q m2 = ev\<close>}, then @{term ev} is the
          new Send.  By @{text sink}, no @{const bhb_step} chain starts
          at @{term ev}.  But @{text bhbs} has it as a target, not a
          source, so this is consistent.  We need to rule out
          @{term \<open>Send p2 n2 q m2 = ev\<close>} by a different argument:
          the matching Receive @{term \<open>Receive q nr2 p2 m2\<close>} exists,
          but by recv-implies-send + send-freshness, no Receive for
          @{term \<open>(p2, m2)\<close>} could exist before adding @{term ev} as
          the Send, and adding the Send doesn't add Receives.\<close>
      have s2_old: "Send p2 n2 q m2 \<in> events_of (cfg_hist cfg)"
      proof -
        from s2 ev_iff have or_cases: "Send p2 n2 q m2 \<in> events_of (cfg_hist cfg)
                                       \<or> Send p2 n2 q m2 = ev" by auto
        thus ?thesis
        proof
          assume eq: "Send p2 n2 q m2 = ev"
          \<comment> \<open>@{term r2} gives a matching Receive in @{term \<open>cfg'\<close>}.\<close>
          from r2 ev_iff
          have "Receive q nr2 p2 m2 \<in> events_of (cfg_hist cfg)
                \<or> Receive q nr2 p2 m2 = ev" by auto
          hence "Receive q nr2 p2 m2 \<in> events_of (cfg_hist cfg)"
            using eq by auto
          \<comment> \<open>Recv-implies-send on @{term cfg} forces a Send for
              @{term \<open>(p2, m2)\<close>} in @{term cfg}, but @{term \<open>ev\<close>}
              is the new Send and freshness says no prior such Send.\<close>
          have ris: "recv_implies_send_inv cfg"
            using ji unfolding causal_inv_def by simp
          have ex_rev_p2: "\<exists>n'. Receive q n' p2 m2 \<in> events_of (cfg_hist cfg)"
            using \<open>Receive q nr2 p2 m2 \<in> events_of (cfg_hist cfg)\<close> by blast
          from ris p2c qc ex_rev_p2
          have "\<exists>k. Send p2 k q m2 \<in> events_of (cfg_hist cfg)"
            by (auto simp: recv_implies_send_inv_def)
          then obtain k where
            send_k_in: "Send p2 k q m2 \<in> events_of (cfg_hist cfg)" by blast
          \<comment> \<open>The new event @{term ev} = @{term \<open>Send p2 n2 q m2\<close>}; by
              send-uniqueness in @{term \<open>cfg'\<close>}, @{term k} = @{term n2}.\<close>
          have "Send p2 k q m2 \<in> events_of (cfg_hist cfg')"
            using send_k_in ev_iff by auto
          have su_local: "send_unique_inv cfg"
            using ji unfolding causal_inv_def by simp
          have su': "send_unique_inv cfg'"
            by (rule send_unique_step[OF su_local step])
          from su' p2c qc
            \<open>Send p2 k q m2 \<in> events_of (cfg_hist cfg')\<close>
            s2
          have "k = n2" by (auto simp: send_unique_inv_def)
          with send_k_in eq ev_fresh show ?thesis by auto
        qed
      qed
      have bhb_old: "bhb correct (cfg_hist cfg)
                        (Send p1 n1 q m1) (Send p2 n2 q m2)"
        by (rule bhb_step_preserved_old_endpoints[OF step ji bhbs s1_old s2_old])
      \<comment> \<open>Case analysis on whether each Receive is the new event.\<close>
      have r1_or: "Receive q nr1 p1 m1 \<in> events_of (cfg_hist cfg)
                   \<or> Receive q nr1 p1 m1 = ev"
        using r1 ev_iff by auto
      have r2_or: "Receive q nr2 p2 m2 \<in> events_of (cfg_hist cfg)
                   \<or> Receive q nr2 p2 m2 = ev"
        using r2 ev_iff by auto
      show "nr1 < nr2"
      proof (cases "Receive q nr1 p1 m1 \<in> events_of (cfg_hist cfg)")
        case r1_in_cfg: True
        show ?thesis
        proof (cases "Receive q nr2 p2 m2 \<in> events_of (cfg_hist cfg)")
          case r2_in_cfg: True
          \<comment> \<open>Case A: both Receives old.\<close>
          from inv p1c p2c qc s1_old s2_old r1_in_cfg r2_in_cfg bhb_old
          show ?thesis
            by (auto simp: recv_order_inv_def)
        next
          case r2_new: False
          \<comment> \<open>Case B: @{term r2} is the new Receive.\<close>
          from r2_or r2_new have ev_is_r2: "ev = Receive q nr2 p2 m2" by auto
          \<comment> \<open>Bound @{term nr1} by length of @{term q}'s local list in
              @{term cfg}, and equate @{term nr2} with the next seq
              number.\<close>
          have nr1_le: "nr1 \<le> length (cfg_hist cfg q)"
            by (rule recv_seq_bounded[OF wf qc r1_in_cfg])
          \<comment> \<open>Inversion via @{thm causal_step_recv_inversion}: the
              recv-rule sets @{term nr2} to the next sequence number
              at @{term q}.\<close>
          have nr2_eq: "nr2 = Suc (length (cfg_hist cfg q))"
            using causal_step_recv_inversion[OF step ext ev_is_r2 qc]
            by simp
          show ?thesis using nr1_le nr2_eq by linarith
        qed
      next
        case r1_new: False
        from r1_or r1_new have ev_is_r1: "ev = Receive q nr1 p1 m1" by auto
        \<comment> \<open>Case C: @{term r1} is the new Receive.  We derive a
            contradiction using @{const recv_causal_inv} on @{term cfg}
            and @{const delivered_drained_inv}.\<close>
        \<comment> \<open>From the recv-rule inversion: triple
            @{term \<open>(p1, q, m1)\<close>} is in @{term cfg}'s buffer.\<close>
        have buf_in: "(p1, q, m1) \<in># cfg_inflight cfg"
          using causal_step_recv_inversion[OF step ext ev_is_r1 qc]
          by simp
        \<comment> \<open>Whether @{term r2} is in @{term cfg} (subcase C1) or
            coincides with the new event @{term ev} (subcase C2),
            we derive a matching Receive for @{term \<open>(p1, m1)\<close>} in
            @{term cfg} -- via @{const recv_causal_inv} in the first
            case, or via @{const causal_recv_ok}'s self-loop instance
            in the second.\<close>
        have ex_recv:
          "\<exists>nr. Receive q nr p1 m1 \<in> events_of (cfg_hist cfg)"
        proof (cases "Receive q nr2 p2 m2 \<in> events_of (cfg_hist cfg)")
          case True
          \<comment> \<open>Subcase C1: @{term r2} is in @{term cfg}.\<close>
          from rci p2c qc s2_old
          have rci_inst: "(\<exists>n. Receive q n p2 m2 \<in> events_of (cfg_hist cfg))
                \<longrightarrow> (\<forall>p' ns' m'. p' \<in> correct \<longrightarrow>
                      Send p' ns' q m' \<in> events_of (cfg_hist cfg) \<longrightarrow>
                      bhb correct (cfg_hist cfg)
                          (Send p' ns' q m') (Send p2 n2 q m2) \<longrightarrow>
                      (\<exists>nr. Receive q nr p' m' \<in> events_of (cfg_hist cfg)))"
            unfolding recv_causal_inv_def by blast
          from rci_inst True
          have all_pred: "\<forall>p' ns' m'. p' \<in> correct \<longrightarrow>
                Send p' ns' q m' \<in> events_of (cfg_hist cfg) \<longrightarrow>
                bhb correct (cfg_hist cfg)
                    (Send p' ns' q m') (Send p2 n2 q m2) \<longrightarrow>
                (\<exists>nr. Receive q nr p' m' \<in> events_of (cfg_hist cfg))"
            by blast
          from all_pred p1c s1_old bhb_old show ?thesis by blast
        next
          case False
          \<comment> \<open>Subcase C2: @{term r2} coincides with the new event @{term ev}.\<close>
          have r2_eq_ev: "Receive q nr2 p2 m2 = ev"
            using r2_or False by auto
          with ev_is_r1 have
            p_match: "p2 = p1" and m_match: "m2 = m1"
            and nr_match: "nr2 = nr1" by auto
          \<comment> \<open>By send-uniqueness on @{term cfg}, @{term n1} and @{term n2}
              agree, so the antecedent's @{const bhb} chain is a
              self-loop on @{term \<open>Send p1 n1 q m1\<close>}.\<close>
          have s2_eq: "Send p2 n2 q m2 = Send p1 n2 q m1"
            using p_match m_match by simp
          have su: "send_unique_inv cfg"
            using ji unfolding causal_inv_def by simp
          have n_eq: "n1 = n2"
          proof -
            have "Send p1 n2 q m1 \<in> events_of (cfg_hist cfg)"
              using s2_old s2_eq by simp
            with su p1c qc s1_old
            show "n1 = n2" by (auto simp: send_unique_inv_def)
          qed
          have send_eq: "Send p1 n1 q m1 = Send p2 n2 q m2"
            using n_eq p_match m_match by simp
          have self_loop: "bhb correct (cfg_hist cfg)
                            (Send p1 n1 q m1) (Send p1 n1 q m1)"
            using bhb_old send_eq by simp
          \<comment> \<open>Recover @{const causal_recv_ok} for the new event via
              the recv-rule inversion helper.\<close>
          have ok: "causal_recv_ok cfg q p1 m1"
            using causal_step_recv_inversion[OF step ext ev_is_r1 qc]
            by simp
          from ok obtain ns0 where
            send_p1_ns0: "Send p1 ns0 q m1 \<in> events_of (cfg_hist cfg)" and
            univ: "\<forall>p'' ns'' m''. p'' \<in> correct \<longrightarrow>
                     Send p'' ns'' q m'' \<in> events_of (cfg_hist cfg) \<longrightarrow>
                     bhb correct (cfg_hist cfg)
                         (Send p'' ns'' q m'') (Send p1 ns0 q m1) \<longrightarrow>
                     (\<exists>nr. Receive q nr p'' m'' \<in> events_of (cfg_hist cfg))"
            unfolding causal_recv_ok_def by auto
          \<comment> \<open>By send-uniqueness, @{term ns0} agrees with @{term n1}.\<close>
          have ns0_eq: "ns0 = n1"
            using su p1c qc s1_old send_p1_ns0
            by (auto simp: send_unique_inv_def)
          have self_loop2:
            "bhb correct (cfg_hist cfg) (Send p1 n1 q m1) (Send p1 ns0 q m1)"
            using self_loop ns0_eq by simp
          from univ p1c s1_old self_loop2
          show ?thesis by blast
        qed
        \<comment> \<open>Final contradiction: @{const delivered_drained_inv} + @{term buf_in}.\<close>
        have dd: "delivered_drained_inv cfg"
          using ji unfolding causal_inv_def by simp
        from dd p1c qc ex_recv
        have not_buf: "\<not> (p1, q, m1) \<in># cfg_inflight cfg"
          by (auto simp: delivered_drained_inv_def)
        from not_buf buf_in show ?thesis by simp
      qed
    qed
  qed
qed

subsection \<open>Initial values of the new invariants and joint preservation\<close>

lemma recv_causal_inv_init [simp]:
  "recv_causal_inv init_config"
  by (simp add: recv_causal_inv_def init_config_def events_of_def)

lemma recv_order_inv_init [simp]:
  "recv_order_inv init_config"
  by (simp add: recv_order_inv_def init_config_def events_of_def)

definition full_causal_inv :: "'p config \<Rightarrow> bool" where
  "full_causal_inv cfg \<longleftrightarrow>
     causal_inv cfg \<and>
     recv_causal_inv cfg \<and>
     recv_order_inv cfg"

lemma full_causal_inv_init [simp]: "full_causal_inv init_config"
  by (simp add: full_causal_inv_def)

lemma full_causal_inv_step:
  assumes inv:  "full_causal_inv cfg"
      and step: "causal_run_step cfg cfg'"
  shows "full_causal_inv cfg'"
proof -
  have ji: "causal_inv cfg" using inv unfolding full_causal_inv_def by simp
  have rci: "recv_causal_inv cfg" using inv unfolding full_causal_inv_def by simp
  have roi: "recv_order_inv cfg" using inv unfolding full_causal_inv_def by simp
  have ji': "causal_inv cfg'" by (rule causal_inv_step[OF ji step])
  have rci': "recv_causal_inv cfg'" by (rule recv_causal_step[OF rci ji step])
  have roi': "recv_order_inv cfg'" by (rule recv_order_step[OF roi rci ji step])
  show ?thesis unfolding full_causal_inv_def
    using ji' rci' roi' by simp
qed

lemma full_causal_inv_run:
  assumes "causal_run cfg"
  shows "full_causal_inv cfg"
  using assms unfolding causal_run_def
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from full_causal_inv_step[OF step.IH step.hyps(2)]
  show ?case .
qed

lemma recv_causal_run:
  assumes "causal_run cfg"
  shows "recv_causal_inv cfg"
  using full_causal_inv_run[OF assms] unfolding full_causal_inv_def by simp

lemma recv_order_run:
  assumes "causal_run cfg"
  shows "recv_order_inv cfg"
  using full_causal_inv_run[OF assms] unfolding full_causal_inv_def by simp

section \<open>BCB causal-order theorem at any @{const causal_run} configuration\<close>

text \<open>At any configuration reachable via @{const causal_run},
@{const bhb_causal_order} holds for the correct set.  The proof
extracts @{const recv_order_inv} (which gives strict sequence-number
ordering at the correct receiver) and lifts it to @{const bhb} via
@{const program_order} at the receiver.\<close>

theorem causal_run_satisfies_bhb_causal_order:
  assumes "causal_run cfg"
  shows "bhb_causal_order correct (cfg_hist cfg)"
proof -
  have roi: "recv_order_inv cfg" by (rule recv_order_run[OF assms])
  have ji: "causal_inv cfg" using full_causal_inv_run[OF assms]
    unfolding full_causal_inv_def by simp
  have wf: "wf_history (cfg_hist cfg)"
    using ji unfolding causal_inv_def by simp
  show ?thesis
  proof (unfold bhb_causal_order_def, intro allI impI)
    fix p1 n1 q m1 p2 n2 m2 nr1 nr2
    assume H: "p1 \<in> correct \<and> p2 \<in> correct \<and> q \<in> correct \<and>
               Send p1 n1 q m1 \<in> events_of (cfg_hist cfg) \<and>
               Send p2 n2 q m2 \<in> events_of (cfg_hist cfg) \<and>
               Receive q nr1 p1 m1 \<in> events_of (cfg_hist cfg) \<and>
               Receive q nr2 p2 m2 \<in> events_of (cfg_hist cfg) \<and>
               bhb correct (cfg_hist cfg)
                   (Send p1 n1 q m1) (Send p2 n2 q m2)"
    \<comment> \<open>Extract strict seq-number ordering at @{term q}.\<close>
    from H roi
    have nr_lt: "nr1 < nr2" by (auto simp: recv_order_inv_def)
    \<comment> \<open>Build a program-order step at @{term q}.\<close>
    have qc: "q \<in> correct" using H by simp
    let ?r1 = "Receive q nr1 p1 m1"
    let ?r2 = "Receive q nr2 p2 m2"
    have r1_in: "?r1 \<in> events_of (cfg_hist cfg)" using H by simp
    have r2_in: "?r2 \<in> events_of (cfg_hist cfg)" using H by simp
    \<comment> \<open>Position of each receive in @{term q}'s local list, as a
        position index together with @{term \<open>nr = Suc k\<close>}.\<close>
    have r1_pos: "\<exists>k1. cfg_hist cfg q ! k1 = ?r1 \<and>
                       k1 < length (cfg_hist cfg q) \<and> nr1 = Suc k1"
    proof -
      from r1_in obtain p' where in_p': "?r1 \<in> set (cfg_hist cfg p')"
        by (auto simp: events_of_def)
      have wfp': "wf_history_local p' (cfg_hist cfg p')"
        using wf unfolding wf_history_def by blast
      have "proc_of ?r1 = p'" using wfp' in_p'
        unfolding wf_history_local_def by blast
      hence p'_eq: "p' = q" by simp
      from in_p' p'_eq obtain k where
        k_lt: "k < length (cfg_hist cfg q)" and
        nth_eq: "cfg_hist cfg q ! k = ?r1" by (auto simp: in_set_conv_nth)
      have wfp: "wf_history_local q (cfg_hist cfg q)"
        using wf unfolding wf_history_def by blast
      hence "seq_of (cfg_hist cfg q ! k) = Suc k"
        using k_lt unfolding wf_history_local_def by blast
      with nth_eq have "nr1 = Suc k" by simp
      with k_lt nth_eq show ?thesis by blast
    qed
    have r2_pos: "\<exists>k2. cfg_hist cfg q ! k2 = ?r2 \<and>
                       k2 < length (cfg_hist cfg q) \<and> nr2 = Suc k2"
    proof -
      from r2_in obtain p' where in_p': "?r2 \<in> set (cfg_hist cfg p')"
        by (auto simp: events_of_def)
      have wfp': "wf_history_local p' (cfg_hist cfg p')"
        using wf unfolding wf_history_def by blast
      have "proc_of ?r2 = p'" using wfp' in_p'
        unfolding wf_history_local_def by blast
      hence p'_eq: "p' = q" by simp
      from in_p' p'_eq obtain k where
        k_lt: "k < length (cfg_hist cfg q)" and
        nth_eq: "cfg_hist cfg q ! k = ?r2" by (auto simp: in_set_conv_nth)
      have wfp: "wf_history_local q (cfg_hist cfg q)"
        using wf unfolding wf_history_def by blast
      hence "seq_of (cfg_hist cfg q ! k) = Suc k"
        using k_lt unfolding wf_history_local_def by blast
      with nth_eq have "nr2 = Suc k" by simp
      with k_lt nth_eq show ?thesis by blast
    qed
    \<comment> \<open>Use positions to assemble a one-step BHB chain.\<close>
    from r1_pos obtain k1 where
      k1_in: "cfg_hist cfg q ! k1 = ?r1" and
      k1_lt: "k1 < length (cfg_hist cfg q)" and nr1_eq: "nr1 = Suc k1" by blast
    from r2_pos obtain k2 where
      k2_in: "cfg_hist cfg q ! k2 = ?r2" and
      k2_lt: "k2 < length (cfg_hist cfg q)" and nr2_eq: "nr2 = Suc k2" by blast
    have idx_lt: "k1 < k2" using nr_lt nr1_eq nr2_eq by simp
    have po: "program_order (cfg_hist cfg) ?r1 ?r2"
      unfolding program_order_def
      using k1_in k2_in k1_lt k2_lt idx_lt by blast
    have proc_r1: "proc_of ?r1 = q" by simp
    have proc_r2: "proc_of ?r2 = q" by simp
    have bhbs1: "bhb_step correct (cfg_hist cfg) ?r1 ?r2"
      unfolding bhb_step_def hb_step_def
      using qc proc_r1 proc_r2 po by simp
    have "bhb correct (cfg_hist cfg) ?r1 ?r2"
      unfolding bhb_def using bhbs1 by blast
    thus "bhb correct (cfg_hist cfg)
              (Receive q nr1 p1 m1) (Receive q nr2 p2 m2)"
      by simp
  qed
qed

section \<open>End-to-end: causal\<open>_run\<close> discharges BCB over BRB\<close>

text \<open>BCB-over-BRB at the BHB layer: a history satisfying both
@{const bru_satisfied} (BRU) and @{const bhb_causal_order} (the
correct-chain version of BCB) realises BCB operationally.  We
introduce a named predicate parallel to
@{const bcb_over_brb_satisfied} (from @{theory_text \<open>Primitives.thy\<close>},
which uses plain @{const hb}) so the operational discharge has its
own name aligned with paper Definition 3.\<close>

definition bhb_over_brb_satisfied :: "'p set \<Rightarrow> 'p history \<Rightarrow> bool" where
  "bhb_over_brb_satisfied C H \<longleftrightarrow>
     bru_satisfied H \<and> bhb_causal_order C H"

lemma bhb_over_brb_implies_bru:
  assumes "bhb_over_brb_satisfied C H"
  shows   "bru_satisfied H"
  using assms by (simp add: bhb_over_brb_satisfied_def)

lemma bhb_over_brb_implies_bhb_causal_order:
  assumes "bhb_over_brb_satisfied C H"
  shows   "bhb_causal_order C H"
  using assms by (simp add: bhb_over_brb_satisfied_def)

text \<open>A drained @{const causal_run} produces a history satisfying
@{const bhb_over_brb_satisfied}.  This is the operational discharge
of BCB-over-BRB that @{theory_text \<open>Primitives.thy\<close>} threads as a
hypothesis.\<close>

theorem causal_run_satisfies_bhb_over_brb:
  assumes run_cfg: "causal_run cfg"
      and drained: "cfg_inflight cfg = empty_inflight"
  shows "bhb_over_brb_satisfied correct (cfg_hist cfg)"
proof -
  have run_step_cfg: "run cfg" by (rule causal_run_imp_run[OF run_cfg])
  have bru: "bru_satisfied (cfg_hist cfg)"
    by (rule drained_run_satisfies_bru[OF run_step_cfg drained])
  have bhb_co: "bhb_causal_order correct (cfg_hist cfg)"
    by (rule causal_run_satisfies_bhb_causal_order[OF run_cfg])
  show ?thesis
    unfolding bhb_over_brb_satisfied_def using bru bhb_co by simp
qed

text \<open>Operational T7 over the @{const causal_run} model: a fair,
drained causal-scheduler run produces a history at which the naive
\<open>CD_B\<close> algorithm with the @{const recv_from_history} view solves
\<open>CD_B\<close> for every admissible adversary whose execution matches the
run.  Parallel to @{thm fair_drained_run_solves_CD_B_broadcast} of
@{theory_text \<open>Primitives.thy\<close>}, both bottoming out at
@{thm T7_broadcast_via_bcb_over_brb}; the BHB causal-order theorem
@{thm causal_run_satisfies_bhb_causal_order} is an independent
structural guarantee of the schedule rather than a discharge of an
active gap in this chain.\<close>

theorem fair_drained_causal_run_solves_CD_B_broadcast:
  assumes run_cfg: "causal_run cfg"
      and drained: "cfg_inflight cfg = empty_inflight"
      and adm:     "adversary_admissible correct adv"
      and adv_eq:  "adv_E adv = cfg_hist cfg"
  shows "valid_B correct (adv_E adv)
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i adv) (adv_E adv))
                        (adv_i adv) (adv_e_star adv)))
                 (adv_e_star adv)"
proof -
  have run_step_cfg: "run cfg" by (rule causal_run_imp_run[OF run_cfg])
  have mode_ok: "mode_admissible Broadcast (adv_E adv)"
    using adv_eq run_completes_to_mode_admissible_broadcast[OF run_step_cfg drained]
    by simp
  show ?thesis by (rule T7_broadcast_via_bcb_over_brb[OF adm mode_ok])
qed

text \<open>The unicast counterpart is also available via the same
operational chain (causal\<open>_run\<close> $\Rightarrow$ @{const run}
$\Rightarrow$ unicast-mode-admissible).\<close>

theorem fair_drained_causal_run_solves_CD_B_unicast:
  assumes run_cfg: "causal_run cfg"
      and drained: "cfg_inflight cfg = empty_inflight"
      and adm:     "adversary_admissible correct adv"
      and adv_eq:  "adv_E adv = cfg_hist cfg"
  shows "valid_B correct (adv_E adv)
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i adv) (adv_E adv))
                        (adv_i adv) (adv_e_star adv)))
                 (adv_e_star adv)"
proof -
  have run_step_cfg: "run cfg" by (rule causal_run_imp_run[OF run_cfg])
  show ?thesis
    by (rule fair_drained_run_solves_CD_B_unicast[OF run_step_cfg drained adm adv_eq])
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
