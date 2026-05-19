(*
  Title:   T6_With_Byzantine.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  A Theorem-6 demonstration in the presence of a live Byzantine
  process.  Builds on T6_Concrete.thy by adding a third process
  \<open>p_c\<close> who is Byzantine and who performs a local internal event
  during the run, exercising the @{const run_step.step_byzantine}
  rule (which is unused in the previous demos).

  The Byzantine process's local activity is operational ``noise'':
  it appears in the global history (via \<open>step_byzantine\<close>) but
  cannot participate in any bhb chain because @{const bhb} only
  follows program-order and message-order steps \<^emph>\<open>through correct
  processes\<close>.  This is the paper-faithful reading of the
  Byzantine-happened-before relation \<open>\<rightarrow>\<^sub>B\<close> of paper Definition 3:
  Byzantine processes' local events are irrelevant to the chain.

  Concretely:

    \<^item> \<open>p_a\<close>, \<open>p_b\<close>: correct, distinct.
    \<^item> \<open>p_c\<close>: Byzantine, distinct from both.
    \<^item> Step 1: \<open>p_b\<close> sends a message to \<open>p_a\<close>  (\<open>step_send\<close>).
    \<^item> Step 2: \<open>p_c\<close> performs a Byzantine internal event
      (\<open>step_byzantine\<close>; the buffer is unchanged).
    \<^item> Step 3: \<open>p_a\<close> receives the message  (\<open>step_recv\<close>).
    \<^item> Step 4: \<open>p_a\<close> performs the target internal event
      (\<open>step_internal\<close>).

  The conclusion is exactly the same as @{thm T6_concrete_demo}:
  under the resulting history, the naive algorithm solves \<open>CD_B\<close>
  at the adversary's target event.  The Byzantine's activity does
  not disrupt this because:

    \<^item> @{const messages_delivered_among} restricted to \<open>correct\<close>
      ignores Byzantine processes (the \<open>p \<in> C \<and> q \<in> C\<close>
      premise filters them out);
    \<^item> @{const bhb} restricted to \<open>correct\<close> rejects steps through
      Byzantine endpoints, so a Byzantine internal event cannot
      appear on any bhb chain.

  This is the paper-faithful demonstration of T6's robustness:
  Byzantine processes can produce arbitrary local events, and the
  algorithm still correctly answers causality queries on the
  correct-process side of the system.
*)

theory T6_With_Byzantine
  imports T6_Concrete
begin

context byzantineSystem
begin

section \<open>Three-process scenario with a Byzantine bystander\<close>

text \<open>The target history.  Two correct processes \<open>p_a\<close>, \<open>p_b\<close>
exchanging one message, plus a Byzantine process \<open>p_c\<close> running an
internal event during the exchange.\<close>

definition byz_demo_H :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p history" where
  "byz_demo_H p_a p_b p_c =
     (\<lambda>p. if p = p_a then [Receive p_a 1 p_b 0, Internal p_a 2]
          else if p = p_b then [Send p_b 1 p_a 0]
          else if p = p_c then [Internal p_c 1]
          else [])"

definition byz_demo_adv :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p adversary" where
  "byz_demo_adv p_a p_b p_c =
     \<lparr> adv_E = byz_demo_H p_a p_b p_c,
       adv_e_star = Internal p_a 2,
       adv_i = p_a \<rparr>"

lemma byz_demo_H_at_p_a:
  assumes "p_a \<noteq> p_b" "p_a \<noteq> p_c"
  shows "byz_demo_H p_a p_b p_c p_a = [Receive p_a 1 p_b 0, Internal p_a 2]"
  using assms by (simp add: byz_demo_H_def)

lemma byz_demo_H_at_p_b:
  assumes "p_a \<noteq> p_b" "p_b \<noteq> p_c"
  shows "byz_demo_H p_a p_b p_c p_b = [Send p_b 1 p_a 0]"
  using assms by (simp add: byz_demo_H_def)

lemma byz_demo_H_at_p_c:
  assumes "p_a \<noteq> p_c" "p_b \<noteq> p_c"
  shows "byz_demo_H p_a p_b p_c p_c = [Internal p_c 1]"
  using assms by (simp add: byz_demo_H_def)

lemma byz_demo_H_elsewhere:
  assumes "p \<noteq> p_a" "p \<noteq> p_b" "p \<noteq> p_c"
  shows "byz_demo_H p_a p_b p_c p = []"
  using assms by (simp add: byz_demo_H_def)

lemma byz_demo_H_events:
  assumes ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "events_of (byz_demo_H p_a p_b p_c) =
           {Receive p_a 1 p_b 0, Internal p_a 2,
            Send p_b 1 p_a 0, Internal p_c 1}"
proof -
  have "events_of (byz_demo_H p_a p_b p_c)
          = (\<Union>p. set (byz_demo_H p_a p_b p_c p))"
    by (simp add: events_of_def)
  also have "\<dots> = set (byz_demo_H p_a p_b p_c p_a)
                   \<union> set (byz_demo_H p_a p_b p_c p_b)
                   \<union> set (byz_demo_H p_a p_b p_c p_c)
                   \<union> (\<Union>p \<in> -{p_a, p_b, p_c}. set (byz_demo_H p_a p_b p_c p))"
    by auto
  also have "set (byz_demo_H p_a p_b p_c p_a)
                = {Receive p_a 1 p_b 0, Internal p_a 2}"
    using ab ac by (simp add: byz_demo_H_at_p_a)
  moreover have "set (byz_demo_H p_a p_b p_c p_b) = {Send p_b 1 p_a 0}"
    using ab bc by (simp add: byz_demo_H_at_p_b)
  moreover have "set (byz_demo_H p_a p_b p_c p_c) = {Internal p_c 1}"
    using ac bc by (simp add: byz_demo_H_at_p_c)
  moreover have "(\<Union>p \<in> -{p_a, p_b, p_c}.
                       set (byz_demo_H p_a p_b p_c p)) = {}"
    by (auto simp: byz_demo_H_elsewhere)
  ultimately show ?thesis by auto
qed

section \<open>Four intermediate configurations along the run\<close>

text \<open>From \<open>init_config\<close> we trace four \<open>run_step\<close> transitions:

  \<^item> \<open>byz_cfg1\<close>: after \<open>step_send p_b 1 p_a 0\<close>
  \<^item> \<open>byz_cfg2\<close>: after \<open>step_byzantine (Internal p_c 1)\<close>
  \<^item> \<open>byz_cfg3\<close>: after \<open>step_recv p_a 1 p_b 0\<close>
  \<^item> \<open>byz_cfg4\<close>: after \<open>step_internal p_a 2\<close>  (drained final)\<close>

definition byz_cfg1 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "byz_cfg1 p_a p_b p_c =
     \<lparr> cfg_hist = (\<lambda>p. if p = p_b then [Send p_b 1 p_a 0] else []),
       cfg_inflight = empty_inflight \<union># {# (p_b, p_a, 0) } \<rparr>"

definition byz_cfg2 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "byz_cfg2 p_a p_b p_c =
     \<lparr> cfg_hist = (\<lambda>p. if p = p_b then [Send p_b 1 p_a 0]
                        else if p = p_c then [Internal p_c 1]
                        else []),
       cfg_inflight = empty_inflight \<union># {# (p_b, p_a, 0) } \<rparr>"

definition byz_cfg3 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "byz_cfg3 p_a p_b p_c =
     \<lparr> cfg_hist = (\<lambda>p. if p = p_a then [Receive p_a 1 p_b 0]
                        else if p = p_b then [Send p_b 1 p_a 0]
                        else if p = p_c then [Internal p_c 1]
                        else []),
       cfg_inflight = empty_inflight \<rparr>"

definition byz_cfg4 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "byz_cfg4 p_a p_b p_c =
     \<lparr> cfg_hist = byz_demo_H p_a p_b p_c,
       cfg_inflight = empty_inflight \<rparr>"

section \<open>The four run\<open>_step\<close> transitions\<close>

lemma byz_step_1_send:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct"
      and ab: "p_a \<noteq> p_b"
  shows "run_step init_config (byz_cfg1 p_a p_b p_c)"
proof -
  let ?cfg0 = "init_config"
  have hist_pb: "cfg_hist ?cfg0 p_b = []"
    by (simp add: init_config_def)
  have n_eq: "(1 :: nat) = Suc (length (cfg_hist ?cfg0 p_b))"
    using hist_pb by simp
  have hist_eq: "cfg_hist (byz_cfg1 p_a p_b p_c)
                  = (cfg_hist ?cfg0)
                      (p_b := cfg_hist ?cfg0 p_b @ [Send p_b 1 p_a 0])"
    by (rule ext) (simp add: byz_cfg1_def init_config_def)
  have inflight_eq: "cfg_inflight (byz_cfg1 p_a p_b p_c)
                       = cfg_inflight ?cfg0 \<union># {# (p_b, p_a, 0) }"
    by (simp add: byz_cfg1_def init_config_def)
  have cfg_eq: "byz_cfg1 p_a p_b p_c
                  = ?cfg0 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg0)
                                (p_b := cfg_hist ?cfg0 p_b @ [Send p_b 1 p_a 0]),
                            cfg_inflight :=
                              cfg_inflight ?cfg0 \<union># {# (p_b, p_a, 0) } \<rparr>"
    using hist_eq inflight_eq by (simp add: byz_cfg1_def init_config_def)
  show ?thesis
    by (rule run_step.step_send[OF pb pa n_eq cfg_eq])
qed

lemma byz_step_2_byzantine:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc_byz: "p_c \<in> byzantine"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "run_step (byz_cfg1 p_a p_b p_c) (byz_cfg2 p_a p_b p_c)"
proof -
  let ?cfg1 = "byz_cfg1 p_a p_b p_c"
  let ?ev = "Internal p_c 1"
  have hist_pc: "cfg_hist ?cfg1 p_c = []"
    using bc by (simp add: byz_cfg1_def)
  have proc_ev: "proc_of ?ev = p_c" by simp
  have seq_ev: "seq_of ?ev = Suc (length (cfg_hist ?cfg1 p_c))"
    using hist_pc by simp
  have hist_eq: "cfg_hist (byz_cfg2 p_a p_b p_c)
                  = (cfg_hist ?cfg1)(p_c := cfg_hist ?cfg1 p_c @ [?ev])"
    using bc ac hist_pc
    by (rule_tac ext) (simp add: byz_cfg1_def byz_cfg2_def)
  have inflight_eq: "cfg_inflight (byz_cfg2 p_a p_b p_c)
                       = cfg_inflight ?cfg1"
    by (simp add: byz_cfg1_def byz_cfg2_def)
  have cfg_eq: "byz_cfg2 p_a p_b p_c
                  = ?cfg1 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg1)(p_c := cfg_hist ?cfg1 p_c @ [?ev]) \<rparr>"
    using hist_eq inflight_eq by (simp add: byz_cfg2_def)
  show ?thesis
    by (rule run_step.step_byzantine[OF pc_byz proc_ev seq_ev cfg_eq])
qed

lemma byz_step_3_recv:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "run_step (byz_cfg2 p_a p_b p_c) (byz_cfg3 p_a p_b p_c)"
proof -
  let ?cfg2 = "byz_cfg2 p_a p_b p_c"
  have buf_in: "(p_b, p_a, 0) \<in># cfg_inflight ?cfg2"
    by (simp add: byz_cfg2_def empty_inflight_def)
  have hist_pa: "cfg_hist ?cfg2 p_a = []"
    using ab ac by (simp add: byz_cfg2_def)
  have n_eq: "(1 :: nat) = Suc (length (cfg_hist ?cfg2 p_a))"
    using hist_pa by simp
  have hist_eq: "cfg_hist (byz_cfg3 p_a p_b p_c)
                  = (cfg_hist ?cfg2)
                      (p_a := cfg_hist ?cfg2 p_a @ [Receive p_a 1 p_b 0])"
    using ab ac hist_pa
    by (rule_tac ext) (simp add: byz_cfg2_def byz_cfg3_def)
  have inflight_eq: "cfg_inflight (byz_cfg3 p_a p_b p_c)
                       = cfg_inflight ?cfg2 -# (p_b, p_a, 0)"
    by (rule ext) (simp add: byz_cfg2_def byz_cfg3_def empty_inflight_def)
  have cfg_eq: "byz_cfg3 p_a p_b p_c
                  = ?cfg2 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg2)
                                (p_a := cfg_hist ?cfg2 p_a @ [Receive p_a 1 p_b 0]),
                            cfg_inflight :=
                              cfg_inflight ?cfg2 -# (p_b, p_a, 0) \<rparr>"
    using hist_eq inflight_eq by (simp add: byz_cfg3_def)
  show ?thesis
    by (rule run_step.step_recv[OF pa pb buf_in n_eq cfg_eq])
qed

lemma byz_step_4_internal:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "run_step (byz_cfg3 p_a p_b p_c) (byz_cfg4 p_a p_b p_c)"
proof -
  let ?cfg3 = "byz_cfg3 p_a p_b p_c"
  have hist_pa: "cfg_hist ?cfg3 p_a = [Receive p_a 1 p_b 0]"
    using ab ac by (simp add: byz_cfg3_def)
  have n_eq: "(2 :: nat) = Suc (length (cfg_hist ?cfg3 p_a))"
    using hist_pa by simp
  have hist_eq: "cfg_hist (byz_cfg4 p_a p_b p_c)
                  = (cfg_hist ?cfg3)
                      (p_a := cfg_hist ?cfg3 p_a @ [Internal p_a 2])"
    using ab ac bc hist_pa
    by (rule_tac ext) (simp add: byz_cfg3_def byz_cfg4_def byz_demo_H_def)
  have inflight_eq: "cfg_inflight (byz_cfg4 p_a p_b p_c)
                       = cfg_inflight ?cfg3"
    by (simp add: byz_cfg3_def byz_cfg4_def)
  have cfg_eq: "byz_cfg4 p_a p_b p_c
                  = ?cfg3 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg3)
                                (p_a := cfg_hist ?cfg3 p_a @ [Internal p_a 2]) \<rparr>"
    using hist_eq inflight_eq by (simp add: byz_cfg4_def)
  show ?thesis
    by (rule run_step.step_internal[OF pa n_eq cfg_eq])
qed

section \<open>The byz-presence run is fair, drained, and produces \<open>byz_demo_H\<close>\<close>

lemma byz_run:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc_byz: "p_c \<in> byzantine"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "run (byz_cfg4 p_a p_b p_c)"
proof -
  have r0: "run init_config" by simp
  have s1: "run_step init_config (byz_cfg1 p_a p_b p_c)"
    by (rule byz_step_1_send[OF pa pb ab])
  have r1: "run (byz_cfg1 p_a p_b p_c)" by (rule run_extend[OF r0 s1])
  have s2: "run_step (byz_cfg1 p_a p_b p_c) (byz_cfg2 p_a p_b p_c)"
    by (rule byz_step_2_byzantine[OF pa pb pc_byz ab ac bc])
  have r2: "run (byz_cfg2 p_a p_b p_c)" by (rule run_extend[OF r1 s2])
  have s3: "run_step (byz_cfg2 p_a p_b p_c) (byz_cfg3 p_a p_b p_c)"
    by (rule byz_step_3_recv[OF pa pb ab ac bc])
  have r3: "run (byz_cfg3 p_a p_b p_c)" by (rule run_extend[OF r2 s3])
  have s4: "run_step (byz_cfg3 p_a p_b p_c) (byz_cfg4 p_a p_b p_c)"
    by (rule byz_step_4_internal[OF pa pb ab ac bc])
  show ?thesis by (rule run_extend[OF r3 s4])
qed

lemma byz_drained:
  shows "cfg_inflight (byz_cfg4 p_a p_b p_c) = empty_inflight"
  by (simp add: byz_cfg4_def)

lemma byz_cfg_hist_eq:
  shows "cfg_hist (byz_cfg4 p_a p_b p_c) = byz_demo_H p_a p_b p_c"
  by (simp add: byz_cfg4_def)

section \<open>Well-formedness and adversary admissibility\<close>

lemma byz_wf_local_p_a:
  assumes ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c"
  shows "wf_history_local p_a (byz_demo_H p_a p_b p_c p_a)"
proof -
  let ?L = "[Receive p_a 1 p_b 0, Internal p_a 2]"
  have list_eq: "byz_demo_H p_a p_b p_c p_a = ?L"
    using ab ac by (rule byz_demo_H_at_p_a)
  have proc_ok: "\<forall>e \<in> set ?L. proc_of e = p_a" by simp
  have seq_ok: "\<forall>k < length ?L. seq_of (?L ! k) = Suc k"
  proof (intro allI impI)
    fix k assume "k < length ?L"
    hence "k = 0 \<or> k = 1" by auto
    thus "seq_of (?L ! k) = Suc k" by auto
  qed
  show ?thesis using list_eq proc_ok seq_ok
    unfolding wf_history_local_def by simp
qed

lemma byz_wf_local_p_b:
  assumes ab: "p_a \<noteq> p_b" and bc: "p_b \<noteq> p_c"
  shows "wf_history_local p_b (byz_demo_H p_a p_b p_c p_b)"
proof -
  let ?L = "[Send p_b 1 p_a 0]"
  have list_eq: "byz_demo_H p_a p_b p_c p_b = ?L"
    using ab bc by (rule byz_demo_H_at_p_b)
  have proc_ok: "\<forall>e \<in> set ?L. proc_of e = p_b" by simp
  have seq_ok: "\<forall>k < length ?L. seq_of (?L ! k) = Suc k"
  proof (intro allI impI)
    fix k assume "k < length ?L"
    hence "k = 0" by auto
    thus "seq_of (?L ! k) = Suc k" by simp
  qed
  show ?thesis using list_eq proc_ok seq_ok
    unfolding wf_history_local_def by simp
qed

lemma byz_wf_local_p_c:
  assumes ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "wf_history_local p_c (byz_demo_H p_a p_b p_c p_c)"
proof -
  let ?L = "[Internal p_c 1]"
  have list_eq: "byz_demo_H p_a p_b p_c p_c = ?L"
    using ac bc by (rule byz_demo_H_at_p_c)
  have proc_ok: "\<forall>e \<in> set ?L. proc_of e = p_c" by simp
  have seq_ok: "\<forall>k < length ?L. seq_of (?L ! k) = Suc k"
  proof (intro allI impI)
    fix k assume "k < length ?L"
    hence "k = 0" by auto
    thus "seq_of (?L ! k) = Suc k" by simp
  qed
  show ?thesis using list_eq proc_ok seq_ok
    unfolding wf_history_local_def by simp
qed

lemma byz_wf_local_elsewhere:
  assumes "p \<noteq> p_a" "p \<noteq> p_b" "p \<noteq> p_c"
  shows "wf_history_local p (byz_demo_H p_a p_b p_c p)"
  using assms by (simp add: byz_demo_H_elsewhere wf_history_local_def)

lemma byz_wf_history:
  assumes ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "wf_history (byz_demo_H p_a p_b p_c)"
proof (unfold wf_history_def, intro allI)
  fix p
  show "wf_history_local p (byz_demo_H p_a p_b p_c p)"
  proof (cases "p = p_a")
    case True
    thus ?thesis using ab ac byz_wf_local_p_a by simp
  next
    case False
    show ?thesis
    proof (cases "p = p_b")
      case True
      thus ?thesis using ab bc byz_wf_local_p_b by simp
    next
      case False
      show ?thesis
      proof (cases "p = p_c")
        case True
        thus ?thesis using ac bc byz_wf_local_p_c by simp
      next
        case False
        with \<open>p \<noteq> p_a\<close> \<open>p \<noteq> p_b\<close> show ?thesis
          by (rule byz_wf_local_elsewhere)
      qed
    qed
  qed
qed

lemma byz_adv_admissible:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "adversary_admissible correct (byz_demo_adv p_a p_b p_c)"
proof -
  have wf: "wf_history (byz_demo_H p_a p_b p_c)"
    using ab ac bc by (rule byz_wf_history)
  have i_corr: "adv_i (byz_demo_adv p_a p_b p_c) \<in> correct"
    using pa by (simp add: byz_demo_adv_def)
  have proc_eq:
    "proc_of (adv_e_star (byz_demo_adv p_a p_b p_c))
       = adv_i (byz_demo_adv p_a p_b p_c)"
    by (simp add: byz_demo_adv_def)
  have target_in:
    "adv_e_star (byz_demo_adv p_a p_b p_c)
        \<in> events_of (adv_E (byz_demo_adv p_a p_b p_c))"
    using ab ac bc by (simp add: byz_demo_adv_def byz_demo_H_events)
  show ?thesis
    using wf i_corr proc_eq target_in
    by (simp add: adversary_admissible_def byz_demo_adv_def)
qed

section \<open>The naive algorithm solves \<open>CD_B\<close> despite the Byzantine bystander\<close>

text \<open>Headline theorem: with a Byzantine process \<open>p_c\<close> actively
producing a local internal event during the run, the naive
algorithm \<^emph>\<open>still\<close> solves \<open>CD_B\<close> at the correct adversary's
target.  This is the operational core of T6's robustness claim.\<close>

theorem T6_with_byzantine_demo:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct"
      and pc_byz: "p_c \<in> byzantine"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "valid_B correct (adv_E (byz_demo_adv p_a p_b p_c))
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i (byz_demo_adv p_a p_b p_c))
                                            (adv_E (byz_demo_adv p_a p_b p_c)))
                        (adv_i (byz_demo_adv p_a p_b p_c))
                        (adv_e_star (byz_demo_adv p_a p_b p_c))))
                 (adv_e_star (byz_demo_adv p_a p_b p_c))"
proof -
  let ?cfg = "byz_cfg4 p_a p_b p_c"
  let ?adv = "byz_demo_adv p_a p_b p_c"
  have run_cfg: "run ?cfg"
    by (rule byz_run[OF pa pb pc_byz ab ac bc])
  have drained: "cfg_inflight ?cfg = empty_inflight" by (rule byz_drained)
  have adm: "adversary_admissible correct ?adv"
    by (rule byz_adv_admissible[OF pa pb ab ac bc])
  have adv_E_eq: "adv_E ?adv = cfg_hist ?cfg"
    using byz_cfg_hist_eq[of p_a p_b p_c] by (simp add: byz_demo_adv_def)
  show ?thesis
    by (rule fair_drained_run_solves_CD_B_unicast[OF run_cfg drained adm adv_E_eq])
qed

text \<open>Existential witness: T6 holds in the presence of a live
Byzantine process whenever the locale supplies two distinct
correct processes plus a distinct Byzantine process.\<close>

theorem T6_with_byzantine_witnessed:
  assumes pieces:
    "\<exists>p_a p_b p_c. p_a \<in> correct \<and> p_b \<in> correct \<and> p_c \<in> byzantine
                  \<and> p_a \<noteq> p_b \<and> p_a \<noteq> p_c \<and> p_b \<noteq> p_c"
  shows "\<exists>adv cfg.
            run cfg
          \<and> cfg_inflight cfg = empty_inflight
          \<and> adversary_admissible correct adv
          \<and> adv_E adv = cfg_hist cfg
          \<and> valid_B correct (adv_E adv)
                    (fst (naive_cd_B_alg
                           (recv_from_history (adv_i adv) (adv_E adv))
                           (adv_i adv) (adv_e_star adv)))
                    (adv_e_star adv)"
proof -
  obtain p_a p_b p_c
    where pa: "p_a \<in> correct" and pb: "p_b \<in> correct"
      and pc_byz: "p_c \<in> byzantine"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
    using pieces by blast
  let ?cfg = "byz_cfg4 p_a p_b p_c"
  let ?adv = "byz_demo_adv p_a p_b p_c"
  have run_cfg: "run ?cfg" by (rule byz_run[OF pa pb pc_byz ab ac bc])
  have drained: "cfg_inflight ?cfg = empty_inflight" by (rule byz_drained)
  have adm: "adversary_admissible correct ?adv"
    by (rule byz_adv_admissible[OF pa pb ab ac bc])
  have adv_E_eq: "adv_E ?adv = cfg_hist ?cfg"
    using byz_cfg_hist_eq[of p_a p_b p_c] by (simp add: byz_demo_adv_def)
  have solves: "valid_B correct (adv_E ?adv)
                       (fst (naive_cd_B_alg
                              (recv_from_history (adv_i ?adv) (adv_E ?adv))
                              (adv_i ?adv) (adv_e_star ?adv)))
                       (adv_e_star ?adv)"
    by (rule T6_with_byzantine_demo[OF pa pb pc_byz ab ac bc])
  from run_cfg drained adm adv_E_eq solves show ?thesis by blast
qed

section \<open>The Byzantine's internal event is not on any bhb chain\<close>

text \<open>The paper-faithful sanity check: the Byzantine's local event
\<open>Internal p_c 1\<close> is \<^emph>\<open>not\<close> on any bhb chain to the adversary's
target (or any other correct event), because @{const bhb} steps
require both endpoints to be in \<open>correct\<close> and \<open>p_c \<in> byzantine\<close>.

Concretely, \<open>Internal p_c 1\<close> has \<open>proc_of = p_c\<close>, which is in
\<open>byzantine\<close>; hence by @{thm bhb_proc_of_endpoints} no bhb chain
ends at this event (or starts from it).\<close>

lemma byzantine_event_not_on_bhb_chain_left:
  assumes pc_byz: "p_c \<in> byzantine"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "\<not> bhb correct (byz_demo_H p_a p_b p_c) (Internal p_c 1) e'"
proof
  assume bhb_chain: "bhb correct (byz_demo_H p_a p_b p_c) (Internal p_c 1) e'"
  hence "proc_of (Internal p_c 1) \<in> correct"
    using bhb_proc_of_endpoints by blast
  hence "p_c \<in> correct" by simp
  thus False using pc_byz partition_disj by blast
qed

lemma byzantine_event_not_on_bhb_chain_right:
  assumes pc_byz: "p_c \<in> byzantine"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "\<not> bhb correct (byz_demo_H p_a p_b p_c) e (Internal p_c 1)"
proof
  assume bhb_chain: "bhb correct (byz_demo_H p_a p_b p_c) e (Internal p_c 1)"
  hence "proc_of (Internal p_c 1) \<in> correct"
    using bhb_proc_of_endpoints by blast
  hence "p_c \<in> correct" by simp
  thus False using pc_byz partition_disj by blast
qed

text \<open>In particular: the Byzantine event neither hb-before-precedes
nor hb-after-succeeds the adversary's target event \<open>Internal p_a 2\<close>
under @{const bhb_eval}.  The algorithm correctly does not include
the Byzantine event in any bhb-relation to the target.\<close>

theorem bhb_eval_byzantine_unrelated_to_target:
  assumes pc_byz: "p_c \<in> byzantine"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "\<not> bhb_eval correct (byz_demo_H p_a p_b p_c)
                 (Internal p_c 1) (Internal p_a 2)"
    and "\<not> bhb_eval correct (byz_demo_H p_a p_b p_c)
                 (Internal p_a 2) (Internal p_c 1)"
proof -
  show "\<not> bhb_eval correct (byz_demo_H p_a p_b p_c)
                  (Internal p_c 1) (Internal p_a 2)"
    using byzantine_event_not_on_bhb_chain_left[OF pc_byz ab ac bc]
    by (simp add: bhb_eval_def)
  show "\<not> bhb_eval correct (byz_demo_H p_a p_b p_c)
                  (Internal p_a 2) (Internal p_c 1)"
    using byzantine_event_not_on_bhb_chain_right[OF pc_byz ab ac bc]
    by (simp add: bhb_eval_def)
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
