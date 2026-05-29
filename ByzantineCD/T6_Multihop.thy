(*
  Title:   T6_Multihop.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  A larger fully-concrete demonstration of Theorem 6 with three
  correct processes and a two-hop causal chain.

  Builds directly on the 1-message demo in T6_Concrete.thy.  The
  three-process variant exercises:

    \<^item> a longer 5-step run_step sequence;
    \<^item> two distinct message identifiers and four message endpoints
      (two correct senders, two correct receivers);
    \<^item> a transitive bhb chain that crosses two messages and three
      processes:

        Send p_b 1 p_a 1
          \<longrightarrow>\<^sub>{msg-order}  Receive p_a 1 p_b 1
          \<longrightarrow>\<^sub>{prog-order} Send p_a 2 p_c 2
          \<longrightarrow>\<^sub>{msg-order}  Receive p_c 1 p_a 2
          \<longrightarrow>\<^sub>{prog-order} Internal p_c 2  (= e_star)

  The target adversary's query is at \<open>p_c\<close> (the end of the chain),
  not at \<open>p_b\<close> (the originator).  The bhb relation correctly
  propagates the causal dependency along the chain, and the naive
  algorithm's output (which equals the global history under
  \<open>recv_from_history\<close>) reflects this.

  This is paper-faithful to the spirit of T6: the BHB-restricted
  causality relation tracks chains through correct processes, and
  under BRU's correct-to-correct delivery the algorithm reconstructs
  enough of the global history to make those chains visible.

  The proof structure mirrors T6_Concrete.thy exactly: five
  \<open>run_step\<close> transitions are constructed, each producing the next
  intermediate configuration, and the composition is composed with
  @{thm fair_drained_run_solves_CD_B_unicast}.
*)

theory T6_Multihop
  imports T6_Concrete
begin

context byzantineSystem
begin

section \<open>Three-process multihop scenario\<close>

text \<open>The target history of the multihop demonstration.  Three
distinct correct processes \<open>p_a\<close>, \<open>p_b\<close>, \<open>p_c\<close>:

  \<^item> \<open>p_b\<close> sends \<open>m\<^sub>1 = 1\<close> to \<open>p_a\<close>;
  \<^item> \<open>p_a\<close> receives \<open>m\<^sub>1\<close>;
  \<^item> \<open>p_a\<close> sends \<open>m\<^sub>2 = 2\<close> to \<open>p_c\<close>;
  \<^item> \<open>p_c\<close> receives \<open>m\<^sub>2\<close>;
  \<^item> \<open>p_c\<close> performs an internal event (the adversary's target).\<close>

definition multi_H :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p history" where
  "multi_H p_a p_b p_c =
     (\<lambda>p. if p = p_a then [Receive p_a 1 p_b 1, Send p_a 2 p_c 2]
          else if p = p_b then [Send p_b 1 p_a 1]
          else if p = p_c then [Receive p_c 1 p_a 2, Internal p_c 2]
          else [])"

definition multi_adv :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p adversary" where
  "multi_adv p_a p_b p_c =
     \<lparr> adv_E = multi_H p_a p_b p_c,
       adv_e_star = Internal p_c 2,
       adv_i = p_c \<rparr>"

lemma multi_H_at_p_a:
  assumes "p_a \<noteq> p_b" "p_a \<noteq> p_c"
  shows "multi_H p_a p_b p_c p_a = [Receive p_a 1 p_b 1, Send p_a 2 p_c 2]"
  using assms by (simp add: multi_H_def)

lemma multi_H_at_p_b:
  assumes "p_a \<noteq> p_b" "p_b \<noteq> p_c"
  shows "multi_H p_a p_b p_c p_b = [Send p_b 1 p_a 1]"
  using assms by (simp add: multi_H_def)

lemma multi_H_at_p_c:
  assumes "p_a \<noteq> p_c" "p_b \<noteq> p_c"
  shows "multi_H p_a p_b p_c p_c = [Receive p_c 1 p_a 2, Internal p_c 2]"
  using assms by (simp add: multi_H_def)

lemma multi_H_elsewhere:
  assumes "p \<noteq> p_a" "p \<noteq> p_b" "p \<noteq> p_c"
  shows "multi_H p_a p_b p_c p = []"
  using assms by (simp add: multi_H_def)

lemma multi_H_events:
  assumes ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "events_of (multi_H p_a p_b p_c) =
           {Receive p_a 1 p_b 1, Send p_a 2 p_c 2, Send p_b 1 p_a 1,
            Receive p_c 1 p_a 2, Internal p_c 2}"
proof -
  have "events_of (multi_H p_a p_b p_c) = (\<Union>p. set (multi_H p_a p_b p_c p))"
    by (simp add: events_of_def)
  also have "\<dots> = set (multi_H p_a p_b p_c p_a)
                   \<union> set (multi_H p_a p_b p_c p_b)
                   \<union> set (multi_H p_a p_b p_c p_c)
                   \<union> (\<Union>p \<in> -{p_a, p_b, p_c}. set (multi_H p_a p_b p_c p))"
    by auto
  also have "set (multi_H p_a p_b p_c p_a)
                = {Receive p_a 1 p_b 1, Send p_a 2 p_c 2}"
    using ab ac by (simp add: multi_H_at_p_a)
  moreover have "set (multi_H p_a p_b p_c p_b) = {Send p_b 1 p_a 1}"
    using ab bc by (simp add: multi_H_at_p_b)
  moreover have "set (multi_H p_a p_b p_c p_c)
                  = {Receive p_c 1 p_a 2, Internal p_c 2}"
    using ac bc by (simp add: multi_H_at_p_c)
  moreover have "(\<Union>p \<in> -{p_a, p_b, p_c}. set (multi_H p_a p_b p_c p)) = {}"
    by (auto simp: multi_H_elsewhere)
  ultimately show ?thesis by auto
qed

section \<open>Five intermediate configurations along the multihop run\<close>

text \<open>From \<open>init_config\<close> we trace five \<open>run_step\<close> transitions:

  \<^item> \<open>multi_cfg1\<close>: after \<open>step_send p_b 1 p_a 1\<close>
  \<^item> \<open>multi_cfg2\<close>: after \<open>step_recv p_a 1 p_b 1\<close>
  \<^item> \<open>multi_cfg3\<close>: after \<open>step_send p_a 2 p_c 2\<close>
  \<^item> \<open>multi_cfg4\<close>: after \<open>step_recv p_c 1 p_a 2\<close>
  \<^item> \<open>multi_cfg5\<close>: after \<open>step_internal p_c 2\<close> (drained final)\<close>

definition multi_cfg1 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "multi_cfg1 p_a p_b p_c =
     \<lparr> cfg_hist = (\<lambda>p. if p = p_b then [Send p_b 1 p_a 1] else []),
       cfg_inflight = empty_inflight \<union># {# (p_b, p_a, 1) } \<rparr>"

definition multi_cfg2 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "multi_cfg2 p_a p_b p_c =
     \<lparr> cfg_hist = (\<lambda>p. if p = p_a then [Receive p_a 1 p_b 1]
                        else if p = p_b then [Send p_b 1 p_a 1]
                        else []),
       cfg_inflight = empty_inflight \<rparr>"

definition multi_cfg3 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "multi_cfg3 p_a p_b p_c =
     \<lparr> cfg_hist = (\<lambda>p. if p = p_a
                          then [Receive p_a 1 p_b 1, Send p_a 2 p_c 2]
                        else if p = p_b then [Send p_b 1 p_a 1]
                        else []),
       cfg_inflight = empty_inflight \<union># {# (p_a, p_c, 2) } \<rparr>"

definition multi_cfg4 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "multi_cfg4 p_a p_b p_c =
     \<lparr> cfg_hist = (\<lambda>p. if p = p_a
                          then [Receive p_a 1 p_b 1, Send p_a 2 p_c 2]
                        else if p = p_b then [Send p_b 1 p_a 1]
                        else if p = p_c then [Receive p_c 1 p_a 2]
                        else []),
       cfg_inflight = empty_inflight \<rparr>"

definition multi_cfg5 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "multi_cfg5 p_a p_b p_c =
     \<lparr> cfg_hist = multi_H p_a p_b p_c,
       cfg_inflight = empty_inflight \<rparr>"

section \<open>The five run\<open>_step\<close> transitions\<close>

lemma multi_step_1_send:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc: "p_c \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "run_step init_config (multi_cfg1 p_a p_b p_c)"
proof -
  let ?cfg0 = "init_config"
  have hist_pb: "cfg_hist ?cfg0 p_b = []"
    by (simp add: init_config_def)
  have n_eq: "(1 :: nat) = Suc (length (cfg_hist ?cfg0 p_b))"
    using hist_pb by simp
  have hist_eq: "cfg_hist (multi_cfg1 p_a p_b p_c)
                  = (cfg_hist ?cfg0)
                      (p_b := cfg_hist ?cfg0 p_b @ [Send p_b 1 p_a 1])"
    by (rule ext) (simp add: multi_cfg1_def init_config_def)
  have inflight_eq: "cfg_inflight (multi_cfg1 p_a p_b p_c)
                       = cfg_inflight ?cfg0 \<union># {# (p_b, p_a, 1) }"
    by (simp add: multi_cfg1_def init_config_def)
  have cfg_eq: "multi_cfg1 p_a p_b p_c
                  = ?cfg0 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg0)
                                (p_b := cfg_hist ?cfg0 p_b @ [Send p_b 1 p_a 1]),
                            cfg_inflight :=
                              cfg_inflight ?cfg0 \<union># {# (p_b, p_a, 1) } \<rparr>"
    using hist_eq inflight_eq by (simp add: multi_cfg1_def init_config_def)
  show ?thesis
    by (rule run_step.step_send[OF pb pa n_eq cfg_eq])
qed

lemma multi_step_2_recv:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc: "p_c \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "run_step (multi_cfg1 p_a p_b p_c) (multi_cfg2 p_a p_b p_c)"
proof -
  let ?cfg1 = "multi_cfg1 p_a p_b p_c"
  have buf_in: "(p_b, p_a, 1) \<in># cfg_inflight ?cfg1"
    by (simp add: multi_cfg1_def empty_inflight_def)
  have hist_pa: "cfg_hist ?cfg1 p_a = []"
    using ab by (simp add: multi_cfg1_def)
  have n_eq: "(1 :: nat) = Suc (length (cfg_hist ?cfg1 p_a))"
    using hist_pa by simp
  have hist_eq: "cfg_hist (multi_cfg2 p_a p_b p_c)
                  = (cfg_hist ?cfg1)
                      (p_a := cfg_hist ?cfg1 p_a @ [Receive p_a 1 p_b 1])"
    using ab hist_pa
    by (rule_tac ext) (simp add: multi_cfg1_def multi_cfg2_def)
  have inflight_eq: "cfg_inflight (multi_cfg2 p_a p_b p_c)
                       = cfg_inflight ?cfg1 -# (p_b, p_a, 1)"
    by (rule ext) (simp add: multi_cfg1_def multi_cfg2_def empty_inflight_def)
  have cfg_eq: "multi_cfg2 p_a p_b p_c
                  = ?cfg1 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg1)
                                (p_a := cfg_hist ?cfg1 p_a @ [Receive p_a 1 p_b 1]),
                            cfg_inflight :=
                              cfg_inflight ?cfg1 -# (p_b, p_a, 1) \<rparr>"
    using hist_eq inflight_eq by (simp add: multi_cfg2_def)
  show ?thesis
    by (rule run_step.step_recv[OF pa pb buf_in n_eq cfg_eq])
qed

lemma multi_step_3_send:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc: "p_c \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "run_step (multi_cfg2 p_a p_b p_c) (multi_cfg3 p_a p_b p_c)"
proof -
  let ?cfg2 = "multi_cfg2 p_a p_b p_c"
  have hist_pa: "cfg_hist ?cfg2 p_a = [Receive p_a 1 p_b 1]"
    using ab by (simp add: multi_cfg2_def)
  have n_eq: "(2 :: nat) = Suc (length (cfg_hist ?cfg2 p_a))"
    using hist_pa by simp
  have hist_eq: "cfg_hist (multi_cfg3 p_a p_b p_c)
                  = (cfg_hist ?cfg2)
                      (p_a := cfg_hist ?cfg2 p_a @ [Send p_a 2 p_c 2])"
    using ab ac hist_pa
    by (rule_tac ext) (simp add: multi_cfg2_def multi_cfg3_def)
  have inflight_eq: "cfg_inflight (multi_cfg3 p_a p_b p_c)
                       = cfg_inflight ?cfg2 \<union># {# (p_a, p_c, 2) }"
    by (rule ext) (simp add: multi_cfg2_def multi_cfg3_def empty_inflight_def)
  have cfg_eq: "multi_cfg3 p_a p_b p_c
                  = ?cfg2 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg2)
                                (p_a := cfg_hist ?cfg2 p_a @ [Send p_a 2 p_c 2]),
                            cfg_inflight :=
                              cfg_inflight ?cfg2 \<union># {# (p_a, p_c, 2) } \<rparr>"
    using hist_eq inflight_eq by (simp add: multi_cfg3_def)
  show ?thesis
    by (rule run_step.step_send[OF pa pc n_eq cfg_eq])
qed

lemma multi_step_4_recv:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc: "p_c \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "run_step (multi_cfg3 p_a p_b p_c) (multi_cfg4 p_a p_b p_c)"
proof -
  let ?cfg3 = "multi_cfg3 p_a p_b p_c"
  have buf_in: "(p_a, p_c, 2) \<in># cfg_inflight ?cfg3"
    by (simp add: multi_cfg3_def empty_inflight_def)
  have hist_pc: "cfg_hist ?cfg3 p_c = []"
    using ac bc by (simp add: multi_cfg3_def)
  have n_eq: "(1 :: nat) = Suc (length (cfg_hist ?cfg3 p_c))"
    using hist_pc by simp
  have hist_eq: "cfg_hist (multi_cfg4 p_a p_b p_c)
                  = (cfg_hist ?cfg3)
                      (p_c := cfg_hist ?cfg3 p_c @ [Receive p_c 1 p_a 2])"
    using ac bc hist_pc
    by (rule_tac ext) (simp add: multi_cfg3_def multi_cfg4_def)
  have inflight_eq: "cfg_inflight (multi_cfg4 p_a p_b p_c)
                       = cfg_inflight ?cfg3 -# (p_a, p_c, 2)"
    by (rule ext) (simp add: multi_cfg3_def multi_cfg4_def empty_inflight_def)
  have cfg_eq: "multi_cfg4 p_a p_b p_c
                  = ?cfg3 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg3)
                                (p_c := cfg_hist ?cfg3 p_c @ [Receive p_c 1 p_a 2]),
                            cfg_inflight :=
                              cfg_inflight ?cfg3 -# (p_a, p_c, 2) \<rparr>"
    using hist_eq inflight_eq by (simp add: multi_cfg4_def)
  show ?thesis
    by (rule run_step.step_recv[OF pc pa buf_in n_eq cfg_eq])
qed

lemma multi_step_5_internal:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc: "p_c \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "run_step (multi_cfg4 p_a p_b p_c) (multi_cfg5 p_a p_b p_c)"
proof -
  let ?cfg4 = "multi_cfg4 p_a p_b p_c"
  have hist_pc: "cfg_hist ?cfg4 p_c = [Receive p_c 1 p_a 2]"
    using ac bc by (simp add: multi_cfg4_def)
  have n_eq: "(2 :: nat) = Suc (length (cfg_hist ?cfg4 p_c))"
    using hist_pc by simp
  have hist_eq: "cfg_hist (multi_cfg5 p_a p_b p_c)
                  = (cfg_hist ?cfg4)
                      (p_c := cfg_hist ?cfg4 p_c @ [Internal p_c 2])"
    using ab ac bc hist_pc
    by (rule_tac ext) (simp add: multi_cfg4_def multi_cfg5_def multi_H_def)
  have inflight_eq: "cfg_inflight (multi_cfg5 p_a p_b p_c)
                       = cfg_inflight ?cfg4"
    by (simp add: multi_cfg4_def multi_cfg5_def)
  have cfg_eq: "multi_cfg5 p_a p_b p_c
                  = ?cfg4 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg4)
                                (p_c := cfg_hist ?cfg4 p_c @ [Internal p_c 2]) \<rparr>"
    using hist_eq inflight_eq by (simp add: multi_cfg5_def)
  show ?thesis
    by (rule run_step.step_internal[OF pc n_eq cfg_eq])
qed

section \<open>The multihop run is fair, drained, and produces \<open>multi_H\<close>\<close>

lemma multi_run:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc: "p_c \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "run (multi_cfg5 p_a p_b p_c)"
proof -
  have r0: "run init_config" by simp
  have s1: "run_step init_config (multi_cfg1 p_a p_b p_c)"
    by (rule multi_step_1_send[OF pa pb pc ab ac bc])
  have r1: "run (multi_cfg1 p_a p_b p_c)" by (rule run_extend[OF r0 s1])
  have s2: "run_step (multi_cfg1 p_a p_b p_c) (multi_cfg2 p_a p_b p_c)"
    by (rule multi_step_2_recv[OF pa pb pc ab ac bc])
  have r2: "run (multi_cfg2 p_a p_b p_c)" by (rule run_extend[OF r1 s2])
  have s3: "run_step (multi_cfg2 p_a p_b p_c) (multi_cfg3 p_a p_b p_c)"
    by (rule multi_step_3_send[OF pa pb pc ab ac bc])
  have r3: "run (multi_cfg3 p_a p_b p_c)" by (rule run_extend[OF r2 s3])
  have s4: "run_step (multi_cfg3 p_a p_b p_c) (multi_cfg4 p_a p_b p_c)"
    by (rule multi_step_4_recv[OF pa pb pc ab ac bc])
  have r4: "run (multi_cfg4 p_a p_b p_c)" by (rule run_extend[OF r3 s4])
  have s5: "run_step (multi_cfg4 p_a p_b p_c) (multi_cfg5 p_a p_b p_c)"
    by (rule multi_step_5_internal[OF pa pb pc ab ac bc])
  show ?thesis by (rule run_extend[OF r4 s5])
qed

lemma multi_drained:
  shows "cfg_inflight (multi_cfg5 p_a p_b p_c) = empty_inflight"
  by (simp add: multi_cfg5_def)

lemma multi_cfg_hist_eq:
  shows "cfg_hist (multi_cfg5 p_a p_b p_c) = multi_H p_a p_b p_c"
  by (simp add: multi_cfg5_def)

section \<open>Well-formedness and adversary admissibility\<close>

lemma multi_wf_history_local_p_a:
  assumes "p_a \<noteq> p_b" "p_a \<noteq> p_c"
  shows "wf_history_local p_a (multi_H p_a p_b p_c p_a)"
proof -
  let ?L = "[Receive p_a 1 p_b 1, Send p_a 2 p_c 2]"
  have list_eq: "multi_H p_a p_b p_c p_a = ?L"
    using assms by (rule multi_H_at_p_a)
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

lemma multi_wf_history_local_p_b:
  assumes "p_a \<noteq> p_b" "p_b \<noteq> p_c"
  shows "wf_history_local p_b (multi_H p_a p_b p_c p_b)"
proof -
  let ?L = "[Send p_b 1 p_a 1]"
  have list_eq: "multi_H p_a p_b p_c p_b = ?L"
    using assms by (rule multi_H_at_p_b)
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

lemma multi_wf_history_local_p_c:
  assumes "p_a \<noteq> p_c" "p_b \<noteq> p_c"
  shows "wf_history_local p_c (multi_H p_a p_b p_c p_c)"
proof -
  let ?L = "[Receive p_c 1 p_a 2, Internal p_c 2]"
  have list_eq: "multi_H p_a p_b p_c p_c = ?L"
    using assms by (rule multi_H_at_p_c)
  have proc_ok: "\<forall>e \<in> set ?L. proc_of e = p_c" by simp
  have seq_ok: "\<forall>k < length ?L. seq_of (?L ! k) = Suc k"
  proof (intro allI impI)
    fix k assume "k < length ?L"
    hence "k = 0 \<or> k = 1" by auto
    thus "seq_of (?L ! k) = Suc k" by auto
  qed
  show ?thesis using list_eq proc_ok seq_ok
    unfolding wf_history_local_def by simp
qed

lemma multi_wf_history_local_elsewhere:
  assumes "p \<noteq> p_a" "p \<noteq> p_b" "p \<noteq> p_c"
  shows "wf_history_local p (multi_H p_a p_b p_c p)"
  using assms by (simp add: multi_H_elsewhere wf_history_local_def)

lemma multi_wf_history:
  assumes ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "wf_history (multi_H p_a p_b p_c)"
proof (unfold wf_history_def, intro allI)
  fix p
  show "wf_history_local p (multi_H p_a p_b p_c p)"
  proof (cases "p = p_a")
    case True
    thus ?thesis using ab ac multi_wf_history_local_p_a by simp
  next
    case False
    show ?thesis
    proof (cases "p = p_b")
      case True
      thus ?thesis using ab bc multi_wf_history_local_p_b by simp
    next
      case False
      show ?thesis
      proof (cases "p = p_c")
        case True
        thus ?thesis using ac bc multi_wf_history_local_p_c by simp
      next
        case False
        with \<open>p \<noteq> p_a\<close> \<open>p \<noteq> p_b\<close> show ?thesis
          by (rule multi_wf_history_local_elsewhere)
      qed
    qed
  qed
qed

lemma multi_adv_admissible:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc: "p_c \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "adversary_admissible correct (multi_adv p_a p_b p_c)"
proof -
  have wf: "wf_history (multi_H p_a p_b p_c)"
    using ab ac bc by (rule multi_wf_history)
  have i_corr: "adv_i (multi_adv p_a p_b p_c) \<in> correct"
    using pc by (simp add: multi_adv_def)
  have proc_eq:
    "proc_of (adv_e_star (multi_adv p_a p_b p_c)) = adv_i (multi_adv p_a p_b p_c)"
    by (simp add: multi_adv_def)
  have target_in:
    "adv_e_star (multi_adv p_a p_b p_c)
        \<in> events_of (adv_E (multi_adv p_a p_b p_c))"
    using ab ac bc by (simp add: multi_adv_def multi_H_events)
  show ?thesis
    using wf i_corr proc_eq target_in
    by (simp add: adversary_admissible_def multi_adv_def)
qed

section \<open>The naive algorithm solves \<open>CD_B\<close> at the multihop adversary\<close>

text \<open>Headline multihop demo: the naive algorithm at
\<open>recv_from_history\<close> solves \<open>CD_B\<close> at the multihop adversary
(target event at \<open>p_c\<close> via a two-hop bhb chain).\<close>

theorem T6_multihop_demo:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc: "p_c \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "valid_B correct (adv_E (multi_adv p_a p_b p_c))
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i (multi_adv p_a p_b p_c))
                                            (adv_E (multi_adv p_a p_b p_c)))
                        (adv_i (multi_adv p_a p_b p_c))
                        (adv_e_star (multi_adv p_a p_b p_c))))
                 (adv_e_star (multi_adv p_a p_b p_c))"
proof -
  let ?cfg = "multi_cfg5 p_a p_b p_c"
  let ?adv = "multi_adv p_a p_b p_c"
  have run_cfg: "run ?cfg"
    by (rule multi_run[OF pa pb pc ab ac bc])
  have drained: "cfg_inflight ?cfg = empty_inflight"
    by (rule multi_drained)
  have adm: "adversary_admissible correct ?adv"
    by (rule multi_adv_admissible[OF pa pb pc ab ac bc])
  have adv_E_eq: "adv_E ?adv = cfg_hist ?cfg"
    using multi_cfg_hist_eq[of p_a p_b p_c] by (simp add: multi_adv_def)
  show ?thesis
    by (rule fair_drained_run_solves_CD_B_unicast[OF run_cfg drained adm adv_E_eq])
qed

text \<open>Existential witness: T6 is non-vacuously satisfiable at the
multihop scenario whenever three distinct correct processes
exist.\<close>

theorem T6_multihop_witnessed:
  assumes three_correct:
    "\<exists>p_a p_b p_c. p_a \<in> correct \<and> p_b \<in> correct \<and> p_c \<in> correct
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
    where pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc: "p_c \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
    using three_correct by blast
  let ?cfg = "multi_cfg5 p_a p_b p_c"
  let ?adv = "multi_adv p_a p_b p_c"
  have run_cfg: "run ?cfg" by (rule multi_run[OF pa pb pc ab ac bc])
  have drained: "cfg_inflight ?cfg = empty_inflight" by (rule multi_drained)
  have adm: "adversary_admissible correct ?adv"
    by (rule multi_adv_admissible[OF pa pb pc ab ac bc])
  have adv_E_eq: "adv_E ?adv = cfg_hist ?cfg"
    using multi_cfg_hist_eq[of p_a p_b p_c] by (simp add: multi_adv_def)
  have solves: "valid_B correct (adv_E ?adv)
                       (fst (naive_cd_B_alg
                              (recv_from_history (adv_i ?adv) (adv_E ?adv))
                              (adv_i ?adv) (adv_e_star ?adv)))
                       (adv_e_star ?adv)"
    by (rule T6_multihop_demo[OF pa pb pc ab ac bc])
  from run_cfg drained adm adv_E_eq solves show ?thesis by blast
qed

section \<open>The transitive bhb chain through three correct processes\<close>

text \<open>We expose the two-hop \<open>\<rightarrow>\<^sub>B\<close> chain from \<open>p_b\<close>'s send through
\<open>p_a\<close>'s relay to \<open>p_c\<close>'s target.  This is the substantive content
of the multihop demo beyond the 1-message case: a causal
dependency that crosses two messages and three processes is
correctly captured by the bhb relation.\<close>

lemma multi_send_to_recv_at_pa_is_message_order:
  assumes ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "message_order (multi_H p_a p_b p_c)
           (Send p_b 1 p_a 1) (Receive p_a 1 p_b 1)"
  using ab ac bc unfolding message_order_def
  by (simp add: multi_H_events)

lemma multi_recv_to_send_at_pa_is_program_order:
  assumes ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "program_order (multi_H p_a p_b p_c)
           (Receive p_a 1 p_b 1) (Send p_a 2 p_c 2)"
proof -
  let ?H = "multi_H p_a p_b p_c"
  have list_eq: "?H p_a = [Receive p_a 1 p_b 1, Send p_a 2 p_c 2]"
    using ab ac by (rule multi_H_at_p_a)
  have len: "length (?H p_a) = 2" by (simp add: list_eq)
  have e0: "(?H p_a) ! 0 = Receive p_a 1 p_b 1" by (simp add: list_eq)
  have e1: "(?H p_a) ! 1 = Send p_a 2 p_c 2" by (simp add: list_eq)
  have "(0 :: nat) < 1" by simp
  moreover have "(1 :: nat) < length (?H p_a)" using len by simp
  ultimately show ?thesis
    using e0 e1 unfolding program_order_def by blast
qed

lemma multi_send_to_recv_at_pc_is_message_order:
  assumes ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "message_order (multi_H p_a p_b p_c)
           (Send p_a 2 p_c 2) (Receive p_c 1 p_a 2)"
  using ab ac bc unfolding message_order_def
  by (simp add: multi_H_events)

lemma multi_recv_to_internal_at_pc_is_program_order:
  assumes ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "program_order (multi_H p_a p_b p_c)
           (Receive p_c 1 p_a 2) (Internal p_c 2)"
proof -
  let ?H = "multi_H p_a p_b p_c"
  have list_eq: "?H p_c = [Receive p_c 1 p_a 2, Internal p_c 2]"
    using ac bc by (rule multi_H_at_p_c)
  have len: "length (?H p_c) = 2" by (simp add: list_eq)
  have e0: "(?H p_c) ! 0 = Receive p_c 1 p_a 2" by (simp add: list_eq)
  have e1: "(?H p_c) ! 1 = Internal p_c 2" by (simp add: list_eq)
  have "(0 :: nat) < 1" by simp
  moreover have "(1 :: nat) < length (?H p_c)" using len by simp
  ultimately show ?thesis
    using e0 e1 unfolding program_order_def by blast
qed

text \<open>The full bhb chain: \<open>Send p_b 1 p_a 1\<close> bhb-precedes
\<open>Internal p_c 2\<close> through four hops crossing three processes.\<close>

theorem multi_bhb_chain:
  assumes pa: "p_a \<in> correct" and pb: "p_b \<in> correct" and pc: "p_c \<in> correct"
      and ab: "p_a \<noteq> p_b" and ac: "p_a \<noteq> p_c" and bc: "p_b \<noteq> p_c"
  shows "bhb correct (multi_H p_a p_b p_c)
           (Send p_b 1 p_a 1) (Internal p_c 2)"
proof -
  let ?H = "multi_H p_a p_b p_c"
  let ?e1 = "Send p_b 1 p_a 1"
  let ?e2 = "Receive p_a 1 p_b 1"
  let ?e3 = "Send p_a 2 p_c 2"
  let ?e4 = "Receive p_c 1 p_a 2"
  let ?e5 = "Internal p_c 2"

  have proc_e1: "proc_of ?e1 = p_b" by simp
  have proc_e2: "proc_of ?e2 = p_a" by simp
  have proc_e3: "proc_of ?e3 = p_a" by simp
  have proc_e4: "proc_of ?e4 = p_c" by simp
  have proc_e5: "proc_of ?e5 = p_c" by simp

  have step12: "bhb_step correct ?H ?e1 ?e2"
    using pa pb proc_e1 proc_e2
          multi_send_to_recv_at_pa_is_message_order[OF ab ac bc]
    unfolding bhb_step_def by simp
  have step23: "bhb_step correct ?H ?e2 ?e3"
    using pa proc_e2 proc_e3
          multi_recv_to_send_at_pa_is_program_order[OF ab ac bc]
    unfolding bhb_step_def by simp
  have step34: "bhb_step correct ?H ?e3 ?e4"
    using pa pc proc_e3 proc_e4
          multi_send_to_recv_at_pc_is_message_order[OF ab ac bc]
    unfolding bhb_step_def by simp
  have step45: "bhb_step correct ?H ?e4 ?e5"
    using pc proc_e4 proc_e5
          multi_recv_to_internal_at_pc_is_program_order[OF ac bc]
    unfolding bhb_step_def by simp

  have t12: "(bhb_step correct ?H)\<^sup>+\<^sup>+ ?e1 ?e2" using step12 by blast
  have t23: "(bhb_step correct ?H)\<^sup>+\<^sup>+ ?e2 ?e3" using step23 by blast
  have t34: "(bhb_step correct ?H)\<^sup>+\<^sup>+ ?e3 ?e4" using step34 by blast
  have t45: "(bhb_step correct ?H)\<^sup>+\<^sup>+ ?e4 ?e5" using step45 by blast
  have t13: "(bhb_step correct ?H)\<^sup>+\<^sup>+ ?e1 ?e3" using t12 t23 by (rule tranclp_trans)
  have t14: "(bhb_step correct ?H)\<^sup>+\<^sup>+ ?e1 ?e4" using t13 t34 by (rule tranclp_trans)
  have "(bhb_step correct ?H)\<^sup>+\<^sup>+ ?e1 ?e5" using t14 t45 by (rule tranclp_trans)
  thus ?thesis unfolding bhb_def .
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
