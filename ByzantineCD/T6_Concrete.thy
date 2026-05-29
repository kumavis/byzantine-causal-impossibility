(*
  Title:   T6_Concrete.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  A fully-concrete end-to-end demonstration of paper Theorem 6
  (CD_B solvable under unicast, no cryptography).

  The existing development states T6 at four increasing levels of
  operational fidelity:

    1. Abstract (\<open>CD_B_Algorithm.CD_B_solvable_unicast\<close>):
       \<exists>alg. produces_valid_F_B_recv correct alg, under
       correct_reporting.

    2. Operational with mode_admissible
       (\<open>Delivery.CD_B_solvable_unicast_operational\<close>):
       under mode_admissible Unicast on the adversary's history,
       the naive algorithm solves CD_B.

    3. Operational with explicit run_step
       (\<open>Primitives.fair_drained_run_solves_CD_B_unicast\<close>):
       any fair drained run of the inductive run_step model
       satisfies mode_admissible Unicast on its history, and the
       naive algorithm at that configuration solves CD_B.

    4. Named explicitly via BRU
       (\<open>Primitives.bru_solves_CD_B_unicast\<close>):
       under BRU on the adversary's history, the naive algorithm
       solves CD_B.

  This theory adds a fifth, fully concrete level: a 2-process
  worked example.  Two distinct correct processes \<open>p_a\<close>, \<open>p_b\<close>
  participate; \<open>p_b\<close> sends one message to \<open>p_a\<close>; \<open>p_a\<close> receives
  it and then performs an internal event.  We construct the
  corresponding three-step \<open>run_step\<close> sequence explicitly, prove
  it produces the expected configuration, and apply T6's
  operational form to conclude that the naive algorithm solves
  CD_B at the resulting adversary.

  This is the smallest non-trivial concrete instance of T6: it
  exercises step_send, step_recv, and step_internal of the
  inductive run model, threads them through a fair drained run,
  and demonstrates that the headline T6 theorem is non-vacuous --
  there is an actual adversary, an actual run, and an actual
  algorithm output that witness the theorem's content.

  Scope.  This is a worked example, not a generalisation of T6.
  A fully constructive ``every mode_admissible Unicast history
  is reachable via run_step'' theorem would require a
  topological-sort proof on the hb partial order plus careful
  handling of Byzantine events; it is left as future work in
  ROADMAP.md.  The example below covers correct-only histories,
  which is the substantive content of T6.
*)

theory T6_Concrete
  imports Primitives
begin

context byzantineSystem
begin

section \<open>Demo scenario: two correct processes, one send and receive\<close>

text \<open>The target history of the demonstration.  Two distinct
correct processes \<open>p_a\<close> and \<open>p_b\<close>: \<open>p_b\<close> sends one message
\<open>m = 0\<close> to \<open>p_a\<close>; \<open>p_a\<close> receives it; \<open>p_a\<close> then performs an
internal event.  Other processes have empty histories.\<close>

definition demo_H :: "'p \<Rightarrow> 'p \<Rightarrow> 'p history" where
  "demo_H p_a p_b =
     (\<lambda>p. if p = p_a then [Receive p_a 1 p_b 0, Internal p_a 2]
          else if p = p_b then [Send p_b 1 p_a 0]
          else [])"

definition demo_adv :: "'p \<Rightarrow> 'p \<Rightarrow> 'p adversary" where
  "demo_adv p_a p_b =
     \<lparr> adv_E = demo_H p_a p_b,
       adv_e_star = Internal p_a 2,
       adv_i = p_a \<rparr>"

text \<open>The events that appear in the demo history.\<close>

lemma demo_H_at_p_a:
  assumes "p_a \<noteq> p_b"
  shows "demo_H p_a p_b p_a = [Receive p_a 1 p_b 0, Internal p_a 2]"
  using assms by (simp add: demo_H_def)

lemma demo_H_at_p_b:
  assumes "p_a \<noteq> p_b"
  shows "demo_H p_a p_b p_b = [Send p_b 1 p_a 0]"
  using assms by (simp add: demo_H_def)

lemma demo_H_elsewhere:
  assumes "p \<noteq> p_a" "p \<noteq> p_b"
  shows "demo_H p_a p_b p = []"
  using assms by (simp add: demo_H_def)

lemma demo_H_events:
  assumes "p_a \<noteq> p_b"
  shows "events_of (demo_H p_a p_b) =
           {Receive p_a 1 p_b 0, Internal p_a 2, Send p_b 1 p_a 0}"
proof -
  have "events_of (demo_H p_a p_b) = (\<Union>p. set (demo_H p_a p_b p))"
    by (simp add: events_of_def)
  also have "\<dots> = set (demo_H p_a p_b p_a) \<union> set (demo_H p_a p_b p_b)
                   \<union> (\<Union>p \<in> -{p_a, p_b}. set (demo_H p_a p_b p))"
    by auto
  also have "set (demo_H p_a p_b p_a) = {Receive p_a 1 p_b 0, Internal p_a 2}"
    using assms by (simp add: demo_H_at_p_a)
  moreover have "set (demo_H p_a p_b p_b) = {Send p_b 1 p_a 0}"
    using assms by (simp add: demo_H_at_p_b)
  moreover have "(\<Union>p \<in> -{p_a, p_b}. set (demo_H p_a p_b p)) = {}"
    by (auto simp: demo_H_elsewhere)
  ultimately show ?thesis by auto
qed

section \<open>The three configurations along the demo run\<close>

text \<open>Three intermediate configurations, named after the step
that produced them.  Starting from \<open>init_config\<close>:

\<^item> \<open>cfg0 = init_config\<close>
\<^item> \<open>cfg1 = after step_send p_b 1 p_a 0\<close>
\<^item> \<open>cfg2 = after step_recv p_a 1 p_b 0\<close>
\<^item> \<open>cfg3 = after step_internal p_a 2\<close> (this is the drained
  final configuration)\<close>

definition demo_cfg1 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "demo_cfg1 p_a p_b =
     \<lparr> cfg_hist = (\<lambda>p. if p = p_b then [Send p_b 1 p_a 0] else []),
       cfg_inflight = empty_inflight \<union># {# (p_b, p_a, 0) } \<rparr>"

definition demo_cfg2 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "demo_cfg2 p_a p_b =
     \<lparr> cfg_hist = (\<lambda>p. if p = p_a then [Receive p_a 1 p_b 0]
                        else if p = p_b then [Send p_b 1 p_a 0]
                        else []),
       cfg_inflight = empty_inflight \<rparr>"

definition demo_cfg3 :: "'p \<Rightarrow> 'p \<Rightarrow> 'p config" where
  "demo_cfg3 p_a p_b =
     \<lparr> cfg_hist = demo_H p_a p_b,
       cfg_inflight = empty_inflight \<rparr>"

section \<open>The three run\<open>_step\<close> transitions\<close>

text \<open>Step 1: \<open>p_b\<close> sends to \<open>p_a\<close>, getting the buffer entry
\<open>(p_b, p_a, 0)\<close>.\<close>

lemma demo_step_send:
  assumes pa: "p_a \<in> correct"
      and pb: "p_b \<in> correct"
  shows "run_step init_config (demo_cfg1 p_a p_b)"
proof -
  let ?cfg0 = "init_config"
  have hist_pb_init: "cfg_hist ?cfg0 p_b = []"
    by (simp add: init_config_def)
  have n_eq: "(1 :: nat) = Suc (length (cfg_hist ?cfg0 p_b))"
    using hist_pb_init by simp
  have hist_eq: "cfg_hist (demo_cfg1 p_a p_b)
                  = (cfg_hist ?cfg0)
                      (p_b := cfg_hist ?cfg0 p_b @ [Send p_b 1 p_a 0])"
    by (rule ext) (simp add: demo_cfg1_def init_config_def)
  have inflight_eq: "cfg_inflight (demo_cfg1 p_a p_b)
                       = cfg_inflight ?cfg0 \<union># {# (p_b, p_a, 0) }"
    by (simp add: demo_cfg1_def init_config_def)
  have cfg_eq: "demo_cfg1 p_a p_b
                  = ?cfg0 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg0)
                                (p_b := cfg_hist ?cfg0 p_b @ [Send p_b 1 p_a 0]),
                            cfg_inflight :=
                              cfg_inflight ?cfg0 \<union># {# (p_b, p_a, 0) } \<rparr>"
    using hist_eq inflight_eq by (simp add: demo_cfg1_def init_config_def)
  show ?thesis
    by (rule run_step.step_send[OF pb pa n_eq cfg_eq])
qed

text \<open>Step 2: \<open>p_a\<close> receives the buffered message from \<open>p_b\<close>,
producing the matching receive event.\<close>

lemma demo_step_recv:
  assumes pa: "p_a \<in> correct"
      and pb: "p_b \<in> correct"
      and dist: "p_a \<noteq> p_b"
  shows "run_step (demo_cfg1 p_a p_b) (demo_cfg2 p_a p_b)"
proof -
  let ?cfg1 = "demo_cfg1 p_a p_b"
  have buf_in: "(p_b, p_a, 0) \<in># cfg_inflight ?cfg1"
    by (simp add: demo_cfg1_def empty_inflight_def)
  have hist_pa_eq: "cfg_hist ?cfg1 p_a = []"
    using dist by (simp add: demo_cfg1_def)
  have n_eq: "(1 :: nat) = Suc (length (cfg_hist ?cfg1 p_a))"
    using hist_pa_eq by simp
  have hist_eq: "cfg_hist (demo_cfg2 p_a p_b)
                  = (cfg_hist ?cfg1)
                      (p_a := cfg_hist ?cfg1 p_a @ [Receive p_a 1 p_b 0])"
    using dist hist_pa_eq
    by (rule_tac ext) (simp add: demo_cfg1_def demo_cfg2_def)
  have inflight_eq: "cfg_inflight (demo_cfg2 p_a p_b)
                       = cfg_inflight ?cfg1 -# (p_b, p_a, 0)"
    by (rule ext) (simp add: demo_cfg1_def demo_cfg2_def empty_inflight_def)
  have cfg_eq: "demo_cfg2 p_a p_b
                  = ?cfg1 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg1)
                                (p_a := cfg_hist ?cfg1 p_a @ [Receive p_a 1 p_b 0]),
                            cfg_inflight :=
                              cfg_inflight ?cfg1 -# (p_b, p_a, 0) \<rparr>"
    using hist_eq inflight_eq by (simp add: demo_cfg2_def)
  show ?thesis
    by (rule run_step.step_recv[OF pa pb buf_in n_eq cfg_eq])
qed

text \<open>Step 3: \<open>p_a\<close> performs an internal event, completing the
local history at the target event.\<close>

lemma demo_step_internal:
  assumes pa: "p_a \<in> correct"
      and dist: "p_a \<noteq> p_b"
  shows "run_step (demo_cfg2 p_a p_b) (demo_cfg3 p_a p_b)"
proof -
  let ?cfg2 = "demo_cfg2 p_a p_b"
  have hist_pa_eq: "cfg_hist ?cfg2 p_a = [Receive p_a 1 p_b 0]"
    using dist by (simp add: demo_cfg2_def)
  have n_eq: "(2 :: nat) = Suc (length (cfg_hist ?cfg2 p_a))"
    using hist_pa_eq by simp
  have hist_eq: "cfg_hist (demo_cfg3 p_a p_b)
                  = (cfg_hist ?cfg2)
                      (p_a := cfg_hist ?cfg2 p_a @ [Internal p_a 2])"
    using dist hist_pa_eq
    by (rule_tac ext) (simp add: demo_cfg2_def demo_cfg3_def demo_H_def)
  have inflight_eq: "cfg_inflight (demo_cfg3 p_a p_b)
                       = cfg_inflight ?cfg2"
    by (simp add: demo_cfg2_def demo_cfg3_def)
  have cfg_eq: "demo_cfg3 p_a p_b
                  = ?cfg2 \<lparr> cfg_hist :=
                              (cfg_hist ?cfg2)
                                (p_a := cfg_hist ?cfg2 p_a @ [Internal p_a 2]) \<rparr>"
    using hist_eq inflight_eq by (simp add: demo_cfg3_def)
  show ?thesis
    by (rule run_step.step_internal[OF pa n_eq cfg_eq])
qed

section \<open>The demo run is fair, drained, and produces \<open>demo_H\<close>\<close>

text \<open>Composing the three steps into a single @{const run}: from
\<open>init_config\<close> via three @{const run_step} transitions to
\<open>demo_cfg3\<close>.\<close>

lemma demo_run:
  assumes pa: "p_a \<in> correct"
      and pb: "p_b \<in> correct"
      and dist: "p_a \<noteq> p_b"
  shows "run (demo_cfg3 p_a p_b)"
proof -
  have base: "run init_config" by simp
  have s1: "run_step init_config (demo_cfg1 p_a p_b)"
    by (rule demo_step_send[OF pa pb])
  have r1: "run (demo_cfg1 p_a p_b)"
    by (rule run_extend[OF base s1])
  have s2: "run_step (demo_cfg1 p_a p_b) (demo_cfg2 p_a p_b)"
    by (rule demo_step_recv[OF pa pb dist])
  have r2: "run (demo_cfg2 p_a p_b)"
    by (rule run_extend[OF r1 s2])
  have s3: "run_step (demo_cfg2 p_a p_b) (demo_cfg3 p_a p_b)"
    by (rule demo_step_internal[OF pa dist])
  show ?thesis by (rule run_extend[OF r2 s3])
qed

lemma demo_drained:
  shows "cfg_inflight (demo_cfg3 p_a p_b) = empty_inflight"
  by (simp add: demo_cfg3_def)

lemma demo_cfg_hist_eq:
  shows "cfg_hist (demo_cfg3 p_a p_b) = demo_H p_a p_b"
  by (simp add: demo_cfg3_def)

section \<open>The naive algorithm solves CD\<open>_B\<close> at the demo adversary\<close>

text \<open>Adversary admissibility on the demo adversary: the target
event @{term "Internal p_a 2"} is at @{term p_a} (which is correct
by assumption) and lies in @{term "events_of (demo_H p_a p_b)"}.\<close>

lemma demo_wf_history_local_p_a:
  assumes "p_a \<noteq> p_b"
  shows "wf_history_local p_a (demo_H p_a p_b p_a)"
proof -
  let ?L = "[Receive p_a 1 p_b 0, Internal p_a 2]"
  have list_eq: "demo_H p_a p_b p_a = ?L"
    using assms by (rule demo_H_at_p_a)
  have proc_ok: "\<forall>e \<in> set ?L. proc_of e = p_a" by simp
  have seq_ok: "\<forall>k < length ?L. seq_of (?L ! k) = Suc k"
  proof (intro allI impI)
    fix k assume "k < length ?L"
    hence "k = 0 \<or> k = 1" by auto
    thus "seq_of (?L ! k) = Suc k" by auto
  qed
  show ?thesis
    using list_eq proc_ok seq_ok
    unfolding wf_history_local_def by simp
qed

lemma demo_wf_history_local_p_b:
  assumes "p_a \<noteq> p_b"
  shows "wf_history_local p_b (demo_H p_a p_b p_b)"
proof -
  let ?L = "[Send p_b 1 p_a 0]"
  have list_eq: "demo_H p_a p_b p_b = ?L"
    using assms by (rule demo_H_at_p_b)
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

lemma demo_wf_history_local_elsewhere:
  assumes "p \<noteq> p_a" "p \<noteq> p_b"
  shows "wf_history_local p (demo_H p_a p_b p)"
  using assms by (simp add: demo_H_elsewhere wf_history_local_def)

lemma demo_wf_history:
  assumes "p_a \<noteq> p_b"
  shows "wf_history (demo_H p_a p_b)"
proof (unfold wf_history_def, intro allI)
  fix p
  show "wf_history_local p (demo_H p_a p_b p)"
  proof (cases "p = p_a")
    case True
    thus ?thesis using assms demo_wf_history_local_p_a by simp
  next
    case False
    show ?thesis
    proof (cases "p = p_b")
      case True
      thus ?thesis using assms demo_wf_history_local_p_b by simp
    next
      case False
      with \<open>p \<noteq> p_a\<close> show ?thesis
        by (rule demo_wf_history_local_elsewhere)
    qed
  qed
qed

lemma demo_adv_admissible:
  assumes pa: "p_a \<in> correct"
      and pb: "p_b \<in> correct"
      and dist: "p_a \<noteq> p_b"
  shows "adversary_admissible correct (demo_adv p_a p_b)"
proof -
  have wf: "wf_history (demo_H p_a p_b)"
    using dist by (rule demo_wf_history)
  have i_corr: "adv_i (demo_adv p_a p_b) \<in> correct"
    using pa by (simp add: demo_adv_def)
  have proc_eq:
    "proc_of (adv_e_star (demo_adv p_a p_b)) = adv_i (demo_adv p_a p_b)"
    by (simp add: demo_adv_def)
  have target_in:
    "adv_e_star (demo_adv p_a p_b) \<in> events_of (adv_E (demo_adv p_a p_b))"
    using dist by (simp add: demo_adv_def demo_H_events)
  have hist_eq: "adv_E (demo_adv p_a p_b) = demo_H p_a p_b"
    by (simp add: demo_adv_def)
  show ?thesis
    using wf i_corr proc_eq target_in
    by (simp add: adversary_admissible_def demo_adv_def)
qed

text \<open>The headline concrete-demo theorem.  Composing the
3-step run with @{thm fair_drained_run_solves_CD_B_unicast} gives
that the naive algorithm at the demo configuration's
@{const recv_from_history} view solves \<open>CD_B\<close> at the demo
adversary's target event.

Spelled out: under the demo adversary, the naive algorithm
\<^enum> takes its received view to be exactly the global history
  (\<open>recv = adv_E adv\<close>),
\<^enum> outputs \<open>F = adv_E adv\<close>,
\<^enum> satisfies @{const valid_B}\<open>(adv_E adv, F, Internal p_a 2)\<close>
  trivially because \<open>F = adv_E adv\<close>.

The composition rests on:
\<^enum> @{thm demo_run}: \<open>run (demo_cfg3 p_a p_b)\<close>.
\<^enum> @{thm demo_drained}: the in-flight buffer is empty at
  \<open>demo_cfg3\<close>.
\<^enum> @{thm demo_adv_admissible}: the demo adversary is admissible
  for the correct set.
\<^enum> @{thm demo_cfg_hist_eq}: \<open>cfg_hist (demo_cfg3 p_a p_b)\<close>
  equals \<open>demo_H p_a p_b\<close>, which is \<open>adv_E (demo_adv p_a p_b)\<close>.\<close>

theorem T6_concrete_demo:
  assumes pa: "p_a \<in> correct"
      and pb: "p_b \<in> correct"
      and dist: "p_a \<noteq> p_b"
  shows "valid_B correct (adv_E (demo_adv p_a p_b))
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i (demo_adv p_a p_b))
                                            (adv_E (demo_adv p_a p_b)))
                        (adv_i (demo_adv p_a p_b))
                        (adv_e_star (demo_adv p_a p_b))))
                 (adv_e_star (demo_adv p_a p_b))"
proof -
  let ?cfg = "demo_cfg3 p_a p_b"
  let ?adv = "demo_adv p_a p_b"
  have run_cfg:    "run ?cfg"
    by (rule demo_run[OF pa pb dist])
  have drained:    "cfg_inflight ?cfg = empty_inflight"
    by (rule demo_drained)
  have adm:        "adversary_admissible correct ?adv"
    by (rule demo_adv_admissible[OF pa pb dist])
  have adv_E_eq:   "adv_E ?adv = cfg_hist ?cfg"
    using demo_cfg_hist_eq[of p_a p_b] by (simp add: demo_adv_def)
  show ?thesis
    by (rule fair_drained_run_solves_CD_B_unicast[OF run_cfg drained adm adv_E_eq])
qed

section \<open>Existence of a non-trivial T6 witness\<close>

text \<open>From the concrete-demo theorem we extract the headline
existence statement: under the standard locale assumption that
two distinct correct processes exist, the operational \<open>CD_B\<close>
unicast theorem is non-vacuously satisfiable -- there is an
admissible adversary, a fair drained run, and an algorithm output
witnessing T6's content.\<close>

theorem T6_witnessed:
  assumes two_correct: "\<exists>p_a p_b. p_a \<in> correct \<and> p_b \<in> correct \<and> p_a \<noteq> p_b"
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
  obtain p_a p_b where pa: "p_a \<in> correct" and pb: "p_b \<in> correct"
                       and dist: "p_a \<noteq> p_b"
    using two_correct by blast
  let ?cfg = "demo_cfg3 p_a p_b"
  let ?adv = "demo_adv p_a p_b"
  have run_cfg: "run ?cfg" by (rule demo_run[OF pa pb dist])
  have drained: "cfg_inflight ?cfg = empty_inflight" by (rule demo_drained)
  have adm: "adversary_admissible correct ?adv"
    by (rule demo_adv_admissible[OF pa pb dist])
  have adv_E_eq: "adv_E ?adv = cfg_hist ?cfg"
    using demo_cfg_hist_eq[of p_a p_b] by (simp add: demo_adv_def)
  have solves: "valid_B correct (adv_E ?adv)
                       (fst (naive_cd_B_alg
                              (recv_from_history (adv_i ?adv) (adv_E ?adv))
                              (adv_i ?adv) (adv_e_star ?adv)))
                       (adv_e_star ?adv)"
    by (rule T6_concrete_demo[OF pa pb dist])
  from run_cfg drained adm adv_E_eq solves show ?thesis by blast
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
