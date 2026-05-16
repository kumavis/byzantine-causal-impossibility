(*
  Title:   Liveness.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  Real-world fairness on the inductive execution model of
  Execution_Model.thy.  Closes the closing-remarks gap of that
  theory: "every fair infinite execution eventually has empty
  buffer".

  The infinite-execution layer is modelled as
  \<open>nat \<Rightarrow> 'p config\<close> with a side condition that each adjacent
  pair satisfies \<open>run_step\<close>.  No coinductive datatype machinery is
  introduced; the function-from-nat shape is the standard "stream"
  representation that does not require importing Coinductive_Stream
  or HOLCF.

  The fairness predicate is the standard "every continuously
  buffered triple is eventually removed" condition:

    \<forall>i p q m.
       (p, q, m) \<in># cfg_inflight (E i)
         \<longrightarrow> (\<exists>j \<ge> i. \<not> (p, q, m) \<in># cfg_inflight (E j)).

  The headline liveness theorem (\<open>fair_run_delivers\<close>) says: in a
  fair infinite run, every correct-to-correct \<open>Send\<close> event
  eventually has a matching \<open>Receive\<close> event.  Its proof composes:

  - finite-prefix run invariants (\<open>sends_match_inv_run\<close> from
    Execution_Model.thy, lifted pointwise to every step of an
    infinite run);
  - "if a triple is in the buffer at step i but not at step j
    (i \<le> j), then a \<open>step_recv\<close> happened in between"
    (\<open>step_removes_triple_is_recv\<close>);
  - monotonicity of \<open>events_of (cfg_hist (E _))\<close> in the index, so
    the receive event found at some intermediate step persists at
    step j.

  Together with the deadlock-freedom theorem
  \<open>not_drained_can_step\<close> of Execution_Model.thy, this gives a
  complete operational story for the unicast / broadcast cases of
  Phase 4 / Phase 5 / Phase 6 / Phase 7 / Phase 8:

  - A non-empty buffer always permits a step (deadlock freedom).
  - A fair infinite execution delivers every correct-to-correct
    send (liveness, here).
  - An execution whose buffer becomes empty has a
    mode-admissible history (already proven in
    \<open>run_completes_to_mode_admissible_unicast/_broadcast\<close>).

  Deviations from a full TLA-style formalisation:

    1. Fairness here is stated globally as a single
       quantifier-prefix condition on the in-flight multiset, not
       as a per-action enabled-then-eventually-taken predicate.
       The two formulations agree for our model because the only
       enabling condition on \<open>step_recv\<close> is membership in the
       buffer; we capture the conclusion of fairness ("the triple
       eventually leaves the buffer") directly rather than the
       scheduling assumption.

    2. We do not introduce a separate codatatype of streams.
       \<open>nat \<Rightarrow> 'p config\<close> is enough for the liveness theorem we
       want, and matches the existing finite-prefix \<open>run\<close>
       predicate one-for-one (each prefix \<open>E 0, \<dots>, E i\<close> of an
       infinite run is itself a finite run; see
       \<open>infinite_run_reach_each\<close>).
*)

theory Liveness
  imports Execution_Model
begin

context byzantineSystem
begin

section \<open>Infinite executions\<close>

text \<open>An infinite execution starts at \<open>init_config\<close> and takes a
single \<open>run_step\<close> at every adjacent index.  Treating an infinite
execution as a function \<open>nat \<Rightarrow> 'p config\<close> sidesteps the need for
a coinductive stream codatatype while still letting us state and
prove temporal properties (``eventually'', ``always'').\<close>

definition infinite_run :: "(nat \<Rightarrow> 'p config) \<Rightarrow> bool" where
  "infinite_run E \<longleftrightarrow>
     E 0 = init_config \<and> (\<forall>i. run_step (E i) (E (Suc i)))"

text \<open>Every prefix of an infinite run is itself a finite run.
Composed with the existing invariant lemmas
(\<open>wf_history_run\<close>, \<open>sends_match_inv_run\<close>,
\<open>buffer_correct_inv_run\<close>) this gives the pointwise invariants
below.\<close>

lemma infinite_run_reach_each:
  assumes "infinite_run E"
  shows   "run (E i)"
proof (induction i)
  case 0
  have "E 0 = init_config" using assms by (simp add: infinite_run_def)
  thus ?case by (simp add: run_def)
next
  case (Suc i)
  have step: "run_step (E i) (E (Suc i))"
    using assms by (simp add: infinite_run_def)
  show ?case by (rule run_extend[OF Suc.IH step])
qed

corollary infinite_run_wf_history:
  assumes "infinite_run E"
  shows   "wf_history (cfg_hist (E i))"
  using wf_history_run[OF infinite_run_reach_each[OF assms, of i]] .

corollary infinite_run_sends_match_inv:
  assumes "infinite_run E"
  shows   "sends_match_inv (E i)"
  using sends_match_inv_run[OF infinite_run_reach_each[OF assms, of i]] .

corollary infinite_run_buffer_correct_inv:
  assumes "infinite_run E"
  shows   "buffer_correct_inv (E i)"
  using buffer_correct_inv_run[OF infinite_run_reach_each[OF assms, of i]] .

section \<open>Event monotonicity in the run index\<close>

text \<open>Every kind of step appends exactly one event to a single
process's history.  In particular, \<open>events_of (cfg_hist _)\<close> only
grows.\<close>

lemma run_step_hist_extends:
  assumes "run_step cfg cfg'"
  shows "\<exists>p e. cfg_hist cfg' = (cfg_hist cfg)(p := cfg_hist cfg p @ [e])"
  using assms
proof induction
  case (step_internal p n cfg cfg')
  show ?case using step_internal.hyps(3) by auto
next
  case (step_send p q n cfg cfg' m)
  show ?case using step_send.hyps(4) by auto
next
  case (step_recv q p m cfg n cfg')
  show ?case using step_recv.hyps(5) by auto
next
  case (step_byzantine p new_event cfg cfg')
  show ?case using step_byzantine.hyps(4) by auto
qed

lemma events_of_subset_step:
  assumes "run_step cfg cfg'"
  shows "events_of (cfg_hist cfg) \<subseteq> events_of (cfg_hist cfg')"
proof -
  obtain p e where eq:
    "cfg_hist cfg' = (cfg_hist cfg)(p := cfg_hist cfg p @ [e])"
    using run_step_hist_extends[OF assms] by blast
  hence "events_of (cfg_hist cfg') = events_of (cfg_hist cfg) \<union> {e}"
    by (simp add: events_of_extend)
  thus ?thesis by blast
qed

lemma events_of_subset_infinite:
  assumes inf: "infinite_run E"
      and ij:  "i \<le> j"
  shows "events_of (cfg_hist (E i)) \<subseteq> events_of (cfg_hist (E j))"
  using ij
proof (induction j)
  case 0
  hence "i = 0" by simp
  thus ?case by simp
next
  case (Suc j)
  show ?case
  proof (cases "i = Suc j")
    case True
    thus ?thesis by simp
  next
    case False
    with Suc.prems have "i \<le> j" by simp
    hence sub1: "events_of (cfg_hist (E i)) \<subseteq> events_of (cfg_hist (E j))"
      by (rule Suc.IH)
    have step: "run_step (E j) (E (Suc j))"
      using inf by (simp add: infinite_run_def)
    have sub2: "events_of (cfg_hist (E j)) \<subseteq> events_of (cfg_hist (E (Suc j)))"
      by (rule events_of_subset_step[OF step])
    show ?thesis using sub1 sub2 by blast
  qed
qed

section \<open>A buffer triple can only disappear via \<open>step_recv\<close>\<close>

text \<open>The pivotal technical lemma: if a triple is in the buffer
before a step and not after, the step must be \<open>step_recv\<close>
removing that very triple -- which also adds a matching
\<open>Receive\<close> event to the history.

The variables \<open>pp, qq, mm\<close> name the triple from outside the
lemma, to avoid name clashes with the case-bound variables of the
\<open>run_step\<close> rule (which use \<open>p, q, m\<close>).\<close>

lemma step_removes_triple_is_recv:
  fixes pp qq :: 'p and mm :: nat
  assumes "run_step cfg cfg'"
      and "(pp, qq, mm) \<in># cfg_inflight cfg"
      and "\<not> (pp, qq, mm) \<in># cfg_inflight cfg'"
  shows "\<exists>n. Receive qq n pp mm \<in> events_of (cfg_hist cfg')"
  using assms
proof induction
  case (step_internal p n cfg cfg')
  \<comment> \<open>Internal steps leave the buffer unchanged; the assumption
      pair contradicts.\<close>
  have buf: "cfg_inflight cfg' = cfg_inflight cfg"
    using step_internal.hyps(3) by simp
  with step_internal.prems show ?case by simp
next
  case (step_send p q n cfg cfg' m)
  \<comment> \<open>Sends only add to the buffer; \<open>(pp, qq, mm)\<close> stays in.\<close>
  have buf: "cfg_inflight cfg' = cfg_inflight cfg \<union># {# (p, q, m) }"
    using step_send.hyps(4) by simp
  have count_le:
    "cfg_inflight cfg (pp, qq, mm) \<le> cfg_inflight cfg' (pp, qq, mm)"
    using buf by simp
  hence "(pp, qq, mm) \<in># cfg_inflight cfg'"
    using step_send.prems(1) by simp
  with step_send.prems(2) show ?case by simp
next
  case (step_recv q p m cfg n cfg')
  have buf: "cfg_inflight cfg' = cfg_inflight cfg -# (p, q, m)"
    using step_recv.hyps(5) by simp
  show ?case
  proof (cases "(pp, qq, mm) = (p, q, m)")
    case True
    \<comment> \<open>This is the live case: the step adds \<open>Receive q n p m\<close>,
        which equals \<open>Receive qq n pp mm\<close>.\<close>
    have hist_eq:
      "cfg_hist cfg'
         = (cfg_hist cfg)(q := cfg_hist cfg q @ [Receive q n p m])"
      using step_recv.hyps(5) by simp
    have "events_of (cfg_hist cfg')
            = events_of (cfg_hist cfg) \<union> {Receive q n p m}"
      using hist_eq by (simp add: events_of_extend)
    hence "Receive q n p m \<in> events_of (cfg_hist cfg')" by blast
    with True show ?thesis by blast
  next
    case False
    \<comment> \<open>A different triple was removed; \<open>(pp, qq, mm)\<close> count is
        unchanged, contradicting the post-assumption.\<close>
    have eq_count:
      "cfg_inflight cfg' (pp, qq, mm) = cfg_inflight cfg (pp, qq, mm)"
      using False buf by auto
    hence "(pp, qq, mm) \<in># cfg_inflight cfg'"
      using step_recv.prems(1) by simp
    with step_recv.prems(2) show ?thesis by simp
  qed
next
  case (step_byzantine p new_event cfg cfg')
  \<comment> \<open>Byzantine steps leave the buffer unchanged.\<close>
  have buf: "cfg_inflight cfg' = cfg_inflight cfg"
    using step_byzantine.hyps(4) by simp
  with step_byzantine.prems show ?case by simp
qed

section \<open>Finding the step at which a triple is removed\<close>

text \<open>If a triple is in the buffer at index \<open>i\<close> and not in the
buffer at some later index \<open>j\<close>, there is a specific step
\<open>k \<in> [i, j)\<close> where the triple goes from ``in'' to ``out''.  By
@{thm step_removes_triple_is_recv} the step at \<open>k\<close> adds a
matching \<open>Receive\<close>.\<close>

lemma triple_disappears_implies_recv:
  assumes inf:    "infinite_run E"
      and ij:     "i \<le> j"
      and in_buf: "(pp, qq, mm) \<in># cfg_inflight (E i)"
      and out:    "\<not> (pp, qq, mm) \<in># cfg_inflight (E j)"
  shows "\<exists>k n. i \<le> k \<and> k < j
              \<and> Receive qq n pp mm \<in> events_of (cfg_hist (E (Suc k)))"
proof -
  \<comment> \<open>Find the smallest index \<open>k_min \<in> [i, j]\<close> where the triple
      is absent.  It is at least \<open>i + 1\<close>, because the triple is
      present at \<open>i\<close>.\<close>
  define S where
    "S = {k. i \<le> k \<and> k \<le> j \<and> \<not> (pp, qq, mm) \<in># cfg_inflight (E k)}"
  have S_subset: "S \<subseteq> {i..j}" by (auto simp: S_def)
  have S_fin: "finite S"
    using S_subset by (rule finite_subset) simp
  have j_in_S: "j \<in> S"
    using ij out by (simp add: S_def)
  hence S_ne: "S \<noteq> {}" by blast
  define k_min where "k_min = Min S"
  have k_min_in_S: "k_min \<in> S" using S_fin S_ne k_min_def Min_in by blast
  have k_min_le_j: "k_min \<le> j" using k_min_in_S by (auto simp: S_def)
  have k_min_ge_i: "i \<le> k_min" using k_min_in_S by (auto simp: S_def)
  have not_in_k_min: "\<not> (pp, qq, mm) \<in># cfg_inflight (E k_min)"
    using k_min_in_S by (auto simp: S_def)
  have i_neq_k_min: "i \<noteq> k_min" using in_buf not_in_k_min by metis
  hence k_min_gt_i: "i < k_min" using k_min_ge_i by simp

  define k where "k = k_min - 1"
  have Suc_k_eq: "Suc k = k_min" using k_min_gt_i k_def by simp
  have i_le_k: "i \<le> k" using k_min_gt_i k_def by simp
  have k_lt_j: "k < j" using k_min_le_j k_min_gt_i k_def by simp

  \<comment> \<open>\<open>k\<close> is below \<open>k_min\<close>, so \<open>k \<notin> S\<close>; combined with the
      range constraints, this forces \<open>(pp, qq, mm) \<in># E k\<close>.\<close>
  have k_lt_k_min: "k < k_min" using k_min_gt_i k_def by simp
  have k_not_in_S: "k \<notin> S"
  proof
    assume "k \<in> S"
    hence "k_min \<le> k" using S_fin k_min_def by (simp add: Min_le)
    thus False using k_lt_k_min by simp
  qed
  have k_le_j: "k \<le> j" using k_lt_j by simp
  have k_in_buf: "(pp, qq, mm) \<in># cfg_inflight (E k)"
  proof (rule ccontr)
    assume not_in_k: "\<not> (pp, qq, mm) \<in># cfg_inflight (E k)"
    have "k \<in> S"
      using i_le_k k_le_j not_in_k by (auto simp: S_def)
    with k_not_in_S show False by contradiction
  qed
  have suc_k_not_in_buf: "\<not> (pp, qq, mm) \<in># cfg_inflight (E (Suc k))"
    using Suc_k_eq not_in_k_min by simp

  have step: "run_step (E k) (E (Suc k))"
    using inf by (simp add: infinite_run_def)
  from step_removes_triple_is_recv[OF step k_in_buf suc_k_not_in_buf]
  obtain n where rec:
    "Receive qq n pp mm \<in> events_of (cfg_hist (E (Suc k)))" by blast

  from i_le_k k_lt_j rec show ?thesis by blast
qed

section \<open>Fair runs\<close>

text \<open>A run is fair if every buffer triple is eventually removed
from the buffer.  This is the standard weak-fairness condition for
\<open>step_recv\<close>: each enabled receive is eventually taken (or, more
formally, each in-flight triple eventually leaves the buffer).\<close>

definition fair_run :: "(nat \<Rightarrow> 'p config) \<Rightarrow> bool" where
  "fair_run E \<longleftrightarrow>
     (\<forall>i p q m. (p, q, m) \<in># cfg_inflight (E i)
                \<longrightarrow> (\<exists>j. i \<le> j \<and> \<not> (p, q, m) \<in># cfg_inflight (E j)))"

section \<open>Liveness: fair runs deliver every correct-to-correct send\<close>

text \<open>The headline liveness theorem.  For every fair infinite run
and every correct-to-correct \<open>Send p n q m\<close> event in some
\<open>cfg_hist (E i)\<close>, there is a step \<open>j\<close> and seq number \<open>n'\<close>
such that \<open>Receive q n' p m\<close> is in \<open>cfg_hist (E j)\<close>.

The proof composes:
\begin{enumerate}
  \item @{thm infinite_run_sends_match_inv}: the
        \<open>sends_match_inv\<close> invariant holds at every step.  So
        either the matching receive is already in \<open>E i\<close>, or
        the triple is in the buffer at \<open>E i\<close>.
  \item In the latter case, fairness gives a \<open>j' \<ge> i\<close> at which
        the triple is out of the buffer.
  \item @{thm triple_disappears_implies_recv} then yields an
        intermediate step at which a matching receive was added.
\end{enumerate}\<close>

theorem fair_run_delivers:
  assumes inf:  "infinite_run E"
      and fair: "fair_run E"
      and pc:   "p \<in> correct"
      and qc:   "q \<in> correct"
      and send: "Send p n q m \<in> events_of (cfg_hist (E i))"
  shows "\<exists>j n'. Receive q n' p m \<in> events_of (cfg_hist (E j))"
proof -
  have inv: "sends_match_inv (E i)"
    by (rule infinite_run_sends_match_inv[OF inf])
  hence alt:
    "(\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist (E i)))
       \<or> (p, q, m) \<in># cfg_inflight (E i)"
    using pc qc send by (auto simp: sends_match_inv_def)
  show ?thesis
  proof (cases "\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist (E i))")
    case True
    thus ?thesis by blast
  next
    case no_rec_at_i: False
    with alt have in_buf: "(p, q, m) \<in># cfg_inflight (E i)" by blast
    from fair[unfolded fair_run_def] in_buf
    obtain j' where j'_ge: "i \<le> j'"
                and j'_out: "\<not> (p, q, m) \<in># cfg_inflight (E j')"
      by blast
    from triple_disappears_implies_recv[OF inf j'_ge in_buf j'_out]
    obtain k n' where
      i_k: "i \<le> k" and k_j': "k < j'"
      and rec: "Receive q n' p m \<in> events_of (cfg_hist (E (Suc k)))"
      by blast
    thus ?thesis by blast
  qed
qed

text \<open>A useful packaging of the liveness theorem at the
@{const messages_delivered_among} level, ranging over a fixed
"sufficiently late" index.  Saying ``every send is eventually
delivered'' is the same as ``the union of histories
\<open>\<Union>_i events_of (cfg_hist (E i))\<close> satisfies
\<open>messages_delivered_among correct\<close>''.\<close>

definition history_union :: "(nat \<Rightarrow> 'p config) \<Rightarrow> 'p history" where
  "history_union E = (\<lambda>p. SOME es.
                            (\<exists>i. es = cfg_hist (E i) p
                                  \<and> (\<forall>j \<ge> i. cfg_hist (E j) p = es)))"

text \<open>The \<open>history_union\<close> definition above is a stub for a fuller
treatment.  The temporally-informed statement that is actually
useful in downstream developments is the form below: it says that
the messages-delivered property is achieved cumulatively over the
infinite run, not at any single index.\<close>

theorem fair_run_delivers_all:
  assumes inf:  "infinite_run E"
      and fair: "fair_run E"
  shows "\<forall>p n q m i.
            p \<in> correct \<and> q \<in> correct
            \<and> Send p n q m \<in> events_of (cfg_hist (E i))
            \<longrightarrow> (\<exists>j n'. Receive q n' p m \<in> events_of (cfg_hist (E j)))"
  using fair_run_delivers[OF inf fair] by blast

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
