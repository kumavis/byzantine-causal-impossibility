(*
  Title:   Execution_Model.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  Phase 6 of #4: a minimal operational execution model that exhibits
  histories witnessing mode_admissible Unicast.

  Up to Phase 5 the development states T6 / T7 over the static
  mode_admissible predicate (Delivery.thy), whose unicast / broadcast
  cases bundle wf_history with the messages_delivered_among delivery
  property.  Phase 5 closed the previously-named operational
  hypothesis ``every history reachable under mode m delivers correct-
  to-correct messages'' by internalising it in mode_admissible.

  The remaining unproven content was: ``mode_admissible Unicast is
  achievable by an operational protocol''.  Phase 6 discharges that
  here.

  We define an inductive single-step relation \<open>run_step\<close> on
  configurations (history + in-flight buffer).  Correct processes
  take internal, send, and receive steps; receive consumes an
  in-flight message from the buffer.  Byzantine processes append
  arbitrary local events to their own history but do not inject
  in-flight entries.

  Theorem (fairness implies delivery): if a run reaches a
  configuration whose in-flight buffer is empty, the configuration's
  history H satisfies messages_delivered_among correct H -- because
  every correct-to-correct Send adds an entry to the buffer, every
  correct-from-correct Receive removes a matching entry, and a
  Byzantine step neither adds nor removes correct-to-correct sends.
  An empty buffer means every Send entry has been matched.

  Corollary: such an H is mode_admissible Unicast (modulo
  wf_history, which Phase 6 does not currently maintain as a run
  invariant -- see the closing remarks of this file).
*)

theory Execution_Model
  imports Delivery
begin

section \<open>Configurations: history + in-flight buffer\<close>

text \<open>An in-flight message is a triple \<open>(sender, receiver, msg_id)\<close>;
we track only correct-to-correct sends in the buffer because only
those are constrained by \<open>messages_delivered_among\<close> restricted
to \<open>correct\<close>.

These declarations live at the theory level (outside the
\<open>byzantineSystem\<close> locale context) because Isabelle does not allow
\<open>record\<close> or \<open>type_synonym\<close> in a context that locally fixes type
variables.\<close>

type_synonym 'q in_flight = "('q \<times> 'q \<times> nat) multiset"

record 'q config =
  cfg_hist     :: "'q history"
  cfg_inflight :: "'q in_flight"

context byzantineSystem
begin

text \<open>Naming the empty buffer separately avoids a parser interaction
between record syntax (\<open>\<lparr> \<dots> \<rparr>\<close>) and the empty multiset literal
(\<open>{#}\<close>).\<close>

definition empty_inflight :: "'p in_flight" where
  "empty_inflight = (\<lambda>_. 0)"

definition init_config :: "'p config" where
  "init_config = \<lparr> cfg_hist = (\<lambda>_. []), cfg_inflight = empty_inflight \<rparr>"

section \<open>One operational step\<close>

text \<open>\<open>run_step\<close> covers four kinds of step.

\begin{itemize}
  \item \<open>step_internal\<close>: a correct \<open>p\<close> appends an \<open>Internal\<close>
        event with the next sequence number.
  \item \<open>step_send\<close>: a correct \<open>p\<close> sends a fresh-id message to a
        correct \<open>q\<close>, appending a \<open>Send\<close> event and adding the
        triple to the buffer.
  \item \<open>step_recv\<close>: a correct \<open>q\<close> consumes an in-flight message
        from a correct \<open>p\<close>, appending a matching \<open>Receive\<close> and
        removing the triple.
  \item \<open>step_byzantine\<close>: a Byzantine \<open>p\<close> appends one event
        whose \<open>proc_of\<close> is \<open>p\<close>; the buffer is unchanged.
        Byzantine sends to correct receivers are not added to the
        buffer -- conservatively, this models a network in which
        Byzantine senders cannot enforce delivery at correct
        receivers, which matches the paper's unicast / broadcast
        setting where correct receivers only believe what they
        actually receive.
\end{itemize}\<close>

inductive run_step :: "'p config \<Rightarrow> 'p config \<Rightarrow> bool" where
  step_internal:
    "p \<in> correct
       \<Longrightarrow> n = Suc (length (cfg_hist cfg p))
       \<Longrightarrow> cfg' = cfg
              \<lparr> cfg_hist := (cfg_hist cfg)
                              (p := cfg_hist cfg p @ [Internal p n]) \<rparr>
       \<Longrightarrow> run_step cfg cfg'"
| step_send:
    "p \<in> correct
       \<Longrightarrow> q \<in> correct
       \<Longrightarrow> n = Suc (length (cfg_hist cfg p))
       \<Longrightarrow> cfg' = cfg
              \<lparr> cfg_hist := (cfg_hist cfg)
                              (p := cfg_hist cfg p @ [Send p n q m]),
                cfg_inflight := cfg_inflight cfg \<union># {# (p, q, m) } \<rparr>
       \<Longrightarrow> run_step cfg cfg'"
| step_recv:
    "q \<in> correct
       \<Longrightarrow> p \<in> correct
       \<Longrightarrow> (p, q, m) \<in># cfg_inflight cfg
       \<Longrightarrow> n = Suc (length (cfg_hist cfg q))
       \<Longrightarrow> cfg' = cfg
              \<lparr> cfg_hist := (cfg_hist cfg)
                              (q := cfg_hist cfg q @ [Receive q n p m]),
                cfg_inflight := cfg_inflight cfg -# (p, q, m) \<rparr>
       \<Longrightarrow> run_step cfg cfg'"
| step_byzantine:
    "p \<in> byzantine
       \<Longrightarrow> proc_of new_event = p
       \<Longrightarrow> seq_of new_event = Suc (length (cfg_hist cfg p))
       \<Longrightarrow> cfg' = cfg
              \<lparr> cfg_hist := (cfg_hist cfg)
                              (p := cfg_hist cfg p @ [new_event]) \<rparr>
       \<Longrightarrow> run_step cfg cfg'"

section \<open>Runs: zero-or-more steps from the initial configuration\<close>

definition run :: "'p config \<Rightarrow> bool" where
  "run cfg \<longleftrightarrow> run_step\<^sup>*\<^sup>* init_config cfg"

lemma run_init [simp]: "run init_config"
  by (simp add: run_def)

lemma run_extend:
  "run cfg \<Longrightarrow> run_step cfg cfg' \<Longrightarrow> run cfg'"
  unfolding run_def by simp

section \<open>events\<open>_of\<close> on per-process updates\<close>

lemma events_of_extend:
  "events_of (H(p := H p @ [e])) = events_of H \<union> {e}"
proof -
  have "(\<Union>q. set ((H(p := H p @ [e])) q))
          = (\<Union>q. if q = p then set (H p @ [e]) else set (H q))"
    by (rule SUP_cong) auto
  also have
    "\<dots> = set (H p @ [e]) \<union> (\<Union>q\<in>{q. q \<noteq> p}. set (H q))"
    by (auto split: if_split_asm)
  also have
    "\<dots> = (set (H p) \<union> {e}) \<union> (\<Union>q\<in>{q. q \<noteq> p}. set (H q))"
    by simp
  also have
    "(\<Union>q. set (H q)) = set (H p) \<union> (\<Union>q\<in>{q. q \<noteq> p}. set (H q))"
    by auto
  ultimately have "events_of (H(p := H p @ [e])) = events_of H \<union> {e}"
    by (simp add: events_of_def)
  thus ?thesis .
qed

section \<open>The key invariant: correct-to-correct Sends are buffered or received\<close>

text \<open>For every correct-to-correct \<open>(p, q, m)\<close> triple, if there is
a \<open>Send p n q m\<close> event in the history then there is either a
matching \<open>Receive q n' p m\<close> event or a buffer entry \<open>(p, q, m)\<close>.

This is the standard ``conservation of in-flight messages''
invariant: every correct-to-correct Send introduces one buffer
entry; every correct-from-correct Receive removes one buffer entry
that pairs with an existing Send.  Byzantine steps neither add
correct-to-correct sends nor remove buffer entries, so the
invariant is preserved trivially.\<close>

definition sends_match_inv :: "'p config \<Rightarrow> bool" where
  "sends_match_inv cfg \<longleftrightarrow>
     (\<forall>p n q m. p \<in> correct \<longrightarrow> q \<in> correct
        \<longrightarrow> Send p n q m \<in> events_of (cfg_hist cfg)
        \<longrightarrow> (\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist cfg))
            \<or> (p, q, m) \<in># cfg_inflight cfg)"

lemma sends_match_inv_init [simp]:
  "sends_match_inv init_config"
  by (simp add: sends_match_inv_def init_config_def empty_inflight_def
                events_of_def)

text \<open>Every step preserves \<open>sends_match_inv\<close>.\<close>

lemma sends_match_inv_step:
  assumes "sends_match_inv cfg"
      and "run_step cfg cfg'"
  shows "sends_match_inv cfg'"
  using assms(2,1)
proof induction
  case (step_internal p n cfg cfg')
  have ev: "events_of (cfg_hist cfg') = events_of (cfg_hist cfg) \<union> {Internal p n}"
    using step_internal.hyps(3) events_of_extend by simp
  have buf: "cfg_inflight cfg' = cfg_inflight cfg"
    using step_internal.hyps(3) by simp
  show ?case
  proof (unfold sends_match_inv_def, intro allI impI)
    fix p' n' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and sevent: "Send p' n' q' m' \<in> events_of (cfg_hist cfg')"
    from sevent ev have "Send p' n' q' m' \<in> events_of (cfg_hist cfg)"
      by auto
    with step_internal.prems pc qc
    have IH:
      "(\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg))
        \<or> (p', q', m') \<in># cfg_inflight cfg"
      by (auto simp: sends_match_inv_def)
    thus "(\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg'))
           \<or> (p', q', m') \<in># cfg_inflight cfg'"
    proof
      assume "\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg)"
      then obtain n'' where "Receive q' n'' p' m' \<in> events_of (cfg_hist cfg)" by blast
      hence "Receive q' n'' p' m' \<in> events_of (cfg_hist cfg')" using ev by auto
      thus ?thesis by blast
    next
      assume "(p', q', m') \<in># cfg_inflight cfg"
      thus ?thesis using buf by simp
    qed
  qed
next
  case (step_send p q n cfg cfg' m)
  let ?new = "Send p n q m"
  have ev: "events_of (cfg_hist cfg') = events_of (cfg_hist cfg) \<union> {?new}"
    using step_send.hyps(4) events_of_extend by simp
  have buf: "cfg_inflight cfg' = cfg_inflight cfg \<union># {# (p, q, m) }"
    using step_send.hyps(4) by simp
  show ?case
  proof (unfold sends_match_inv_def, intro allI impI)
    fix p' n' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and sevent: "Send p' n' q' m' \<in> events_of (cfg_hist cfg')"
    from sevent ev
    have "Send p' n' q' m' \<in> events_of (cfg_hist cfg) \<or>
          Send p' n' q' m' = ?new"
      by auto
    thus "(\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg'))
           \<or> (p', q', m') \<in># cfg_inflight cfg'"
    proof
      assume "Send p' n' q' m' \<in> events_of (cfg_hist cfg)"
      with step_send.prems pc qc
      have IH:
        "(\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg))
         \<or> (p', q', m') \<in># cfg_inflight cfg"
        by (auto simp: sends_match_inv_def)
      thus ?thesis
      proof
        assume "\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg)"
        then obtain n''
          where "Receive q' n'' p' m' \<in> events_of (cfg_hist cfg)" by blast
        hence "Receive q' n'' p' m' \<in> events_of (cfg_hist cfg')"
          using ev by auto
        thus ?thesis by blast
      next
        assume "(p', q', m') \<in># cfg_inflight cfg"
        thus ?thesis using buf by simp
      qed
    next
      assume eq: "Send p' n' q' m' = ?new"
      hence eq': "(p', q', m') = (p, q, m)" by simp
      have "(p, q, m) \<in># cfg_inflight cfg'"
        using buf by simp
      with eq' have "(p', q', m') \<in># cfg_inflight cfg'" by simp
      thus ?thesis by blast
    qed
  qed
next
  case (step_recv q p m cfg n cfg')
  let ?new = "Receive q n p m"
  have ev: "events_of (cfg_hist cfg') = events_of (cfg_hist cfg) \<union> {?new}"
    using step_recv.hyps(5) events_of_extend by simp
  have buf: "cfg_inflight cfg' = cfg_inflight cfg -# (p, q, m)"
    using step_recv.hyps(5) by simp
  have buf_in: "(p, q, m) \<in># cfg_inflight cfg" by (rule step_recv.hyps(3))
  show ?case
  proof (unfold sends_match_inv_def, intro allI impI)
    fix p' n' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and sevent: "Send p' n' q' m' \<in> events_of (cfg_hist cfg')"
    \<comment> \<open>A Send event cannot equal the Receive ?new.\<close>
    from sevent ev
    have "Send p' n' q' m' \<in> events_of (cfg_hist cfg)" by auto
    with step_recv.prems pc qc
    have IH:
      "(\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg))
       \<or> (p', q', m') \<in># cfg_inflight cfg"
      by (auto simp: sends_match_inv_def)
    thus "(\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg'))
           \<or> (p', q', m') \<in># cfg_inflight cfg'"
    proof
      assume "\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg)"
      then obtain n''
        where "Receive q' n'' p' m' \<in> events_of (cfg_hist cfg)" by blast
      hence "Receive q' n'' p' m' \<in> events_of (cfg_hist cfg')"
        using ev by auto
      thus ?thesis by blast
    next
      assume buf_in': "(p', q', m') \<in># cfg_inflight cfg"
      show ?thesis
      proof (cases "(p', q', m') = (p, q, m)")
        case True
        have "Receive q n p m \<in> events_of (cfg_hist cfg')"
          using ev by simp
        with True show ?thesis by auto
      next
        case neq: False
        have neq': "(p', q', m') \<noteq> (p, q, m)"
          using neq by simp
        have eq_count:
          "(cfg_inflight cfg -# (p, q, m)) (p', q', m')
             = cfg_inflight cfg (p', q', m')"
          using neq' by auto
        have "(p', q', m') \<in># cfg_inflight cfg -# (p, q, m)"
          using buf_in' eq_count by simp
        hence "(p', q', m') \<in># cfg_inflight cfg'"
          using buf by simp
        thus ?thesis by blast
      qed
    qed
  qed
next
  case (step_byzantine p new_event cfg cfg')
  have ev: "events_of (cfg_hist cfg') = events_of (cfg_hist cfg) \<union> {new_event}"
    using step_byzantine.hyps(4) events_of_extend by simp
  have buf: "cfg_inflight cfg' = cfg_inflight cfg"
    using step_byzantine.hyps(4) by simp
  show ?case
  proof (unfold sends_match_inv_def, intro allI impI)
    fix p' n' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and sevent: "Send p' n' q' m' \<in> events_of (cfg_hist cfg')"
    \<comment> \<open>A correct-Send cannot be the newly added Byzantine event:
        the new event's @{term proc_of} is @{term p} \<open>\<in>\<close> byzantine,
        whereas the Send's @{term proc_of} would be @{term p'}
        \<open>\<in>\<close> correct.\<close>
    have pby: "p \<in> byzantine" by (rule step_byzantine.hyps(1))
    have neq: "p' \<noteq> p"
      using pc pby partition_disj by blast
    have proc_new: "proc_of new_event = p"
      by (rule step_byzantine.hyps(2))
    have proc_send: "proc_of (Send p' n' q' m') = p'" by simp
    have not_new: "Send p' n' q' m' \<noteq> new_event"
      using neq proc_new proc_send by metis
    from sevent ev
    have "Send p' n' q' m' \<in> events_of (cfg_hist cfg) \<or>
          Send p' n' q' m' = new_event"
      by auto
    with not_new
    have sevent_cfg: "Send p' n' q' m' \<in> events_of (cfg_hist cfg)"
      by blast
    with step_byzantine.prems pc qc
    have IH:
      "(\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg))
       \<or> (p', q', m') \<in># cfg_inflight cfg"
      by (auto simp: sends_match_inv_def)
    thus "(\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg'))
           \<or> (p', q', m') \<in># cfg_inflight cfg'"
    proof
      assume "\<exists>n''. Receive q' n'' p' m' \<in> events_of (cfg_hist cfg)"
      then obtain n''
        where "Receive q' n'' p' m' \<in> events_of (cfg_hist cfg)" by blast
      hence "Receive q' n'' p' m' \<in> events_of (cfg_hist cfg')"
        using ev by auto
      thus ?thesis by blast
    next
      assume "(p', q', m') \<in># cfg_inflight cfg"
      thus ?thesis using buf by simp
    qed
  qed
qed

text \<open>Invariant is preserved by any run (zero-or-more steps).\<close>

lemma sends_match_inv_run:
  assumes "run cfg"
  shows "sends_match_inv cfg"
  using assms
  unfolding run_def
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule sends_match_inv_init)
next
  case (step y z)
  from sends_match_inv_step[OF step.IH step.hyps(2)]
  show ?case .
qed

section \<open>Fairness implies delivery\<close>

text \<open>The headline Phase 6 theorem: if a run reaches a configuration
with empty in-flight buffer, the configuration's history satisfies
@{const messages_delivered_among} \<open>correct\<close>.  Operationally: ``the
schedule was completed fairly'' \<open>\<Longrightarrow>\<close> ``every correct-to-correct
send was delivered''.\<close>

theorem fairness_implies_delivery:
  assumes "run cfg"
      and "cfg_inflight cfg = empty_inflight"
  shows "messages_delivered_among correct (cfg_hist cfg)"
proof (unfold messages_delivered_among_def, intro allI impI)
  fix p n q m
  assume pc: "p \<in> correct" and qc: "q \<in> correct"
     and sevent: "Send p n q m \<in> events_of (cfg_hist cfg)"
  from sends_match_inv_run[OF assms(1)] pc qc sevent
  have alt: "(\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist cfg))
              \<or> (p, q, m) \<in># cfg_inflight cfg"
    by (auto simp: sends_match_inv_def)
  have "\<not> (p, q, m) \<in># cfg_inflight cfg"
    using assms(2) by (simp add: empty_inflight_def)
  with alt show
    "\<exists>n'. Receive q n' p m \<in> events_of (cfg_hist cfg)"
    by blast
qed

section \<open>wf\<open>_history\<close> is a run invariant\<close>

text \<open>Each step appends one event whose @{const proc_of} matches the
target process and whose @{const seq_of} is exactly
\<open>Suc (length ...)\<close> of the existing per-process list.  These are
exactly the @{const wf_history_local} conditions for an extension
by one element, so each step preserves @{const wf_history}.

For \<open>step_byzantine\<close> the @{const proc_of} and @{const seq_of}
constraints are explicit premises; for \<open>step_internal\<close> /
\<open>step_send\<close> / \<open>step_recv\<close> they follow from the event
constructors used and the \<open>n = Suc (length ...)\<close> side condition.\<close>

lemma wf_history_local_extend:
  assumes wf:     "wf_history_local p es"
      and proc_e: "proc_of e = p"
      and seq_e:  "seq_of e = Suc (length es)"
  shows   "wf_history_local p (es @ [e])"
proof (unfold wf_history_local_def, intro conjI ballI allI impI)
  fix ev assume mem: "ev \<in> set (es @ [e])"
  show "proc_of ev = p"
  proof (cases "ev \<in> set es")
    case True
    thus ?thesis using wf unfolding wf_history_local_def by blast
  next
    case False
    with mem have "ev = e" by simp
    thus ?thesis using proc_e by simp
  qed
next
  fix k assume k: "k < length (es @ [e])"
  show "seq_of ((es @ [e]) ! k) = Suc k"
  proof (cases "k < length es")
    case True
    have "(es @ [e]) ! k = es ! k"
      using True by (simp add: nth_append)
    moreover have "seq_of (es ! k) = Suc k"
      using wf True unfolding wf_history_local_def by blast
    ultimately show ?thesis by simp
  next
    case False
    with k have k_eq: "k = length es" by simp
    have "(es @ [e]) ! k = e" using k_eq by simp
    moreover have "seq_of e = Suc (length es)" by (rule seq_e)
    ultimately show ?thesis using k_eq by simp
  qed
qed

lemma wf_history_extend:
  assumes wf:     "wf_history H"
      and proc_e: "proc_of e = p"
      and seq_e:  "seq_of e = Suc (length (H p))"
  shows "wf_history (H(p := H p @ [e]))"
proof (unfold wf_history_def, intro allI)
  fix p'
  show "wf_history_local p' ((H(p := H p @ [e])) p')"
  proof (cases "p' = p")
    case True
    have "wf_history_local p (H p)"
      using wf unfolding wf_history_def by blast
    hence "wf_history_local p (H p @ [e])"
      by (rule wf_history_local_extend[OF _ proc_e seq_e])
    thus ?thesis using True by simp
  next
    case False
    hence eq: "(H(p := H p @ [e])) p' = H p'" by simp
    have "wf_history_local p' (H p')"
      using wf unfolding wf_history_def by blast
    thus ?thesis using eq by simp
  qed
qed

lemma wf_history_init [simp]:
  "wf_history (cfg_hist init_config)"
  by (simp add: init_config_def wf_history_def wf_history_local_def)

lemma wf_history_step:
  assumes wf:   "wf_history (cfg_hist cfg)"
      and step: "run_step cfg cfg'"
  shows "wf_history (cfg_hist cfg')"
  using step wf
proof induction
  case (step_internal p n cfg cfg')
  have proc_new: "proc_of (Internal p n) = p" by simp
  have seq_new: "seq_of (Internal p n) = Suc (length (cfg_hist cfg p))"
    using step_internal.hyps(2) by simp
  have wf_prev: "wf_history (cfg_hist cfg)" by (rule step_internal.prems)
  have wf_ext:
    "wf_history ((cfg_hist cfg)(p := cfg_hist cfg p @ [Internal p n]))"
    by (rule wf_history_extend[OF wf_prev proc_new seq_new])
  have cfg'_eq:
    "cfg_hist cfg' = (cfg_hist cfg)(p := cfg_hist cfg p @ [Internal p n])"
    using step_internal.hyps(3) by simp
  show ?case using wf_ext cfg'_eq by metis
next
  case (step_send p q n cfg cfg' m)
  have proc_new: "proc_of (Send p n q m) = p" by simp
  have seq_new: "seq_of (Send p n q m) = Suc (length (cfg_hist cfg p))"
    using step_send.hyps(3) by simp
  have wf_prev: "wf_history (cfg_hist cfg)" by (rule step_send.prems)
  have wf_ext:
    "wf_history ((cfg_hist cfg)(p := cfg_hist cfg p @ [Send p n q m]))"
    by (rule wf_history_extend[OF wf_prev proc_new seq_new])
  have cfg'_eq:
    "cfg_hist cfg' = (cfg_hist cfg)(p := cfg_hist cfg p @ [Send p n q m])"
    using step_send.hyps(4) by simp
  show ?case using wf_ext cfg'_eq by metis
next
  case (step_recv q p m cfg n cfg')
  have proc_new: "proc_of (Receive q n p m) = q" by simp
  have seq_new: "seq_of (Receive q n p m) = Suc (length (cfg_hist cfg q))"
    using step_recv.hyps(4) by simp
  have wf_prev: "wf_history (cfg_hist cfg)" by (rule step_recv.prems)
  have wf_ext:
    "wf_history ((cfg_hist cfg)(q := cfg_hist cfg q @ [Receive q n p m]))"
    by (rule wf_history_extend[OF wf_prev proc_new seq_new])
  have cfg'_eq:
    "cfg_hist cfg' = (cfg_hist cfg)(q := cfg_hist cfg q @ [Receive q n p m])"
    using step_recv.hyps(5) by simp
  show ?case using wf_ext cfg'_eq by metis
next
  case (step_byzantine p new_event cfg cfg')
  have proc_new: "proc_of new_event = p" by (rule step_byzantine.hyps(2))
  have seq_new: "seq_of new_event = Suc (length (cfg_hist cfg p))"
    by (rule step_byzantine.hyps(3))
  have wf_prev: "wf_history (cfg_hist cfg)" by (rule step_byzantine.prems)
  have wf_ext:
    "wf_history ((cfg_hist cfg)(p := cfg_hist cfg p @ [new_event]))"
    by (rule wf_history_extend[OF wf_prev proc_new seq_new])
  have cfg'_eq:
    "cfg_hist cfg' = (cfg_hist cfg)(p := cfg_hist cfg p @ [new_event])"
    using step_byzantine.hyps(4) by simp
  show ?case using wf_ext cfg'_eq by metis
qed

lemma wf_history_run:
  assumes "run cfg"
  shows "wf_history (cfg_hist cfg)"
  using assms unfolding run_def
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from wf_history_step[OF step.IH step.hyps(2)]
  show ?case .
qed

section \<open>Closing the Phase 5 gap: run produces mode-admissible histories\<close>

text \<open>The combined headline: any run that fairly completes (empty
in-flight buffer at the end) produces a history that is
@{const mode_admissible} under both @{term Unicast} and
@{term Broadcast} -- because the run preserves @{const wf_history}
(\<open>wf_history_run\<close>) and empty buffer gives
@{const messages_delivered_among} (\<open>fairness_implies_delivery\<close>).

This closes the Phase 5 gap: the unicast / broadcast cases of
@{const mode_admissible} were the structural content of T6 / T7's
operational claim, and we have now exhibited an operational
construction that produces such histories.  Composing with Phase 5's
\<open>CD_B_solvable_unicast_operational\<close> and
\<open>CD_B_solvable_broadcast_operational\<close> gives a fully derived chain

  \<open>operational run \<longrightarrow> mode-admissible H \<longrightarrow> naive algorithm solves CD_B\<close>

with no remaining operational hypothesis.\<close>

theorem run_completes_to_mode_admissible_unicast:
  assumes run_cfg: "run cfg"
      and empty:   "cfg_inflight cfg = empty_inflight"
  shows "mode_admissible Unicast (cfg_hist cfg)"
proof -
  have wf: "wf_history (cfg_hist cfg)" by (rule wf_history_run[OF run_cfg])
  have del: "messages_delivered_among correct (cfg_hist cfg)"
    by (rule fairness_implies_delivery[OF run_cfg empty])
  show ?thesis
    unfolding mode_admissible_def using wf del by simp
qed

theorem run_completes_to_mode_admissible_broadcast:
  assumes run_cfg: "run cfg"
      and empty:   "cfg_inflight cfg = empty_inflight"
  shows "mode_admissible Broadcast (cfg_hist cfg)"
proof -
  have wf: "wf_history (cfg_hist cfg)" by (rule wf_history_run[OF run_cfg])
  have del: "messages_delivered_among correct (cfg_hist cfg)"
    by (rule fairness_implies_delivery[OF run_cfg empty])
  show ?thesis
    unfolding mode_admissible_def using wf del by simp
qed

section \<open>Deadlock freedom\<close>

text \<open>The remaining gap below Phase 7 is the temporal-fairness gap:
in a real network the buffer is drained by a fair scheduler over an
infinite (or unboundedly long) execution.  Phase 8 takes one step
toward closing it by establishing \emph{deadlock freedom}: from any
configuration reachable via @{const run} with a non-empty in-flight
buffer, a @{const run_step} can always be taken (specifically a
\<open>step_recv\<close>).  Together with @{thm fairness_implies_delivery}
this means: as long as the scheduler keeps making moves, drainage
continues; the model never gets stuck.

What is left for a true closure is the liveness theorem
``every fair execution eventually has empty buffer''.  That requires
a temporal predicate over infinite executions -- stream / coinductive
machinery -- and is documented as the remaining out-of-scope step.\<close>

subsection \<open>The buffer only contains correct-to-correct triples\<close>

text \<open>Invariant \<open>buffer_correct_inv\<close>: every triple
\<open>(p, q, m)\<close> in the buffer has both \<open>p \<in> correct\<close> and
\<open>q \<in> correct\<close>.  This follows directly from the structure of
@{const run_step}: only the \<open>step_send\<close> rule adds to the buffer,
and its premises require both endpoints to be in @{term correct}.\<close>

definition buffer_correct_inv :: "'p config \<Rightarrow> bool" where
  "buffer_correct_inv cfg \<longleftrightarrow>
     (\<forall>p q m. (p, q, m) \<in># cfg_inflight cfg \<longrightarrow> p \<in> correct \<and> q \<in> correct)"

lemma buffer_correct_inv_init [simp]:
  "buffer_correct_inv init_config"
  by (simp add: buffer_correct_inv_def init_config_def empty_inflight_def)

lemma buffer_correct_inv_step:
  assumes "buffer_correct_inv cfg"
      and "run_step cfg cfg'"
  shows "buffer_correct_inv cfg'"
  using assms(2,1)
proof induction
  case (step_internal p n cfg cfg')
  have buf: "cfg_inflight cfg' = cfg_inflight cfg"
    using step_internal.hyps(3) by simp
  thus ?case
    using step_internal.prems by (simp add: buffer_correct_inv_def)
next
  case (step_send p q n cfg cfg' m)
  have buf: "cfg_inflight cfg' = cfg_inflight cfg \<union># {# (p, q, m) }"
    using step_send.hyps(4) by simp
  have pc: "p \<in> correct" by (rule step_send.hyps(1))
  have qc: "q \<in> correct" by (rule step_send.hyps(2))
  show ?case
  proof (unfold buffer_correct_inv_def, intro allI impI)
    fix p' q' m'
    assume "(p', q', m') \<in># cfg_inflight cfg'"
    hence in_buf: "0 < (cfg_inflight cfg \<union># {# (p, q, m) }) (p', q', m')"
      using buf by simp
    show "p' \<in> correct \<and> q' \<in> correct"
    proof (cases "(p', q', m') = (p, q, m)")
      case True
      thus ?thesis using pc qc by simp
    next
      case nq: False
      have neq: "(p, q, m) \<noteq> (p', q', m')" using nq by auto
      have "(cfg_inflight cfg \<union># {# (p, q, m) }) (p', q', m')
              = cfg_inflight cfg (p', q', m')"
        using neq by simp
      with in_buf have "0 < cfg_inflight cfg (p', q', m')" by simp
      hence in_cfg: "(p', q', m') \<in># cfg_inflight cfg" by simp
      show ?thesis
        using step_send.prems in_cfg
        unfolding buffer_correct_inv_def by blast
    qed
  qed
next
  case (step_recv q p m cfg n cfg')
  have buf: "cfg_inflight cfg' = cfg_inflight cfg -# (p, q, m)"
    using step_recv.hyps(5) by simp
  show ?case
  proof (unfold buffer_correct_inv_def, intro allI impI)
    fix p' q' m'
    assume "(p', q', m') \<in># cfg_inflight cfg'"
    hence "0 < (cfg_inflight cfg -# (p, q, m)) (p', q', m')"
      using buf by simp
    \<comment> \<open>Removing one occurrence only decreases the count, so
        \<open>(p',q',m')\<close> was already in the original buffer.\<close>
    hence "0 < cfg_inflight cfg (p', q', m')"
      by (auto split: if_split_asm)
    hence in_cfg: "(p', q', m') \<in># cfg_inflight cfg" by simp
    show "p' \<in> correct \<and> q' \<in> correct"
      using step_recv.prems in_cfg
      unfolding buffer_correct_inv_def by blast
  qed
next
  case (step_byzantine p new_event cfg cfg')
  have buf: "cfg_inflight cfg' = cfg_inflight cfg"
    using step_byzantine.hyps(4) by simp
  thus ?case
    using step_byzantine.prems by (simp add: buffer_correct_inv_def)
qed

lemma buffer_correct_inv_run:
  assumes "run cfg"
  shows "buffer_correct_inv cfg"
  using assms unfolding run_def
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from buffer_correct_inv_step[OF step.IH step.hyps(2)]
  show ?case .
qed

subsection \<open>Progress: a non-empty buffer always permits a step\<close>

text \<open>From a run-reachable configuration with non-empty buffer, a
\<open>step_recv\<close> rule application is always available: pick any
buffered triple (it exists, since the buffer is non-empty), and
the \<open>buffer_correct_inv\<close> invariant guarantees both endpoints are
correct, which is exactly what \<open>step_recv\<close>'s premises require.\<close>

lemma not_drained_can_step:
  assumes run_cfg:  "run cfg"
      and not_done: "cfg_inflight cfg \<noteq> empty_inflight"
  shows "\<exists>cfg'. run_step cfg cfg'"
proof -
  have inv: "buffer_correct_inv cfg" by (rule buffer_correct_inv_run[OF run_cfg])
  \<comment> \<open>A non-empty buffer means @{term "cfg_inflight cfg"} is not the
      constantly-zero function, so some triple has positive count.\<close>
  from not_done obtain p q m
    where pos: "cfg_inflight cfg (p, q, m) > 0"
  proof -
    have "\<exists>x. cfg_inflight cfg x \<noteq> empty_inflight x"
      using not_done by (auto simp: empty_inflight_def fun_eq_iff)
    then obtain x where x_ne: "cfg_inflight cfg x \<noteq> 0"
      by (auto simp: empty_inflight_def)
    obtain p' q' m' where x_eq: "x = (p', q', m')"
      by (cases x) auto
    from x_ne x_eq have "cfg_inflight cfg (p', q', m') > 0" by simp
    thus thesis by (rule that)
  qed
  hence in_buf: "(p, q, m) \<in># cfg_inflight cfg" by simp
  from inv in_buf have pc: "p \<in> correct" and qc: "q \<in> correct"
    by (auto simp: buffer_correct_inv_def)
  let ?n = "Suc (length (cfg_hist cfg q))"
  let ?cfg' =
    "cfg \<lparr> cfg_hist := (cfg_hist cfg)
                          (q := cfg_hist cfg q @ [Receive q ?n p m]),
           cfg_inflight := cfg_inflight cfg -# (p, q, m) \<rparr>"
  have "run_step cfg ?cfg'"
    by (rule run_step.step_recv[OF qc pc in_buf refl refl])
  thus ?thesis by blast
qed

text \<open>\textit{What this proves.}  @{thm not_drained_can_step}
together with @{thm fairness_implies_delivery} gives the two halves
of behavioural well-formedness for our model:

\begin{itemize}
  \item \<open>step_recv\<close> is applicable whenever the buffer is
        non-empty (deadlock freedom).
  \item Once the buffer is empty, the history is
        @{const messages_delivered_among}-complete (delivery).
\end{itemize}

\textit{What remains.}  A real-world fairness theorem of the form
``every fair infinite execution eventually has empty buffer'' would
require modelling infinite executions as streams and stating
fairness as a temporal predicate -- separate machinery the
development can be parametric over.\<close>

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
