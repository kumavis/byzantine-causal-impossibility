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
  case (step_byzantine p new_event cfg' cfg)
  have ev: "events_of (cfg_hist cfg') = events_of (cfg_hist cfg) \<union> {new_event}"
    using step_byzantine.hyps(3) events_of_extend by simp
  have buf: "cfg_inflight cfg' = cfg_inflight cfg"
    using step_byzantine.hyps(3) by simp
  show ?case
  proof (unfold sends_match_inv_def, intro allI impI)
    fix p' n' q' m'
    assume pc: "p' \<in> correct" and qc: "q' \<in> correct"
       and sevent: "Send p' n' q' m' \<in> events_of (cfg_hist cfg')"
    \<comment> \<open>A correct-Send cannot be the newly added Byzantine event:
        the new event's @{term proc_of} is @{term p} \<in> byzantine,
        whereas the Send's @{term proc_of} would be @{term p'}
        \<in> correct.\<close>
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

text \<open>\textit{Note on \<open>wf_history\<close>.}  Phase 6 does not maintain
@{const wf_history} as a run invariant.  A polished development
would extend @{const run_step} with sequence-number side
conditions (e.g.\ the Byzantine step would constrain
\<open>seq_of new_event = Suc (length (cfg_hist cfg p))\<close>) and then
prove \<open>run cfg \<Longrightarrow> wf_history (cfg_hist cfg)\<close>.  At that point
\<open>fairness_implies_delivery\<close> upgrades to the headline corollary

  \<open>run cfg \<Longrightarrow> cfg_inflight cfg = empty_inflight
       \<Longrightarrow> mode_admissible Unicast (cfg_hist cfg)\<close>

closing the Phase 5 gap completely.\<close>

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
