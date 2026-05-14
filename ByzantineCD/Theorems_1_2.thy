(*
  Title:   Theorems_1_2.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  Theorems 1 and 2 of the paper (Section 4.1, "Two basic results"):

    Theorem 1 (paper, Section 4.1): "It is impossible to prevent
      false negatives in solving the causality determination problem
      (Definition 5) as specified by CD(E, F, e*_i) in an asynchronous
      unicast/multicast/broadcast-based message passing system with
      one or more Byzantine processes."

    Theorem 2 (paper, Section 4.1): "For an internal event e^x_h, it
      is impossible to prevent false negatives or false positives in
      determining e^x_h --> e*_i at a correct process p_i in an
      asynchronous message passing system with one or more Byzantine
      processes."

  Both theorems are constructive.  Given any candidate CD solver, we
  exhibit a concrete admissible adversary -- a Byzantine process
  whose actions cannot be predicted by the algorithm because they
  involve a "fresh" natural number that no event in the algorithm's
  output F uses.  For Theorem 1 the fresh number is a message
  identifier; for Theorem 2 it is a sequence number of an internal
  event at the Byzantine process.

  Why a fresh nat works.  The CD algorithm sees only the inputs
  (i, e_star) and produces a finite F.  By choosing an adversary
  whose execution E includes an event with a "fresh" identifier, we
  ensure that event is outside events_of F -- and therefore the hb
  relation in E (where the event participates in a chain to e_star)
  is not mirrored in F (where the event is absent).  This is the
  paper's Byzantine-omits-an-event scenario, with the choice of
  identifier made adversarially.

  Stated and proved against the abstract CD-solver signature of
  CD.thy.  Theorems 1 and 2 do NOT invoke FLP, so they are unaffected
  by the vacuity issue that earlier surrounded the abstract
  Consensus impossibility (see Foundation_Vacuity.thy).

  Deviations from the paper:

    1. The paper's proof of Theorem 1 mentions two Byzantine
       strategies: "A Byzantine p_g can suppress letting the rest of
       the system know of the occurrence of e_g^v or swap the order
       of occurrence of e_g^v and e_g^v'".  We formalise only the
       suppression strategy (fresh-id construction); swap is a
       different attack producing the same conclusion.

    2. The paper's proof of Theorem 2 covers both omit (-> FN) and
       fake (-> FP) Byzantine strategies.  We discharge only the
       FN side; FN-OR-FP is the conjunctive disjunction in the
       theorem statement, so one suffices.

    3. The paper does not assume the CD output is finite.  We do --
       hypothesis fin_F in both theorems below ("forall i e_star.
       finite (events_of (fst (alg i e_star)))").  Without this we
       cannot prove a fresh natural number exists.  Any "reasonable"
       CD algorithm satisfies this (its F should be supported on
       procs, which is finite).
*)

theory Theorems_1_2
  imports CD
begin

section \<open>Natural numbers used by an algorithm's output\<close>

text \<open>For a finitely-supported collected history @{term F}, the set of
natural numbers appearing as either a local sequence number or a
message identifier of any event in @{term "events_of F"} is finite.
Hence a fresh natural number, strictly larger than all those that
appear, exists.\<close>

fun nats_of_event :: "'p event \<Rightarrow> nat set" where
  "nats_of_event (Internal _ n)     = {n}"
| "nats_of_event (Send _ n _ m)     = {n, m}"
| "nats_of_event (Receive _ n _ m)  = {n, m}"

definition nats_in_F :: "'p history \<Rightarrow> nat set" where
  "nats_in_F F \<equiv> \<Union>e\<in>events_of F. nats_of_event e"

definition fresh_nat :: "'p history \<Rightarrow> nat" where
  "fresh_nat F \<equiv> Suc (Max (insert 0 (nats_in_F F)))"

lemma finite_nats_of_event [simp]: "finite (nats_of_event e)"
  by (cases e) auto

lemma finite_nats_in_F:
  assumes "finite (events_of F)"
  shows   "finite (nats_in_F F)"
  using assms unfolding nats_in_F_def by simp

lemma nats_in_F_le_Max:
  assumes "finite (events_of F)" "k \<in> nats_in_F F"
  shows   "k \<le> Max (insert 0 (nats_in_F F))"
proof -
  have "finite (insert 0 (nats_in_F F))"
    using assms(1) finite_nats_in_F by simp
  thus ?thesis using assms(2) by (intro Max_ge) auto
qed

lemma fresh_nat_above:
  assumes "finite (events_of F)" "k \<in> nats_in_F F"
  shows   "k < fresh_nat F"
proof -
  have "k \<le> Max (insert 0 (nats_in_F F))"
    using assms by (rule nats_in_F_le_Max)
  thus ?thesis by (simp add: fresh_nat_def)
qed

lemma fresh_nat_positive [simp]: "fresh_nat F > 0"
  by (simp add: fresh_nat_def)

text \<open>Concrete corollaries: any specific event constructed at
@{term "fresh_nat F"} as either its sequence number or its message
identifier is outside @{term "events_of F"}.\<close>

lemma Internal_at_fresh_nat_not_in_F:
  assumes "finite (events_of F)"
  shows   "Internal p (fresh_nat F) \<notin> events_of F"
proof
  let ?e = "Internal p (fresh_nat F)"
  assume H: "?e \<in> events_of F"
  have inside: "fresh_nat F \<in> nats_of_event ?e" by simp
  have "fresh_nat F \<in> nats_in_F F"
    using H inside unfolding nats_in_F_def by blast
  with assms fresh_nat_above show False by fastforce
qed

lemma Send_at_fresh_nat_not_in_F:
  assumes "finite (events_of F)"
  shows   "Send p n q (fresh_nat F) \<notin> events_of F"
proof
  let ?e = "Send p n q (fresh_nat F)"
  assume H: "?e \<in> events_of F"
  have inside: "fresh_nat F \<in> nats_of_event ?e" by simp
  have "fresh_nat F \<in> nats_in_F F"
    using H inside unfolding nats_in_F_def by blast
  with assms fresh_nat_above show False by fastforce
qed

context process_partition
begin

section \<open>Theorem 1: false negatives are unavoidable\<close>

text \<open>Paper, Theorem 1 (Section 4.1):
\begin{quote}
``It is impossible to prevent false negatives in solving the
causality determination problem (Definition 5) as specified by
CD(\<open>E, F, e_i^*\<close>) in an asynchronous unicast/multicast/broadcast-based
message passing system with one or more Byzantine processes.''
\end{quote}

Paper's proof sketch:
\begin{quote}
``In the determination of \<open>e_h^x \<rightarrow> e_i^*\<close>, a false negative may
arise when a send-receive event pair (\<open>e_f^u, e_g^v\<close>) in a causal
chain from \<open>e_h^x\<close> to \<open>e_i^*\<close> is missing as per \<open>F\<close>.  \dots\
A Byzantine \<open>p_g\<close> can suppress letting the rest of the system know
of the occurrence of \<open>e_g^v\<close> or swap the order of occurrence of
\<open>e_g^v\<close> and \<open>e_g^v'\<close> in what it lets the rest of the system know
about the occurrence of the two local events.''
\end{quote}

\textbf{Our construction.}  Given an algorithm \<open>alg\<close>, pick a correct
process \<open>p_i\<close> and a Byzantine process \<open>p_b\<close>.  Take \<open>e_star
= Internal p_i 2\<close>, and let \<open>F = fst (alg p_i e_star)\<close> be the
algorithm's collected history on this input.  Use a fresh message
id \<open>m = fresh_nat F\<close> and build the execution \<open>E\<close>:
\begin{itemize}
  \item \<open>E p_b = [Send p_b 1 p_i m]\<close>;
  \item \<open>E p_i = [Receive p_i 1 p_b m, Internal p_i 2]\<close>;
  \item \<open>E p = []\<close> elsewhere.
\end{itemize}
The Send event has a hb-chain to \<open>e_star\<close> in \<open>E\<close> (message order
plus program order at \<open>p_i\<close>), but it is not in \<open>events_of F\<close>
because its message id was chosen fresh.  Hence \<open>hb_eval E s e_star\<close>
holds while \<open>hb_eval F s e_star\<close> does not -- a false negative.\<close>

definition fn_E :: "'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> 'p history" where
  "fn_E p_i p_b m \<equiv>
     (\<lambda>p. if p = p_b then [Send p_b 1 p_i m]
          else if p = p_i then [Receive p_i 1 p_b m, Internal p_i 2]
          else [])"

definition fn_adv :: "'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> 'p adversary" where
  "fn_adv p_i p_b m \<equiv>
     \<lparr> adv_E = fn_E p_i p_b m,
       adv_e_star = Internal p_i 2,
       adv_i = p_i \<rparr>"

lemma fn_E_at_pb [simp]:
  assumes "p_b \<noteq> p_i"
  shows "fn_E p_i p_b m p_b = [Send p_b 1 p_i m]"
  using assms by (simp add: fn_E_def)

lemma fn_E_at_pi:
  assumes "p_b \<noteq> p_i"
  shows "fn_E p_i p_b m p_i = [Receive p_i 1 p_b m, Internal p_i 2]"
  using assms by (auto simp: fn_E_def)

lemma fn_E_elsewhere:
  assumes "p \<noteq> p_b" "p \<noteq> p_i"
  shows "fn_E p_i p_b m p = []"
  using assms by (simp add: fn_E_def)

lemma fn_E_events:
  assumes "p_b \<noteq> p_i"
  shows "events_of (fn_E p_i p_b m) =
           {Send p_b 1 p_i m, Receive p_i 1 p_b m, Internal p_i 2}"
proof -
  have "events_of (fn_E p_i p_b m) = (\<Union>p. set (fn_E p_i p_b m p))"
    by (simp add: events_of_def)
  also have "\<dots> = set (fn_E p_i p_b m p_b) \<union> set (fn_E p_i p_b m p_i)
                  \<union> (\<Union>p \<in> -{p_b, p_i}. set (fn_E p_i p_b m p))"
    by auto
  also have "set (fn_E p_i p_b m p_b) = {Send p_b 1 p_i m}"
    using assms by simp
  moreover have "set (fn_E p_i p_b m p_i)
                    = {Receive p_i 1 p_b m, Internal p_i 2}"
    using assms by (simp add: fn_E_at_pi)
  moreover have "(\<Union>p \<in> -{p_b, p_i}. set (fn_E p_i p_b m p)) = {}"
    by (auto simp: fn_E_elsewhere)
  ultimately show ?thesis by auto
qed

lemma wf_history_local_pb_in_fn_E:
  assumes "p_b \<noteq> p_i"
  shows "wf_history_local p_b (fn_E p_i p_b m p_b)"
proof -
  have list_eq: "fn_E p_i p_b m p_b = [Send p_b 1 p_i m]"
    using assms by simp
  have "\<forall>e \<in> set [Send p_b 1 p_i m]. proc_of e = p_b" by simp
  moreover have "\<forall>k < length [Send p_b 1 p_i m].
                    seq_of ([Send p_b 1 p_i m] ! k) = Suc k"
    by (simp add: less_Suc_eq)
  ultimately show ?thesis
    using list_eq unfolding wf_history_local_def by simp
qed

lemma wf_history_local_pi_in_fn_E:
  assumes "p_b \<noteq> p_i"
  shows "wf_history_local p_i (fn_E p_i p_b m p_i)"
proof -
  let ?l = "[Receive p_i 1 p_b m, Internal p_i 2]"
  have list_eq: "fn_E p_i p_b m p_i = ?l"
    using assms by (rule fn_E_at_pi)
  have proc_ok: "\<forall>e \<in> set ?l. proc_of e = p_i" by simp
  have seq_ok: "\<forall>k < length ?l. seq_of (?l ! k) = Suc k"
  proof (intro allI impI)
    fix k assume "k < length ?l"
    hence "k = 0 \<or> k = 1" by auto
    thus "seq_of (?l ! k) = Suc k" by auto
  qed
  show ?thesis using list_eq proc_ok seq_ok
    unfolding wf_history_local_def by simp
qed

lemma wf_history_local_elsewhere_in_fn_E:
  assumes "p \<noteq> p_b" "p \<noteq> p_i"
  shows "wf_history_local p (fn_E p_i p_b m p)"
  using assms by (simp add: fn_E_elsewhere wf_history_local_def)

lemma wf_history_fn_E:
  assumes "p_b \<noteq> p_i"
  shows "wf_history (fn_E p_i p_b m)"
proof (unfold wf_history_def, intro allI)
  fix p
  show "wf_history_local p (fn_E p_i p_b m p)"
  proof (cases "p = p_b")
    case True
    thus ?thesis using assms wf_history_local_pb_in_fn_E by simp
  next
    case False
    show ?thesis
    proof (cases "p = p_i")
      case True
      thus ?thesis using assms wf_history_local_pi_in_fn_E by simp
    next
      case False
      with \<open>p \<noteq> p_b\<close> show ?thesis
        by (rule wf_history_local_elsewhere_in_fn_E)
    qed
  qed
qed

lemma program_order_fn_E_at_pi:
  assumes "p_b \<noteq> p_i"
  shows "program_order (fn_E p_i p_b m)
           (Receive p_i 1 p_b m) (Internal p_i 2)"
proof -
  let ?H = "fn_E p_i p_b m"
  have list_eq: "?H p_i = [Receive p_i 1 p_b m, Internal p_i 2]"
    using assms by (rule fn_E_at_pi)
  have len: "length (?H p_i) = 2" by (simp add: list_eq)
  have e0: "(?H p_i) ! 0 = Receive p_i 1 p_b m" by (simp add: list_eq)
  have e1: "(?H p_i) ! 1 = Internal p_i 2" by (simp add: list_eq)
  have "(0::nat) < 1" by simp
  moreover have "(1::nat) < length (?H p_i)" using len by simp
  ultimately show ?thesis
    using e0 e1 unfolding program_order_def by blast
qed

lemma message_order_fn_E_send_receive:
  assumes "p_b \<noteq> p_i"
  shows "message_order (fn_E p_i p_b m)
           (Send p_b 1 p_i m) (Receive p_i 1 p_b m)"
  using assms unfolding message_order_def
  by (simp add: fn_E_events)

lemma hb_send_to_estar_in_fn_E:
  assumes "p_b \<noteq> p_i"
  shows "hb (fn_E p_i p_b m) (Send p_b 1 p_i m) (Internal p_i 2)"
proof -
  let ?H = "fn_E p_i p_b m"
  let ?s = "Send p_b 1 p_i m"
  let ?r = "Receive p_i 1 p_b m"
  let ?es = "Internal p_i 2"
  have step1: "hb_step ?H ?s ?r"
    using message_order_fn_E_send_receive[OF assms]
    by (simp add: hb_step_def)
  have step2: "hb_step ?H ?r ?es"
    using program_order_fn_E_at_pi[OF assms] by (simp add: hb_step_def)
  have base: "(hb_step ?H)\<^sup>+\<^sup>+ ?s ?r"
    using step1 by blast
  have extend: "(hb_step ?H)\<^sup>+\<^sup>+ ?r ?es"
    using step2 by blast
  have "(hb_step ?H)\<^sup>+\<^sup>+ ?s ?es"
    using base extend by (rule tranclp_trans)
  thus ?thesis by (simp add: hb_def)
qed

lemma hb_eval_send_to_estar_in_fn_E:
  assumes "p_b \<noteq> p_i"
  shows "hb_eval (fn_E p_i p_b m) (Send p_b 1 p_i m) (Internal p_i 2)"
proof -
  have e1: "Send p_b 1 p_i m \<in> events_of (fn_E p_i p_b m)"
    using assms by (simp add: fn_E_events)
  have e2: "Internal p_i 2 \<in> events_of (fn_E p_i p_b m)"
    using assms by (simp add: fn_E_events)
  have h: "hb (fn_E p_i p_b m) (Send p_b 1 p_i m) (Internal p_i 2)"
    using assms by (rule hb_send_to_estar_in_fn_E)
  show ?thesis using e1 e2 h by (simp add: hb_eval_def)
qed

lemma adv_admissible_fn_adv:
  assumes "p_i \<in> correct" "p_b \<noteq> p_i"
  shows "adversary_admissible correct (fn_adv p_i p_b m)"
proof -
  have a: "wf_history (fn_E p_i p_b m)"
    using assms(2) by (rule wf_history_fn_E)
  have b: "p_i \<in> correct" by (rule assms(1))
  have c: "proc_of (Internal p_i 2) = p_i" by simp
  have d: "Internal p_i 2 \<in> events_of (fn_E p_i p_b m)"
    using assms(2) by (simp add: fn_E_events)
  show ?thesis using a b c d
    by (simp add: adversary_admissible_def fn_adv_def)
qed

theorem CD_FN_unavoidable:
  assumes byz_cor_distinct:
                  "\<exists>p_i p_b. p_i \<in> correct \<and> p_b \<in> byzantine \<and> p_b \<noteq> p_i"
      and fin_F:  "\<forall>p_i_in. finite (events_of
                                       (fst (alg p_i_in (Internal p_i_in 2))))"
  shows "\<exists>adv. adversary_admissible correct adv \<and>
               false_negative (adv_E adv)
                              (fst (alg (adv_i adv) (adv_e_star adv)))
                              (adv_e_star adv)"
proof -
  obtain p_i p_b where
      pi_cor: "p_i \<in> correct" and pb_byz: "p_b \<in> byzantine"
      and dist: "p_b \<noteq> p_i"
    using byz_cor_distinct by blast

  let ?e_star = "Internal p_i 2"
  let ?F = "fst (alg p_i ?e_star)"
  let ?m = "fresh_nat ?F"
  let ?adv = "fn_adv p_i p_b ?m"
  let ?s = "Send p_b 1 p_i ?m"

  have finF: "finite (events_of ?F)" using fin_F by blast

  have adm: "adversary_admissible correct ?adv"
    using pi_cor dist by (rule adv_admissible_fn_adv)

  have witness_in_E: "?s \<in> events_of (adv_E ?adv)"
    using dist by (simp add: fn_adv_def fn_E_events)
  have hbE: "hb_eval (adv_E ?adv) ?s (adv_e_star ?adv)"
  proof -
    have "hb_eval (fn_E p_i p_b ?m) ?s (Internal p_i 2)"
      by (rule hb_eval_send_to_estar_in_fn_E[OF dist])
    thus ?thesis by (simp add: fn_adv_def)
  qed
  have witness_not_in_F: "?s \<notin> events_of ?F"
    using finF Send_at_fresh_nat_not_in_F[of ?F] by blast
  have not_hbF: "\<not> hb_eval ?F ?s (adv_e_star ?adv)"
    using witness_not_in_F by (simp add: hb_eval_def fn_adv_def)

  from witness_in_E hbE not_hbF
  have "\<exists>e \<in> events_of (adv_E ?adv) \<union> events_of ?F.
            hb_eval (adv_E ?adv) e (adv_e_star ?adv) \<and>
            \<not> hb_eval ?F e (adv_e_star ?adv)"
    by blast
  hence FN: "false_negative (adv_E ?adv) ?F (adv_e_star ?adv)"
    by (simp add: false_negative_def)

  have F_eq: "fst (alg (adv_i ?adv) (adv_e_star ?adv)) = ?F"
    by (simp add: fn_adv_def)

  from adm FN F_eq show ?thesis by metis
qed

section \<open>Theorem 2: false negatives or false positives are unavoidable
                       for internal events\<close>

text \<open>Paper, Theorem 2 (Section 4.1):
\begin{quote}
``For an internal event \<open>e_h^x\<close>, it is impossible to prevent false
negatives or false positives in determining \<open>e_h^x \<rightarrow> e_i^*\<close> at a
correct process \<open>p_i\<close> in an asynchronous message passing system
with one or more Byzantine processes.''
\end{quote}

Paper's proof sketch:
\begin{quote}
``There may be no other event in the rest of the system to
corroborate the occurrence of an internal event at a process.  A
Byzantine process \<open>p_h\<close> can choose to not reveal about an internal
event \<open>e_h^x\<close> to the rest of the system, leading to a false
negative that cannot be prevented.  It may also choose to add a fake
internal event \<open>e_h^x\<close> in what it reveals to the rest of the
system, leading to a false positive that cannot be prevented.''
\end{quote}

\textbf{Our construction.}  We strengthen the Theorem 1 construction
so that the witness event is an Internal event at a Byzantine
process, rather than a Send event.  The Byzantine process \<open>p_b\<close>
performs a chain of \<open>k\<close> internal events followed by a single Send
to the correct target \<open>p_i\<close>, where \<open>k = fresh_nat F\<close> is chosen so
that the \<open>k\<close>-th internal event has a sequence number absent from
\<open>events_of F\<close>.  The internal event still has an hb-chain to
\<open>e_star\<close> in \<open>E\<close> (through subsequent program order to the Send,
then message order, then program order at \<open>p_i\<close>); but the internal
event itself is not in \<open>events_of F\<close>, so a false negative arises.

\textit{Deviation:} the paper's Theorem 2 is an FN-or-FP disjunction
(``the Byzantine \<open>p_h\<close> can choose to not reveal \<open>\<dots>\<close> OR \<open>\<dots>\<close>
add a fake internal event'').  We discharge the FN side
constructively.  Since the statement is a disjunction (\<open>FN \<or> FP\<close>),
exhibiting an adversary that produces FN is sufficient.\<close>

definition fn_internal_E :: "'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'p history" where
  "fn_internal_E p_i p_b k m \<equiv>
     (\<lambda>p. if p = p_b
          then (map (Internal p_b) [1..<Suc k])
                @ [Send p_b (Suc k) p_i m]
          else if p = p_i
          then [Receive p_i 1 p_b m, Internal p_i 2]
          else [])"

definition fn_internal_adv :: "'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'p adversary" where
  "fn_internal_adv p_i p_b k m \<equiv>
     \<lparr> adv_E = fn_internal_E p_i p_b k m,
       adv_e_star = Internal p_i 2,
       adv_i = p_i \<rparr>"

lemma fn_internal_E_at_pb [simp]:
  assumes "p_b \<noteq> p_i"
  shows "fn_internal_E p_i p_b k m p_b
           = (map (Internal p_b) [1..<Suc k]) @ [Send p_b (Suc k) p_i m]"
  using assms by (simp add: fn_internal_E_def)

lemma fn_internal_E_at_pi:
  assumes "p_b \<noteq> p_i"
  shows "fn_internal_E p_i p_b k m p_i
           = [Receive p_i 1 p_b m, Internal p_i 2]"
  using assms by (auto simp: fn_internal_E_def)

lemma fn_internal_E_elsewhere:
  assumes "p \<noteq> p_b" "p \<noteq> p_i"
  shows "fn_internal_E p_i p_b k m p = []"
  using assms by (simp add: fn_internal_E_def)

lemma length_fn_internal_E_pb:
  assumes "p_b \<noteq> p_i"
  shows "length (fn_internal_E p_i p_b k m p_b) = Suc k"
  using assms by simp

lemma nth_fn_internal_E_pb_lt:
  assumes "p_b \<noteq> p_i" "j < k"
  shows "fn_internal_E p_i p_b k m p_b ! j = Internal p_b (Suc j)"
proof -
  let ?xs = "map (Internal p_b) [1..<Suc k]"
  let ?L = "?xs @ [Send p_b (Suc k) p_i m]"
  have list_eq: "fn_internal_E p_i p_b k m p_b = ?L"
    using assms(1) by simp
  have len_xs: "length ?xs = k"
    using assms(2) by simp
  with assms(2) have j_lt_len: "j < length ?xs" by simp
  have j_lt_upt: "j < length [1..<Suc k]"
    using assms(2) by simp
  have step1: "?L ! j = ?xs ! j"
    using j_lt_len by (simp add: nth_append)
  have step2: "?xs ! j = Internal p_b ([1..<Suc k] ! j)"
    using j_lt_upt by (rule nth_map)
  have step3: "[1..<Suc k] ! j = Suc j"
  proof -
    have "[1..<Suc k] ! j = 1 + j"
      using assms(2) by (intro nth_upt) simp
    thus ?thesis by simp
  qed
  from step1 step2 step3 list_eq show ?thesis by simp
qed

lemma nth_fn_internal_E_pb_eq:
  assumes "p_b \<noteq> p_i"
  shows "fn_internal_E p_i p_b k m p_b ! k = Send p_b (Suc k) p_i m"
  using assms by (simp add: nth_append)

lemma set_fn_internal_E_pb:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "set (fn_internal_E p_i p_b k m p_b)
            = (Internal p_b ` {1..k}) \<union> {Send p_b (Suc k) p_i m}"
proof -
  have set_map: "set (map (Internal p_b) [1..<Suc k]) = Internal p_b ` {1..<Suc k}"
    by auto
  have rng_eq: "{1..<Suc k} = {1..k}" by auto
  have "set (fn_internal_E p_i p_b k m p_b)
          = set (map (Internal p_b) [1..<Suc k]) \<union> {Send p_b (Suc k) p_i m}"
    using assms(1) by simp
  also have "\<dots> = (Internal p_b ` {1..k}) \<union> {Send p_b (Suc k) p_i m}"
    using set_map rng_eq by simp
  finally show ?thesis .
qed

lemma fn_internal_E_events:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "events_of (fn_internal_E p_i p_b k m) =
           (Internal p_b ` {1..k})
           \<union> {Send p_b (Suc k) p_i m,
              Receive p_i 1 p_b m,
              Internal p_i 2}"
proof -
  have "events_of (fn_internal_E p_i p_b k m)
            = (\<Union>p. set (fn_internal_E p_i p_b k m p))"
    by (simp add: events_of_def)
  also have "\<dots> = set (fn_internal_E p_i p_b k m p_b)
                  \<union> set (fn_internal_E p_i p_b k m p_i)
                  \<union> (\<Union>p \<in> -{p_b, p_i}. set (fn_internal_E p_i p_b k m p))"
    by auto
  also have "(\<Union>p \<in> -{p_b, p_i}. set (fn_internal_E p_i p_b k m p)) = {}"
    by (auto simp: fn_internal_E_elsewhere)
  moreover have "set (fn_internal_E p_i p_b k m p_b)
                   = (Internal p_b ` {1..k}) \<union> {Send p_b (Suc k) p_i m}"
    using assms by (rule set_fn_internal_E_pb)
  moreover have "set (fn_internal_E p_i p_b k m p_i)
                   = {Receive p_i 1 p_b m, Internal p_i 2}"
    using assms(1) by (simp add: fn_internal_E_at_pi)
  ultimately show ?thesis by auto
qed

lemma wf_history_local_pb_in_fn_internal_E:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "wf_history_local p_b (fn_internal_E p_i p_b k m p_b)"
proof -
  let ?L = "fn_internal_E p_i p_b k m p_b"
  have len_L: "length ?L = Suc k" using assms(1) by simp

  have all_proc: "\<forall>e \<in> set ?L. proc_of e = p_b"
  proof
    fix e assume "e \<in> set ?L"
    hence "e \<in> (Internal p_b ` {1..k}) \<union> {Send p_b (Suc k) p_i m}"
      using set_fn_internal_E_pb[OF assms] by simp
    thus "proc_of e = p_b" by (auto simp: image_iff)
  qed

  have all_seq: "\<forall>j < length ?L. seq_of (?L ! j) = Suc j"
  proof (intro allI impI)
    fix j assume "j < length ?L"
    hence j_lt: "j < Suc k" using len_L by simp
    show "seq_of (?L ! j) = Suc j"
    proof (cases "j < k")
      case True
      thus ?thesis using nth_fn_internal_E_pb_lt[OF assms(1)] by simp
    next
      case False
      with j_lt have "j = k" by simp
      thus ?thesis using nth_fn_internal_E_pb_eq[OF assms(1)] by simp
    qed
  qed

  show ?thesis using all_proc all_seq
    unfolding wf_history_local_def by blast
qed

lemma wf_history_local_pi_in_fn_internal_E:
  assumes "p_b \<noteq> p_i"
  shows "wf_history_local p_i (fn_internal_E p_i p_b k m p_i)"
proof -
  let ?L = "[Receive p_i 1 p_b m, Internal p_i 2]"
  have list_eq: "fn_internal_E p_i p_b k m p_i = ?L"
    using assms by (rule fn_internal_E_at_pi)
  have proc_ok: "\<forall>e \<in> set ?L. proc_of e = p_i" by simp
  have seq_ok: "\<forall>j < length ?L. seq_of (?L ! j) = Suc j"
  proof (intro allI impI)
    fix j assume "j < length ?L"
    hence "j = 0 \<or> j = 1" by auto
    thus "seq_of (?L ! j) = Suc j" by auto
  qed
  show ?thesis using list_eq proc_ok seq_ok
    unfolding wf_history_local_def by simp
qed

lemma wf_history_local_elsewhere_in_fn_internal_E:
  assumes "p \<noteq> p_b" "p \<noteq> p_i"
  shows "wf_history_local p (fn_internal_E p_i p_b k m p)"
  using assms by (simp add: fn_internal_E_elsewhere wf_history_local_def)

lemma wf_history_fn_internal_E:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "wf_history (fn_internal_E p_i p_b k m)"
proof (unfold wf_history_def, intro allI)
  fix p
  show "wf_history_local p (fn_internal_E p_i p_b k m p)"
  proof (cases "p = p_b")
    case True
    thus ?thesis using assms wf_history_local_pb_in_fn_internal_E by simp
  next
    case False
    show ?thesis
    proof (cases "p = p_i")
      case True
      thus ?thesis using assms(1) wf_history_local_pi_in_fn_internal_E by simp
    next
      case False
      with \<open>p \<noteq> p_b\<close> show ?thesis
        by (rule wf_history_local_elsewhere_in_fn_internal_E)
    qed
  qed
qed

lemma program_order_internal_to_send_at_pb:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "program_order (fn_internal_E p_i p_b k m)
           (Internal p_b k) (Send p_b (Suc k) p_i m)"
proof -
  let ?H = "fn_internal_E p_i p_b k m"
  have len: "length (?H p_b) = Suc k" using assms(1) by simp
  from assms(2) have km1_lt_k: "k - 1 < k" by simp
  have at_km1: "(?H p_b) ! (k - 1) = Internal p_b (Suc (k - 1))"
    using assms(1) km1_lt_k nth_fn_internal_E_pb_lt by simp
  hence at_km1': "(?H p_b) ! (k - 1) = Internal p_b k"
    using assms(2) by simp
  have at_k: "(?H p_b) ! k = Send p_b (Suc k) p_i m"
    using assms(1) by (rule nth_fn_internal_E_pb_eq)
  have idx1: "k - 1 < k" using assms(2) by simp
  have idx2: "k < length (?H p_b)" using len by simp
  show ?thesis using at_km1' at_k idx1 idx2
    unfolding program_order_def by blast
qed

lemma program_order_receive_to_estar_in_fn_internal_E:
  assumes "p_b \<noteq> p_i"
  shows "program_order (fn_internal_E p_i p_b k m)
           (Receive p_i 1 p_b m) (Internal p_i 2)"
proof -
  let ?H = "fn_internal_E p_i p_b k m"
  have list_eq: "?H p_i = [Receive p_i 1 p_b m, Internal p_i 2]"
    using assms by (rule fn_internal_E_at_pi)
  have len: "length (?H p_i) = 2" by (simp add: list_eq)
  have e0: "(?H p_i) ! 0 = Receive p_i 1 p_b m" by (simp add: list_eq)
  have e1: "(?H p_i) ! 1 = Internal p_i 2" by (simp add: list_eq)
  have "(0::nat) < 1" by simp
  moreover have "(1::nat) < length (?H p_i)" using len by simp
  ultimately show ?thesis using e0 e1
    unfolding program_order_def by blast
qed

lemma message_order_in_fn_internal_E:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "message_order (fn_internal_E p_i p_b k m)
           (Send p_b (Suc k) p_i m) (Receive p_i 1 p_b m)"
  using assms unfolding message_order_def
  by (simp add: fn_internal_E_events)

lemma hb_internal_to_estar_in_fn_internal_E:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "hb (fn_internal_E p_i p_b k m) (Internal p_b k) (Internal p_i 2)"
proof -
  let ?H = "fn_internal_E p_i p_b k m"
  let ?ih = "Internal p_b k"
  let ?s = "Send p_b (Suc k) p_i m"
  let ?r = "Receive p_i 1 p_b m"
  let ?es = "Internal p_i 2"
  have step1: "hb_step ?H ?ih ?s"
    using program_order_internal_to_send_at_pb[OF assms]
    by (simp add: hb_step_def)
  have step2: "hb_step ?H ?s ?r"
    using message_order_in_fn_internal_E[OF assms]
    by (simp add: hb_step_def)
  have step3: "hb_step ?H ?r ?es"
    using program_order_receive_to_estar_in_fn_internal_E[OF assms(1)]
    by (simp add: hb_step_def)
  have t1: "(hb_step ?H)\<^sup>+\<^sup>+ ?ih ?s" using step1 by blast
  have t2: "(hb_step ?H)\<^sup>+\<^sup>+ ?s ?r" using step2 by blast
  have t3: "(hb_step ?H)\<^sup>+\<^sup>+ ?r ?es" using step3 by blast
  have "(hb_step ?H)\<^sup>+\<^sup>+ ?ih ?r" using t1 t2 by (rule tranclp_trans)
  hence "(hb_step ?H)\<^sup>+\<^sup>+ ?ih ?es" using t3 by (rule tranclp_trans)
  thus ?thesis by (simp add: hb_def)
qed

lemma hb_eval_internal_to_estar_in_fn_internal_E:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "hb_eval (fn_internal_E p_i p_b k m)
           (Internal p_b k) (Internal p_i 2)"
proof -
  let ?H = "fn_internal_E p_i p_b k m"
  have e_ih: "Internal p_b k \<in> events_of ?H"
    using assms by (simp add: fn_internal_E_events)
  have e_es: "Internal p_i 2 \<in> events_of ?H"
    using assms by (simp add: fn_internal_E_events)
  have h: "hb ?H (Internal p_b k) (Internal p_i 2)"
    using assms by (rule hb_internal_to_estar_in_fn_internal_E)
  show ?thesis using e_ih e_es h by (simp add: hb_eval_def)
qed

lemma adv_admissible_fn_internal_adv:
  assumes "p_i \<in> correct" "p_b \<noteq> p_i" "k \<ge> 1"
  shows "adversary_admissible correct (fn_internal_adv p_i p_b k m)"
proof -
  have a: "wf_history (fn_internal_E p_i p_b k m)"
    using assms(2) assms(3) by (rule wf_history_fn_internal_E)
  have b: "p_i \<in> correct" by (rule assms(1))
  have c: "proc_of (Internal p_i 2) = p_i" by simp
  have d: "Internal p_i 2 \<in> events_of (fn_internal_E p_i p_b k m)"
    using assms(2) assms(3) by (simp add: fn_internal_E_events)
  show ?thesis using a b c d
    by (simp add: adversary_admissible_def fn_internal_adv_def)
qed

theorem CD_FN_or_FP_unavoidable_internal:
  assumes byz_cor_distinct:
                  "\<exists>p_i p_b. p_i \<in> correct \<and> p_b \<in> byzantine \<and> p_b \<noteq> p_i"
      and fin_F:  "\<forall>p_i_in. finite (events_of
                                       (fst (alg p_i_in (Internal p_i_in 2))))"
  shows "\<exists>adv e_h. adversary_admissible correct adv \<and>
                    (\<exists>p n. e_h = Internal p n) \<and>
                    ((hb_eval (adv_E adv) e_h (adv_e_star adv) \<and>
                      \<not> hb_eval (fst (alg (adv_i adv) (adv_e_star adv)))
                                e_h (adv_e_star adv))
                     \<or>
                     (\<not> hb_eval (adv_E adv) e_h (adv_e_star adv) \<and>
                      hb_eval (fst (alg (adv_i adv) (adv_e_star adv)))
                              e_h (adv_e_star adv)))"
proof -
  obtain p_i p_b where
      pi_cor: "p_i \<in> correct" and pb_byz: "p_b \<in> byzantine"
      and dist: "p_b \<noteq> p_i"
    using byz_cor_distinct by blast

  let ?e_star = "Internal p_i 2"
  let ?F = "fst (alg p_i ?e_star)"
  let ?k = "fresh_nat ?F"
  let ?m = "fresh_nat ?F"
  let ?adv = "fn_internal_adv p_i p_b ?k ?m"
  let ?ih = "Internal p_b ?k"

  have finF: "finite (events_of ?F)" using fin_F by blast

  have k_pos: "?k \<ge> 1"
    by (simp add: fresh_nat_def Suc_leI)

  have adm: "adversary_admissible correct ?adv"
    using pi_cor dist k_pos by (rule adv_admissible_fn_internal_adv)

  have witness_in_E: "?ih \<in> events_of (adv_E ?adv)"
    using dist k_pos
    by (auto simp: fn_internal_adv_def fn_internal_E_events)
  have hbE: "hb_eval (adv_E ?adv) ?ih (adv_e_star ?adv)"
  proof -
    have "hb_eval (fn_internal_E p_i p_b ?k ?m) ?ih (Internal p_i 2)"
      by (rule hb_eval_internal_to_estar_in_fn_internal_E[OF dist k_pos])
    thus ?thesis by (simp add: fn_internal_adv_def)
  qed
  have witness_not_in_F: "?ih \<notin> events_of ?F"
    using finF Internal_at_fresh_nat_not_in_F[of ?F] by blast
  have not_hbF: "\<not> hb_eval ?F ?ih (adv_e_star ?adv)"
    using witness_not_in_F by (simp add: hb_eval_def fn_internal_adv_def)

  have F_eq: "fst (alg (adv_i ?adv) (adv_e_star ?adv)) = ?F"
    by (simp add: fn_internal_adv_def)

  have e_h_internal: "\<exists>p n. ?ih = Internal p n" by blast

  from adm e_h_internal hbE not_hbF F_eq witness_in_E
  show ?thesis by metis
qed

end \<comment> \<open>context @{locale process_partition}\<close>

end
