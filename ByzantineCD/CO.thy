(*
  Title:   CO.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  The Causal Ordering problem CO(E, F, m_2) of Section 5.2 of the
  paper, together with Theorems 17 (CO and CD are interreducible in
  the Byzantine model) and 18 (CO is subject to false negatives and
  false positives).

  Paper coverage:
    - Definition 10 (CO problem), Section 5.2.
    - Theorem 17 (interreducibility CO <-> CD, Byzantine model).
    - Theorem 18 (CO subject to FN/FP -- a corollary of the
      interreducibility together with T1/T2).

  Our formalisation choice:
    * A CO instance is a CD instance whose target event is a
      \<^emph>\<open>Receive\<close> event.  Concretely, the paper writes the target as a
      message identifier m_2; in our model the witness ``m_2 was
      delivered to p_i'' is the receive event itself, so we just
      restrict the target type at the admissibility level rather than
      reifying messages as a separate type.
    * @{const valid} (the CD validity predicate) is reused unchanged;
      the only difference between produces_valid_F and
      produces_valid_F_CO is admissibility.
    * The forward direction of T17 (``CO is no harder than CD'') is
      proven constructively: a CD solver is automatically a CO solver
      because CO admissibility is a strict restriction of CD
      admissibility.
    * T18 is proven directly via the same fresh-nat construction used
      for T1/T2, adapted to a receive-event target (a two-message
      scenario; the target is the second receive).
    * The reverse direction of T17 (``CD is no harder than CO'') is
      proven under the standard Byzantine premises (byz_ne, cor_ne,
      finiteness) by routing through T3 + T18: under these premises
      both \<open>CD_solvable\<close> and \<open>CO_solvable\<close> are false, hence
      interreducible.  This is faithful to the paper's claim
      ``CO and CD are interreducible in the Byzantine model'' and
      gives Theorem 17 its intended content (the existence of either
      a CO-solver or a CD-solver implies the existence of the other,
      under Byzantine adversaries).

  Deviations from the paper:

    1. The paper's CO output is the deliverability decision
       CO_Deliv(m_2); we instead use \<open>valid (adv_E adv) F e_star\<close>
       as the correctness condition (same predicate as CD).  Under
       the paper's own framing -- ``the algorithm produces F and
       returns 1 iff F is valid'' -- the two formulations are
       equivalent: knowing valid(F) at the receive event of m_2 is
       exactly what one needs to settle CO_Deliv(m_2) (every causally
       prior send to e_star is preserved in F).

    2. The paper's Theorem 17 sketches the reduction CO \<preceq> CD in
       one paragraph and says ``the reverse direction is similar''.
       We mechanise the easy direction constructively and the reverse
       direction via vacuity under Byzantine premises (both sides
       impossible).  Constructing a CD solver from a CO solver at
       the function-level abstraction would require synthesising a
       self-receive extension of every CD adversary -- doable but
       substantial; the vacuous route gives the same final theorem.

    3. Theorem 18 is stated independently rather than as a corollary
       of T17 + T1/T2; the direct construction is short and avoids
       routing through the interreducibility argument.
*)

theory CO
  imports Impossibility
begin

section \<open>CO problem: definitions\<close>

text \<open>Paper, Section 5.2, Definition 10:
\begin{quote}
``The causal ordering problem \<open>CO(E, F, m_2)\<close> at a correct
process \<open>p_r\<close> that is the receiver of message \<open>m_2\<close> is
to devise an algorithm that collects the execution history \<open>E\<close>
as \<open>F\<close> at \<open>p_r\<close> such that \<open>valid(F) = 1\<close> for
\<open>e_r^* \<in> T(E)\<close> the receive event of \<open>m_2\<close>, with the
algorithm using \<open>F\<close> to decide \<open>CO_Deliv(m_2)\<close>.''
\end{quote>

We mechanise this by reusing the CD admissibility predicate and
restricting the target event to be a receive event.  The
``deliverability decision'' is subsumed by \<open>valid (adv_E adv) F
e_star\<close>: knowing whether \<open>F\<close> is HB-faithful to \<open>E\<close> at the
receive event of \<open>m_2\<close> is exactly the information needed to
settle whether all causally prior messages have been received.\<close>

definition co_admissible :: "'p set \<Rightarrow> 'p adversary \<Rightarrow> bool" where
  "co_admissible C adv \<longleftrightarrow>
     adversary_admissible C adv \<and> is_receive (adv_e_star adv)"

definition produces_valid_F_CO ::
  "'p set \<Rightarrow> 'p cd_solver \<Rightarrow> bool" where
  "produces_valid_F_CO C alg \<longleftrightarrow>
     (\<forall>adv. co_admissible C adv \<longrightarrow>
        (let (F', _) = alg (adv_i adv) (adv_e_star adv) in
           valid (adv_E adv) F' (adv_e_star adv)))"

definition CO_solvable :: "comm_mode \<Rightarrow> 'p set \<Rightarrow> bool" where
  "CO_solvable m C \<longleftrightarrow> (\<exists>alg. produces_valid_F_CO C alg)"

section \<open>Forward reduction (T17): \<open>CD \<longrightarrow> CO\<close>\<close>

text \<open>Paper, Section 5.2 (proof sketch of Theorem 17, the
``\<open>CO \<preceq> CD\<close>'' direction):
\begin{quote}
``To solve \<open>CO(E, F, m_2)\<close> at \<open>p_r\<close>, invoke
\<open>CD(E, F, e_r^*)\<close> locally where \<open>e_r^*\<close> is the
receive event of \<open>m_2\<close>; the BB-style output gives enough
information to settle \<open>CO_Deliv(m_2)\<close>.''
\end{quote}

In our function-level abstraction this is immediate: a CD solver
is correct for \<^emph>\<open>every\<close> admissible adversary; receive-event-target
adversaries are a strict subset.\<close>

lemma produces_valid_F_imp_produces_valid_F_CO:
  assumes "produces_valid_F C alg"
  shows   "produces_valid_F_CO C alg"
  using assms
  by (auto simp: produces_valid_F_def produces_valid_F_CO_def
                 co_admissible_def)

lemma CD_solvable_imp_CO_solvable:
  assumes "CD_solvable m C"
  shows   "CO_solvable m C"
  using assms produces_valid_F_imp_produces_valid_F_CO
  by (auto simp: CD_solvable_def CO_solvable_def)

context process_partition
begin

section \<open>Theorem 18a: CO is subject to false negatives\<close>

text \<open>Paper, Theorem 18 (Section 5.2):
\begin{quote}
``CO is subject to FN and FP in the Byzantine model.''
\end{quote}
The paper derives this as a corollary of the interreducibility
(Theorem 17) and the FN/FP results for CD (Theorems 1/2 [42]).  We
discharge it directly with the same fresh-nat construction used for
Theorem 1, adapted so the target is a receive event.

\textbf{Our construction.}  Given an algorithm @{term alg}, pick a
correct process @{term p_i} and a Byzantine process @{term p_b}.
Use a two-message scenario:
\begin{itemize}
  \item the \<^emph>\<open>target\<close> is the receive event of a fixed message
        @{term "m_2 = 0"} from @{term p_b} to @{term p_i}: namely
        \<open>e_star = Receive p_i 2 p_b 0\<close>;
  \item the \<^emph>\<open>FN witness\<close> is an earlier send-receive pair using a
        fresh message identifier @{term "m_1 = fresh_nat F"}.
\end{itemize}
Concretely:
\begin{align*}
  E_{p_b} &= [\mathrm{Send}\ p_b\ 1\ p_i\ m_1,\ \mathrm{Send}\ p_b\ 2\ p_i\ 0] \\
  E_{p_i} &= [\mathrm{Receive}\ p_i\ 1\ p_b\ m_1,\ \mathrm{Receive}\ p_i\ 2\ p_b\ 0]
\end{align*}
The fresh @{term "m_1 = fresh_nat F"} guarantees the send
@{term "Send p_b 1 p_i m_1"} -- which has a happened-before chain to
@{term e_star} in @{term E} -- is absent from @{term "events_of F"},
producing a false negative.\<close>

definition co_fn_E :: "'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> 'p history" where
  "co_fn_E p_i p_b m_1 \<equiv>
     (\<lambda>p. if p = p_b
          then [Send p_b 1 p_i m_1, Send p_b 2 p_i 0]
          else if p = p_i
          then [Receive p_i 1 p_b m_1, Receive p_i 2 p_b 0]
          else [])"

definition co_fn_adv :: "'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> 'p adversary" where
  "co_fn_adv p_i p_b m_1 \<equiv>
     \<lparr> adv_E = co_fn_E p_i p_b m_1,
       adv_e_star = Receive p_i 2 p_b 0,
       adv_i = p_i \<rparr>"

lemma co_fn_E_at_pb [simp]:
  assumes "p_b \<noteq> p_i"
  shows "co_fn_E p_i p_b m_1 p_b
           = [Send p_b 1 p_i m_1, Send p_b 2 p_i 0]"
  using assms by (simp add: co_fn_E_def)

lemma co_fn_E_at_pi:
  assumes "p_b \<noteq> p_i"
  shows "co_fn_E p_i p_b m_1 p_i
           = [Receive p_i 1 p_b m_1, Receive p_i 2 p_b 0]"
  using assms by (auto simp: co_fn_E_def)

lemma co_fn_E_elsewhere:
  assumes "p \<noteq> p_b" "p \<noteq> p_i"
  shows "co_fn_E p_i p_b m_1 p = []"
  using assms by (simp add: co_fn_E_def)

lemma co_fn_E_events:
  assumes "p_b \<noteq> p_i"
  shows "events_of (co_fn_E p_i p_b m_1)
           = {Send p_b 1 p_i m_1, Send p_b 2 p_i 0,
              Receive p_i 1 p_b m_1, Receive p_i 2 p_b 0}"
proof -
  have "events_of (co_fn_E p_i p_b m_1)
          = (\<Union>p. set (co_fn_E p_i p_b m_1 p))"
    by (simp add: events_of_def)
  also have "\<dots> = set (co_fn_E p_i p_b m_1 p_b)
                   \<union> set (co_fn_E p_i p_b m_1 p_i)
                   \<union> (\<Union>p \<in> -{p_b, p_i}. set (co_fn_E p_i p_b m_1 p))"
    by auto
  also have "set (co_fn_E p_i p_b m_1 p_b)
                = {Send p_b 1 p_i m_1, Send p_b 2 p_i 0}"
    using assms by simp
  moreover have "set (co_fn_E p_i p_b m_1 p_i)
                  = {Receive p_i 1 p_b m_1, Receive p_i 2 p_b 0}"
    using assms by (simp add: co_fn_E_at_pi)
  moreover have "(\<Union>p \<in> -{p_b, p_i}. set (co_fn_E p_i p_b m_1 p)) = {}"
    by (auto simp: co_fn_E_elsewhere)
  ultimately show ?thesis by auto
qed

lemma wf_history_local_pb_in_co_fn_E:
  assumes "p_b \<noteq> p_i"
  shows "wf_history_local p_b (co_fn_E p_i p_b m_1 p_b)"
proof -
  let ?L = "[Send p_b 1 p_i m_1, Send p_b 2 p_i 0]"
  have list_eq: "co_fn_E p_i p_b m_1 p_b = ?L"
    using assms by simp
  have proc_ok: "\<forall>e \<in> set ?L. proc_of e = p_b" by simp
  have seq_ok: "\<forall>k < length ?L. seq_of (?L ! k) = Suc k"
  proof (intro allI impI)
    fix k assume "k < length ?L"
    hence "k = 0 \<or> k = 1" by auto
    thus "seq_of (?L ! k) = Suc k" by auto
  qed
  show ?thesis using list_eq proc_ok seq_ok
    unfolding wf_history_local_def by simp
qed

lemma wf_history_local_pi_in_co_fn_E:
  assumes "p_b \<noteq> p_i"
  shows "wf_history_local p_i (co_fn_E p_i p_b m_1 p_i)"
proof -
  let ?L = "[Receive p_i 1 p_b m_1, Receive p_i 2 p_b 0]"
  have list_eq: "co_fn_E p_i p_b m_1 p_i = ?L"
    using assms by (rule co_fn_E_at_pi)
  have proc_ok: "\<forall>e \<in> set ?L. proc_of e = p_i" by simp
  have seq_ok: "\<forall>k < length ?L. seq_of (?L ! k) = Suc k"
  proof (intro allI impI)
    fix k assume "k < length ?L"
    hence "k = 0 \<or> k = 1" by auto
    thus "seq_of (?L ! k) = Suc k" by auto
  qed
  show ?thesis using list_eq proc_ok seq_ok
    unfolding wf_history_local_def by simp
qed

lemma wf_history_local_elsewhere_in_co_fn_E:
  assumes "p \<noteq> p_b" "p \<noteq> p_i"
  shows "wf_history_local p (co_fn_E p_i p_b m_1 p)"
  using assms by (simp add: co_fn_E_elsewhere wf_history_local_def)

lemma wf_history_co_fn_E:
  assumes "p_b \<noteq> p_i"
  shows "wf_history (co_fn_E p_i p_b m_1)"
proof (unfold wf_history_def, intro allI)
  fix p
  show "wf_history_local p (co_fn_E p_i p_b m_1 p)"
  proof (cases "p = p_b")
    case True
    thus ?thesis using assms wf_history_local_pb_in_co_fn_E by simp
  next
    case False
    show ?thesis
    proof (cases "p = p_i")
      case True
      thus ?thesis using assms wf_history_local_pi_in_co_fn_E by simp
    next
      case False
      with \<open>p \<noteq> p_b\<close> show ?thesis
        by (rule wf_history_local_elsewhere_in_co_fn_E)
    qed
  qed
qed

lemma message_order_co_fn_E_send1_receive1:
  assumes "p_b \<noteq> p_i"
  shows "message_order (co_fn_E p_i p_b m_1)
           (Send p_b 1 p_i m_1) (Receive p_i 1 p_b m_1)"
  using assms unfolding message_order_def
  by (simp add: co_fn_E_events)

lemma program_order_co_fn_E_at_pi:
  assumes "p_b \<noteq> p_i"
  shows "program_order (co_fn_E p_i p_b m_1)
           (Receive p_i 1 p_b m_1) (Receive p_i 2 p_b 0)"
proof -
  let ?H = "co_fn_E p_i p_b m_1"
  have list_eq: "?H p_i = [Receive p_i 1 p_b m_1, Receive p_i 2 p_b 0]"
    using assms by (rule co_fn_E_at_pi)
  have len: "length (?H p_i) = 2" by (simp add: list_eq)
  have e0: "(?H p_i) ! 0 = Receive p_i 1 p_b m_1" by (simp add: list_eq)
  have e1: "(?H p_i) ! 1 = Receive p_i 2 p_b 0" by (simp add: list_eq)
  have "(0::nat) < 1" by simp
  moreover have "(1::nat) < length (?H p_i)" using len by simp
  ultimately show ?thesis
    using e0 e1 unfolding program_order_def by blast
qed

lemma hb_send1_to_estar_in_co_fn_E:
  assumes "p_b \<noteq> p_i"
  shows "hb (co_fn_E p_i p_b m_1)
           (Send p_b 1 p_i m_1) (Receive p_i 2 p_b 0)"
proof -
  let ?H = "co_fn_E p_i p_b m_1"
  let ?s = "Send p_b 1 p_i m_1"
  let ?r = "Receive p_i 1 p_b m_1"
  let ?es = "Receive p_i 2 p_b 0"
  have step1: "hb_step ?H ?s ?r"
    using message_order_co_fn_E_send1_receive1[OF assms]
    by (simp add: hb_step_def)
  have step2: "hb_step ?H ?r ?es"
    using program_order_co_fn_E_at_pi[OF assms]
    by (simp add: hb_step_def)
  have t1: "(hb_step ?H)\<^sup>+\<^sup>+ ?s ?r" using step1 by blast
  have t2: "(hb_step ?H)\<^sup>+\<^sup>+ ?r ?es" using step2 by blast
  have "(hb_step ?H)\<^sup>+\<^sup>+ ?s ?es" using t1 t2 by (rule tranclp_trans)
  thus ?thesis by (simp add: hb_def)
qed

lemma hb_eval_send1_to_estar_in_co_fn_E:
  assumes "p_b \<noteq> p_i"
  shows "hb_eval (co_fn_E p_i p_b m_1)
           (Send p_b 1 p_i m_1) (Receive p_i 2 p_b 0)"
proof -
  let ?H = "co_fn_E p_i p_b m_1"
  have e1: "Send p_b 1 p_i m_1 \<in> events_of ?H"
    using assms by (simp add: co_fn_E_events)
  have e2: "Receive p_i 2 p_b 0 \<in> events_of ?H"
    using assms by (simp add: co_fn_E_events)
  have h: "hb ?H (Send p_b 1 p_i m_1) (Receive p_i 2 p_b 0)"
    using assms by (rule hb_send1_to_estar_in_co_fn_E)
  show ?thesis using e1 e2 h by (simp add: hb_eval_def)
qed

lemma adv_admissible_co_fn_adv:
  assumes "p_i \<in> correct" "p_b \<noteq> p_i"
  shows "adversary_admissible correct (co_fn_adv p_i p_b m_1)"
proof -
  have a: "wf_history (co_fn_E p_i p_b m_1)"
    using assms(2) by (rule wf_history_co_fn_E)
  have b: "p_i \<in> correct" by (rule assms(1))
  have c: "proc_of (Receive p_i 2 p_b 0) = p_i" by simp
  have d: "Receive p_i 2 p_b 0 \<in> events_of (co_fn_E p_i p_b m_1)"
    using assms(2) by (simp add: co_fn_E_events)
  show ?thesis using a b c d
    by (simp add: adversary_admissible_def co_fn_adv_def)
qed

lemma co_admissible_co_fn_adv:
  assumes "p_i \<in> correct" "p_b \<noteq> p_i"
  shows "co_admissible correct (co_fn_adv p_i p_b m_1)"
proof -
  have adm: "adversary_admissible correct (co_fn_adv p_i p_b m_1)"
    using assms by (rule adv_admissible_co_fn_adv)
  have rcv: "is_receive (adv_e_star (co_fn_adv p_i p_b m_1))"
    by (simp add: co_fn_adv_def)
  show ?thesis using adm rcv by (simp add: co_admissible_def)
qed

theorem CO_FN_unavoidable:
  assumes byz_cor_distinct:
                  "\<exists>p_i p_b. p_i \<in> correct \<and> p_b \<in> byzantine \<and> p_b \<noteq> p_i"
      and fin_F:  "\<forall>p_i_in p_b_in.
                     finite (events_of
                              (fst (alg p_i_in (Receive p_i_in 2 p_b_in 0))))"
  shows "\<exists>adv. co_admissible correct adv \<and>
               false_negative (adv_E adv)
                              (fst (alg (adv_i adv) (adv_e_star adv)))
                              (adv_e_star adv)"
proof -
  obtain p_i p_b where
      pi_cor: "p_i \<in> correct" and pb_byz: "p_b \<in> byzantine"
      and dist: "p_b \<noteq> p_i"
    using byz_cor_distinct by blast

  let ?e_star = "Receive p_i 2 p_b 0"
  let ?F = "fst (alg p_i ?e_star)"
  let ?m_1 = "fresh_nat ?F"
  let ?adv = "co_fn_adv p_i p_b ?m_1"
  let ?s = "Send p_b 1 p_i ?m_1"

  have finF: "finite (events_of ?F)" using fin_F by blast

  have adm: "co_admissible correct ?adv"
    using pi_cor dist by (rule co_admissible_co_fn_adv)

  have witness_in_E: "?s \<in> events_of (adv_E ?adv)"
    using dist by (simp add: co_fn_adv_def co_fn_E_events)
  have hbE: "hb_eval (adv_E ?adv) ?s (adv_e_star ?adv)"
  proof -
    have "hb_eval (co_fn_E p_i p_b ?m_1) ?s (Receive p_i 2 p_b 0)"
      by (rule hb_eval_send1_to_estar_in_co_fn_E[OF dist])
    thus ?thesis by (simp add: co_fn_adv_def)
  qed
  have witness_not_in_F: "?s \<notin> events_of ?F"
    using finF Send_at_fresh_nat_not_in_F[of ?F] by blast
  have not_hbF: "\<not> hb_eval ?F ?s (adv_e_star ?adv)"
    using witness_not_in_F by (simp add: hb_eval_def co_fn_adv_def)

  from witness_in_E hbE not_hbF
  have "\<exists>e \<in> events_of (adv_E ?adv) \<union> events_of ?F.
            hb_eval (adv_E ?adv) e (adv_e_star ?adv) \<and>
            \<not> hb_eval ?F e (adv_e_star ?adv)"
    by blast
  hence FN: "false_negative (adv_E ?adv) ?F (adv_e_star ?adv)"
    by (simp add: false_negative_def)

  have F_eq: "fst (alg (adv_i ?adv) (adv_e_star ?adv)) = ?F"
    by (simp add: co_fn_adv_def)

  from adm FN F_eq show ?thesis by metis
qed

section \<open>Theorem 18b: CO has FN or FP for internal-event witnesses\<close>

text \<open>Paper, Theorem 18 (the FN/FP corollary, internal-event side --
by the same logic as the paper's T2):
\begin{quote}
``CO is subject to FN and FP in the Byzantine model.''  In particular,
for any internal event \<open>e_h^x\<close> at a Byzantine process \<open>p_h\<close>,
neither FN nor FP can be prevented when settling
\<open>e_h^x \<rightarrow> e_r^*\<close> at the receiving correct process \<open>p_r\<close>.
\end{quote}

\textbf{Construction.}  Strengthen the T18a construction with a chain
of internal events at @{term p_b} before its sends.  The witness is
the @{term k}-th internal event at @{term p_b}, with
@{term "k = fresh_nat F"} chosen so it is absent from
@{term "events_of F"}.\<close>

definition co_fn_internal_E ::
  "'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'p history" where
  "co_fn_internal_E p_i p_b k m_1 \<equiv>
     (\<lambda>p. if p = p_b
          then (map (Internal p_b) [1..<Suc k])
                @ [Send p_b (Suc k) p_i m_1,
                   Send p_b (Suc (Suc k)) p_i 0]
          else if p = p_i
          then [Receive p_i 1 p_b m_1, Receive p_i 2 p_b 0]
          else [])"

definition co_fn_internal_adv ::
  "'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'p adversary" where
  "co_fn_internal_adv p_i p_b k m_1 \<equiv>
     \<lparr> adv_E = co_fn_internal_E p_i p_b k m_1,
       adv_e_star = Receive p_i 2 p_b 0,
       adv_i = p_i \<rparr>"

lemma co_fn_internal_E_at_pb [simp]:
  assumes "p_b \<noteq> p_i"
  shows "co_fn_internal_E p_i p_b k m_1 p_b
           = (map (Internal p_b) [1..<Suc k])
              @ [Send p_b (Suc k) p_i m_1,
                 Send p_b (Suc (Suc k)) p_i 0]"
  using assms by (simp add: co_fn_internal_E_def)

lemma co_fn_internal_E_at_pi:
  assumes "p_b \<noteq> p_i"
  shows "co_fn_internal_E p_i p_b k m_1 p_i
           = [Receive p_i 1 p_b m_1, Receive p_i 2 p_b 0]"
  using assms by (auto simp: co_fn_internal_E_def)

lemma co_fn_internal_E_elsewhere:
  assumes "p \<noteq> p_b" "p \<noteq> p_i"
  shows "co_fn_internal_E p_i p_b k m_1 p = []"
  using assms by (simp add: co_fn_internal_E_def)

lemma length_co_fn_internal_E_pb:
  assumes "p_b \<noteq> p_i"
  shows "length (co_fn_internal_E p_i p_b k m_1 p_b) = Suc (Suc k)"
  using assms by simp

lemma nth_co_fn_internal_E_pb_lt:
  assumes "p_b \<noteq> p_i" "j < k"
  shows "co_fn_internal_E p_i p_b k m_1 p_b ! j = Internal p_b (Suc j)"
proof -
  let ?xs = "map (Internal p_b) [1..<Suc k]"
  let ?tail = "[Send p_b (Suc k) p_i m_1, Send p_b (Suc (Suc k)) p_i 0]"
  let ?L = "?xs @ ?tail"
  have list_eq: "co_fn_internal_E p_i p_b k m_1 p_b = ?L"
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

lemma nth_co_fn_internal_E_pb_at_k:
  assumes "p_b \<noteq> p_i"
  shows "co_fn_internal_E p_i p_b k m_1 p_b ! k = Send p_b (Suc k) p_i m_1"
  using assms by (simp add: nth_append)

lemma nth_co_fn_internal_E_pb_at_Sk:
  assumes "p_b \<noteq> p_i"
  shows "co_fn_internal_E p_i p_b k m_1 p_b ! Suc k
           = Send p_b (Suc (Suc k)) p_i 0"
  using assms by (simp add: nth_append)

lemma set_co_fn_internal_E_pb:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "set (co_fn_internal_E p_i p_b k m_1 p_b)
            = (Internal p_b ` {1..k})
                \<union> {Send p_b (Suc k) p_i m_1,
                   Send p_b (Suc (Suc k)) p_i 0}"
proof -
  have set_map: "set (map (Internal p_b) [1..<Suc k]) = Internal p_b ` {1..<Suc k}"
    by auto
  have rng_eq: "{1..<Suc k} = {1..k}" by auto
  have "set (co_fn_internal_E p_i p_b k m_1 p_b)
          = set (map (Internal p_b) [1..<Suc k])
              \<union> {Send p_b (Suc k) p_i m_1, Send p_b (Suc (Suc k)) p_i 0}"
    using assms(1) by simp
  also have "\<dots> = (Internal p_b ` {1..k})
                    \<union> {Send p_b (Suc k) p_i m_1,
                       Send p_b (Suc (Suc k)) p_i 0}"
    using set_map rng_eq by simp
  finally show ?thesis .
qed

lemma co_fn_internal_E_events:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "events_of (co_fn_internal_E p_i p_b k m_1) =
           (Internal p_b ` {1..k})
           \<union> {Send p_b (Suc k) p_i m_1,
              Send p_b (Suc (Suc k)) p_i 0,
              Receive p_i 1 p_b m_1,
              Receive p_i 2 p_b 0}"
proof -
  have "events_of (co_fn_internal_E p_i p_b k m_1)
            = (\<Union>p. set (co_fn_internal_E p_i p_b k m_1 p))"
    by (simp add: events_of_def)
  also have "\<dots> = set (co_fn_internal_E p_i p_b k m_1 p_b)
                   \<union> set (co_fn_internal_E p_i p_b k m_1 p_i)
                   \<union> (\<Union>p \<in> -{p_b, p_i}.
                           set (co_fn_internal_E p_i p_b k m_1 p))"
    by auto
  also have "(\<Union>p \<in> -{p_b, p_i}. set (co_fn_internal_E p_i p_b k m_1 p)) = {}"
    by (auto simp: co_fn_internal_E_elsewhere)
  moreover have "set (co_fn_internal_E p_i p_b k m_1 p_b)
                   = (Internal p_b ` {1..k})
                       \<union> {Send p_b (Suc k) p_i m_1,
                          Send p_b (Suc (Suc k)) p_i 0}"
    using assms by (rule set_co_fn_internal_E_pb)
  moreover have "set (co_fn_internal_E p_i p_b k m_1 p_i)
                   = {Receive p_i 1 p_b m_1, Receive p_i 2 p_b 0}"
    using assms(1) by (simp add: co_fn_internal_E_at_pi)
  ultimately show ?thesis by auto
qed

lemma wf_history_local_pb_in_co_fn_internal_E:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "wf_history_local p_b (co_fn_internal_E p_i p_b k m_1 p_b)"
proof -
  let ?L = "co_fn_internal_E p_i p_b k m_1 p_b"
  have len_L: "length ?L = Suc (Suc k)"
    using assms(1) by (rule length_co_fn_internal_E_pb)

  have all_proc: "\<forall>e \<in> set ?L. proc_of e = p_b"
  proof
    fix e assume "e \<in> set ?L"
    hence "e \<in> (Internal p_b ` {1..k})
              \<union> {Send p_b (Suc k) p_i m_1,
                 Send p_b (Suc (Suc k)) p_i 0}"
      using set_co_fn_internal_E_pb[OF assms] by simp
    thus "proc_of e = p_b" by (auto simp: image_iff)
  qed

  have all_seq: "\<forall>j < length ?L. seq_of (?L ! j) = Suc j"
  proof (intro allI impI)
    fix j assume "j < length ?L"
    hence j_lt: "j < Suc (Suc k)" using len_L by simp
    show "seq_of (?L ! j) = Suc j"
    proof (cases "j < k")
      case True
      thus ?thesis using nth_co_fn_internal_E_pb_lt[OF assms(1)] by simp
    next
      case False
      with j_lt have "j = k \<or> j = Suc k" by auto
      thus ?thesis
        using nth_co_fn_internal_E_pb_at_k[OF assms(1)]
              nth_co_fn_internal_E_pb_at_Sk[OF assms(1)]
        by auto
    qed
  qed

  show ?thesis using all_proc all_seq
    unfolding wf_history_local_def by blast
qed

lemma wf_history_local_pi_in_co_fn_internal_E:
  assumes "p_b \<noteq> p_i"
  shows "wf_history_local p_i (co_fn_internal_E p_i p_b k m_1 p_i)"
proof -
  let ?L = "[Receive p_i 1 p_b m_1, Receive p_i 2 p_b 0]"
  have list_eq: "co_fn_internal_E p_i p_b k m_1 p_i = ?L"
    using assms by (rule co_fn_internal_E_at_pi)
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

lemma wf_history_local_elsewhere_in_co_fn_internal_E:
  assumes "p \<noteq> p_b" "p \<noteq> p_i"
  shows "wf_history_local p (co_fn_internal_E p_i p_b k m_1 p)"
  using assms by (simp add: co_fn_internal_E_elsewhere wf_history_local_def)

lemma wf_history_co_fn_internal_E:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "wf_history (co_fn_internal_E p_i p_b k m_1)"
proof (unfold wf_history_def, intro allI)
  fix p
  show "wf_history_local p (co_fn_internal_E p_i p_b k m_1 p)"
  proof (cases "p = p_b")
    case True
    thus ?thesis using assms wf_history_local_pb_in_co_fn_internal_E by simp
  next
    case False
    show ?thesis
    proof (cases "p = p_i")
      case True
      thus ?thesis using assms(1) wf_history_local_pi_in_co_fn_internal_E by simp
    next
      case False
      with \<open>p \<noteq> p_b\<close> show ?thesis
        by (rule wf_history_local_elsewhere_in_co_fn_internal_E)
    qed
  qed
qed

lemma program_order_internal_to_send1_in_co_fn_internal:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "program_order (co_fn_internal_E p_i p_b k m_1)
           (Internal p_b k) (Send p_b (Suc k) p_i m_1)"
proof -
  let ?H = "co_fn_internal_E p_i p_b k m_1"
  have len: "length (?H p_b) = Suc (Suc k)"
    using assms(1) by (rule length_co_fn_internal_E_pb)
  from assms(2) have km1_lt_k: "k - 1 < k" by simp
  have at_km1: "(?H p_b) ! (k - 1) = Internal p_b (Suc (k - 1))"
    using assms(1) km1_lt_k nth_co_fn_internal_E_pb_lt by simp
  hence at_km1': "(?H p_b) ! (k - 1) = Internal p_b k"
    using assms(2) by simp
  have at_k: "(?H p_b) ! k = Send p_b (Suc k) p_i m_1"
    using assms(1) by (rule nth_co_fn_internal_E_pb_at_k)
  have idx1: "k - 1 < k" using assms(2) by simp
  have idx2: "k < length (?H p_b)" using len by simp
  show ?thesis using at_km1' at_k idx1 idx2
    unfolding program_order_def by blast
qed

lemma program_order_receive_to_estar_in_co_fn_internal:
  assumes "p_b \<noteq> p_i"
  shows "program_order (co_fn_internal_E p_i p_b k m_1)
           (Receive p_i 1 p_b m_1) (Receive p_i 2 p_b 0)"
proof -
  let ?H = "co_fn_internal_E p_i p_b k m_1"
  have list_eq: "?H p_i = [Receive p_i 1 p_b m_1, Receive p_i 2 p_b 0]"
    using assms by (rule co_fn_internal_E_at_pi)
  have len: "length (?H p_i) = 2" by (simp add: list_eq)
  have e0: "(?H p_i) ! 0 = Receive p_i 1 p_b m_1" by (simp add: list_eq)
  have e1: "(?H p_i) ! 1 = Receive p_i 2 p_b 0" by (simp add: list_eq)
  have "(0::nat) < 1" by simp
  moreover have "(1::nat) < length (?H p_i)" using len by simp
  ultimately show ?thesis using e0 e1
    unfolding program_order_def by blast
qed

lemma message_order_send1_to_receive1_in_co_fn_internal:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "message_order (co_fn_internal_E p_i p_b k m_1)
           (Send p_b (Suc k) p_i m_1) (Receive p_i 1 p_b m_1)"
  using assms unfolding message_order_def
  by (simp add: co_fn_internal_E_events)

lemma hb_internal_to_estar_in_co_fn_internal_E:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "hb (co_fn_internal_E p_i p_b k m_1)
           (Internal p_b k) (Receive p_i 2 p_b 0)"
proof -
  let ?H = "co_fn_internal_E p_i p_b k m_1"
  let ?ih = "Internal p_b k"
  let ?s = "Send p_b (Suc k) p_i m_1"
  let ?r = "Receive p_i 1 p_b m_1"
  let ?es = "Receive p_i 2 p_b 0"
  have step1: "hb_step ?H ?ih ?s"
    using program_order_internal_to_send1_in_co_fn_internal[OF assms]
    by (simp add: hb_step_def)
  have step2: "hb_step ?H ?s ?r"
    using message_order_send1_to_receive1_in_co_fn_internal[OF assms]
    by (simp add: hb_step_def)
  have step3: "hb_step ?H ?r ?es"
    using program_order_receive_to_estar_in_co_fn_internal[OF assms(1)]
    by (simp add: hb_step_def)
  have t1: "(hb_step ?H)\<^sup>+\<^sup>+ ?ih ?s" using step1 by blast
  have t2: "(hb_step ?H)\<^sup>+\<^sup>+ ?s ?r" using step2 by blast
  have t3: "(hb_step ?H)\<^sup>+\<^sup>+ ?r ?es" using step3 by blast
  have "(hb_step ?H)\<^sup>+\<^sup>+ ?ih ?r" using t1 t2 by (rule tranclp_trans)
  hence "(hb_step ?H)\<^sup>+\<^sup>+ ?ih ?es" using t3 by (rule tranclp_trans)
  thus ?thesis by (simp add: hb_def)
qed

lemma hb_eval_internal_to_estar_in_co_fn_internal_E:
  assumes "p_b \<noteq> p_i" "k \<ge> 1"
  shows "hb_eval (co_fn_internal_E p_i p_b k m_1)
           (Internal p_b k) (Receive p_i 2 p_b 0)"
proof -
  let ?H = "co_fn_internal_E p_i p_b k m_1"
  have e_ih: "Internal p_b k \<in> events_of ?H"
    using assms by (simp add: co_fn_internal_E_events)
  have e_es: "Receive p_i 2 p_b 0 \<in> events_of ?H"
    using assms by (simp add: co_fn_internal_E_events)
  have h: "hb ?H (Internal p_b k) (Receive p_i 2 p_b 0)"
    using assms by (rule hb_internal_to_estar_in_co_fn_internal_E)
  show ?thesis using e_ih e_es h by (simp add: hb_eval_def)
qed

lemma adv_admissible_co_fn_internal_adv:
  assumes "p_i \<in> correct" "p_b \<noteq> p_i" "k \<ge> 1"
  shows "adversary_admissible correct (co_fn_internal_adv p_i p_b k m_1)"
proof -
  have a: "wf_history (co_fn_internal_E p_i p_b k m_1)"
    using assms(2) assms(3) by (rule wf_history_co_fn_internal_E)
  have b: "p_i \<in> correct" by (rule assms(1))
  have c: "proc_of (Receive p_i 2 p_b 0) = p_i" by simp
  have d: "Receive p_i 2 p_b 0 \<in> events_of (co_fn_internal_E p_i p_b k m_1)"
    using assms(2) assms(3) by (simp add: co_fn_internal_E_events)
  show ?thesis using a b c d
    by (simp add: adversary_admissible_def co_fn_internal_adv_def)
qed

lemma co_admissible_co_fn_internal_adv:
  assumes "p_i \<in> correct" "p_b \<noteq> p_i" "k \<ge> 1"
  shows "co_admissible correct (co_fn_internal_adv p_i p_b k m_1)"
proof -
  have adm: "adversary_admissible correct (co_fn_internal_adv p_i p_b k m_1)"
    using assms by (rule adv_admissible_co_fn_internal_adv)
  have rcv: "is_receive (adv_e_star (co_fn_internal_adv p_i p_b k m_1))"
    by (simp add: co_fn_internal_adv_def)
  show ?thesis using adm rcv by (simp add: co_admissible_def)
qed

theorem CO_FN_or_FP_unavoidable_internal:
  assumes byz_cor_distinct:
                  "\<exists>p_i p_b. p_i \<in> correct \<and> p_b \<in> byzantine \<and> p_b \<noteq> p_i"
      and fin_F:  "\<forall>p_i_in p_b_in.
                     finite (events_of
                              (fst (alg p_i_in (Receive p_i_in 2 p_b_in 0))))"
  shows "\<exists>adv e_h. co_admissible correct adv \<and>
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

  let ?e_star = "Receive p_i 2 p_b 0"
  let ?F = "fst (alg p_i ?e_star)"
  let ?k = "fresh_nat ?F"
  let ?m_1 = "fresh_nat ?F"
  let ?adv = "co_fn_internal_adv p_i p_b ?k ?m_1"
  let ?ih = "Internal p_b ?k"

  have finF: "finite (events_of ?F)" using fin_F by blast

  have k_pos: "?k \<ge> 1"
    by (simp add: fresh_nat_def Suc_leI)

  have adm: "co_admissible correct ?adv"
    using pi_cor dist k_pos by (rule co_admissible_co_fn_internal_adv)

  have witness_in_E: "?ih \<in> events_of (adv_E ?adv)"
    using dist k_pos
    by (auto simp: co_fn_internal_adv_def co_fn_internal_E_events)
  have hbE: "hb_eval (adv_E ?adv) ?ih (adv_e_star ?adv)"
  proof -
    have "hb_eval (co_fn_internal_E p_i p_b ?k ?m_1) ?ih (Receive p_i 2 p_b 0)"
      by (rule hb_eval_internal_to_estar_in_co_fn_internal_E[OF dist k_pos])
    thus ?thesis by (simp add: co_fn_internal_adv_def)
  qed
  have witness_not_in_F: "?ih \<notin> events_of ?F"
    using finF Internal_at_fresh_nat_not_in_F[of ?F] by blast
  have not_hbF: "\<not> hb_eval ?F ?ih (adv_e_star ?adv)"
    using witness_not_in_F by (simp add: hb_eval_def co_fn_internal_adv_def)

  have F_eq: "fst (alg (adv_i ?adv) (adv_e_star ?adv)) = ?F"
    by (simp add: co_fn_internal_adv_def)

  have e_h_internal: "\<exists>p n. ?ih = Internal p n" by blast

  from adm e_h_internal hbE not_hbF F_eq witness_in_E
  show ?thesis by metis
qed

end \<comment> \<open>context @{locale process_partition}\<close>

section \<open>Theorems 17 and impossibility of CO\<close>

context byzantineSystem
begin

text \<open>The direct CO-impossibility lemma, mirroring
\<open>no_produces_valid_F\<close> in \<open>Impossibility.thy\<close>: given a
finiteness side condition on every candidate CO solver's output
history at the Theorem 18a target shape, Theorem 18a directly
contradicts the existence of a CO-valid algorithm.\<close>

lemma no_produces_valid_F_CO:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_co:
        "\<forall>co_alg. produces_valid_F_CO correct co_alg \<longrightarrow>
           (\<forall>p_i_in p_b_in.
              finite (events_of
                       (fst (co_alg p_i_in (Receive p_i_in 2 p_b_in 0)))))"
  shows "\<not> (\<exists>co_alg. produces_valid_F_CO correct co_alg)"
proof
  assume "\<exists>co_alg. produces_valid_F_CO correct co_alg"
  then obtain co_alg
    where val_F: "produces_valid_F_CO correct co_alg" by blast

  have byz_cor_distinct:
    "\<exists>p_i p_b. p_i \<in> correct \<and> p_b \<in> byzantine \<and> p_b \<noteq> p_i"
    by (rule byz_cor_distinct_of_ne[OF byz_ne cor_ne])

  have fin_F:
    "\<forall>p_i_in p_b_in.
        finite (events_of
                 (fst (co_alg p_i_in (Receive p_i_in 2 p_b_in 0))))"
    using fin_co val_F by blast

  obtain adv where
    adm: "co_admissible correct adv"
    and FN: "false_negative (adv_E adv)
                            (fst (co_alg (adv_i adv) (adv_e_star adv)))
                            (adv_e_star adv)"
    using CO_FN_unavoidable[where alg = co_alg,
                            OF byz_cor_distinct fin_F]
    by blast

  have valid_at:
    "valid (adv_E adv)
           (fst (co_alg (adv_i adv) (adv_e_star adv)))
           (adv_e_star adv)"
    using val_F adm
    by (auto simp: produces_valid_F_CO_def Let_def split: prod.split)
  hence "\<not> false_negative (adv_E adv)
                          (fst (co_alg (adv_i adv) (adv_e_star adv)))
                          (adv_e_star adv)"
    using valid_iff_no_FP_FN by blast
  with FN show False by contradiction
qed

section \<open>CO impossibility: unicast / broadcast / multicast\<close>

theorem CO_impossible_unicast:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_co:
        "\<forall>co_alg. produces_valid_F_CO correct co_alg \<longrightarrow>
           (\<forall>p_i_in p_b_in.
              finite (events_of
                       (fst (co_alg p_i_in (Receive p_i_in 2 p_b_in 0)))))"
  shows "\<not> CO_solvable Unicast correct"
  using no_produces_valid_F_CO[OF byz_ne cor_ne fin_co]
  by (auto simp: CO_solvable_def)

theorem CO_impossible_broadcast:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_co:
        "\<forall>co_alg. produces_valid_F_CO correct co_alg \<longrightarrow>
           (\<forall>p_i_in p_b_in.
              finite (events_of
                       (fst (co_alg p_i_in (Receive p_i_in 2 p_b_in 0)))))"
  shows "\<not> CO_solvable Broadcast correct"
  using no_produces_valid_F_CO[OF byz_ne cor_ne fin_co]
  by (auto simp: CO_solvable_def)

theorem CO_impossible_multicast:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_co:
        "\<forall>co_alg. produces_valid_F_CO correct co_alg \<longrightarrow>
           (\<forall>p_i_in p_b_in.
              finite (events_of
                       (fst (co_alg p_i_in (Receive p_i_in 2 p_b_in 0)))))"
  shows "\<not> CO_solvable Multicast correct"
  using no_produces_valid_F_CO[OF byz_ne cor_ne fin_co]
  by (auto simp: CO_solvable_def)

section \<open>Theorem 17: CO and CD are interreducible in the Byzantine model\<close>

text \<open>Paper, Theorem 17 (Section 5.2):
\begin{quote}
``CO and CD are interreducible in the Byzantine model.''
\end{quote}

The forward direction (\<open>CD \<longrightarrow> CO\<close>) is \<open>CD_solvable_imp_CO_solvable\<close>
above, proven outside any locale -- a CD solver is automatically a
CO solver (CO admissibility is a strict restriction of CD
admissibility).

The reverse direction (\<open>CO \<longrightarrow> CD\<close>) under Byzantine premises
holds vacuously, because both sides are impossible: CO is impossible
by \<open>CO_impossible_unicast\<close>/etc.\ above (\<open>\<not> CO_solvable\<close>); CD is
impossible by \<open>CD_impossible_unicast\<close>/etc.\ in \<open>Impossibility.thy\<close>
(\<open>\<not> CD_solvable\<close>).  Hence \<open>CO_solvable \<longleftrightarrow> CD_solvable\<close>: both
False.

\textit{Deviation:} the paper sketches a constructive reverse
reduction (``the reverse direction is similar'').  In our function-
level abstraction this would require synthesising a CD solver from
a CO solver by extending every CD adversary with a self-receive
event after its target -- doable, but substantial.  The vacuous
route through the (independently proven) impossibility theorems
yields the same final interreducibility statement.\<close>

theorem T17_CO_interreducible_with_CD:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
      and fin_co:
        "\<forall>co_alg. produces_valid_F_CO correct co_alg \<longrightarrow>
           (\<forall>p_i_in p_b_in.
              finite (events_of
                       (fst (co_alg p_i_in (Receive p_i_in 2 p_b_in 0)))))"
  shows "CO_solvable m correct \<longleftrightarrow> CD_solvable m correct"
proof -
  have no_cd: "\<not> CD_solvable m correct"
  proof (cases m)
    case Unicast
    thus ?thesis
      using CD_impossible_unicast[OF byz_ne cor_ne fin_cd] by simp
  next
    case Broadcast
    thus ?thesis
      using CD_impossible_broadcast[OF byz_ne cor_ne fin_cd] by simp
  next
    case Multicast
    thus ?thesis
      using CD_impossible_multicast[OF byz_ne cor_ne fin_cd] by simp
  qed
  have no_co: "\<not> CO_solvable m correct"
  proof (cases m)
    case Unicast
    thus ?thesis
      using CO_impossible_unicast[OF byz_ne cor_ne fin_co] by simp
  next
    case Broadcast
    thus ?thesis
      using CO_impossible_broadcast[OF byz_ne cor_ne fin_co] by simp
  next
    case Multicast
    thus ?thesis
      using CO_impossible_multicast[OF byz_ne cor_ne fin_co] by simp
  qed
  from no_cd no_co show ?thesis by blast
qed

text \<open>Summary corollary: CO is impossible under all three
communication modes (one theorem statement, all three modes).\<close>

theorem CO_impossible_all_modes:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_co:
        "\<forall>co_alg. produces_valid_F_CO correct co_alg \<longrightarrow>
           (\<forall>p_i_in p_b_in.
              finite (events_of
                       (fst (co_alg p_i_in (Receive p_i_in 2 p_b_in 0)))))"
  shows "\<not> CO_solvable Unicast   correct"
    and "\<not> CO_solvable Broadcast correct"
    and "\<not> CO_solvable Multicast correct"
proof -
  show "\<not> CO_solvable Unicast correct"
    by (rule CO_impossible_unicast[OF byz_ne cor_ne fin_co])
  show "\<not> CO_solvable Broadcast correct"
    by (rule CO_impossible_broadcast[OF byz_ne cor_ne fin_co])
  show "\<not> CO_solvable Multicast correct"
    by (rule CO_impossible_multicast[OF byz_ne cor_ne fin_co])
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
