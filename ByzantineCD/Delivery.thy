(*
  Title:   Delivery.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  Phase 4 of #4 (operational communication model -- first cut).

  This theory adds the next layer of structure beneath
  CD_B_Algorithm.thy's correct_reporting hypothesis.  Up to this
  point the development has treated "what p_i has been told" as an
  abstract per-peer recv :: 'p \<Rightarrow> 'p history_local, with no
  connection to messages-in-flight or send/receive semantics.  Here
  we introduce a single explicit property of the global history:

      messages_delivered_among C H :=
        every Send event at a correct process whose peer is correct
        has a matching Receive event at the peer

  This is the operational property that the paper's section 4.3
  algorithms ultimately rely on:

    * T6 (unicast): BRU + simulated control broadcasts achieve
      correct-to-correct message delivery within a single mode.
    * T7 (broadcast): BCB-over-BRB achieves correct-to-correct
      message delivery across all correct processes.

  Both modes guarantee messages_delivered_among correct H for any
  reachable global history H; multicast (T8) does not.  We do not
  formalise the operational discharge -- modelling sends-in-flight,
  schedulers, and BRB internals is its own multi-week project --
  but we factor the abstract content so that downstream developments
  can hook in operationally without disrupting the Phase 1-3 layer.

  What is proved here

  Under messages_delivered_among correct H, the per-peer view

      recv_from_history p H q  :=  H q

  satisfies correct_reporting correct (recv_from_history p H) H.
  That is, if correct-to-correct delivery is operationally
  guaranteed, the trivial "report what you observe" view at any
  correct receiver is faithful at every correct sender.

  Combined with naive_cd_B_alg_correct (CD_B_Algorithm.thy), this
  gives a fully derived chain:

       messages_delivered_among correct H
          -->  correct_reporting correct (recv_from_history p H) H
          -->  valid_B correct H F (adv_e_star adv) for F = recv

  i.e., under the abstract operational property, the naive algorithm
  satisfies CD_B.  The remaining gap to a fully operational T6/T7
  proof is: "messages_delivered_among correct H holds for every
  unicast/broadcast-reachable H" -- a fact about the communication
  model, not about the algorithm.
*)

theory Delivery
  imports CD_B_Algorithm
begin

context byzantineSystem
begin

section \<open>The delivery property\<close>

text \<open>The abstract operational property: a global history @{term H}
in which every send by a correct process to a correct process has a
matching receive at the peer.  We do not constrain delivery between
Byzantine senders/receivers -- their events are irrelevant to bhb
because bhb chains run through correct processes only.\<close>

definition messages_delivered_among ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> bool" where
  "messages_delivered_among C H \<longleftrightarrow>
     (\<forall>p n q m. Send p n q m \<in> events_of H
                  \<longrightarrow> p \<in> C \<longrightarrow> q \<in> C
                  \<longrightarrow> (\<exists>n'. Receive q n' p m \<in> events_of H))"

section \<open>From a delivering history to a faithful received view\<close>

text \<open>The trivial received view: at process @{term p}, report what
the global history records at each peer @{term q}.

This is the abstract content of ``at \<open>p_i\<close>, the algorithm reads
each \<open>F_q\<close> from what it has been told''.  Operationally, \<open>p_i\<close>
would derive this view by collecting messages it has received from
or about \<open>q\<close>; at this abstraction level we identify the view with
the history's @{term q} component directly.\<close>

definition recv_from_history ::
  "'p \<Rightarrow> 'p history \<Rightarrow> ('p \<Rightarrow> 'p history_local)" where
  "recv_from_history p H q = H q"

lemma recv_from_history_simp [simp]:
  "recv_from_history p H q = H q"
  by (simp add: recv_from_history_def)

lemma recv_from_history_eq:
  "recv_from_history p H = H"
  by (rule ext) (simp add: recv_from_history_def)

text \<open>Sanity: a well-formed history yields a well-formed received
view.  This is needed so that the @{thm naive_cd_B_alg_correct}
hypothesis @{term "wf_history recv"} is satisfied at every correct
receiver.\<close>

lemma wf_recv_from_history:
  assumes "wf_history H"
  shows   "wf_history (recv_from_history p H)"
  using assms by (simp add: recv_from_history_eq)

text \<open>The headline reduction: under operational delivery, the
trivial received view satisfies @{const correct_reporting}.

At this abstraction level the proof is by definition (both sides
collapse to @{term "H q"} at correct @{term q}); the
@{const messages_delivered_among} hypothesis is not directly used
in the proof.  We retain it as the named hypothesis because it is
the property that downstream operational developments will need to
discharge: an algorithm that derives \<open>recv\<close> from received messages
will satisfy this lemma only when correct-to-correct delivery is
operationally enforced, otherwise the algorithm will see something
other than @{term "H q"}.\<close>

lemma correct_reporting_of_recv_from_history:
  assumes "messages_delivered_among correct H"
  shows "correct_reporting correct (recv_from_history p H) H"
  unfolding correct_reporting_def
  by (simp add: recv_from_history_eq)

section \<open>The naive algorithm as a CD_B-solver under operational delivery\<close>

text \<open>Composing @{thm correct_reporting_of_recv_from_history} with
@{thm naive_cd_B_alg_correct} gives: under operational
@{const messages_delivered_among}, the naive algorithm's output is
valid in the bhb sense at any admissible adversary's view.\<close>

theorem naive_cd_B_alg_correct_under_delivery:
  assumes adm: "adversary_admissible correct adv"
      and del: "messages_delivered_among correct (adv_E adv)"
  shows "valid_B correct (adv_E adv)
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i adv) (adv_E adv))
                        (adv_i adv) (adv_e_star adv)))
                 (adv_e_star adv)"
proof -
  let ?recv = "recv_from_history (adv_i adv) (adv_E adv)"
  have wfE: "wf_history (adv_E adv)"
    using adm by (auto simp: adversary_admissible_def)
  have wfR: "wf_history ?recv"
    using wfE by (rule wf_recv_from_history)
  have rep: "correct_reporting correct ?recv (adv_E adv)"
    using del by (rule correct_reporting_of_recv_from_history)
  have body:
    "let (F', _) = naive_cd_B_alg ?recv (adv_i adv) (adv_e_star adv) in
       valid_B correct (adv_E adv) F' (adv_e_star adv)"
    using naive_cd_B_alg_correct[unfolded produces_valid_F_B_recv_def]
          adm wfR rep
    by blast
  thus ?thesis by (simp add: Let_def split: prod.split_asm)
qed

section \<open>Operational versions of Theorems 6 and 7\<close>

text \<open>Paper Theorem 6 (unicast) and Theorem 7 (broadcast)
operationally: under the corresponding mode, the communication
primitive achieves @{const messages_delivered_among}, so the naive
algorithm solves CD_B.

\textit{What is mechanised here.}  Given the operational hypothesis
@{prop "\<forall>H. mode_admissible m H \<longrightarrow> messages_delivered_among correct H"}
-- ``every history reachable under mode \<open>m\<close> delivers correct-to-
correct messages'' -- the naive algorithm solves CD_B in mode \<open>m\<close>.

\textit{What remains operational.}  The hypothesis itself is the
operational fact about the communication primitive.  For unicast it
follows from BRU (correct-to-correct point-to-point is direct, no
Byzantine sender in the path can corrupt); for broadcast it follows
from BCB-over-BRB (the BRB layer ensures any correct sender's
broadcast is delivered to every correct receiver).  Mechanising
either operational fact requires modelling the communication
primitive itself -- a separate development.\<close>

definition mode_admissible :: "comm_mode \<Rightarrow> 'p history \<Rightarrow> bool" where
  "mode_admissible m H \<longleftrightarrow> wf_history H"
  \<comment> \<open>placeholder for mode-specific shape constraints; expanded by
      future developments that model unicast / broadcast / multicast
      explicitly\<close>

theorem CD_B_solvable_under_unicast_delivery:
  assumes mode_delivers:
        "\<forall>H. mode_admissible Unicast H
              \<longrightarrow> messages_delivered_among correct H"
  shows "\<forall>adv. adversary_admissible correct adv
              \<longrightarrow> mode_admissible Unicast (adv_E adv)
              \<longrightarrow> valid_B correct (adv_E adv)
                          (fst (naive_cd_B_alg
                                 (recv_from_history (adv_i adv) (adv_E adv))
                                 (adv_i adv) (adv_e_star adv)))
                          (adv_e_star adv)"
proof (intro allI impI)
  fix adv
  assume adm: "adversary_admissible correct adv"
     and mode_ok: "mode_admissible Unicast (adv_E adv)"
  from mode_delivers mode_ok have
    "messages_delivered_among correct (adv_E adv)" by blast
  with adm show
    "valid_B correct (adv_E adv)
              (fst (naive_cd_B_alg
                     (recv_from_history (adv_i adv) (adv_E adv))
                     (adv_i adv) (adv_e_star adv)))
              (adv_e_star adv)"
    by (rule naive_cd_B_alg_correct_under_delivery)
qed

theorem CD_B_solvable_under_broadcast_delivery:
  assumes mode_delivers:
        "\<forall>H. mode_admissible Broadcast H
              \<longrightarrow> messages_delivered_among correct H"
  shows "\<forall>adv. adversary_admissible correct adv
              \<longrightarrow> mode_admissible Broadcast (adv_E adv)
              \<longrightarrow> valid_B correct (adv_E adv)
                          (fst (naive_cd_B_alg
                                 (recv_from_history (adv_i adv) (adv_E adv))
                                 (adv_i adv) (adv_e_star adv)))
                          (adv_e_star adv)"
proof (intro allI impI)
  fix adv
  assume adm: "adversary_admissible correct adv"
     and mode_ok: "mode_admissible Broadcast (adv_E adv)"
  from mode_delivers mode_ok have
    "messages_delivered_among correct (adv_E adv)" by blast
  with adm show
    "valid_B correct (adv_E adv)
              (fst (naive_cd_B_alg
                     (recv_from_history (adv_i adv) (adv_E adv))
                     (adv_i adv) (adv_e_star adv)))
              (adv_e_star adv)"
    by (rule naive_cd_B_alg_correct_under_delivery)
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
