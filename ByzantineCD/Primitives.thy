(*
  Title:   Primitives.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  Operational discharge of the two communication primitives that
  paper Section 4.3 invokes when proving Theorems 6 and 7:

    BRU  (Byzantine Reliable Unicast): correct-to-correct
         point-to-point delivery is guaranteed even when other
         processes in the network are Byzantine.

    BCB-over-BRB  (Byzantine Causal Broadcast over Byzantine
         Reliable Broadcast):  every correct sender's broadcast
         reaches every correct receiver (BRB), and the resulting
         per-receiver delivery order respects the causal order
         of the sends (the CB part on top of BRB).

  -----------------------------------------------------------------
  At the abstraction level of our development -- events without
  message contents, an inductive run_step over correct-to-correct
  send/recv triples -- BRU has a direct expression: it is the
  property that every correct-to-correct \<open>Send\<close> event in the
  global history has a matching \<open>Receive\<close>.  The existing
  @{const messages_delivered_among} predicate of @{theory_text
  \<open>Delivery.thy\<close>} is exactly this property; the existing
  @{thm fairness_implies_delivery} theorem of @{theory_text
  \<open>Execution_Model.thy\<close>} is exactly its operational discharge.

  BCB-over-BRB has additional content beyond BRU: not just
  delivery but \<^emph>\<open>causally ordered\<close> delivery.  The CB part says: if
  @{term "Send p1 n1 q m1"} happens-before @{term "Send p2 n2 q
  m2"} in the global history, then every correct receiver's
  matching @{term "Receive q nr1 p1 m1"} happens-before its
  matching @{term "Receive q nr2 p2 m2"}.  We capture this as
  @{term bcb_causal_order} below.

  -----------------------------------------------------------------
  What we mechanise here

  (a) Named BRU and BCB-over-BRB abstractions at our event-level
      view of the global history.

  (b) An operational realisation of BRU: any finite run of the
      inductive run_step model that drains its in-flight buffer
      satisfies BRU.  Composed with @{thm fair_run_delivers}, fair
      infinite runs realise BRU pointwise.

  (c) Definitions for the BCB causal-order property and the
      compound BCB-over-BRB predicate; structural connections to
      BRU.

  (d) Mode-tagged composition theorems: under the existing
      \<open>mode_admissible Unicast / Broadcast\<close> predicate of
      @{theory_text \<open>Delivery.thy\<close>}, the naive algorithm with the
      @{const recv_from_history} view solves \<open>CD_B\<close>.  These are the
      operational T6 and T7 named explicitly as ``unicast via BRU''
      and ``broadcast via BCB-over-BRB''.

  What remains beyond this theory.  Operationally realising BCB's
  causal-order delivery requires a scheduler-level model: the order
  of @{const run_step.step_recv} invocations at each correct
  receiver must respect the causal order of the corresponding
  @{const run_step.step_send} events at the senders.  Our
  @{const run_step} relation does not constrain the receive
  schedule beyond fairness, so the causal-order operational
  realisation is not in scope here -- it is the same
  out-of-scope band as the BRU/BCB cryptographic implementations.

  Scope note.  The cryptographic discharge of the multicast case
  (Theorem 14) lives in @{theory_text \<open>CD_with_Crypto.thy\<close>};
  multicast without cryptography is unachievable (Theorem 8) and is
  outside the BRU/BCB story.
*)

theory Primitives
  imports Liveness
begin

context byzantineSystem
begin

section \<open>BRU: Byzantine Reliable Unicast\<close>

text \<open>The \<^emph>\<open>operational content\<close> of Byzantine Reliable Unicast
collapses, at our event-based abstraction, to the structural
condition that every correct-to-correct send has a matching
receive.  BRU's interesting operational properties -- a Byzantine
intermediary in the network path cannot drop, reorder, or
fabricate messages between two correct endpoints -- are below the
abstraction layer of this development; their downstream effect on
the global history is exactly the @{const messages_delivered_among}
predicate.

We expose a named alias \<open>bru_satisfied\<close> below so downstream
theorems can read ``BRU-satisfied'' rather than
``messages-delivered'' and so the operational role of the primitive
is documented at the predicate name.\<close>

definition bru_satisfied :: "'p history \<Rightarrow> bool" where
  "bru_satisfied H \<longleftrightarrow> messages_delivered_among correct H"

lemma bru_satisfied_iff:
  "bru_satisfied H \<longleftrightarrow> messages_delivered_among correct H"
  by (simp add: bru_satisfied_def)

subsection \<open>Operational discharge of BRU from the run model\<close>

text \<open>A finite run of the inductive @{const run_step} relation that
drains its in-flight buffer realises BRU.  This is exactly
@{thm fairness_implies_delivery}, repackaged under the BRU name.
Operationally: a unicast network where every correct-to-correct
in-flight message is eventually delivered produces histories that
satisfy BRU.\<close>

theorem drained_run_satisfies_bru:
  assumes run_cfg: "run cfg"
      and drained: "cfg_inflight cfg = empty_inflight"
  shows "bru_satisfied (cfg_hist cfg)"
  unfolding bru_satisfied_def
  by (rule fairness_implies_delivery[OF run_cfg drained])

text \<open>Fair infinite runs realise BRU \<^emph>\<open>per event\<close>: every
correct-to-correct \<open>Send\<close> that appears in some \<open>E i\<close> eventually
has a matching \<open>Receive\<close> in some \<open>E j\<close>.  This is the infinite-
execution analogue of @{thm drained_run_satisfies_bru}, proved in
@{thm fair_run_delivers}.\<close>

theorem fair_run_satisfies_bru_pointwise:
  assumes inf:  "infinite_run E"
      and fair: "fair_run E"
      and pc:   "p \<in> correct"
      and qc:   "q \<in> correct"
      and send: "Send p n q m \<in> events_of (cfg_hist (E i))"
  shows "\<exists>j nr. Receive q nr p m \<in> events_of (cfg_hist (E j))"
  by (rule fair_run_delivers[OF inf fair pc qc send])

section \<open>BCB-over-BRB: BRU plus causal-order delivery\<close>

text \<open>Byzantine Causal Broadcast over Byzantine Reliable Broadcast
is a strictly stronger primitive than BRU.  On top of BRU's
correct-to-correct reliability (the BRB part), BCB guarantees that
the delivery order at every correct receiver respects the causal
order of the sends.  Concretely, if two send events at correct
processes (possibly different senders) are causally ordered in the
global history, then every correct receiver sees the matching
receives in the same causal order.

We capture the CB part as \<open>bcb_causal_order\<close> below.  Together
with \<open>bru_satisfied\<close> it gives BCB-over-BRB:
\<open>bcb_over_brb_satisfied\<close>.\<close>

definition bcb_causal_order :: "'p set \<Rightarrow> 'p history \<Rightarrow> bool" where
  "bcb_causal_order C H \<longleftrightarrow>
     (\<forall>p1 n1 q m1 p2 n2 m2 nr1 nr2.
        p1 \<in> C \<and> p2 \<in> C \<and> q \<in> C \<and>
        Send p1 n1 q m1 \<in> events_of H \<and>
        Send p2 n2 q m2 \<in> events_of H \<and>
        Receive q nr1 p1 m1 \<in> events_of H \<and>
        Receive q nr2 p2 m2 \<in> events_of H \<and>
        hb H (Send p1 n1 q m1) (Send p2 n2 q m2)
        \<longrightarrow> hb H (Receive q nr1 p1 m1) (Receive q nr2 p2 m2))"

definition bcb_over_brb_satisfied :: "'p set \<Rightarrow> 'p history \<Rightarrow> bool" where
  "bcb_over_brb_satisfied C H \<longleftrightarrow>
     bru_satisfied H \<and> bcb_causal_order C H"

lemma bcb_over_brb_implies_bru:
  assumes "bcb_over_brb_satisfied C H"
  shows   "bru_satisfied H"
  using assms by (simp add: bcb_over_brb_satisfied_def)

lemma bcb_over_brb_implies_causal_order:
  assumes "bcb_over_brb_satisfied C H"
  shows   "bcb_causal_order C H"
  using assms by (simp add: bcb_over_brb_satisfied_def)

section \<open>Operational T6 and T7 named explicitly via the primitives\<close>

text \<open>Operational Theorem 6 (unicast via BRU): under
@{const mode_admissible} unicast on the adversary's execution, the
naive algorithm with the @{const recv_from_history} view solves
\<open>CD_B\<close>.

This is @{thm CD_B_solvable_unicast_operational}, repackaged under
the BRU name to make the operational role of the primitive
explicit.\<close>

theorem T6_unicast_via_bru:
  assumes adm:     "adversary_admissible correct adv"
      and mode_ok: "mode_admissible Unicast (adv_E adv)"
  shows "valid_B correct (adv_E adv)
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i adv) (adv_E adv))
                        (adv_i adv) (adv_e_star adv)))
                 (adv_e_star adv)"
  by (rule CD_B_solvable_unicast_operational[OF adm mode_ok])

text \<open>Connection from BRU to T6.  Any history that satisfies BRU
(plus the well-formedness baked into @{const mode_admissible}) is
unicast-mode-admissible by construction, so any algorithm whose
view is built from the history's correct components solves \<open>CD_B\<close>.\<close>

lemma bru_realises_mode_admissible_unicast:
  assumes wf:  "wf_history H"
      and bru: "bru_satisfied H"
  shows "mode_admissible Unicast H"
  using wf bru by (simp add: mode_admissible_def bru_satisfied_def)

theorem bru_solves_CD_B_unicast:
  assumes adm:  "adversary_admissible correct adv"
      and wf:   "wf_history (adv_E adv)"
      and bru:  "bru_satisfied (adv_E adv)"
  shows "valid_B correct (adv_E adv)
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i adv) (adv_E adv))
                        (adv_i adv) (adv_e_star adv)))
                 (adv_e_star adv)"
proof -
  have mode_ok: "mode_admissible Unicast (adv_E adv)"
    by (rule bru_realises_mode_admissible_unicast[OF wf bru])
  show ?thesis by (rule T6_unicast_via_bru[OF adm mode_ok])
qed

text \<open>Operational Theorem 7 (broadcast via BCB-over-BRB): under
@{const mode_admissible} broadcast on the adversary's execution,
the naive algorithm with the @{const recv_from_history} view solves
\<open>CD_B\<close>.

This is @{thm CD_B_solvable_broadcast_operational}, repackaged
under the BCB-over-BRB name.\<close>

theorem T7_broadcast_via_bcb_over_brb:
  assumes adm:     "adversary_admissible correct adv"
      and mode_ok: "mode_admissible Broadcast (adv_E adv)"
  shows "valid_B correct (adv_E adv)
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i adv) (adv_E adv))
                        (adv_i adv) (adv_e_star adv)))
                 (adv_e_star adv)"
  by (rule CD_B_solvable_broadcast_operational[OF adm mode_ok])

text \<open>Connection from BCB-over-BRB to T7.  A history satisfying
BCB-over-BRB also satisfies BRU (by @{thm bcb_over_brb_implies_bru})
and hence -- together with well-formedness -- is broadcast-mode-
admissible.  The causal-order half of BCB-over-BRB is not directly
needed at this abstraction (it would matter if our recv view were
derived from the receive sequence at each \<open>q\<close> rather than from the
global history @{term H} directly).  It is nonetheless the
operational property that, in a richer scheduler model, would let
a correct receiver assemble the senders' histories in the order
they actually happened.\<close>

lemma bcb_over_brb_realises_mode_admissible_broadcast:
  assumes wf:    "wf_history H"
      and bcb:   "bcb_over_brb_satisfied correct H"
  shows "mode_admissible Broadcast H"
proof -
  have bru: "bru_satisfied H" by (rule bcb_over_brb_implies_bru[OF bcb])
  show ?thesis
    using wf bru by (simp add: mode_admissible_def bru_satisfied_def)
qed

theorem bcb_over_brb_solves_CD_B_broadcast:
  assumes adm:  "adversary_admissible correct adv"
      and wf:   "wf_history (adv_E adv)"
      and bcb:  "bcb_over_brb_satisfied correct (adv_E adv)"
  shows "valid_B correct (adv_E adv)
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i adv) (adv_E adv))
                        (adv_i adv) (adv_e_star adv)))
                 (adv_e_star adv)"
proof -
  have mode_ok: "mode_admissible Broadcast (adv_E adv)"
    by (rule bcb_over_brb_realises_mode_admissible_broadcast[OF wf bcb])
  show ?thesis by (rule T7_broadcast_via_bcb_over_brb[OF adm mode_ok])
qed

section \<open>End-to-end: from a fair run of the model to a \<open>CD_B\<close>-solved configuration\<close>

text \<open>The full operational chain: a fair finite run (one that
drains the in-flight buffer) plus a unicast or broadcast mode
yields a configuration whose history is mode-admissible, and the
naive algorithm with the run-derived recv view solves \<open>CD_B\<close> at
every admissible adversary whose execution matches the run.\<close>

theorem fair_drained_run_solves_CD_B_unicast:
  assumes run_cfg: "run cfg"
      and drained: "cfg_inflight cfg = empty_inflight"
      and adm:     "adversary_admissible correct adv"
      and adv_eq:  "adv_E adv = cfg_hist cfg"
  shows "valid_B correct (adv_E adv)
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i adv) (adv_E adv))
                        (adv_i adv) (adv_e_star adv)))
                 (adv_e_star adv)"
proof -
  have wf:  "wf_history (cfg_hist cfg)"
    by (rule wf_history_run[OF run_cfg])
  have bru: "bru_satisfied (cfg_hist cfg)"
    by (rule drained_run_satisfies_bru[OF run_cfg drained])
  have wf':  "wf_history (adv_E adv)"  using wf  adv_eq by simp
  have bru': "bru_satisfied (adv_E adv)" using bru adv_eq by simp
  show ?thesis by (rule bru_solves_CD_B_unicast[OF adm wf' bru'])
qed

text \<open>The broadcast counterpart of @{thm fair_drained_run_solves_CD_B_unicast}.
We need the additional BCB causal-order property to assert
@{const bcb_over_brb_satisfied}; under our event model the
underlying scheduler does not enforce it operationally, so we leave
it as a hypothesis.  In a richer scheduler model satisfying BCB
operationally, that hypothesis is discharged.\<close>

theorem fair_drained_run_solves_CD_B_broadcast:
  assumes run_cfg: "run cfg"
      and drained: "cfg_inflight cfg = empty_inflight"
      and bcb_ord: "bcb_causal_order correct (cfg_hist cfg)"
      and adm:     "adversary_admissible correct adv"
      and adv_eq:  "adv_E adv = cfg_hist cfg"
  shows "valid_B correct (adv_E adv)
                 (fst (naive_cd_B_alg
                        (recv_from_history (adv_i adv) (adv_E adv))
                        (adv_i adv) (adv_e_star adv)))
                 (adv_e_star adv)"
proof -
  have wf:  "wf_history (cfg_hist cfg)"
    by (rule wf_history_run[OF run_cfg])
  have bru: "bru_satisfied (cfg_hist cfg)"
    by (rule drained_run_satisfies_bru[OF run_cfg drained])
  have bcb: "bcb_over_brb_satisfied correct (cfg_hist cfg)"
    using bru bcb_ord by (simp add: bcb_over_brb_satisfied_def)
  have wf':  "wf_history (adv_E adv)"   using wf  adv_eq by simp
  have bcb': "bcb_over_brb_satisfied correct (adv_E adv)"
    using bcb adv_eq by simp
  show ?thesis by (rule bcb_over_brb_solves_CD_B_broadcast[OF adm wf' bcb'])
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
