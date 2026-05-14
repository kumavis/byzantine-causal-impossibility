(*
  Title:   Events.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  Events, per-process execution histories E_i, global history E, the
  algorithm-perceived history F, and the happened-before relation \<rightarrow>
  evaluated against either history.  Mirrors Definitions 1 and 5 of the
  paper.
*)

theory Events
  imports ByzantineSystem
begin

section \<open>Events\<close>

text \<open>An event identifier records the process at which it occurred and a
local sequence index, matching the @{term "e_i^x"} notation of the paper
(Section~2).  We additionally tag each event with its kind: an internal step,
the send of a message, or the receipt of a message.  Sends and receives carry
the message and the peer process.\<close>

datatype 'p event =
    Internal (proc_of: 'p) (seq_of: nat)
  | Send     (proc_of: 'p) (seq_of: nat) (peer: 'p) (msg_id: nat)
  | Receive  (proc_of: 'p) (seq_of: nat) (peer: 'p) (msg_id: nat)

abbreviation is_send :: "'p event \<Rightarrow> bool" where
  "is_send e \<equiv> (\<exists>p n q m. e = Send p n q m)"

abbreviation is_receive :: "'p event \<Rightarrow> bool" where
  "is_receive e \<equiv> (\<exists>p n q m. e = Receive p n q m)"

abbreviation is_internal :: "'p event \<Rightarrow> bool" where
  "is_internal e \<equiv> (\<exists>p n. e = Internal p n)"

text \<open>The send and the corresponding receive of the same message are
identified by a shared @{term msg_id}.  The \<open>matches\<close> predicate below
captures this.\<close>

fun matches :: "'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "matches (Send p n q m) (Receive q' n' p' m') \<longleftrightarrow> (p = p' \<and> q = q' \<and> m = m')"
| "matches _ _ \<longleftrightarrow> False"

section \<open>Per-process and global histories\<close>

text \<open>The per-process execution history @{term "E i"} is the finite list of
events executed at process @{term i} up to its current local state (paper,
Section~2).  In Definition~5 the global history @{term E} is the family
\<open>{E_i}_i\<close>; we model it directly as the family of finite event-lists indexed by
process.\<close>

type_synonym 'p history_local = "'p event list"
type_synonym 'p history       = "'p \<Rightarrow> 'p history_local"

definition events_of :: "'p history \<Rightarrow> 'p event set" where
  "events_of H = (\<Union>p. set (H p))"

text \<open>Well-formedness of a history: each per-process history records only
events of that process, with strictly increasing local sequence numbers
starting from 1.  This is a faithful encoding of the paper's enumeration
\<open>\<langle>s_i^0, e_i^1, s_i^1, e_i^2, \<dots>\<rangle>\<close>.\<close>

definition wf_history_local :: "'p \<Rightarrow> 'p history_local \<Rightarrow> bool" where
  "wf_history_local p es \<longleftrightarrow>
     (\<forall>e \<in> set es. proc_of e = p) \<and>
     (\<forall>k < length es. seq_of (es ! k) = Suc k)"

definition wf_history :: "'p history \<Rightarrow> bool" where
  "wf_history H \<longleftrightarrow> (\<forall>p. wf_history_local p (H p))"

lemma events_of_simp:
  "e \<in> events_of H \<longleftrightarrow> (\<exists>p. e \<in> set (H p))"
  by (auto simp: events_of_def)

section \<open>Program order and the happened-before relation\<close>

text \<open>Program order at process @{term p}: event @{term e} precedes
@{term e'} in @{term "H p"} iff @{term e} appears strictly earlier in the
list.\<close>

definition program_order :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "program_order H e e' \<longleftrightarrow>
     (\<exists>p i j. i < j \<and> j < length (H p) \<and> (H p) ! i = e \<and> (H p) ! j = e')"

text \<open>Message order: if @{term e} is a send recorded somewhere in the global
history and the matching receive @{term e'} is also recorded, then
\<open>e \<rightarrow> e'\<close> holds (Definition~1, rule~2 of the paper).\<close>

definition message_order :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "message_order H e e' \<longleftrightarrow>
     is_send e \<and> is_receive e' \<and> matches e e' \<and>
     e \<in> events_of H \<and> e' \<in> events_of H"

text \<open>The immediate happened-before step combines program-order and
message-order.  The full @{term hb} relation of Definition~1 is its
transitive closure (Rule~3, Transitive Order).\<close>

definition hb_step :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "hb_step H e e' \<longleftrightarrow> program_order H e e' \<or> message_order H e e'"

definition hb :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "hb H e e' \<longleftrightarrow> (hb_step H)\<^sup>+\<^sup>+ e e'"

text \<open>Boolean evaluation, matching the paper's \<open>e \<rightarrow> e'|_E\<close> notation
(Section~3).  By convention, if either endpoint is absent from the history
the evaluation is false (Definition~5, ``If \<open>e_h^x \<notin> T(E)\<close> then
\<open>e_h^x \<rightarrow> e_i^* |_E\<close> evaluates to false'').\<close>

definition hb_eval :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "hb_eval H e e' \<longleftrightarrow>
     (e \<in> events_of H \<and> e' \<in> events_of H \<and> hb H e e')"

section \<open>Causal past\<close>

text \<open>Definition~2: the causal past \<open>CP e\<close> is the set of events that
causally precede @{term e} under \<open>\<rightarrow>\<close>.\<close>

definition causal_past :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event set" where
  "causal_past H e = {e'. hb_eval H e' e}"

lemma causal_past_subset_events:
  "causal_past H e \<subseteq> events_of H"
  by (auto simp: causal_past_def hb_eval_def)

section \<open>Algorithm-perceived history\<close>

text \<open>Definition~5 distinguishes the \emph{actual} global history @{term E}
from the \emph{collected} history @{term F} as observed by the algorithm.
The paper notes that ``a single Byzantine process can cause @{term F}
\dots to be different from @{term E}.  This is not just a mismatch between
@{term "E p_b"} and @{term "F p_b"} at @{term p_b} but also at other
processes\dots''.  Consequently we do \emph{not} bake an
agreement-at-correct-processes constraint into admissibility; agreement at
correct processes is a property an algorithm \emph{achieves} (or fails to)
and is captured below as @{term correct_processes_agree}.\<close>

definition correct_processes_agree ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> 'p history \<Rightarrow> bool" where
  "correct_processes_agree C E F \<longleftrightarrow> (\<forall>p \<in> C. F p = E p)"

text \<open>An admissible pair @{term "(E, F)"} for a given partition: both
well-formed.  This is the weakest invariant; stronger constraints appear in
@{theory_text \<open>CD.thy\<close>} as part of @{term valid}.\<close>

definition admissible_pair ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> 'p history \<Rightarrow> bool" where
  "admissible_pair C E F \<longleftrightarrow> wf_history E \<and> wf_history F"

end
