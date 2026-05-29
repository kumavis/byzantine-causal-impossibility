(*
  Title:   Events.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  Events, per-process execution histories E_i, global history E, the
  algorithm-perceived history F, and the happened-before relation
  evaluated against either history.

  Paper coverage:
    - Definition 1 (happened-before "->"), Section 2.
    - Definition 2 (causal past CP(e)), Section 2.
    - The E, F, T(E), T(F) bookkeeping of Section 3.

  Deviations from the paper (deliberate; all are simplifications that
  do not weaken the impossibility chain):

    1. Events are records of (process, sequence_number) plus a tag,
       not literal symbols.  The paper writes "e_i^x"; we write
       Internal p n, Send p n q m, Receive p n q m.  Each event
       carries its proc_of and seq_of selectors.

    2. The paper's "alternating events and states <s_i^0, e_i^1,
       s_i^1, ...>" is collapsed: we store only the event list at
       each process.  States are implicit; the impossibility proofs
       never need to inspect them.

    3. Both program_order and message_order are defined uniformly
       over all processes (correct and Byzantine alike) -- matching
       Definition 1, which states the rules without reference to the
       failure model.  The paper's Byzantine happened-before relation
       (Definition 3), which restricts to correct processes, is not
       formalised in this development (intended for future work on
       Theorems 6-8).

    4. The paper's FIFO-channel assumption (Section 2: "C is the set
       of FIFO (logical) communication links") is not enforced
       here.  None of the impossibility proofs we mechanise need
       FIFO; lifting to allow non-FIFO only strengthens the
       impossibility results.
*)

theory Events
  imports ByzantineSystem
begin

section \<open>Events\<close>

text \<open>The paper writes \<open>e_i^x\<close> for the \<open>x\<close>-th event of process
\<open>p_i\<close> (Section 2: ``Let \<open>e_i^x\<close>, where \<open>x \<ge> 1\<close>, denote the
\<open>x\<close>th event executed by process \<open>p_i\<close>'').  We represent this as a
tagged record carrying both the process \<open>p\<close> and the local sequence
number \<open>n\<close>, plus -- for sends and receives -- the peer process and
a message identifier that links the matching send and receive.\<close>

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

text \<open>A send and the corresponding receive of the same message are
identified by a shared \<open>msg_id\<close>.  The \<open>matches\<close> predicate also
checks that the peer fields are dual (the send's \<open>peer\<close> is the
receiver, the receive's \<open>peer\<close> is the sender).

\textit{Deviation:} the paper does not bother to give \<open>matches\<close>
a separate name; it is implicit in ``the corresponding message
receive event'' (Definition 1).  We name it because Isabelle's
inductive happened-before definition needs it as a predicate.\<close>

fun matches :: "'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "matches (Send p n q m) (Receive q' n' p' m') \<longleftrightarrow> (p = p' \<and> q = q' \<and> m = m')"
| "matches _ _ \<longleftrightarrow> False"

section \<open>Per-process and global histories\<close>

text \<open>Section 2 of the paper: ``The execution history at \<open>p_i\<close>
is the finite execution at \<open>p_i\<close> up to the current or most
recent or specified local state.''  Section 3: ``Let \<open>E_i\<close>
denote the actual execution history at \<open>p_i\<close> \dots\ and let
\<open>E = \<Union>_i {E_i}\<close>.''  We represent both \<open>E_i\<close> (per process) and
\<open>E\<close> (global) by a single mapping @{typ "'p \<Rightarrow> 'p event list"}:
the per-process history is recovered by applying the mapping to a
process, and the set of all events \<open>T(E)\<close> is given by
\<open>events_of\<close> below.\<close>

type_synonym 'p history_local = "'p event list"
type_synonym 'p history       = "'p \<Rightarrow> 'p history_local"

text \<open>\<open>T(E)\<close> in the paper: the set of all events occurring in
\<open>E\<close>, taken process-by-process and unioned.\<close>

definition events_of :: "'p history \<Rightarrow> 'p event set" where
  "events_of H = (\<Union>p. set (H p))"

text \<open>Well-formedness of a history: each per-process list
(a) records only events whose \<open>proc_of\<close> field is that process,
and (b) numbers its events 1, 2, 3, \dots\ consecutively, matching
the paper's enumeration \<open>\<langle>e_i^1, e_i^2, \<dots>\<rangle>\<close>.\<close>

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

text \<open>Definition 1, rule 1 (Section 2):
\begin{quote}
``Program Order: For the sequence of events \<open>\<langle>e_i^1, e_i^2, \<dots>\<rangle>\<close>
executed by process \<open>p_i\<close>, \<open>\<forall> x, y\<close> such that \<open>x < y\<close> we have
\<open>e_i^x \<rightarrow> e_i^y\<close>.''
\end{quote}
We mechanise this as: \<open>e\<close> precedes \<open>e'\<close> in \<open>H p\<close> iff \<open>e\<close> appears
at a strictly earlier list index than \<open>e'\<close> in the same per-process
list.\<close>

definition program_order :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "program_order H e e' \<longleftrightarrow>
     (\<exists>p i j. i < j \<and> j < length (H p) \<and> (H p) ! i = e \<and> (H p) ! j = e')"

text \<open>Definition 1, rule 2 (Section 2):
\begin{quote}
``Message Order: If event \<open>e_i^x\<close> is a message send event executed
at process \<open>p_i\<close> and \<open>e_j^y\<close> is the corresponding message receive
event at process \<open>p_j\<close>, then \<open>e_i^x \<rightarrow> e_j^y\<close>.''
\end{quote}
Our \<open>message_order\<close> fires when the send and receive are
matched by @{const matches} (same peer, same message id) and both
events are recorded in the history.

\textit{Deviation:} the paper takes for granted that the send-receive
pair really happened; we make this explicit by requiring both
endpoints to be in @{term "events_of H"}.  For the algorithm-collected
history \<open>F\<close> this is the right reading -- if either endpoint is not
in \<open>F\<close>, then ``the algorithm doesn't know about it'', and this is
how the paper itself reasons when discussing false negatives
(``Byzantine processes may delete information about \<open>e_h^x\<close> and \<open>m\<close>
from \<open>F_h\<close>, leading to a false negative'', Section 4.2).\<close>

definition message_order :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "message_order H e e' \<longleftrightarrow>
     is_send e \<and> is_receive e' \<and> matches e e' \<and>
     e \<in> events_of H \<and> e' \<in> events_of H"

text \<open>One step of the happened-before relation: either a
program-order step or a message-order step.\<close>

definition hb_step :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "hb_step H e e' \<longleftrightarrow> program_order H e e' \<or> message_order H e e'"

text \<open>Definition 1, rule 3 (Section 2):
\begin{quote}
``Transitive Order: If \<open>e \<rightarrow> e' \<and> e' \<rightarrow> e''\<close> then \<open>e \<rightarrow> e''\<close>.''
\end{quote}
We define \<open>hb\<close> as the transitive closure of @{const hb_step}.
This is the standard Lamport happened-before relation, evaluated
against an arbitrary history @{term H}.

\textit{Note:} the paper's Definition 3 is the
Byzantine-happened-before relation \<open>\<rightarrow>_B\<close> that restricts both
program order and message order to correct-process chains.  We do
not formalise \<open>\<rightarrow>_B\<close> in this development -- the impossibility
theorems we cover (T1-T5) work on the plain \<open>\<rightarrow>\<close>.  The @{const Send}
and @{const Receive} constructors carry the peer field precisely so
that a future development of Theorems 6-8 can define \<open>\<rightarrow>_B\<close> by an
inductive predicate quantifying over a correct set.\<close>

definition hb :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "hb H e e' \<longleftrightarrow> (hb_step H)\<^sup>+\<^sup>+ e e'"

text \<open>The paper's \<open>e \<rightarrow> e'|_E\<close> notation (Section 3):
\begin{quote}
``Let \<open>e_1 \<rightarrow> e_2 |_E\<close> and \<open>e_1 \<rightarrow> e_2 |_F\<close> be the evaluation
(1 or 0) of \<open>e_1 \<rightarrow> e_2\<close> using \<open>E\<close> and \<open>F\<close>, respectively. \dots\
If \<open>e_h^x \<notin> T(E)\<close> then \<open>e_h^x \<rightarrow> e_i^*|_E\<close> evaluates to false; \dots\
If \<open>e_h^x \<notin> T(F)\<close> (or \<open>e_i^* \<notin> T(F)\<close>) then \<open>e_h^x \<rightarrow> e_i^*|_F\<close>
evaluates to false.''
\end{quote}
We mechanise this via a boolean \<open>hb_eval\<close> that requires both
endpoints to be in @{term "events_of H"} before consulting the
transitive closure.\<close>

definition hb_eval :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event \<Rightarrow> bool" where
  "hb_eval H e e' \<longleftrightarrow>
     (e \<in> events_of H \<and> e' \<in> events_of H \<and> hb H e e')"

section \<open>Causal past\<close>

text \<open>Definition 2 (Section 2): ``The causal past of an event \<open>e\<close>
is denoted as \<open>CP(e)\<close> and defined as the set of events that
causally precede \<open>e\<close> under \<open>\<rightarrow>\<close>.''  We parameterise the
definition by the history @{term H} against which the relation is
evaluated -- the paper writes simply \<open>CP(e)\<close> because in Section 2
only the actual history \<open>E\<close> is in play.\<close>

definition causal_past :: "'p history \<Rightarrow> 'p event \<Rightarrow> 'p event set" where
  "causal_past H e = {e'. hb_eval H e' e}"

lemma causal_past_subset_events:
  "causal_past H e \<subseteq> events_of H"
  by (auto simp: causal_past_def hb_eval_def)

section \<open>Algorithm-perceived history\<close>

text \<open>Section 3 of the paper distinguishes the actual global history
\<open>E\<close> from the algorithm-collected history \<open>F\<close>:
\begin{quote}
``For any causality determination algorithm, let \<open>F_i\<close> be the
execution history at \<open>p_i\<close> as perceived and collected by the
algorithm and let \<open>F = \<Union>_i {F_i}\<close>. \dots\  Byzantine processes
may corrupt the collection of \<open>F\<close> to make it different from \<open>E\<close>.
\dots\  Therefore it is not sufficient for the correct processes
to agree mutually on a \<open>F\<close> that differs from \<open>E\<close> in what happened
in \<open>E\<close> at the Byzantine processes; their \<open>F_j\<close> must also agree
with \<open>E_j\<close> at all processes \<open>p_j\<close>.''
\end{quote}

\<open>correct_processes_agree\<close> below is the property an algorithm
\emph{would} like to achieve at correct processes.  Crucially, we do
\emph{not} bake it into admissibility: a Byzantine adversary can
cause \<open>F\<close> to disagree with \<open>E\<close> even at correct processes
(via contamination), so the impossibility argument needs to keep
this as a separate property an algorithm might fail.\<close>

definition correct_processes_agree ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> 'p history \<Rightarrow> bool" where
  "correct_processes_agree C E F \<longleftrightarrow> (\<forall>p \<in> C. F p = E p)"

text \<open>An admissible pair \<open>(E, F)\<close>: both are well-formed histories.
This is the weakest invariant we need; stronger constraints
(the formal CD problem itself) appear in \<open>CD.thy\<close> via
\<open>valid\<close>.\<close>

definition admissible_pair ::
  "'p set \<Rightarrow> 'p history \<Rightarrow> 'p history \<Rightarrow> bool" where
  "admissible_pair C E F \<longleftrightarrow> wf_history E \<and> wf_history F"

end
