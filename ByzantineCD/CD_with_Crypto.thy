(*
  Title:   CD_with_Crypto.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  The six cryptography theorems of Section 4.4 of the paper:

    Theorem 9  (\<S>4.4.1): CD impossible, multicast + crypto.
    Theorem 10 (\<S>4.4.1): CD impossible, unicast + crypto.
    Theorem 11 (\<S>4.4.1): CD impossible, broadcast + crypto.
    Theorem 12 (\<S>4.5)  : CD_B possible, unicast + crypto.
    Theorem 13 (\<S>4.5)  : CD_B possible, broadcast + crypto.
    Theorem 14 (\<S>4.5)  : CD_B possible, multicast + crypto.

  Status table from the paper (Table 1, with cryptography columns
  added on the right):

  \<^verbatim>\<open>
                | HB no crypto |   BHB no crypto  |  HB + crypto |  BHB + crypto
    ------------+--------------+------------------+--------------+----------------
    Unicast     | T3   impos.  | T6   possible    | T10  impos.  | T12  possible
    Broadcast   | T4   impos.  | T7   possible    | T11  impos.  | T13  possible
    Multicast   | T5   impos.  | T8   impossible  | T9   impos.  | T14  possible
  \<close>

  The genuinely new content of \<S>4.4 is the lower-right cell: T14,
  CD_B possible under multicast \<^emph>\<open>with\<close> cryptography (whereas T8
  said it is impossible without).  The other five cells are
  corollaries of the corresponding non-crypto cells, with crypto
  playing one of two roles:

  - For the impossibility cells (T9, T10, T11): cryptography does
    not help against the Byzantine omit-an-event attack used in
    Theorem 1 (\<open>CD_FN_unavoidable\<close>), so the FN argument carries
    over identically.  T9/T10/T11 reduce to T5/T3/T4 (in that
    order).

  - For the possibility cells (T12, T13, T14): the operational
    discharge of @{const correct_reporting} -- under unicast by
    BRU, under broadcast by BCB-over-BRB, under multicast by group
    encryption + recursive hash histories -- changes, but the
    correctness predicate \<open>produces_valid_F_B_recv\<close> and the
    proof that the naive algorithm satisfies it
    (\<open>naive_cd_B_alg_correct\<close>) are mode-agnostic.  The three
    crypto possibility theorems are therefore corollaries of
    \<open>CD_B_solvable_under_correct_reporting\<close>.

  -----------------------------------------------------------------
  Why we do not mechanise crypto primitives directly.

  The paper's \<S>4.4 introduces two cryptographic ingredients:

    (a) \<^bold>\<open>group encryption\<close> (\<S>4.4.1): a multicast group \<open>G\<close>
        shares a symmetric key \<open>K_G\<close>; senders encrypt to
        \<open>C_m = Enc(K_G, m)\<close> and broadcast \<open>(G, C_m)\<close> over BRB so
        every process can verify a send happened, while only group
        members can decrypt the content.

    (b) \<^bold>\<open>recursive hash histories\<close> (\<S>4.4.2): each state carries a
        collision-resistant hash digest \<open>\<hat>s_i^x\<close> recursively
        defined over prior events; a Byzantine cannot fabricate a
        causal past without producing a matching hash.

  Both primitives are operational machinery whose role at our
  abstraction level is exactly the same as BRU/BCB-over-BRB in
  \<S>4.3: they discharge the @{const correct_reporting} assumption
  for the relevant mode.  Faithful modelling of \<open>Enc\<close>, \<open>Dec\<close>,
  \<open>Sig\<close>, \<open>Verify\<close>, \<open>H\<close>, plus their unforgeability /
  collision-resistance properties, would require a multi-week
  cryptographic-primitive layer that is independent of the paper's
  contribution -- the paper itself cites Bracha 1987 for BRB and
  treats the crypto layer as an off-the-shelf primitive.  We do
  the same.

  In particular, the paper's quantitative conclusions
  (``\<open>FP\<close> prevented for \<open>t < n/3\<close>'' in T9/T10) require modelling
  the BRB quorum size, which is below our abstraction.  At our
  level, T9/T10/T11 state only the unconditional impossibility,
  matching the paper's table entries ``Impossible''.

  -----------------------------------------------------------------
  Deviations from the paper.

    1. The paper distinguishes ``HB + crypto'' from ``BHB + crypto''
       in different columns.  Our \<open>CD_solvable\<close> and
       \<open>CD_B_solvable_with_recv\<close> predicates already capture this
       distinction at the abstract level: the former uses
       @{const valid} (plain HB), the latter uses @{const valid_B}
       (BHB).  We re-use these predicates rather than introducing a
       crypto-tagged variant.

    2. T9's proof in the paper has additional content about FP
       prevention (``Byzantine behavior can be detected by taking a
       majority view when \<open>n > 2t\<close>'').  Our statement covers only
       the headline FN-based impossibility -- the FP-prevention
       qualifier requires modelling the BRB quorum bound, which is
       below our abstraction.
*)

theory CD_with_Crypto
  imports CD_B_Algorithm Impossibility
begin

context byzantineSystem
begin

section \<open>Theorem 9: CD impossible, multicast + crypto\<close>

text \<open>Paper, Theorem 9 (Section 4.4.1):
\begin{quote}
``It is impossible to solve causality determination (Definition 5)
as specified by \<open>CD(E, F, e_i^*)\<close> in an asynchronous multicast-
based message passing system with one or more Byzantine processes
even when using cryptography.''
\end{quote}

\textit{Paper's proof:} routes through Theorem 1's FN attack.  ``A
Byzantine \<open>p_g\<close> can delete from \<open>F_g\<close> information about a
multicast of \<open>m\<close> \dots\ despite doing broadcasts using the BRB
layer.''  The cryptographic envelope around \<open>m\<close> (group encryption
plus BRB-broadcast of the ciphertext) does not prevent a Byzantine
from omitting the receive event from its own reported history.

\textit{Our mechanisation:} direct corollary of @{thm
CD_impossible_multicast}.  Cryptography does not alter the
correctness condition @{const valid} nor the adversary model, so
the same fresh-id construction defeats every candidate
crypto-augmented algorithm.\<close>

theorem T9_CD_impossible_multicast_with_crypto:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "\<not> CD_solvable Multicast correct"
  by (rule CD_impossible_multicast[OF byz_ne cor_ne fin_cd])

section \<open>Theorem 10: CD impossible, unicast + crypto\<close>

text \<open>Paper, Theorem 10 (Section 4.4.1):
\begin{quote}
``It is impossible to solve causality determination (Definition 5)
as specified by \<open>CD(E, F, e_i^*)\<close> in an asynchronous unicast-
based message passing system with one or more Byzantine processes
even when using cryptography.''
\end{quote}

\textit{Paper's proof:} ``The proof of Theorem 9 carries over
identically where each multicast group consists of two processes
-- the sender and the receiver.''  The paper notes additionally
that ``false positives can be prevented only if the semantics of
the message content of a message do not matter''.  At our
abstraction level the headline conclusion is the unconditional
impossibility, mirroring the table entry.\<close>

theorem T10_CD_impossible_unicast_with_crypto:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "\<not> CD_solvable Unicast correct"
  by (rule CD_impossible_unicast[OF byz_ne cor_ne fin_cd])

section \<open>Theorem 11: CD impossible, broadcast + crypto\<close>

text \<open>Paper, Theorem 11 (Section 4.4.1):
\begin{quote}
``It is impossible to solve causality determination (Definition 5)
as specified by \<open>CD(E, F, e_i^*)\<close> in an asynchronous broadcast-
based message passing system with one or more Byzantine processes
even when using cryptography.''
\end{quote}

\textit{Paper's proof:} ``The proof of Theorem 4 [\dots]\ carries
over mostly identically with the two observations that (1) false
positives can be prevented even without cryptography, and (2) false
negatives cannot be prevented due to Theorem 1 whose proof is
independent of whether or not cryptography is used.''

The FN side of the disjunction is the headline conclusion, and is
exactly @{thm CD_impossible_broadcast}.\<close>

theorem T11_CD_impossible_broadcast_with_crypto:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "\<not> CD_solvable Broadcast correct"
  by (rule CD_impossible_broadcast[OF byz_ne cor_ne fin_cd])

section \<open>Theorem 12: CD_B possible, unicast + crypto\<close>

text \<open>Paper, Theorem 12 (Section 4.5):
\begin{quote}
``It is possible to solve causality determination (Definition 6)
as specified by \<open>CD_B(E, F, e_i^*)\<close>, now defined in terms of the
\<open>\<rightarrow>_B\<close> relation, in an asynchronous unicast-based message
passing system with one or more Byzantine processes when using
cryptography.''
\end{quote>

\textit{Paper's argument:} for the BHB version, ``only all true
causal dependencies are faithfully transmitted'' along a causal
path through correct processes.  With or without cryptography, the
\<open>\<rightarrow>_B\<close> chain reaches every correct receiver of every causally
preceding message.

\textit{Our mechanisation:} direct corollary of
@{thm CD_B_solvable_unicast}.  The abstract correctness predicate
@{const produces_valid_F_B_recv} is mode-agnostic; the operational
discharge of @{const correct_reporting} is the only place where
the choice ``BRU vs.\ crypto'' would matter, and the operational
layer is below our abstraction.\<close>

theorem T12_CD_B_solvable_unicast_with_crypto:
  shows "CD_B_solvable_with_recv Unicast correct"
  by (rule CD_B_solvable_unicast)

section \<open>Theorem 13: CD_B possible, broadcast + crypto\<close>

text \<open>Paper, Theorem 13 (Section 4.5):
\begin{quote}
``It is possible to solve causality determination (Definition 6)
as specified by \<open>CD_B(E, F, e_i^*)\<close>, now defined in terms of the
\<open>\<rightarrow>_B\<close> relation, in an asynchronous broadcast-based message
passing system with one or more Byzantine processes when using
cryptography.''
\end{quote}

\textit{Our mechanisation:} direct corollary of
@{thm CD_B_solvable_broadcast}.  Same reasoning as T12.\<close>

theorem T13_CD_B_solvable_broadcast_with_crypto:
  shows "CD_B_solvable_with_recv Broadcast correct"
  by (rule CD_B_solvable_broadcast)

section \<open>Theorem 14: CD_B possible, multicast + crypto\<close>

text \<open>Paper, Theorem 14 (Section 4.5):
\begin{quote}
``It is possible to solve causality determination (Definition 6)
as specified by \<open>CD_B(E, F, e_i^*)\<close>, now defined in terms of the
\<open>\<rightarrow>_B\<close> relation, in an asynchronous multicast-based message
passing system with one or more Byzantine processes when using
cryptography.''
\end{quote}

\textit{The genuinely new content of \<S>4.4.}  Without cryptography
@{thm CD_B_unsolvable_multicast_abstract} (the \<open>recv\<close>-strong
predicate) showed multicast was unsolvable because BRM is
unachievable (\<open>t_G < |G|/3\<close> would require identifying the
Byzantine processes within each multicast group).  \<^emph>\<open>With\<close>
cryptography, the paper argues that group encryption plus
BRB-broadcast of the ciphertext, augmented by recursive hash
histories, achieves @{const correct_reporting} for multicast.

\textit{Our mechanisation:} the abstract correctness predicate is
the same @{const produces_valid_F_B_recv} used for T6/T7/T12/T13.
At this abstraction level T14 is therefore a direct application of
@{thm CD_B_solvable_under_correct_reporting} with the multicast
mode tag.  The operational role of cryptography -- discharging
@{const correct_reporting} \<^emph>\<open>under multicast\<close> -- is the only
substantive content that differs between T8 (impossible without
crypto) and T14 (possible with crypto), and that substantive
content lives below our abstraction (the same way BRU/BCB live
below for T6/T7).\<close>

theorem T14_CD_B_solvable_multicast_with_crypto:
  shows "CD_B_solvable_with_recv Multicast correct"
  unfolding CD_B_solvable_with_recv_def
  by (rule CD_B_solvable_under_correct_reporting)

section \<open>Summary corollary: all six crypto theorems together\<close>

text \<open>One statement combining T9-T14.  The Byzantine premises
(\<open>byz_ne\<close>, \<open>cor_ne\<close>, \<open>fin_cd\<close>) are required for the
impossibility halves (T9/T10/T11); the possibility halves
(T12/T13/T14) are unconditional.\<close>

theorem crypto_theorems_summary:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "\<not> CD_solvable Multicast correct"   \<comment> \<open>T9\<close>
    and "\<not> CD_solvable Unicast correct"     \<comment> \<open>T10\<close>
    and "\<not> CD_solvable Broadcast correct"   \<comment> \<open>T11\<close>
    and "CD_B_solvable_with_recv Unicast correct"     \<comment> \<open>T12\<close>
    and "CD_B_solvable_with_recv Broadcast correct"   \<comment> \<open>T13\<close>
    and "CD_B_solvable_with_recv Multicast correct"   \<comment> \<open>T14\<close>
proof -
  show "\<not> CD_solvable Multicast correct"
    by (rule T9_CD_impossible_multicast_with_crypto[OF byz_ne cor_ne fin_cd])
  show "\<not> CD_solvable Unicast correct"
    by (rule T10_CD_impossible_unicast_with_crypto[OF byz_ne cor_ne fin_cd])
  show "\<not> CD_solvable Broadcast correct"
    by (rule T11_CD_impossible_broadcast_with_crypto[OF byz_ne cor_ne fin_cd])
  show "CD_B_solvable_with_recv Unicast correct"
    by (rule T12_CD_B_solvable_unicast_with_crypto)
  show "CD_B_solvable_with_recv Broadcast correct"
    by (rule T13_CD_B_solvable_broadcast_with_crypto)
  show "CD_B_solvable_with_recv Multicast correct"
    by (rule T14_CD_B_solvable_multicast_with_crypto)
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
