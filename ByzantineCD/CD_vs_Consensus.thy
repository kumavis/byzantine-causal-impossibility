(*
  Title:   CD_vs_Consensus.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  Theorems 15 and 16 of the paper (Section 5.1, "Relationship to
  consensus") -- auxiliary results placing CD's hardness against
  Consensus across the two failure models the paper considers.

  Theorem 15 (paper, Section 5.1): "In an asynchronous system with
    Byzantine failures, CD \<not>\<preceq> Consensus and the CD problem is
    harder than Consensus."

  Theorem 16 (paper, Section 5.1): "In an asynchronous system with
    crash failures, CD is solvable but Consensus is not solvable;
    thus Consensus \<not>\<preceq> CD and CD \<preceq> Consensus."

  ----------------------------------------------------------------
  What we formalise

  Theorem 15 fits cleanly into the existing setup.  Its formal content
  is: a hypothetical reduction CD \<preceq> Consensus (a Consensus
  solver yields a CD solver) is logically impossible in our model,
  because CD is unsolvable (proved as part of Theorem 3 via
  CD_FN_unavoidable) but the abstract predicate solves_Consensus
  admits an HOL witness (simple_alg in Foundation_Vacuity.thy).  The
  conjunction "CD unsolvable AND Consensus abstractly solvable"
  directly refutes the implication "Consensus solver \<longrightarrow> CD solver".

  Theorem 16 is only partially formalisable in the present setup.
  Its formal content has two halves:
    (a)  CD is solvable under crash failures.
    (b)  Consensus is not solvable under crash failures (FLP).

  Half (b) is fully proved in our development (\<open>flp_consensus_unsolvable\<close>
  in FLP_Consensus.thy, discharged against the AFP entry's
  ConsensusFails).  We re-export it here for contrast with Theorem 15.

  Half (a) requires a crash-failure model in which the CD-solver can
  *collect* the execution history E -- which in turn requires modelling
  messages and communication.  Our abstract 'p cd_solver is a HOL
  function over (i, e_star), with no notion of in-transit messages or
  collected E; the paper's proof of (a) ("crashed processes'
  execution histories propagate transitively via messages") therefore
  cannot be carried out at this abstraction level.  A faithful
  mechanisation of (a) would commute the asynchronous-system locale
  of the AFP FLP entry with our adversary model -- a substantial
  follow-on rather than a small corollary.

  We state half (b) below and document half (a) as deliberately
  out of scope.
*)

theory CD_vs_Consensus
  imports Impossibility Foundation_Vacuity FLP_Consensus
begin

section \<open>Theorem 15: in a Byzantine setting, CD is harder than Consensus\<close>

text \<open>Paper, Section 5.1:
\begin{quote}
``Theorem 15. In an asynchronous system with Byzantine failures,
\<open>CD \<not>\<preceq> Consensus\<close> and the CD problem is harder than Consensus.''
\end{quote}

The paper's proof first exhibits an oracle (process-identification)
that is sufficient to solve Consensus, then revisits Theorem 1 to
argue that even with that oracle CD still admits false negatives.
Hence ``Consensus-solvability does not imply CD-solvability''.

\textit{Our formalisation.}  At the abstraction level of this
development, the abstract predicate @{const solves_Consensus} is
trivially satisfiable by a pure-HOL function (see
@{thm exists_consensus_alg} in @{theory_text \<open>Foundation_Vacuity.thy\<close>},
a regression diagnostic that retains the witness).  CD on the other
hand is unsolvable by Theorem 1.  Conjoining these two facts already
gives the formal content of Theorem 15:

\begin{quote}
   \<open>solves_Consensus\<close>-witness exists, but no
   \<open>produces_valid_F\<close>-witness does, so the reduction
   ``Consensus-solver \<longrightarrow> CD-solver'' is False.
\end{quote}

A note on idiom.  The paper uses the formal symbol \<open>\<preceq>\<close> for the
``reduces to'' relation: \<open>X \<preceq> Y\<close> means ``a Y-solver yields an
X-solver''.  Under that reading, \<open>CD \<preceq> Consensus\<close>
unfolds to ``every Consensus-solver yields some CD-solver''.  In
HOL: \<open>(\<exists> a. solves_Consensus correct a) \<longrightarrow> (\<exists> a. produces_valid_F correct a)\<close>.
Theorem 15 negates that.\<close>

context byzantineSystem
begin

theorem CD_unsolvable_but_Consensus_solvable:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "(\<exists>cons_alg. solves_Consensus correct cons_alg)
       \<and> \<not> (\<exists>cd_alg. produces_valid_F correct cd_alg)"
proof
  show "\<exists>cons_alg. solves_Consensus correct cons_alg"
    by (rule exists_consensus_alg)
  show "\<not> (\<exists>cd_alg. produces_valid_F correct cd_alg)"
    by (rule no_produces_valid_F[OF byz_ne cor_ne fin_cd])
qed

theorem CD_not_reducible_to_Consensus:
  \<comment> \<open>Paper's ``\<open>CD \<not>\<preceq> Consensus\<close>'' in Byzantine setting.
      Reading \<open>X \<preceq> Y\<close> as ``Y-solver yields X-solver'',
      \<open>CD \<preceq> Consensus\<close> would be
      \<open>(\<exists>a. solves_Consensus correct a) \<longrightarrow> (\<exists>a. produces_valid_F correct a)\<close>;
      we negate that.\<close>
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "\<not> ((\<exists>cons_alg. solves_Consensus correct cons_alg) \<longrightarrow>
            (\<exists>cd_alg. produces_valid_F correct cd_alg))"
proof -
  from CD_unsolvable_but_Consensus_solvable[OF byz_ne cor_ne fin_cd]
  show ?thesis by blast
qed

theorem CD_harder_than_Consensus:
  \<comment> \<open>Paper's headline conclusion of Theorem 15: ``the CD problem
      is harder than Consensus''.  In our setting this is the
      conjunction of (i) Consensus is abstractly solvable, (ii) CD
      is unsolvable, (iii) hence no reduction CD \<preceq> Consensus
      exists.\<close>
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_cd:
        "\<forall>cd_alg. produces_valid_F correct cd_alg \<longrightarrow>
           (\<forall>p_i_in. finite (events_of
                              (fst (cd_alg p_i_in (Internal p_i_in 2)))))"
  shows "(\<exists>cons_alg. solves_Consensus correct cons_alg)
       \<and> \<not> (\<exists>cd_alg. produces_valid_F correct cd_alg)
       \<and> \<not> ((\<exists>cons_alg. solves_Consensus correct cons_alg)
              \<longrightarrow> (\<exists>cd_alg. produces_valid_F correct cd_alg))"
  using CD_unsolvable_but_Consensus_solvable[OF byz_ne cor_ne fin_cd]
        CD_not_reducible_to_Consensus[OF byz_ne cor_ne fin_cd]
  by blast

end \<comment> \<open>context @{locale byzantineSystem}\<close>

section \<open>Theorem 16: in a crash-failure setting, Consensus is harder than CD\<close>

text \<open>Paper, Section 5.1:
\begin{quote}
``Theorem 16. In an asynchronous system with crash failures, CD
is solvable but Consensus is not solvable; thus \<open>Consensus
\<not>\<preceq> CD\<close> and \<open>CD \<preceq> Consensus\<close>.''
\end{quote}

The paper's proof has two parts:
\begin{enumerate}
  \item ``To solve CD does not require identifying the crashed
        processes; their (correct) execution histories can be
        faithfully transmitted to other processes (transitively)
        via the execution messages \dots'' -- i.e., CD is solvable
        in the crash-failure model.
  \item ``Solving Consensus in the crash failure model is impossible
        by the FLP impossibility result.''
\end{enumerate}

\textit{Half (2) -- formalised.}  The FLP impossibility on the
asynchronous-distributed model of the AFP entry is the proven
theorem @{thm flp_consensus_unsolvable} in @{theory_text
\<open>FLP_Consensus.thy\<close>}.  We re-export it below as the partial
formalisation of Theorem 16.

\textit{Half (1) -- deliberately out of scope.}  Our abstract
@{type cd_solver} signature is @{typ "'p \<Rightarrow> 'p event \<Rightarrow> 'p history \<times> bool"};
the algorithm sees only the query indices @{term i} and @{term
e_star}, not any messages or in-transit history.  The paper's proof
of half (1) constructs the CD-solver by ``transitive propagation
via execution messages'', which requires a model with explicit
messages and a notion of `which messages are in transit at a given
configuration'.  The AFP FLP entry provides such a model
(@{theory \<open>FLP.AsynchronousSystem\<close>}), but commuting it with our
adversary model is a substantial follow-on rather than a small
corollary.  A faithful formalisation of half (1) is therefore left
as future work.

The full ``Consensus is harder than CD'' conclusion (and the
\<open>Consensus \<not>\<preceq> CD\<close>, \<open>CD \<preceq> Consensus\<close> derivations
of the paper) ultimately depends on half (1) as well, so the
overall Theorem 16 is reported here as partially-formalised.\<close>

theorem T16_Consensus_unsolvable_part:
  \<comment> \<open>The proved half of Theorem 16: in the AFP entry's
      asynchronous-distributed model, FLP-style consensus is
      unsolvable.  See @{theory_text \<open>FLP_Consensus.thy\<close>} for the
      proof against AFP's @{thm flpPseudoConsensus.ConsensusFails}.\<close>
  shows "\<not> flp_consensus_solvable transFn sendsFn startFn"
  by (rule flp_consensus_unsolvable)

end
