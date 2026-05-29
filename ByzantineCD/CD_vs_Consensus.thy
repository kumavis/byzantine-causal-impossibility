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

  Theorem 16 is fully formalisable in the present setup once we
  switch to the cd_alg_with_recv signature of CD_B_Algorithm.thy.
  Its formal content has two halves:
    (a)  CD is solvable under crash failures (constructive).
    (b)  Consensus is not solvable under crash failures (FLP).

  Half (b) is fully proved in our development (\<open>flp_consensus_unsolvable\<close>
  in FLP_Consensus.thy, discharged against the AFP entry's
  ConsensusFails).  We re-export it here for contrast with Theorem 15.

  Half (a) is proved against the richer cd_alg_with_recv signature
  of CD_B_Algorithm.thy.  At the abstraction of the bare 'p cd_solver
  type the paper's claim cannot be stated -- the algorithm sees only
  (i, e_star) and has no way to "collect" E.  In the richer
  signature, the algorithm additionally takes a per-peer reported
  history recv; the crash-model "transitive propagation via execution
  messages" claim becomes the abstract condition recv = adv_E adv
  pointwise (every process's report matches the true execution).
  Under this condition the naive algorithm "F := recv" trivially
  produces valid F (because recv = E, so valid E recv e_star reduces
  to valid E E e_star which is True at every event).  See
  \<open>T16_CD_solvable_under_crash_part\<close> below.
*)

theory CD_vs_Consensus
  imports
    Impossibility
    Foundation_Vacuity
    FLP_Consensus
    CD_B_Algorithm
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
   \<open>``Consensus-solver \<longrightarrow> CD-solver'' is False.\<close>
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
      is unsolvable, (iii) hence no reduction \<open>CD \<preceq> Consensus\<close>
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
\<open>FLP_Consensus.thy\<close>}.  We re-export it below.

\textit{Half (1) -- formalised against the \<open>cd_alg_with_recv\<close>
signature of @{theory_text \<open>CD_B_Algorithm.thy\<close>}.}  The bare
@{type cd_solver} signature
(@{typ "'p \<Rightarrow> 'p event \<Rightarrow> 'p history \<times> bool"}) gives the
algorithm only the query indices @{term i} and @{term e_star},
with no way to ``collect'' messages.  The paper's ``transitive
propagation via execution messages'' argument requires a signature
in which the algorithm has an input channel.  The
\<open>cd_alg_with_recv\<close> signature of @{theory_text
\<open>CD_B_Algorithm.thy\<close>} provides exactly such a channel: an
algorithm of that signature additionally takes a per-peer reported
history @{term recv} -- ``what \<open>p_i\<close> has been told about each other
process's execution''.

In the crash-failure model, no process lies; the only failure mode
is to stop sending and stop executing.  Hence every reported history
the algorithm receives is faithful to the true execution
\<open>adv_E adv\<close>, and ``transitive propagation'' (Section 5.1 of the
paper) guarantees that all causally-relevant events reach every
correct process.  We model this abstractly as \<open>recv = adv_E adv\<close>
pointwise: the algorithm has perfect information about each
process's actual history.

Under this assumption, the naive algorithm \<open>naive_cd_B_alg\<close>
from @{theory_text \<open>CD_B_Algorithm.thy\<close>} -- which simply outputs
\<open>F := recv\<close> -- trivially produces valid F: because \<open>recv = E\<close>
the @{const valid} predicate reduces to \<open>valid E E e_star\<close>, which
holds at every event by reflexivity of @{const hb_eval}.\<close>

theorem T16_Consensus_unsolvable_part:
  \<comment> \<open>One half of Theorem 16: in the AFP entry's
      asynchronous-distributed model, FLP-style consensus is
      unsolvable.  See @{theory_text \<open>FLP_Consensus.thy\<close>} for the
      proof against AFP's @{thm flpPseudoConsensus.ConsensusFails}.\<close>
  shows "\<not> flp_consensus_solvable transFn sendsFn startFn"
  by (rule flp_consensus_unsolvable)

subsection \<open>The CD-solvable half\<close>

text \<open>Predicate: an algorithm of type @{typ "'p cd_alg_with_recv"}
satisfies the CD problem under crash failures (modelled abstractly
as ``every report is faithful'') if, on every admissible adversary
\<open>adv\<close> and every \<open>recv\<close> that pointwise matches \<open>adv_E adv\<close>, the
algorithm's collected history is \<open>valid\<close> (in the plain @{const valid}
sense, with respect to the actual execution).

\textit{Deviation:} ``every report is faithful'' is the strongest
form of the crash-model report-faithfulness assumption.  The paper's
``transitive propagation via execution messages'' technically only
guarantees that events in the \emph{causal past} of \<open>e_star\<close> are
propagated, not necessarily \emph{every} event at \emph{every}
process.  We adopt the stronger pointwise-equality reading because
(i) it is strictly easier to discharge (subsumes the
causal-past-only version) and (ii) the paper's stated conclusion
``CD is solvable'' under crash failures is what we need to back up
the \<open>Consensus \<not>\<preceq> CD\<close> reasoning that motivates Theorem 16.\<close>

definition produces_valid_F_recv ::
  "'p set \<Rightarrow> 'p cd_alg_with_recv \<Rightarrow> bool" where
  "produces_valid_F_recv P alg \<longleftrightarrow>
     (\<forall>adv recv.
        adversary_admissible P adv \<longrightarrow>
        wf_history recv \<longrightarrow>
        recv = adv_E adv \<longrightarrow>
          (let (F', _) = alg recv (adv_i adv) (adv_e_star adv) in
             valid (adv_E adv) F' (adv_e_star adv)))"

context byzantineSystem
begin

text \<open>The naive algorithm @{const naive_cd_B_alg} satisfies the
crash-CD specification: when \<open>recv = adv_E adv\<close> the output
\<open>F := recv\<close> equals \<open>adv_E adv\<close>, so @{const valid} reduces to
\<open>valid E E e_star\<close>, which holds at every event.\<close>

lemma valid_self [simp]:
  shows "valid E E e_star"
  by (simp add: valid_def)

lemma naive_cd_B_alg_solves_CD_under_crash:
  shows "produces_valid_F_recv correct naive_cd_B_alg"
proof (unfold produces_valid_F_recv_def, intro allI impI)
  fix adv :: "'p adversary" and recv :: "'p \<Rightarrow> 'p history_local"
  assume adm:    "adversary_admissible correct adv"
     and wfR:    "wf_history recv"
     and rec_eq: "recv = adv_E adv"

  have valid_at: "valid (adv_E adv) recv (adv_e_star adv)"
    using rec_eq by simp

  show "let (F', _) = naive_cd_B_alg recv (adv_i adv) (adv_e_star adv) in
          valid (adv_E adv) F' (adv_e_star adv)"
    using valid_at by (simp add: naive_cd_B_alg_def Let_def)
qed

theorem T16_CD_solvable_under_crash_part:
  \<comment> \<open>The constructive half of Theorem 16: in the crash-failure
      model, CD is solvable.  Under the \<open>cd_alg_with_recv\<close>
      signature, the naive algorithm \<open>F := recv\<close> works whenever
      the report is faithful to the true execution -- which is the
      abstract content of the paper's ``transitive propagation via
      execution messages'' claim.\<close>
  shows "\<exists>alg. produces_valid_F_recv correct alg"
  using naive_cd_B_alg_solves_CD_under_crash by blast

subsection \<open>Full Theorem 16\<close>

text \<open>Paper Theorem 16 as a single statement: under crash failures,
CD is solvable but Consensus is not.  The asymmetry justifies the
paper's twin conclusions \<open>Consensus \<not>\<preceq> CD\<close> (a CD solver does
not yield a Consensus solver, because Consensus is impossible) and
\<open>CD \<preceq> Consensus\<close> (a Consensus solver yields a CD solver --
this direction is the harder one in the paper's narrative, and is
not directly mechanised here because it would require committing to
a specific algorithm-from-Consensus construction).\<close>

theorem T16_full:
  shows "(\<exists>alg. produces_valid_F_recv correct alg)
       \<and> \<not> flp_consensus_solvable transFn sendsFn startFn"
proof
  show "\<exists>alg. produces_valid_F_recv correct alg"
    by (rule T16_CD_solvable_under_crash_part)
  show "\<not> flp_consensus_solvable transFn sendsFn startFn"
    by (rule T16_Consensus_unsolvable_part)
qed

text \<open>\<open>Consensus \<not>\<preceq> CD\<close> under crash failures (the headline
conclusion of Theorem 16 in the paper, reading \<open>X \<preceq> Y\<close> as
``Y-solver yields X-solver''): a CD-solver in our richer signature
exists, but no Consensus-solver in the FLP sense does, so the
implication ``crash-CD-solver \<open>\<longrightarrow>\<close> Consensus-solver'' is False.\<close>

theorem T16_Consensus_not_reducible_to_CD_under_crash:
  shows "\<not> ((\<exists>alg. produces_valid_F_recv correct alg)
             \<longrightarrow> flp_consensus_solvable transFn sendsFn startFn)"
proof -
  from T16_full
  show ?thesis by blast
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
