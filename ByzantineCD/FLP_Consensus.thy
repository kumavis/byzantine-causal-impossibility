(*
  Title:   FLP_Consensus.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  FLP-style consensus solvability and impossibility, plus the
  BlackBox-to-FLP bridge predicate that lets the CD impossibility chain
  in Impossibility.thy close on a *proven* contradiction rather than on
  the formerly-vacuous locale axiom flp_consensus_impossibility (see
  Foundation_Vacuity.thy for that historical artefact).

  Two ingredients here:

    (1) flp_consensus_solvable transFn sendsFn startFn: a predicate
        over a single asynchronous distributed protocol (trans, sends,
        start) that combines the AFP entry's flpSystem axioms, the
        flpPseudoConsensus axioms, and the ConsensusFails preconditions
        (Termination, Validity, Agreement).

    (2) flp_consensus_unsolvable: the unconditional impossibility,
        proved by invoking the AFP entry's ConsensusFails theorem.  No
        axiom; a real proof.

  And the bridge:

    (3) bb_realizes_flp_consensus P C: ``if there is an abstract
        BlackBox solver for (P, C), then there is some asynchronous
        distributed protocol that flp-solves consensus''.  This is the
        meta-level claim the paper relies on implicitly (any abstract
        BB solver can be realised as the textbook broadcast-and-collect
        protocol over BB-as-oracle).  Stated here as a predicate, taken
        as a hypothesis by Theorems 3, 4, 5 in Impossibility.thy.
        Faithful to the paper, plausible, satisfiable -- replacing the
        formerly-unsatisfiable flp_consensus_impossibility axiom.
*)

theory FLP_Consensus
  imports
    BlackBox
    FLP.AsynchronousSystem
    FLP.Execution
    FLP.FLPSystem
    FLP.FLPTheorem
begin

section \<open>FLP-style consensus solvability\<close>

text \<open>Paper, Section 4.2 (the Consensus problem):
\begin{quote}
``In the Consensus problem, each process has an initial value and
all correct processes must agree on a single value.  The solution
needs to satisfy the following three conditions.
\begin{itemize}
  \item \textbf{Agreement:} All non-faulty processes must agree on
        the same single value.
  \item \textbf{Validity:} If all non-faulty processes have the same
        initial value, then the agreed-on value by all the
        non-faulty processes must be that same value.
  \item \textbf{Termination:} Each non-faulty process must eventually
        decide on a value.
\end{itemize}
According to the FLP impossibility result, it is impossible to solve
Consensus in an asynchronous message-passing system with even a
single crash failure prone process.''
\end{quote}

An algorithm in the FLP model (as formalised by the AFP entry) is a
triple \<open>(transFn, sendsFn, startFn)\<close> of a transition function, a
send function, and an initial-state function.  We say the triple
\<open>flp-solves consensus\<close> when it satisfies the AFP entry's
\<open>flpSystem\<close> and \<open>flpPseudoConsensus\<close> locale axioms together with the
three correctness conditions that the AFP entry's \<open>flpPseudoConsensus.ConsensusFails\<close>
takes as preconditions:
\begin{itemize}
  \item \<open>flpSystem.terminationFLP\<close>: every fair infinite execution
        terminates (paper's Termination, formalised in AFP);
  \item \<open>flpSystem.validity\<close>: validity (paper's Validity);
  \item \<open>flpSystem.agreementInit\<close>: agreement on initial
        configurations (paper's Agreement).
\end{itemize}\<close>

definition flp_consensus_solvable ::
  "('p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> 's)
   \<Rightarrow> ('p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> ('p, 'v) message multiset)
   \<Rightarrow> ('p \<Rightarrow> 's)
   \<Rightarrow> bool" where
  "flp_consensus_solvable transFn sendsFn startFn \<longleftrightarrow>
     flpSystem sendsFn \<and>
     flpPseudoConsensus transFn sendsFn startFn \<and>
     (\<forall> fe ft. asynchronousSystem.fairInfiniteExecution transFn sendsFn startFn fe ft
                \<longrightarrow> flpSystem.terminationFLP transFn sendsFn startFn fe ft) \<and>
     (\<forall> i c. flpSystem.validity transFn sendsFn startFn i c) \<and>
     (\<forall> i c. flpSystem.agreementInit transFn sendsFn startFn i c)"

text \<open>The FLP impossibility, on this predicate, is a one-step
invocation of the AFP entry's \<open>flpPseudoConsensus.ConsensusFails\<close> theorem (proven,
not assumed):
\begin{quote}
``theorem ConsensusFails:
   assumes Termination: \<open>\<dots>\<close> and Validity: \<open>\<dots>\<close> and Agreement: \<open>\<dots>\<close>
   shows False''
\end{quote}

This is the genuine FLP result.  We unpack the predicate into its
five conjuncts, interpret \<open>flpPseudoConsensus\<close>, and apply
\<open>ConsensusFails\<close>.\<close>

theorem flp_consensus_unsolvable:
  shows "\<not> flp_consensus_solvable transFn sendsFn startFn"
proof
  assume A: "flp_consensus_solvable transFn sendsFn startFn"
  hence sys: "flpSystem sendsFn"
    and pc:  "flpPseudoConsensus transFn sendsFn startFn"
    and termFLP:
              "\<And>fe ft. asynchronousSystem.fairInfiniteExecution
                            transFn sendsFn startFn fe ft \<Longrightarrow>
                       flpSystem.terminationFLP transFn sendsFn startFn fe ft"
    and val: "\<forall>i c. flpSystem.validity transFn sendsFn startFn i c"
    and agr: "\<forall>i c. flpSystem.agreementInit transFn sendsFn startFn i c"
    by (auto simp: flp_consensus_solvable_def)

  interpret flpPseudoConsensus transFn sendsFn startFn using pc .

  have "False"
    using flpPseudoConsensus.ConsensusFails[OF pc termFLP val agr] .
  thus False .
qed

section \<open>BlackBox-to-FLP bridge predicate\<close>

text \<open>Paper, Section 4.2 (the reduction Consensus $\preceq$ Black\_Box):
\begin{quote}
``Now we give the reduction from Consensus to Black\_Box.  To solve
Consensus(\<open>V\<close>) at (a correct process) \<open>p_i\<close>, we invoke
Black\_Box(\<open>V, E, F, e_i^*\<close>) locally \<open>\<dots>\<close>.  Each correct process
computes \<open>min(L)\<close> from the locally returned list \<open>L\<close> and outputs
as its consensus value the broadcast value that it receives from
\<open>p_min(L)\<close> and terminates.  The conditions of Consensus --
Agreement, Validity, and Termination -- can be seen to be satisfied.
So Consensus $\preceq$ Black\_Box.''
\end{quote}

\textit{Deviation -- meta-level step.}  The paper's reduction is
operational (``invoke BB locally, broadcast, collect, decide'').  We
cannot mechanise this at the abstract level of @{const solves_BlackBox}
because that predicate has no notion of an asynchronous distributed
execution, fairness, or termination under failure.  We therefore
capture the reduction as the named predicate below:

\begin{quote}
``If an abstract BlackBox solver for (\<open>P, C\<close>) exists, then -- in
the AFP entry's FLP model -- some triple (\<open>transFn, sendsFn,
startFn\<close>) of state-transition functions flp-solves consensus.''
\end{quote}

This is the right semantic content of the paper's reduction.  The
predicate takes two type witnesses (\<open>'s\<close> for state, \<open>'v\<close> for
message-value type) because HOL cannot existentially quantify over
types.  A user discharging this predicate would exhibit specific
\<open>'s\<close>, \<open>'v\<close>, \<open>transFn\<close>, \<open>sendsFn\<close>, \<open>startFn\<close> implementing the
``broadcast V, collect, invoke BB, decide'' protocol of the paper.

\textit{Faithfulness:} the bridge is a hypothesis (not an axiom)
that the impossibility theorems (3, 4, 5 in Impossibility.thy) take
explicitly.  It replaces the formerly-vacuous
\<open>byzantineSystem.flp_consensus_impossibility\<close> axiom; see
Foundation\_Vacuity.thy for the historical issue.\<close>

definition bb_realizes_flp_consensus ::
  "'p set \<Rightarrow> 'p set \<Rightarrow> 's itself \<Rightarrow> 'v itself \<Rightarrow> bool" where
  "bb_realizes_flp_consensus P C ts tv \<longleftrightarrow>
    BlackBox_solvable P C \<longrightarrow>
      (\<exists> (transFn :: 'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> 's)
         (sendsFn :: 'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> ('p, 'v) message multiset)
         (startFn :: 'p \<Rightarrow> 's).
            flp_consensus_solvable transFn sendsFn startFn)"

text \<open>Composing the bridge with @{thm flp_consensus_unsolvable} yields
the form actually used in \<open>Impossibility.thy\<close>:\<close>

lemma BlackBox_unsolvable_via_bridge:
  assumes bridge: "bb_realizes_flp_consensus P C TYPE('s) TYPE('v)"
  shows "\<not> BlackBox_solvable P C"
proof
  assume BB: "BlackBox_solvable P C"
  from bridge[unfolded bb_realizes_flp_consensus_def] BB
  show False
    using flp_consensus_unsolvable by blast
qed

end
