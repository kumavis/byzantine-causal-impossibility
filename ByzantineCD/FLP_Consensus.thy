(*
  Title:   FLP_Consensus.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  This theory imports the FLP impossibility result from the AFP entry
  FLP, packaged as a single proven theorem about the predicate
  flp_consensus_solvable.  Two ingredients:

    (1) flp_consensus_solvable transFn sendsFn startFn: a predicate
        over a single asynchronous distributed protocol (trans, sends,
        start) that combines the AFP entry's flpSystem and
        flpPseudoConsensus locale axioms with the three ConsensusFails
        preconditions (Termination, Validity, Agreement).

    (2) flp_consensus_unsolvable: \<not> flp_consensus_solvable t s st
        for any t/s/st.  Proved by invoking the AFP entry's
        flpPseudoConsensus.ConsensusFails theorem.  No axiom.

  Relationship to the impossibility chain in Impossibility.thy
  ------------------------------------------------------------
  Because flp_consensus_unsolvable is a universal statement on the
  protocol triple, the existential
       \<exists> transFn sendsFn startFn. flp_consensus_solvable \<dots>
  is unconditionally False.  Earlier revisions of this development
  defined a "bridge" predicate

       bb_realizes_flp_consensus P C TYPE('s) TYPE('v) \<equiv>
          BlackBox_solvable P C \<longrightarrow>
             (\<exists> transFn sendsFn startFn. flp_consensus_solvable \<dots>)

  intended as the meta-level link from BlackBox-solvability to FLP-style
  consensus solvability.  By the observation above, that bridge is
  logically equivalent to "\<not> BlackBox_solvable P C": its consequent
  is always False, so the implication is just the negation of its
  antecedent.  Carrying the bridge around (with its two type witnesses)
  hid this equivalence behind a more elaborate-looking definition.

  Impossibility.thy therefore takes "\<not> BlackBox_solvable procs correct"
  as the explicit meta-level hypothesis of Theorems 3/4/5.  Discharging
  that hypothesis is exactly the paper's informal reduction
  "Consensus \<preceq> BlackBox" (an asynchronous distributed protocol that
  uses a BlackBox oracle and FLP-solves consensus); doing so within the
  AFP FLP locale is the natural follow-on work item.

  flp_consensus_unsolvable below is the AFP-FLP citation that motivates
  the hypothesis: it makes precise what "Consensus is unsolvable" means
  in the formal model the hypothesis ultimately appeals to.
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
three correctness conditions that the AFP entry's
\<open>flpPseudoConsensus.ConsensusFails\<close> takes as preconditions:
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
invocation of the AFP entry's \<open>flpPseudoConsensus.ConsensusFails\<close>
theorem (proven, not assumed):
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

end
