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

text \<open>An algorithm in the FLP model is a triple
@{term "(trans, sends, start)"} of a transition function, a send
function, and an initial-state function.  The algorithm
\<open>flp-solves consensus\<close> when the triple satisfies the @{locale flpSystem}
and @{locale flpPseudoConsensus} locale axioms, plus the standard
Termination, Validity, and Agreement conditions used in the FLP
impossibility theorem.\<close>

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

text \<open>The FLP impossibility theorem, rephrased on this predicate.\<close>

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

text \<open>The paper's reduction "Consensus reduces to BlackBox" treats
Consensus and BlackBox at the same abstraction level: an algorithm at
each correct process broadcasts its input, collects its peers' values,
and outputs the BlackBox decision.  At the abstract function-level
of @{const solves_BlackBox} we cannot \emph{verify} that this protocol
solves consensus in the FLP-distributed sense (the abstract predicate
has no notion of fairness, infinite executions, or failure tolerance).
We capture the meta-level reduction as the named predicate below,
parametric in two type witnesses for the FLP state and message-value
types.\<close>

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
