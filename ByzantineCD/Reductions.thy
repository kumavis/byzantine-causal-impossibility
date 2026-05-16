(*
  Title:   Reductions.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  The two reductions of Section 4.2 of the paper:

    (R1)  consensus_reduces_to_blackbox:
              a BlackBox solver yields a Consensus solver.
          Paper, Section 4.2: "To solve Consensus(V) at p_i, invoke
            Black_Box(V, E, F, e*_i) locally ... Each correct process
            computes min(L) from the locally returned list L and outputs
            as its consensus value the broadcast value that it receives
            from p_min(L) and terminates.  The conditions of Consensus
            -- Agreement, Validity, and Termination -- can be seen to
            be satisfied.  So Consensus \<preceq> Black_Box."
          We make this fully constructive and prove it mechanically.

    (R2)  blackbox_reduces_to_cd:
              a CD solver yields a BlackBox solver.
          Paper, Section 4.2: "If there were an algorithm to make F
            match E, it requires identifying whether each of the
            processes that input their execution histories is correct
            or Byzantine, and tracing and dealing with/resolving the
            impact of contamination via message passing by the
            Byzantine processes from and through those Byzantine
            processes on the execution histories of processes at other
            processes.  Thus, Black_Box \<preceq> CD."
          The paper's argument is meta-level (no syntactic construction
          of the BB solver from CD is given).  We capture the
          meta-level step as a named locale assumption
          (cd_can_identify_correct in byzantineSystem_with_identification)
          and discharge the reduction proper as a constructive proof
          from that assumption.

  Composition Consensus \<preceq> BlackBox \<preceq> CD is preserved here as
  paper-faithful documentation of the paper's section 4.2 chain.  It
  is *not* on the critical path of Theorems 3, 4, 5: the headline
  theorems in Impossibility.thy bypass this chain and route directly
  through Theorem 1 (CD_FN_unavoidable) instead.  Together with
  BlackBox_Unsolvable.thy and the proven FLP impossibility in
  FLP_Consensus.thy, R1 + R2 still form a fully-proven alternative
  derivation of Theorems 3/4/5 -- just not the one used.

  Key deviations from the paper:

    1. R1's "min(L)" is replaced by a hard-wired correct process
       p_star, threaded as a parameter of consensus_from_bb.  This is
       semantically equivalent given that bb_L = correct (one of BB's
       output requirements) -- min(L) and any fixed p_star \<in> L produce
       the same value because every correct process invoking BB gets
       the same bb_w.  We do not need to actually compute the minimum
       in our abstraction.

    2. The paper's BB invocation runs at every correct p_i; our
       consensus_from_bb is structurally constant in i (the BB output
       is read once at p_star).  This is correct because, again,
       bb_L = correct guarantees a single common reference point that
       every correct process would resolve to.

    3. R1 uses the "trivial" admissible adversary -- a single internal
       event Internal p_star 1 at a chosen correct process -- as the
       canonical context in which BB's correctness condition is
       instantiated.  The paper does not need such a gadget because
       it works at the operational level; at our function-level
       abstraction we need an actual admissible adversary to feed BB.
*)

theory Reductions
  imports BlackBox
begin

section \<open>The trivial-execution gadget\<close>

text \<open>To invoke the universal quantifier in @{const solves_BlackBox}
and @{const produces_valid_F} (the validity-condition predicates over
all admissible adversaries) we need at least one concrete admissible
adversary to instantiate them at.  This gadget supplies the simplest
such adversary: a one-event history at a designated correct process
\<open>p_star\<close>, with that single event playing the role of the target
\<open>e_star\<close>.

This is a mechanisation artefact, not a step of the paper.  Existing
distributed-algorithm literature usually formulates BB as ``runs
correctly on the actual execution''; we need an ``actual'' execution
the universal quantifier can range over, and the trivial one is
sufficient for Validity.\<close>

definition trivial_history :: "'p \<Rightarrow> 'p history" where
  "trivial_history p_star \<equiv>
     (\<lambda>p. if p = p_star then [Internal p_star 1] else [])"

definition trivial_event :: "'p \<Rightarrow> 'p event" where
  "trivial_event p_star \<equiv> Internal p_star 1"

definition trivial_adversary :: "'p \<Rightarrow> 'p adversary" where
  "trivial_adversary p_star \<equiv>
     \<lparr> adv_E = trivial_history p_star,
       adv_e_star = trivial_event p_star,
       adv_i = p_star \<rparr>"

lemma wf_history_local_one:
  shows "wf_history_local p_star [Internal p_star 1]"
  by (simp add: wf_history_local_def)

lemma wf_history_local_empty:
  shows "wf_history_local p []"
  by (simp add: wf_history_local_def)

lemma wf_history_trivial:
  shows "wf_history (trivial_history p_star)"
proof -
  have "\<And>p. wf_history_local p (trivial_history p_star p)"
  proof -
    fix p
    show "wf_history_local p (trivial_history p_star p)"
    proof (cases "p = p_star")
      case True
      hence "trivial_history p_star p = [Internal p_star 1]"
        by (simp add: trivial_history_def)
      thus ?thesis
        using True wf_history_local_one by simp
    next
      case False
      hence "trivial_history p_star p = []"
        by (simp add: trivial_history_def)
      thus ?thesis
        using wf_history_local_empty by simp
    qed
  qed
  thus ?thesis by (simp add: wf_history_def)
qed

lemma events_of_trivial:
  shows "events_of (trivial_history p_star) = {Internal p_star 1}"
proof -
  have "events_of (trivial_history p_star)
          = (\<Union>p. set (trivial_history p_star p))"
    by (simp add: events_of_def)
  also have "\<dots> = {Internal p_star 1}"
    by (auto simp: trivial_history_def)
  finally show ?thesis .
qed

lemma adversary_admissible_trivial:
  assumes "p_star \<in> C"
  shows "adversary_admissible C (trivial_adversary p_star)"
proof -
  have eE: "adv_E (trivial_adversary p_star) = trivial_history p_star"
    by (simp add: trivial_adversary_def)
  have eI: "adv_i (trivial_adversary p_star) = p_star"
    by (simp add: trivial_adversary_def)
  have eS: "adv_e_star (trivial_adversary p_star) = trivial_event p_star"
    by (simp add: trivial_adversary_def)
  have "wf_history (adv_E (trivial_adversary p_star))"
    using wf_history_trivial eE by simp
  moreover have "adv_i (trivial_adversary p_star) \<in> C"
    using assms eI by simp
  moreover have
    "proc_of (adv_e_star (trivial_adversary p_star))
       = adv_i (trivial_adversary p_star)"
    by (simp add: eS eI trivial_event_def)
  moreover have
    "adv_e_star (trivial_adversary p_star)
       \<in> events_of (adv_E (trivial_adversary p_star))"
    by (simp add: eE eS events_of_trivial trivial_event_def)
  ultimately show ?thesis by (simp add: adversary_admissible_def)
qed

section \<open>Reduction R1: Consensus reduces to BlackBox\<close>

text \<open>Paper, Section 4.2 (proof of Theorem 3, step 2):
\begin{quote}
``Now we give the reduction from Consensus to Black\_Box.  To solve
Consensus(\<open>V\<close>) at (a correct process) \<open>p_i\<close>, we invoke
Black\_Box(\<open>V, E, F, e_i^*\<close>) locally (and likewise to solve
Consensus(\<open>V\<close>) at (each process) \<open>p_j\<close>, invoke
Black\_Box(\<open>V, E, F, e_j^*\<close>) at each \<open>p_j\<close>).  Each correct process
computes \<open>min(L)\<close> from the locally returned list \<open>L\<close> and outputs
as its consensus value the broadcast value that it receives from
\<open>p_min(L)\<close> and terminates.  The conditions of Consensus -- Agreement,
Validity, and Termination -- can be seen to be satisfied.  So
Consensus $\preceq$ Black\_Box.''
\end{quote}

\textit{Deviation:} we do not compute \<open>min(L)\<close>.  Since BB's
correctness condition guarantees \<open>bb_L = correct\<close> -- the set is the
same at every correct process -- every correct process resolves
\<open>p_min(L)\<close> to the same value, so any fixed correct \<open>p_star\<close> serves
in place of \<open>min(L)\<close>.  We thread \<open>p_star\<close> as a constructor parameter.\<close>

definition consensus_from_bb ::
  "'p set \<Rightarrow> 'p \<Rightarrow> 'p bb_solver \<Rightarrow> 'p consensus_alg" where
  "consensus_from_bb P p_star bb_alg \<equiv>
     (\<lambda>V _. bb_w (bb_alg P V (trivial_event p_star) p_star))"

context byzantineSystem
begin

subsection \<open>Agreement\<close>

text \<open>Paper's first Consensus property (Section 4.2):
\begin{quote}
``Agreement: All non-faulty processes must agree on the same single
value.''
\end{quote}

In our construction every correct process reads the same
\<open>bb_w (bb_alg \<dots>)\<close> value (\<open>consensus_from_bb\<close> ignores its second
argument).  Agreement is immediate from this constancy.\<close>

lemma consensus_from_bb_agreement:
  fixes V :: "'p \<Rightarrow> bool"
  shows "consensus_agreement correct (consensus_from_bb procs p_star bb_alg) V"
proof -
  have const_in_i:
    "\<And>p q. consensus_from_bb procs p_star bb_alg V p
              = consensus_from_bb procs p_star bb_alg V q"
    by (simp add: consensus_from_bb_def)
  show ?thesis by (simp add: consensus_agreement_def const_in_i)
qed

subsection \<open>Validity\<close>

text \<open>Paper's second Consensus property (Section 4.2):
\begin{quote}
``Validity: If all non-faulty processes have the same initial value,
then the agreed-on value by all the non-faulty processes must be
that same value.''
\end{quote}

We get Validity by instantiating \<open>solves_BlackBox\<close> at the trivial
adversary and reading off the uniform-case branches of \<open>w_value\<close>:
if all correct processes have \<open>V[p] = True\<close>, the BB output is the
\<open>w_value_uniform_true\<close> branch, which is \<open>True\<close>; similarly for
\<open>False\<close>.\<close>

lemma bb_w_at_trivial:
  assumes bb:       "solves_BlackBox procs correct bb_alg"
      and p_star_C: "p_star \<in> correct"
  shows "bb_w (bb_alg procs V (trivial_event p_star) p_star)
           = w_value correct V
                     (trivial_history p_star)
                     (bb_F (bb_alg procs V (trivial_event p_star) p_star))
                     (trivial_event p_star)"
proof -
  let ?adv = "trivial_adversary p_star"
  have adm: "adversary_admissible correct ?adv"
    using p_star_C by (rule adversary_admissible_trivial)
  from bb have univ:
    "\<forall>V adv. adversary_admissible correct adv \<longrightarrow>
        bb_correct_output procs correct V
          (adv_E adv) (adv_e_star adv) (adv_i adv)
          (bb_alg procs V (adv_e_star adv) (adv_i adv))"
    by (simp add: solves_BlackBox_def)
  from univ adm have bb_inst:
    "bb_correct_output procs correct V
       (adv_E ?adv) (adv_e_star ?adv) (adv_i ?adv)
       (bb_alg procs V (adv_e_star ?adv) (adv_i ?adv))"
    by blast
  hence
    "bb_w (bb_alg procs V (adv_e_star ?adv) (adv_i ?adv))
       = w_value correct V (adv_E ?adv)
           (bb_F (bb_alg procs V (adv_e_star ?adv) (adv_i ?adv)))
           (adv_e_star ?adv)"
    by (simp add: bb_correct_output_def)
  thus ?thesis
    by (simp add: trivial_adversary_def)
qed

lemma consensus_from_bb_validity:
  assumes bb:       "solves_BlackBox procs correct bb_alg"
      and p_star_C: "p_star \<in> correct"
  shows "consensus_validity correct (consensus_from_bb procs p_star bb_alg) V"
proof -
  let ?out = "bb_alg procs V (trivial_event p_star) p_star"
  have C_ne: "correct \<noteq> {}" using p_star_C by blast
  have bb_w_eq:
    "bb_w ?out
       = w_value correct V (trivial_history p_star)
                 (bb_F ?out) (trivial_event p_star)"
    by (rule bb_w_at_trivial[OF bb p_star_C])

  have case_True:
    "(\<forall>p \<in> correct. V p)
       \<longrightarrow> (\<forall>p \<in> correct. (consensus_from_bb procs p_star bb_alg) V p)"
  proof
    assume H: "\<forall>p \<in> correct. V p"
    have "bb_w ?out = True"
      using bb_w_eq w_value_uniform_true[OF C_ne H] by simp
    thus "\<forall>p \<in> correct. (consensus_from_bb procs p_star bb_alg) V p"
      by (simp add: consensus_from_bb_def)
  qed

  have case_False:
    "(\<forall>p \<in> correct. \<not> V p)
       \<longrightarrow> (\<forall>p \<in> correct. \<not> (consensus_from_bb procs p_star bb_alg) V p)"
  proof
    assume H: "\<forall>p \<in> correct. \<not> V p"
    have "bb_w ?out = False"
      using bb_w_eq w_value_uniform_false[OF H] by simp
    thus "\<forall>p \<in> correct. \<not> (consensus_from_bb procs p_star bb_alg) V p"
      by (simp add: consensus_from_bb_def)
  qed

  from case_True case_False
  show ?thesis by (simp add: consensus_validity_def)
qed

subsection \<open>Termination is implicit in totality\<close>

text \<open>Paper's third Consensus property (Section 4.2):
\begin{quote}
``Termination: Each non-faulty process must eventually decide on a
value.''
\end{quote}

\textit{Deviation (a load-bearing one):} our @{typ "'p consensus_alg"}
is a total HOL function, so every correct process \emph{always}
returns a decision and Termination holds trivially.  This trivialisation
of Termination is exactly what makes the abstract \<open>solves_Consensus\<close>
predicate too weak to express FLP -- see @{theory_text
\<open>Foundation_Vacuity.thy\<close>} -- and is the reason the impossibility
chain in @{theory_text \<open>Impossibility.thy\<close>} goes through the
FLP-style \<open>flp_consensus_solvable\<close> predicate of \<open>FLP_Consensus.thy\<close>
rather than directly through \<open>solves_Consensus\<close>.\<close>

subsection \<open>Composition: the headline reduction\<close>

theorem consensus_reduces_to_blackbox:
  assumes p_star_C: "p_star \<in> correct"
      and bb:       "solves_BlackBox procs correct bb_alg"
  shows "solves_Consensus correct (consensus_from_bb procs p_star bb_alg)"
proof -
  have agr: "\<And>V. consensus_agreement correct
                    (consensus_from_bb procs p_star bb_alg) V"
    by (rule consensus_from_bb_agreement)
  have val: "\<And>V. consensus_validity correct
                    (consensus_from_bb procs p_star bb_alg) V"
    by (rule consensus_from_bb_validity[OF bb p_star_C])
  show ?thesis using agr val by (simp add: solves_Consensus_def)
qed

corollary BlackBox_solvable_imp_Consensus_solvable:
  assumes ne: "correct \<noteq> {}" and bb: "BlackBox_solvable procs correct"
  shows "\<exists>alg. solves_Consensus correct alg"
proof -
  obtain bb_alg where solver: "solves_BlackBox procs correct bb_alg"
    using bb by (auto simp: BlackBox_solvable_def)
  obtain p_star where pc: "p_star \<in> correct" using ne by blast
  have "solves_Consensus correct (consensus_from_bb procs p_star bb_alg)"
    by (rule consensus_reduces_to_blackbox[OF pc solver])
  thus ?thesis by blast
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

section \<open>Reduction R2: BlackBox reduces to CD\<close>

text \<open>Paper, Section 4.2 (proof of Theorem 3, step 1):
\begin{quote}
``If there were an algorithm to make \<open>F\<close> match \<open>E\<close>, it requires
identifying whether each of the processes that input their execution
histories is correct or Byzantine, and tracing and dealing with /
resolving the impact of contamination via message passing by the
Byzantine processes from and through those Byzantine processes on the
execution histories of processes at other processes.  Thus,
Black\_Box $\preceq$ CD.''
\end{quote}

\textit{Deviation -- meta-level step.}  The paper does not exhibit a
syntactic construction of a Black\_Box solver from a CD solver; the
argument is meta-level (``it requires identifying \dots'').  We
capture this faithfully as a single named locale assumption
\<open>cd_can_identify_correct\<close> in the sub-locale
\<open>byzantineSystem_with_identification\<close>:

\begin{quote}
``If there is an algorithm \<open>cd_alg\<close> that produces a valid \<open>F\<close>,
then there is an algorithm \<open>cd_alg'\<close> that (i) produces the same valid
\<open>F\<close>, (ii) returns the decision \<open>True\<close>, and (iii) also returns the
set of correct processes.''
\end{quote}

This is the positive form of the paper's contrapositive (``producing
valid \<open>F\<close> is impossible without internally identifying the correct
set'').  From this assumption the rest of R2 is fully constructive:
the BB solver projects the augmented CD solver's @{term L} field into
\<open>bb_L\<close>, its @{term F} field into \<open>bb_F\<close>, and applies the piecewise
definition of @{const w_value} to obtain \<open>bb_w\<close>.\<close>

context byzantineSystem
begin

type_synonym 'q cd_solver_with_L =
  "'q \<Rightarrow> 'q event \<Rightarrow> 'q history \<times> bool \<times> 'q set"

text \<open>The augmented predicate insists on the three properties
Misra--Kshemkalyani actually need from the meta-level step:
\begin{enumerate}
  \item the collected \<open>F\<close> is valid in the sense of Definition 5;
  \item the algorithm's claim \<open>b\<close> is \<open>True\<close>, matching Definition 5's
        ``returning 1 indicates that the problem has been solved
        correctly'';
  \item the reported list \<open>L\<close> equals the correct set.
\end{enumerate}\<close>

definition produces_valid_F_with_L ::
  "'p set \<Rightarrow> 'p cd_solver_with_L \<Rightarrow> bool" where
  "produces_valid_F_with_L C alg \<longleftrightarrow>
     (\<forall>adv. adversary_admissible C adv \<longrightarrow>
        (let (F', b, L) = alg (adv_i adv) (adv_e_star adv) in
           valid (adv_E adv) F' (adv_e_star adv)
           \<and> b
           \<and> L = C))"

end \<comment> \<open>context @{locale byzantineSystem}\<close>

text \<open>\textbf{Role of this locale in the development.}  The locale
\<open>byzantineSystem_with_identification\<close> below extends @{locale
byzantineSystem} with the single named meta-level axiom
\<open>cd_can_identify_correct\<close> -- the positive form of the paper's
contrapositive ``producing valid F is impossible without identifying
the correct set'' (paper Section 4.2).  Together with the
constructive \<open>bb_from_cd_with_L\<close> defined below it gives R2 (BB
\<open>\<preceq>\<close> CD), which is what the paper actually proves to establish
Theorems 3/4/5.

\textit{Note on critical path.}  After the discharge of the BB
impossibility via Theorem 1 (\<open>BlackBox_Unsolvable.thy\<close>) and the
direct Theorem-1 chain for the headline impossibility theorems
(\<open>Impossibility.thy\<close>), the locale and its axiom are no longer on
the critical path of Theorems 3/4/5: the headline theorems live in
plain @{locale byzantineSystem} and route through Theorem 1 in one
step.  The locale and R2 are nevertheless retained, as paper-faithful
documentation of the §4.2 chain and as a fully-proven alternative
derivation (composing R2 with @{theory_text \<open>BlackBox_Unsolvable.thy\<close>}
yields the same headline conclusion via the route the paper
actually uses).  This is the only locale axiom anywhere in the
development; it is explicitly localised in this sub-locale rather
than added to the base locale.\<close>

locale byzantineSystem_with_identification = byzantineSystem +
  assumes cd_can_identify_correct:
    "produces_valid_F correct cd_alg \<Longrightarrow>
       \<exists>cd_alg'. produces_valid_F_with_L correct cd_alg'
                  \<and> (\<forall>i e. fst (cd_alg' i e) = fst (cd_alg i e))"

context byzantineSystem_with_identification
begin

subsection \<open>Constructive part: BB from an augmented CD solver\<close>

text \<open>Given an augmented CD solver (one that, by
@{thm cd_can_identify_correct}, also reports the correct set), we
build a Black\_Box solver by simple projection:
\begin{itemize}
  \item \<open>bb_F\<close> := the augmented CD solver's collected \<open>F'\<close>;
  \item \<open>bb_L\<close> := the augmented CD solver's reported \<open>L\<close>
        (which equals \<open>correct\<close> by assumption);
  \item \<open>bb_w\<close> := the paper's piecewise \<open>w_value\<close>, computed against
        \<open>L\<close> and the CD solver's boolean.
\end{itemize}

This matches the paper's reduction in Section 4.2: ``Solving
Black\_Box at \<open>p_i\<close> requires identifying the set of correct
processes and solving CD.''  The augmented CD solver does both; the
projection just exposes its outputs in the BB record shape.\<close>

definition bb_from_cd_with_L ::
  "'p cd_solver_with_L \<Rightarrow> 'p bb_solver" where
  "bb_from_cd_with_L cd_alg' \<equiv>
     (\<lambda>P V e_star i.
        let (F', b, L) = cd_alg' i e_star in
        \<lparr> bb_F = F',
          bb_w = (if (\<forall>p \<in> L. \<not> V p) then False
                  else if (\<forall>p \<in> L. V p) then True
                  else b),
          bb_L = L \<rparr>)"

subsection \<open>Three sub-claims mirroring @{const bb_correct_output}\<close>

lemma bb_from_cd_with_L_correct:
  assumes augmented: "produces_valid_F_with_L correct cd_alg'"
  shows "solves_BlackBox procs correct (bb_from_cd_with_L cd_alg')"
proof (unfold solves_BlackBox_def, intro allI impI)
  fix V adv
  assume adm: "adversary_admissible correct adv"

  \<comment> \<open>Decompose the augmented CD solver's output.\<close>
  obtain F' b L where
    decomp: "cd_alg' (adv_i adv) (adv_e_star adv) = (F', b, L)"
    by (cases "cd_alg' (adv_i adv) (adv_e_star adv)") auto

  from augmented adm decomp
  have valid_F': "valid (adv_E adv) F' (adv_e_star adv)"
    and b_True:  "b"
    and L_eq:    "L = correct"
    by (auto simp: produces_valid_F_with_L_def Let_def)

  let ?out = "bb_from_cd_with_L cd_alg' procs V
                                (adv_e_star adv) (adv_i adv)"

  have F_field: "bb_F ?out = F'"
    by (simp add: bb_from_cd_with_L_def decomp)
  have L_field: "bb_L ?out = correct"
    by (simp add: bb_from_cd_with_L_def decomp L_eq)
  have w_field:
    "bb_w ?out =
       (if (\<forall>p \<in> correct. \<not> V p) then False
        else if (\<forall>p \<in> correct. V p) then True
        else b)"
    by (simp add: bb_from_cd_with_L_def decomp L_eq)

  \<comment> \<open>Sub-claim 1: \<open>F\<close> is valid.\<close>
  have claim_valid:
    "valid (adv_E adv) (bb_F ?out) (adv_e_star adv)"
    using valid_F' F_field by simp

  \<comment> \<open>Sub-claim 2: \<open>bb_w\<close> matches @{const w_value}.  Three
      branches following the piecewise definition (Section 4.2):
      uniform-false, uniform-true, mixed.\<close>
  have claim_w:
    "bb_w ?out =
       w_value correct V (adv_E adv) (bb_F ?out) (adv_e_star adv)"
  proof -
    consider
        (uniform_false) "\<forall>p \<in> correct. \<not> V p"
      | (uniform_true)  "\<not> (\<forall>p \<in> correct. \<not> V p)" "\<forall>p \<in> correct. V p"
      | (mixed)         "\<not> (\<forall>p \<in> correct. \<not> V p)"
                        "\<not> (\<forall>p \<in> correct. V p)"
      by blast
    thus ?thesis
    proof cases
      case uniform_false
      have "bb_w ?out = False"
        by (simp add: w_field uniform_false)
      moreover have
        "w_value correct V (adv_E adv) (bb_F ?out) (adv_e_star adv) = False"
        by (simp add: w_value_uniform_false[OF uniform_false])
      ultimately show ?thesis by simp
    next
      case uniform_true
      have C_ne: "correct \<noteq> {}" using uniform_true(2) uniform_true(1) by blast
      have inner_reduce:
        "(if (\<forall>p \<in> correct. V p) then True else b) = True"
        using uniform_true(2) by simp
      have outer_reduce:
        "(if (\<forall>p \<in> correct. \<not> V p) then False
          else if (\<forall>p \<in> correct. V p) then True
          else b)
         = (if (\<forall>p \<in> correct. V p) then True else b)"
        using uniform_true(1) by (rule if_not_P)
      have "bb_w ?out = True"
        using w_field outer_reduce inner_reduce by simp
      moreover have
        "w_value correct V (adv_E adv) (bb_F ?out) (adv_e_star adv) = True"
        by (rule w_value_uniform_true[OF C_ne uniform_true(2)])
      ultimately show ?thesis by simp
    next
      case mixed
      have "bb_w ?out = b"
        by (simp add: w_field mixed)
      hence bb_w_True: "bb_w ?out = True" using b_True by simp
      have
        "w_value correct V (adv_E adv) (bb_F ?out) (adv_e_star adv)
           = valid (adv_E adv) (bb_F ?out) (adv_e_star adv)"
        by (rule w_value_mixed[OF mixed(1) mixed(2)])
      also have
        "\<dots> = valid (adv_E adv) F' (adv_e_star adv)"
        by (simp add: F_field)
      also have "\<dots> = True" using valid_F' by simp
      finally show ?thesis using bb_w_True by simp
    qed
  qed

  \<comment> \<open>Sub-claim 3: \<open>bb_L\<close> equals the correct set.\<close>
  have claim_L: "bb_L ?out = correct" by (rule L_field)

  show "bb_correct_output procs correct V
          (adv_E adv) (adv_e_star adv) (adv_i adv) ?out"
    using claim_valid claim_w claim_L
    by (simp add: bb_correct_output_def)
qed

theorem blackbox_reduces_to_cd:
  assumes cd: "produces_valid_F correct cd_alg"
  shows "\<exists>bb_alg. solves_BlackBox procs correct bb_alg"
proof -
  from cd_can_identify_correct[OF cd]
  obtain cd_alg' where
    aug: "produces_valid_F_with_L correct cd_alg'"
    by blast
  have "solves_BlackBox procs correct (bb_from_cd_with_L cd_alg')"
    by (rule bb_from_cd_with_L_correct[OF aug])
  thus ?thesis by blast
qed

corollary CD_solvable_imp_BlackBox_solvable:
  assumes "CD_solvable m correct"
  shows   "BlackBox_solvable procs correct"
proof -
  obtain cd_alg where "produces_valid_F correct cd_alg"
    using assms by (auto simp: CD_solvable_def)
  thus ?thesis
    using blackbox_reduces_to_cd by (auto simp: BlackBox_solvable_def)
qed

end \<comment> \<open>context @{locale byzantineSystem_with_identification}\<close>

end
