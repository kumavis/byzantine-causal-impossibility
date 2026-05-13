(*
  Title:   Reductions.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  The two reductions of \S4.2 of the paper:

    (R1)  consensus_reduces_to_blackbox: a BlackBox solver yields a
          Consensus solver.  Constructive: p_i broadcasts w, all output
          the w broadcast by p_{min(L)}.  Proved here mechanically.

    (R2)  blackbox_reduces_to_cd: a CD solver yields a BlackBox solver.
          Meta-level in the paper ("solving CD requires identifying all
          Byzantine processes").  We capture the paper's meta-level step
          as the named locale assumption cd_can_identify_correct in
          byzantineSystem_with_identification.  The reduction proper is
          then constructive and proved here.

  The composition Consensus \<preceq> BlackBox \<preceq> CD then yields the headline
  impossibility theorem in Impossibility.thy.
*)

theory Reductions
  imports BlackBox
begin

section \<open>The trivial-execution gadget\<close>

text \<open>To invoke the universal quantifier in @{const solves_BlackBox} and
@{const produces_valid_F} we need at least one admissible adversary.  The
following gadget supplies one: a singleton history at a designated correct
process, exposing one internal event.\<close>

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
    by (simp add: trivial_history_def wf_history_local_one wf_history_local_empty)
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
  have "wf_history (trivial_history p_star)"
    by (rule wf_history_trivial)
  moreover have "adv_i (trivial_adversary p_star) \<in> C"
    using assms by (simp add: trivial_adversary_def)
  moreover have
    "proc_of (adv_e_star (trivial_adversary p_star))
       = adv_i (trivial_adversary p_star)"
    by (simp add: trivial_adversary_def trivial_event_def)
  moreover have
    "adv_e_star (trivial_adversary p_star)
       \<in> events_of (adv_E (trivial_adversary p_star))"
    by (simp add: trivial_adversary_def trivial_event_def events_of_trivial)
  ultimately show ?thesis by (simp add: adversary_admissible_def)
qed

section \<open>Reduction R1: Consensus \<preceq> BlackBox\<close>

text \<open>The paper's construction (\S4.2):
\begin{quote}
   To solve Consensus(V) at $p_i$, invoke Black\_Box(V, E, F, $e_i^*$)
   locally\dots\ Each correct process computes $\min(L)$ from the locally
   returned list $L$ and outputs as its consensus value the broadcast
   value that it receives from $p_{\min(L)}$ and terminates.
\end{quote}

In our function-level abstraction the ``broadcast'' is realised by reading
@{term p_star}'s @{term bb_w} field directly; correctness of Black\_Box
guarantees @{term "bb_L = C"} so the $\min(L)$ is determined and stable
across correct processes.  We thread @{term p_star} as a parameter of the
constructor for clarity.\<close>

definition consensus_from_bb ::
  "'p set \<Rightarrow> 'p \<Rightarrow> 'p bb_solver \<Rightarrow> 'p consensus_alg" where
  "consensus_from_bb P p_star bb_alg \<equiv>
     (\<lambda>V _. bb_w (bb_alg P V (trivial_event p_star) p_star))"

context byzantineSystem
begin

subsection \<open>Agreement\<close>

text \<open>The constructor is constant in @{term i}; Agreement is immediate.\<close>

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

text \<open>Validity is obtained by instantiating BB-correctness at the trivial
adversary and at the user-supplied @{term V}.\<close>

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

text \<open>Our @{typ "'p consensus_alg"} is a total function, so every correct
process \emph{always} returns a decision and the Termination clause of
\S4.2 holds automatically.\<close>

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

section \<open>Reduction R2: BlackBox \<preceq> CD\<close>

text \<open>The paper's argument (\S4.2):
\begin{quote}
  If there were an algorithm to make $F$ match $E$, it requires identifying
  whether each of the processes that input their execution histories is
  correct or Byzantine\dots\ Thus, to solve CD, it is necessary to identify
  Byzantine processes, their actual execution histories, and causal chains
  from and through them.  So we have Black\_Box $\preceq$ CD.
\end{quote}

The paper does not exhibit a syntactic construction of a Black\_Box solver
from a CD solver; the argument is meta-level.  We capture this faithfully
as a single, named locale assumption (@{thm [source]
\<open>byzantineSystem_with_identification.cd_can_identify_correct\<close>}) and
discharge the reduction from it constructively.

\medskip
\textbf{Faithfulness statement.}  The assumption says: \emph{If there is an
algorithm that produces a valid F (Definition~5), then there is an algorithm
that produces the same valid F, returns the decision True, and \emph{also}
returns the set of correct processes.}  The paper's argument is the
contrapositive: producing a valid F is impossible without internally
identifying the correct set.  Our locale assumption is the positive form
of that meta-level claim.\<close>

context byzantineSystem
begin

type_synonym 'q cd_solver_with_L =
  "'q \<Rightarrow> 'q event \<Rightarrow> 'q history \<times> bool \<times> 'q set"

text \<open>The augmented predicate.  We insist on the three properties Misra--
Kshemkalyani actually need from the meta-level step: (i) the collected F is
valid, (ii) the algorithm's claim @{term b} is @{term True}, matching
Definition~5's ``returning 1 indicates that the problem has been solved
correctly'', and (iii) @{term "L = correct"}.\<close>

definition produces_valid_F_with_L ::
  "'p set \<Rightarrow> 'p cd_solver_with_L \<Rightarrow> bool" where
  "produces_valid_F_with_L C alg \<longleftrightarrow>
     (\<forall>adv. adversary_admissible C adv \<longrightarrow>
        (let (F', b, L) = alg (adv_i adv) (adv_e_star adv) in
           valid (adv_E adv) F' (adv_e_star adv)
           \<and> b
           \<and> L = C))"

end \<comment> \<open>context @{locale byzantineSystem}\<close>

locale byzantineSystem_with_identification = byzantineSystem +
  assumes cd_can_identify_correct:
    "produces_valid_F correct cd_alg \<Longrightarrow>
       \<exists>cd_alg'. produces_valid_F_with_L correct cd_alg'
                  \<and> (\<forall>i e. fst (cd_alg' i e) = fst (cd_alg i e))"

context byzantineSystem_with_identification
begin

subsection \<open>Constructive part: BB from an augmented CD solver\<close>

text \<open>Given an augmented CD solver, build a Black\_Box solver by projection.
The @{term bb_F} field is the CD solver's @{term F'}; @{term bb_L} is its
@{term L}; @{term bb_w} is the paper's piecewise @{const w_value} using the
augmented solver's reported @{term L}.\<close>

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
  fix V :: "'p \<Rightarrow> bool" and adv :: "'p adversary"
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

  \<comment> \<open>Sub-claim 1: F is valid.\<close>
  have claim_valid:
    "valid (adv_E adv) (bb_F ?out) (adv_e_star adv)"
    using valid_F' F_field by simp

  \<comment> \<open>Sub-claim 2: bb_w matches @{const w_value}.  Three branches
      following the piecewise definition (\S4.2): uniform-false,
      uniform-true, mixed.\<close>
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
      have "bb_w ?out = True"
        by (simp add: w_field uniform_true)
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

  \<comment> \<open>Sub-claim 3: bb_L = correct.\<close>
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
