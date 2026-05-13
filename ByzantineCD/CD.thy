(*
  Title:   CD.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  The Causality Determination problem CD(E, F, e*_i) (Definition 5),
  together with explicit predicates for false positives and false negatives
  and an adversary-explicit notion of "solver".

  Modelling choices:
   * The adversary specifies the actual execution E (Goddess-truth) and the
     target event e*_i at a correct process p_i.
   * The algorithm outputs a collected history F (the F_i union of paper) and
     a boolean claim of validity.
   * "produces_valid_F" demands that the algorithm's collected F actually
     matches E in the sense of Definition 5.
*)

theory CD
  imports Events
begin

section \<open>valid(F), false positives, false negatives\<close>

text \<open>Definition~5 of the paper:
\[ \mathit{valid}(F) =
   \begin{cases} 1 & \text{if } \forall e_h^x.\
                                e_h^x \rightarrow e_i^* |_E
                                = e_h^x \rightarrow e_i^* |_F \\
                 0 & \text{otherwise}
   \end{cases}. \]
The paper clarifies that the universal quantifier ranges over
@{term "T(E) \<union> T(F)"} (``we have to evaluate \dots\ even if
\<open>e_h^x \<in> (T(E) \<union> T(F)) \\ T(E)\<close> because such an \<open>e_h^x\<close> is recorded by the
algorithm as part of \<open>F\<close>'').\<close>

definition valid :: "'p history \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> bool" where
  "valid E F e_star \<longleftrightarrow>
     (\<forall>e \<in> events_of E \<union> events_of F.
        hb_eval E e e_star = hb_eval F e e_star)"

text \<open>False negatives and false positives, named exactly as in Definition~5.\<close>

definition false_negative ::
  "'p history \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> bool" where
  "false_negative E F e_star \<longleftrightarrow>
     (\<exists>e \<in> events_of E \<union> events_of F.
        hb_eval E e e_star \<and> \<not> hb_eval F e e_star)"

definition false_positive ::
  "'p history \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> bool" where
  "false_positive E F e_star \<longleftrightarrow>
     (\<exists>e \<in> events_of E \<union> events_of F.
        \<not> hb_eval E e e_star \<and> hb_eval F e e_star)"

lemma valid_iff_no_FP_FN:
  shows "valid E F e_star
           \<longleftrightarrow> \<not> false_negative E F e_star
              \<and> \<not> false_positive E F e_star"
proof -
  have "valid E F e_star
          \<longleftrightarrow> (\<forall>e \<in> events_of E \<union> events_of F.
                 hb_eval E e e_star = hb_eval F e e_star)"
    by (simp add: valid_def)
  also have "\<dots> \<longleftrightarrow> \<not> false_negative E F e_star
                  \<and> \<not> false_positive E F e_star"
    by (auto simp: false_negative_def false_positive_def)
  finally show ?thesis .
qed

section \<open>Adversary model\<close>

text \<open>An adversary in our model fixes the actual execution @{term E}, the
process @{term i} at which the determination is to be made, and the target
event @{term e_star}.  The collected history @{term F} is NOT specified by
the adversary: it is an output of the algorithm under the adversary's
strategy.  At our abstraction level we treat the algorithm as a function of
@{term i} and @{term e_star} that produces @{term F} as part of its output;
the dependence on the adversary's Byzantine strategy is implicit and is
exactly what the impossibility argument quantifies over.\<close>

record 'p adversary =
  adv_E       :: "'p history"
  adv_e_star  :: "'p event"
  adv_i       :: 'p

definition adversary_admissible ::
  "'p set \<Rightarrow> 'p adversary \<Rightarrow> bool" where
  "adversary_admissible C adv \<longleftrightarrow>
     wf_history (adv_E adv) \<and>
     adv_i adv \<in> C \<and>
     proc_of (adv_e_star adv) = adv_i adv \<and>
     adv_e_star adv \<in> events_of (adv_E adv)"

section \<open>CD-solver signature\<close>

text \<open>A CD-solver outputs the collected history @{term F'} and a boolean
claim of validity.  The interpretation of the boolean is the value the paper
calls ``$\mathit{valid}(F)$''; the algorithm \emph{wants} to return 1.\<close>

type_synonym 'p cd_solver =
  "'p \<Rightarrow> 'p event \<Rightarrow> 'p history \<times> bool"

text \<open>Two notions of correctness, in increasing strength.

  @{term solves_CD_decision}: the boolean output of the algorithm is correct
  \emph{relative to the algorithm's own @{term F'}}, i.e.\ @{term b}
  equals @{term "valid (adv_E adv) F' (adv_e_star adv)"}.

  @{term produces_valid_F}: the algorithm's @{term F'} \emph{actually} matches
  the truth @{term "adv_E adv"} in the sense of Definition~5.  This is the
  paper's intended ``correctly solves CD'' (``When 1 is returned, the
  algorithm output matches God's truth and solves CD correctly'').\<close>

definition solves_CD_decision ::
  "'p set \<Rightarrow> 'p cd_solver \<Rightarrow> bool" where
  "solves_CD_decision C alg \<longleftrightarrow>
     (\<forall>adv. adversary_admissible C adv \<longrightarrow>
        (let (F', b) = alg (adv_i adv) (adv_e_star adv) in
           b = valid (adv_E adv) F' (adv_e_star adv)))"

definition produces_valid_F ::
  "'p set \<Rightarrow> 'p cd_solver \<Rightarrow> bool" where
  "produces_valid_F C alg \<longleftrightarrow>
     (\<forall>adv. adversary_admissible C adv \<longrightarrow>
        (let (F', _) = alg (adv_i adv) (adv_e_star adv) in
           valid (adv_E adv) F' (adv_e_star adv)))"

lemma produces_valid_F_implies_solves_CD_decision:
  assumes "produces_valid_F C alg"
  shows "\<exists>alg'. solves_CD_decision C alg'"
proof -
  define alg' :: "'p cd_solver" where
    "alg' i e \<equiv> (fst (alg i e), True)"
  have "solves_CD_decision C alg'"
  proof (unfold solves_CD_decision_def, intro allI impI)
    fix adv :: "'p adversary"
    assume A: "adversary_admissible C adv"
    have "fst (alg' (adv_i adv) (adv_e_star adv))
            = fst (alg (adv_i adv) (adv_e_star adv))"
      by (simp add: alg'_def)
    moreover from A assms
    have "valid (adv_E adv) (fst (alg (adv_i adv) (adv_e_star adv)))
                (adv_e_star adv)"
      by (auto simp: produces_valid_F_def Let_def split: prod.split)
    ultimately show
      "(let (F', b) = alg' (adv_i adv) (adv_e_star adv) in
           b = valid (adv_E adv) F' (adv_e_star adv))"
      by (simp add: alg'_def Let_def)
  qed
  thus ?thesis ..
qed

section \<open>Communication mode: unicast / broadcast / multicast\<close>

text \<open>The paper distinguishes three modes of communication (Section~2).
Unicasts are the special case of multicast with @{term "|G| = 1"};
broadcasts are the special case with @{term "G = P"}.  We carry the mode as
a tag, used in @{theory_text Impossibility.thy} to specialise the three
impossibility theorems.\<close>

datatype comm_mode = Unicast | Broadcast | Multicast

definition CD_solvable :: "comm_mode \<Rightarrow> 'p set \<Rightarrow> bool" where
  "CD_solvable m C \<longleftrightarrow> (\<exists>alg. produces_valid_F C alg)"

text \<open>The communication mode does not appear on the right-hand side because
at the abstraction level of Definition~5 the validity check is
mode-agnostic.  The mode enters only when relating CD to Black\_Box and
Consensus (the reductions are mode-specific in detail but identical in
shape; the broadcast and multicast variants merely strengthen what the
adversary may do).  This is the design that lets Theorems~4 and~5 of the
paper share the proof skeleton of Theorem~3.\<close>

end
