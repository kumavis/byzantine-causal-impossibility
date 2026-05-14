(*
  Title:   CD.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  The Causality Determination problem CD(E, F, e*_i) of Definition 5,
  together with explicit predicates for false positives, false
  negatives, and a CD-solver signature.

  Paper coverage:
    - Definition 5 (CD problem), Section 4.
    - The notions of false positive / false negative, Section 3 and 4.
    - "Solver" as a function of observable inputs producing (F, b),
      Section 4 ("When 1 is returned, the algorithm output matches
      God's truth and solves CD correctly").

  Deviations from the paper (deliberate):

    1. Adversary model is *explicit*.  The paper writes
       "CD(E, F, e*_i)" treating E and F as parameters in the
       problem definition.  We separate roles: the adversary fixes
       (E, e*_i, i); the algorithm produces F and a decision boolean.
       This makes the universal quantification over Byzantine
       strategies precise.

    2. Two notions of "solver".  The paper says only "valid(F) = 1".
       We split this into (a) solves_CD_decision (algorithm's claim
       agrees with its own F) and (b) produces_valid_F (the F the
       algorithm produces actually matches E).  Lemma
       produces_valid_F_implies_solves_CD_decision shows the second
       is at least as strong as the first.  The impossibility
       theorems use produces_valid_F (the paper's intended reading).

    3. CD_solvable is annotated with a communication mode tag (unicast
       / broadcast / multicast).  At the abstraction of Definition 5
       the tag is informational only -- valid(F) is mode-agnostic; the
       tag is used in Impossibility.thy to specialise the three
       theorems (T3 unicast, T4 broadcast, T5 multicast).
*)

theory CD
  imports Events
begin

section \<open>valid(F), false positives, false negatives\<close>

text \<open>Definition 5 of the paper:
\begin{quote}
``The causality determination problem @{term "CD(E, F, e_i^*)"} for
any event @{term "e_i^* \<in> T(E)"} at a correct process @{term p_i} is
to devise an algorithm to collect the execution history @{term E} as
@{term F} at @{term p_i} such that @{term "valid(F) = 1"}, where
\begin{align*}
\mathit{valid}(F) =
  \begin{cases}
    1 & \text{if } \forall e_h^x,\ e_h^x \rightarrow e_i^* |_E
                    = e_h^x \rightarrow e_i^* |_F \\
    0 & \text{otherwise}
  \end{cases}
\end{align*}''
\end{quote}

The paper later clarifies (Section 4) that the universal quantifier
ranges over \<open>T(E) \<union> T(F)\<close>: ``we have to evaluate \dots\ even if
\<open>e_h^x \<in> (T(E) \<union> T(F)) \\ T(E)\<close> because such an \<open>e_h^x\<close> is
recorded by the algorithm as part of \<open>F\<close>''.  This is the
inclusion of fake events the algorithm may have invented.

\textit{Faithfulness:} we mechanise exactly this -- the quantifier
ranges over @{term "events_of E \<union> events_of F"}, not just
@{term "events_of E"}.\<close>

definition valid :: "'p history \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> bool" where
  "valid E F e_star \<longleftrightarrow>
     (\<forall>e \<in> events_of E \<union> events_of F.
        hb_eval E e e_star = hb_eval F e e_star)"

text \<open>False negative (paper Section 4):
\begin{quote}
``\<open>\<exists> e_h^x\<close> such that \<open>e_h^x \<rightarrow> e_i^*|_E = 1\<close> \<open>\<and>\<close>
\<open>e_h^x \<rightarrow> e_i^*|_F = 0\<close> (denoting a false negative,
abbreviated FN).''
\end{quote}

\textit{Note:} the paper writes the disjunction ``either FN or FP''
when saying ``0 is returned if one of the following two cases
holds''.  We define the two cases separately and prove \<open>valid\<close>
iff neither occurs (lemma below).\<close>

definition false_negative ::
  "'p history \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> bool" where
  "false_negative E F e_star \<longleftrightarrow>
     (\<exists>e \<in> events_of E \<union> events_of F.
        hb_eval E e e_star \<and> \<not> hb_eval F e e_star)"

text \<open>False positive (paper Section 4):
\begin{quote}
``\<open>\<exists> e_h^x\<close> such that \<open>e_h^x \<rightarrow> e_i^*|_E = 0\<close> \<open>\<and>\<close>
\<open>e_h^x \<rightarrow> e_i^*|_F = 1\<close> (denoting a false positive,
abbreviated FP).''
\end{quote}\<close>

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

text \<open>In our model an adversary fixes the actual execution
@{term E}, the process @{term i} at which the determination is to be
made, and the target event @{term e_star}.  The algorithm-collected
@{term F} is \emph{not} part of the adversary record -- it is an
output of the algorithm, computed from observable inputs
(@{term i}, @{term e_star}) under the adversary's chosen Byzantine
strategy.

\textit{Deviation:} the paper's CD problem statement gives
\<open>(E, F, e_i^*)\<close> as parameters of the problem.  We separate roles
so that ``algorithm sees only its observable inputs'' is an explicit
modelling property, not buried in interpretation.

Section 3 of the paper:
\begin{quote}
``We assume that a correct process \<open>p_i\<close> needs to determine
whether \<open>e_h^x \<rightarrow> e_i^*\<close> holds and \<open>e_i^*\<close> is an event in \<open>T(E)\<close>.''
\end{quote}
We mechanise this admissibility as: \<open>E\<close> is well-formed, \<open>i\<close> is
correct (i.e.\ in \<open>C\<close>), \<open>e_star\<close> is an event at \<open>i\<close>, and
\<open>e_star\<close> actually occurs in \<open>E\<close>.\<close>

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

text \<open>A CD-solver, given the inputs the algorithm at \<open>p_i\<close> can
see -- namely the process identifier \<open>i\<close> and the target event
\<open>e_star\<close> -- produces the collected history \<open>F'\<close> it proposes plus
a boolean ``claim of validity''.  Paper Section 4:
\begin{quote}
``When 1 is returned, the algorithm output matches God's truth and
solves CD correctly.  Thus, returning 1 indicates that the problem
has been solved correctly by the algorithm using \<open>F\<close>.''
\end{quote}

\textit{Deviation:} the paper does not pin down whether the algorithm
sees \<open>E\<close> during its computation.  Our type signature commits to
``algorithm sees only (\<open>i\<close>, \<open>e_star\<close>); \<open>F\<close> is its constructed
view'' -- which is the strongest reading consistent with the paper's
notion of \<open>F\<close> as ``the execution history at \<open>p_i\<close> as perceived
and collected by the algorithm'' (Section 3).\<close>

type_synonym 'p cd_solver =
  "'p \<Rightarrow> 'p event \<Rightarrow> 'p history \<times> bool"

text \<open>Two notions of correctness in increasing strength.

\<open>solves_CD_decision\<close> is the weaker form: the algorithm's boolean
output agrees with \<open>valid\<close> \emph{computed against the algorithm's
own \<open>F'\<close>}.  An algorithm satisfying this is internally consistent
-- it returns 1 iff its \<open>F'\<close> is a valid reconstruction of
\emph{some} execution.

\<open>produces_valid_F\<close> is the paper's intended reading: \<open>F'\<close> actually
matches the adversary's true \<open>E\<close> in the sense of Definition 5.
The impossibility theorems are stated about this stronger predicate;
the lemma below shows it always entails the weaker form (so
impossibility of one entails impossibility of the other).\<close>

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

text \<open>From a \<open>produces_valid_F\<close> solver we trivially obtain a
\<open>solves_CD_decision\<close> solver by always returning the boolean \<open>True\<close>:
if \<open>F'\<close> is genuinely valid, then claiming ``valid'' is correct.\<close>

lemma produces_valid_F_implies_solves_CD_decision:
  assumes "produces_valid_F C alg"
  shows "\<exists>alg'. solves_CD_decision C alg'"
proof -
  define alg' where
    "alg' \<equiv> (\<lambda>i e. (fst (alg i e), True))"
  have "solves_CD_decision C alg'"
  proof (unfold solves_CD_decision_def, intro allI impI)
    fix adv
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
  thus ?thesis by blast
qed

section \<open>Communication mode: unicast / broadcast / multicast\<close>

text \<open>Section 2 of the paper:
\begin{quote}
``There are three modes of communication: multicast, unicast, and
broadcast.  In multicast, a message is sent to a group \<open>G\<close> of
processes corresponding to some subset of \<open>P\<close>.  A unicast is a
multicast where \<open>|G| = 1\<close>.  A broadcast is a multicast where
\<open>G = P\<close>.''
\end{quote}

We carry the mode as a datatype tag.

\textit{Deviation:} our \<open>CD_solvable\<close> predicate is \emph{not}
sensitive to the mode tag -- it just existentially quantifies over
algorithms producing valid \<open>F\<close>, and the \<open>valid\<close>
predicate is mode-agnostic at the level of Definition 5.  This is a
deliberate simplification: at this abstraction the modes only differ
in what an adversary may do (the adversary in broadcast mode commits
to sending to all processes, etc.), not in the validity criterion
itself.  The three impossibility theorems are nevertheless stated
separately so a richer development that refines the mode (e.g.\
adding BRB-as-layer for Theorem 4) can specialise the proof without
re-stating the theorem.\<close>

datatype comm_mode = Unicast | Broadcast | Multicast

definition CD_solvable :: "comm_mode \<Rightarrow> 'p set \<Rightarrow> bool" where
  "CD_solvable m C \<longleftrightarrow> (\<exists>alg. produces_valid_F C alg)"

end
