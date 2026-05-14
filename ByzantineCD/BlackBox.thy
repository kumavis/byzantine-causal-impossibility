(*
  Title:   BlackBox.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  The Black_Box(V, E, F, e*_i) problem of Section 4.2.

  Paper coverage:
    - The Black_Box problem definition (Section 4.2, in the proof of
      Theorem 3, immediately after "The definition of the Black_Box
      problem is as follows.").
    - The piecewise w_value (the "w = 0 / 1 / CD(E, F, e*_i)" cases).
    - The "locally returns L, a list of ids of correct processes"
      output requirement.

  Deviations from the paper:

    1. The paper's Black_Box "broadcasts" the value w; we treat the
      broadcast as a record field bb_w in the output, since at this
      abstraction level we do not formalise the broadcast medium.
      The reduction R1 (consensus_reduces_to_blackbox) reads bb_w
      directly, which corresponds to "the broadcast value that it
      receives from p_min(L)" in the paper.

    2. The paper's Black_Box has w_value's else-branch as
       "CD(E, F, e*_i)" -- treating CD as a procedure call.  We
       inline this: w_value is evaluated as valid E F e_star
       directly, since CD's output (in the paper) is exactly
       valid(F).

    3. We add an explicit bb_F field to the BB output -- the
       collected history that the embedded CD sub-call produced.
       The paper does not name it; we expose it so that the
       reduction in Reductions.thy can refer to it and prove
       validity claims with respect to it.
*)

theory BlackBox
  imports CD
begin

section \<open>The broadcast value w (paper, Section 4.2)\<close>

text \<open>Paper, Section 4.2, immediately after Theorem 3's proof opens
the BB definition:
\begin{quote}
``Black\_Box(@{term V}, @{term E}, @{term F}, @{term "e_i^*"})
executed at @{term p_i} takes as input a vector @{term V} of initial
boolean values, one per process, @{term E}, @{term F}, and local
event @{term "e_i^*"} at a process @{term p_i}.  Black\_Box invoked
at @{term p_i} acts as follows.  The correct process @{term p_i}
broadcasts the value @{term w} where:
\[
w =
\begin{cases}
0 & \text{if each correct } p_j \text{ has } V[j] = 0 \\
1 & \text{if each correct } p_j \text{ has } V[j] = 1 \\
\mathit{CD}(E, F, e_i^*) & \text{otherwise}
\end{cases}
\]
and locally returns @{term L}, a list of ids of correct processes.''
\end{quote}

The CD output ``valid(F)'' is a boolean; we inline ``CD(E, F, e*_i)''
as @{const valid}@{text " E F e_star"}.\<close>

definition w_value ::
  "'p set \<Rightarrow> ('p \<Rightarrow> bool) \<Rightarrow> 'p history \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> bool" where
  "w_value C V E F e_star =
     (if (\<forall>p \<in> C. \<not> V p) then False
      else if (\<forall>p \<in> C. V p) then True
      else valid E F e_star)"

text \<open>Three helper lemmas that decompose @{const w_value} by case --
used both by the reduction R1 in @{theory_text \<open>Reductions.thy\<close>} and
by Validity arguments later.\<close>

lemma w_value_uniform_false:
  assumes "\<forall>p \<in> C. \<not> V p"
  shows   "w_value C V E F e_star = False"
  using assms unfolding w_value_def by simp

lemma w_value_uniform_true:
  assumes nonempty: "C \<noteq> {}" and all_true: "\<forall>p \<in> C. V p"
  shows "w_value C V E F e_star = True"
proof -
  from nonempty all_true have "\<not> (\<forall>p \<in> C. \<not> V p)" by blast
  with all_true show ?thesis unfolding w_value_def by simp
qed

lemma w_value_mixed:
  assumes notF: "\<not> (\<forall>p \<in> C. \<not> V p)" and notT: "\<not> (\<forall>p \<in> C. V p)"
  shows "w_value C V E F e_star = valid E F e_star"
proof -
  have step1: "(if (\<forall>p \<in> C. \<not> V p) then False
                else if (\<forall>p \<in> C. V p) then True
                else valid E F e_star)
               = (if (\<forall>p \<in> C. V p) then True else valid E F e_star)"
    using notF by (rule if_not_P)
  have step2: "(if (\<forall>p \<in> C. V p) then True else valid E F e_star)
                 = valid E F e_star"
    using notT by (rule if_not_P)
  have "w_value C V E F e_star =
          (if (\<forall>p \<in> C. \<not> V p) then False
           else if (\<forall>p \<in> C. V p) then True
           else valid E F e_star)"
    by (simp add: w_value_def)
  also have "\<dots> = (if (\<forall>p \<in> C. V p) then True else valid E F e_star)"
    by (rule step1)
  also have "\<dots> = valid E F e_star"
    by (rule step2)
  finally show ?thesis .
qed

section \<open>Black\_Box output\<close>

text \<open>A Black\_Box solver at @{term p_i} outputs three things:
\begin{itemize}
  \item the collected history @{term F'} (carried over from the
        embedded CD sub-invocation: the paper's ``else'' branch of
        @{term w} reads @{term "CD(E, F, e_i^*)"});
  \item the broadcast value @{term w} (paper: ``broadcasts the value
        @{term w}'');
  \item the set @{term L} of correct-process ids (paper: ``locally
        returns @{term L}, a list of ids of correct processes'').
\end{itemize}

\textit{Deviation:} the paper uses a list, we use a set.  This loses
nothing for the impossibility -- only the SET of correct ids matters
when we later say ``@{term "L = correct"}'' in the correctness
condition.  For the reduction R1, where the paper writes
@{term "min(L)"}, we hard-wire a single @{term p_star} instead;
see @{theory_text \<open>Reductions.thy\<close>}.\<close>

record 'p bb_output =
  bb_F :: "'p history"
  bb_w :: bool
  bb_L :: "'p set"

text \<open>Algorithmic signature: given the BB inputs (@{term P} the full
process set, @{term V} the initial-value vector, @{term e_star} the
local target event, @{term i} the invoking process), produce a
@{type bb_output}.\<close>

type_synonym 'p bb_solver =
  "'p set \<Rightarrow> ('p \<Rightarrow> bool) \<Rightarrow> 'p event \<Rightarrow> 'p \<Rightarrow> 'p bb_output"

section \<open>Correctness of Black\_Box\<close>

text \<open>Combining the paper's three demands on a Black\_Box output:
\begin{enumerate}
  \item @{term "bb_F out"} is a valid reconstruction of the
        adversary's @{term "adv_E"} (this is the embedded
        CD-correctness clause: ``Solving Black\_Box at @{term p_i}
        requires \<dots>\ solving CD'', paper Section 4.2);
  \item @{term "bb_w out"} equals @{const w_value} as paper-defined,
        evaluated at the algorithm's own @{term "bb_F out"};
  \item @{term "bb_L out"} is exactly the set @{term C} of correct
        processes (paper: ``Solving Black\_Box at @{term p_i}
        requires identifying the set of correct processes'').
\end{enumerate}\<close>

definition bb_correct_output ::
  "'p set \<Rightarrow> 'p set \<Rightarrow> ('p \<Rightarrow> bool)
     \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> 'p
     \<Rightarrow> 'p bb_output \<Rightarrow> bool" where
  "bb_correct_output P C V E e_star i out \<longleftrightarrow>
     valid E (bb_F out) e_star \<and>
     bb_w out = w_value C V E (bb_F out) e_star \<and>
     bb_L out = C"

text \<open>A BB solver @{term alg} \emph{solves} the BB problem for
@{term P}, @{term C} when, for every initial vector @{term V} and
every admissible adversary, the output is correct in the sense
above.\<close>

definition solves_BlackBox ::
  "'p set \<Rightarrow> 'p set \<Rightarrow> 'p bb_solver \<Rightarrow> bool" where
  "solves_BlackBox P C alg \<longleftrightarrow>
     (\<forall>V adv. adversary_admissible C adv \<longrightarrow>
        bb_correct_output P C V (adv_E adv)
          (adv_e_star adv) (adv_i adv)
          (alg P V (adv_e_star adv) (adv_i adv)))"

definition BlackBox_solvable :: "'p set \<Rightarrow> 'p set \<Rightarrow> bool" where
  "BlackBox_solvable P C \<longleftrightarrow> (\<exists>alg. solves_BlackBox P C alg)"

end

