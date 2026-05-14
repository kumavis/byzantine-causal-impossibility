(*
  Title:   BlackBox.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  The Black_Box(V, E, F, e*_i) problem of \S4.2.  A Black_Box invocation at
  a correct process p_i:
    * takes as input a vector V of initial boolean values, one per process,
      and the local target event e*_i;
    * broadcasts a value w computed from V and the local CD evaluation;
    * locally returns L, a list of ids of correct processes;
    * additionally, since the BB invocation implicitly subsumes a CD
      sub-call, it produces the collected history F' (paper does not name
      it but uses it in w_value's "else" branch).
*)

theory BlackBox
  imports CD
begin

section \<open>The broadcast value w (paper, \S4.2)\<close>

text \<open>The piecewise definition.  Inputs: the correct set @{term C}, the
initial-value vector @{term V}, the actual execution @{term E}, the
algorithm-collected history @{term F}, and the target event
@{term e_star}.\<close>

definition w_value ::
  "'p set \<Rightarrow> ('p \<Rightarrow> bool) \<Rightarrow> 'p history \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> bool" where
  "w_value C V E F e_star =
     (if (\<forall>p \<in> C. \<not> V p) then False
      else if (\<forall>p \<in> C. V p) then True
      else valid E F e_star)"

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

text \<open>A solver for the Black\_Box problem at @{term p_i} returns:
\begin{itemize}
  \item the collected history @{term F'} (carried over from the CD
        sub-invocation, paper \S4.2's ``else'' branch);
  \item a broadcast value @{term w}, of type @{typ bool};
  \item a list @{term L} of ids of correct processes (paper: ``locally
        returns @{term L}'').
\end{itemize}\<close>

record 'p bb_output =
  bb_F :: "'p history"
  bb_w :: bool
  bb_L :: "'p set"

text \<open>Algorithmic signature: given the inputs of Definition (\S4.2),
produce the output.\<close>

type_synonym 'p bb_solver =
  "'p set \<Rightarrow> ('p \<Rightarrow> bool) \<Rightarrow> 'p event \<Rightarrow> 'p \<Rightarrow> 'p bb_output"

section \<open>Correctness of Black\_Box\<close>

text \<open>Combining the three demands:
\begin{enumerate}
  \item @{term "bb_F out"} is valid with respect to the adversary's
        @{term "adv_E"} (the embedded CD-correctness clause);
  \item @{term "bb_w out"} equals @{term w_value} as paper-defined,
        evaluated at the algorithm's own @{term F'};
  \item @{term "bb_L out"} is exactly the set of correct processes.
\end{enumerate}\<close>

definition bb_correct_output ::
  "'p set \<Rightarrow> 'p set \<Rightarrow> ('p \<Rightarrow> bool)
     \<Rightarrow> 'p history \<Rightarrow> 'p event \<Rightarrow> 'p
     \<Rightarrow> 'p bb_output \<Rightarrow> bool" where
  "bb_correct_output P C V E e_star i out \<longleftrightarrow>
     valid E (bb_F out) e_star \<and>
     bb_w out = w_value C V E (bb_F out) e_star \<and>
     bb_L out = C"

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
