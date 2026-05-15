(*
  Title:   BlackBox_Unsolvable.thy
  Author:  Formalization of Misra & Kshemkalyani, "Byzantine-tolerant
           detection of causality" (Parallel Computing 124, 2025).

  Discharges the meta-level hypothesis "\<not> BlackBox_solvable procs
  correct" (named bb_unsolv in Impossibility.thy) via a direct
  reduction to Theorem 1 (CD_FN_unavoidable, Theorems_1_2.thy) -- not
  via FLP.

  The observation: solves_BlackBox already demands that bb_F satisfies
  valid(E, bb_F, e_star) for every admissible adversary -- which is
  exactly the produces_valid_F property a CD-solver would have to
  satisfy.  Any BlackBox solver therefore induces a CD-solver of type
  'p cd_solver by projection.  Theorem 1 (CD_FN_unavoidable) says no
  such CD-solver exists -- given the standard byz_cor_distinct and a
  mild finiteness condition on the algorithm's output F.  We pull this
  back through the projection to obtain a contradiction with the
  assumed BlackBox solvability.

  This shortcut bypasses the paper's "Consensus \<preceq> BlackBox \<preceq> CD +
  FLP" chain entirely.  The chain is still mathematically interesting
  (and is preserved in FLP_Consensus.thy as the proven FLP-style
  consensus impossibility), but for the headline CD impossibility we
  only need Theorem 1, the BB-to-CD projection, and a finiteness side
  condition.
*)

theory BlackBox_Unsolvable
  imports BlackBox Theorems_1_2
begin

context byzantineSystem
begin

theorem BlackBox_unsolvable:
  assumes byz_ne: "byzantine \<noteq> {}"
      and cor_ne: "correct \<noteq> {}"
      and fin_bb_F:
        "\<forall>alg p_i_in.
           solves_BlackBox procs correct alg \<longrightarrow>
             finite (events_of
                       (bb_F (alg procs (\<lambda>_. False)
                                   (Internal p_i_in 2) p_i_in)))"
  shows "\<not> BlackBox_solvable procs correct"
proof
  assume BB: "BlackBox_solvable procs correct"
  then obtain bb_alg :: "'p bb_solver"
    where solver: "solves_BlackBox procs correct bb_alg"
    by (auto simp: BlackBox_solvable_def)

  \<comment> \<open>Project the BB-solver onto a CD-solver: take \<open>F\<close> from \<open>bb_F\<close>
      at the fixed input vector \<open>(\<lambda>_. False)\<close>, and report decision
      \<open>True\<close>.\<close>
  define cd :: "'p cd_solver" where
    "cd \<equiv> (\<lambda>i e. (bb_F (bb_alg procs (\<lambda>_. False) e i), True))"

  have cd_fst:
    "\<And>i e. fst (cd i e) = bb_F (bb_alg procs (\<lambda>_. False) e i)"
    by (simp add: cd_def)

  \<comment> \<open>Step 1: the projected CD-solver produces valid F.\<close>
  have valid_cd: "produces_valid_F correct cd"
  proof (unfold produces_valid_F_def, intro allI impI)
    fix adv :: "'p adversary"
    assume adm: "adversary_admissible correct adv"
    from solver adm have
      "bb_correct_output procs correct (\<lambda>_. False)
         (adv_E adv) (adv_e_star adv) (adv_i adv)
         (bb_alg procs (\<lambda>_. False) (adv_e_star adv) (adv_i adv))"
      by (auto simp: solves_BlackBox_def)
    hence valid_at:
      "valid (adv_E adv)
             (bb_F (bb_alg procs (\<lambda>_. False)
                           (adv_e_star adv) (adv_i adv)))
             (adv_e_star adv)"
      by (simp add: bb_correct_output_def)
    show "let (F', _) = cd (adv_i adv) (adv_e_star adv) in
            valid (adv_E adv) F' (adv_e_star adv)"
      using valid_at by (simp add: cd_def Let_def)
  qed

  \<comment> \<open>Step 2: package the byz_cor_distinct hypothesis Theorem 1 wants.\<close>
  have byz_cor_distinct:
    "\<exists>p_i p_b. p_i \<in> correct \<and> p_b \<in> byzantine \<and> p_b \<noteq> p_i"
  proof -
    obtain p_i where pi: "p_i \<in> correct" using cor_ne by blast
    obtain p_b where pb: "p_b \<in> byzantine" using byz_ne by blast
    have "p_i \<noteq> p_b"
      using pi pb partition_disj by blast
    thus ?thesis using pi pb by blast
  qed

  \<comment> \<open>Step 3: the projected CD-solver satisfies the finiteness side
      condition Theorem 1 wants.\<close>
  have fin_cd:
    "\<forall>p_i_in. finite (events_of (fst (cd p_i_in (Internal p_i_in 2))))"
  proof
    fix p_i_in :: 'p
    have "fst (cd p_i_in (Internal p_i_in 2))
            = bb_F (bb_alg procs (\<lambda>_. False) (Internal p_i_in 2) p_i_in)"
      by (rule cd_fst)
    moreover have
      "finite (events_of
                 (bb_F (bb_alg procs (\<lambda>_. False)
                               (Internal p_i_in 2) p_i_in)))"
      using fin_bb_F solver by blast
    ultimately show
      "finite (events_of (fst (cd p_i_in (Internal p_i_in 2))))"
      by simp
  qed

  \<comment> \<open>Step 4: Theorem 1 says no CD-solver avoids false negatives.\<close>
  obtain adv :: "'p adversary" where
    adm: "adversary_admissible correct adv"
    and FN: "false_negative (adv_E adv)
                            (fst (cd (adv_i adv) (adv_e_star adv)))
                            (adv_e_star adv)"
    using CD_FN_unavoidable[where alg = cd, OF byz_cor_distinct fin_cd]
    by blast

  \<comment> \<open>Step 5: false negative contradicts produces_valid_F.\<close>
  have valid_at_adv:
    "valid (adv_E adv)
           (fst (cd (adv_i adv) (adv_e_star adv)))
           (adv_e_star adv)"
    using valid_cd adm
    by (auto simp: produces_valid_F_def Let_def split: prod.split)
  hence no_FN:
    "\<not> false_negative (adv_E adv)
                       (fst (cd (adv_i adv) (adv_e_star adv)))
                       (adv_e_star adv)"
    using valid_iff_no_FP_FN by blast
  from FN no_FN show False by contradiction
qed

end \<comment> \<open>context @{locale byzantineSystem}\<close>

end
