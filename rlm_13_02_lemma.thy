theory rlm_13_02_lemma
  imports "RLM_learn"
begin

context learning_basics1
begin


text\<open>S_index is a set where the i-th data point in S is replaced with an arbitrary one\<close>
definition S_index :: "(nat \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> nat \<Rightarrow> ('b \<times> 'c) \<Rightarrow> (nat \<Rightarrow> ('b * 'c))" where
  "S_index S' i z = S'(i := z)"

lemma S_index_similar : "\<forall>i. \<forall> j \<noteq> i. l v (S' j) = l v ((S_index S' i z) j)"
  by (simp add: S_index_def)

lemma sum_split :"\<forall>i \<in>{0..<n}. sum f {0..<n} = sum f {0..<i} + f i + sum f {i+1..<n}"
  for f :: "nat \<Rightarrow> real"
proof 
  fix i assume"i \<in>{0..<n}"
  show "sum f {0..<n} = sum f {0..<i} + f i + sum f {i+1..<n}"
  proof -
    have 1: "({0..<i} \<inter> {i..<n}) = {} " using `i \<in>{0..<n}`  using ivl_disj_int_two(3) by blast

    have "{0..<n} = ({0..<i} \<union> {i..<n})" using `i \<in>{0..<n}` by auto
    then  have "sum f {0..<n} = sum f ({0..<i} \<union> {i..<n})" by simp
    also have "sum f ({0..<i} \<union> {i..<n}) = 
      sum f {0..<i} + sum f {i..<n} - sum f ({0..<i} \<inter> {i..<n})"
      using sum_Un by blast
    also have "sum f {0..<i} + sum f {i..<n} - sum f ({0..<i} \<inter> {i..<n}) = 
              sum f {0..<i} + sum f {i..<n}" using 1 by auto
    also have " sum f {0..<i} + sum f {i..<n} = 
          sum f {0..<i} + f i + sum f {i+1..<n}" 
      using \<open>i \<in> {0..<n}\<close> sum.atLeast_Suc_lessThan by fastforce
    finally show "sum f {0..<n} = sum f {0..<i} + f i + sum f {i+1..<n}" by auto
  qed
qed

lemma S_index_eq_without_i : " i \<notin> A \<Longrightarrow>
     sum (\<lambda> j.  l v (S' j)) A = sum (\<lambda> j. l v ((S_index S' i z) j)) A"
proof -
  assume  "i \<notin> A" 
  then  show "sum (\<lambda> j.  l v (S' j)) A = sum (\<lambda> j. l v ((S_index S' i z) j)) A" 
    by (metis (mono_tags, lifting) S_index_similar  sum.cong)
qed



lemma restrict: "integral\<^sup>L M f = integral\<^sup>L M   (restrict f (space M))" 
  by (metis Bochner_Integration.integral_cong restrict_apply)

lemma restrict_nn: "integral\<^sup>N M f = integral\<^sup>N M   (restrict f (space M))" 
  by (metis nn_integral_cong restrict_apply)


lemma integral_measure_pmf_real_indicator:
  fixes f :: "'e \<Rightarrow> real"
  shows "(\<integral>x. f x \<partial>measure_pmf M) =  (\<integral>x. f x * indicator M x \<partial>measure_pmf M)"
proof -
  have "\<And>y. y \<in> set_pmf M \<Longrightarrow> f y = f y * 1" 
    by linarith
  then show "(\<integral>x. f x \<partial>measure_pmf M) = (\<integral>x. f x * indicator M x \<partial>measure_pmf M)"
    by (intro integral_cong_AE) (auto split: split_indicator simp: AE_measure_pmf_iff)
qed

lemma nn_integral_measure_pmf_real_indicator:
  fixes f :: "'e \<Rightarrow> real"
  shows "(\<integral>\<^sup>+ x. f x \<partial>measure_pmf M) =  (\<integral>\<^sup>+ x. f x * indicator M x \<partial>measure_pmf M)"
proof -
  have "\<And>y. y \<in> set_pmf M \<Longrightarrow> f y = f y * 1" 
    by linarith
  then show "(\<integral>\<^sup>+ x. f x \<partial>measure_pmf M) = (\<integral>\<^sup>+ x. f x * indicator M x \<partial>measure_pmf M)"
    by (intro nn_integral_cong_AE) (auto split: split_indicator simp: AE_measure_pmf_iff)
qed



lemma asd:
  fixes f :: "'e \<Rightarrow> real"
  fixes M :: " 'e pmf"
  shows "integral\<^sup>L (restrict_space M M) f = integral\<^sup>L M f" 
  by (simp add: integral_pmf_restrict)

lemma asd1: 
  fixes f :: "'e \<Rightarrow> real"
  fixes M :: " 'e pmf"
  shows "integral\<^sup>L (restrict_space M M) f = integral\<^sup>L M (restrict f (set_pmf M))"
  by (metis UNIV_I asd restrict sets_measure_pmf space_restrict_space2)


lemma pmf_restrict:
  fixes f :: "'e \<Rightarrow> real"
  shows "measure_pmf.expectation M (\<lambda> x. f x) = measure_pmf.expectation M (\<lambda> x\<in>M. f x)" 
  using asd asd1  by metis


lemma nn_integral_pmf_restrict:
  fixes f::"'e \<Rightarrow> real"
  shows "(\<integral>\<^sup>+ x. f x \<partial>measure_pmf M) = (\<integral>\<^sup>+ x. f x \<partial>restrict_space M M)"
  by (auto intro!: nn_integral_cong_AE simp add: nn_integral_restrict_space AE_measure_pmf_iff)

lemma asd4: 
  fixes f :: "'e \<Rightarrow> real"
  fixes M :: " 'e pmf"
  shows "integral\<^sup>N (restrict_space M M) f = integral\<^sup>N M (restrict f (set_pmf M))"
  by (smt UNIV_I nn_integral_cong nn_integral_pmf_restrict restrict_apply' sets_measure_pmf space_restrict_space2)

lemma asd5:
  fixes f :: "'e \<Rightarrow> real"
  fixes M :: " 'e pmf"
  shows "integral\<^sup>N M (restrict f (set_pmf M)) = integral\<^sup>N M f"
  using nn_integral_pmf_restrict asd4 by metis




lemma min_in_H: "S \<in> (Samples n D) \<longrightarrow>  (ridge_mine S k) \<in> H"
proof 
  assume "S \<in> (Samples n D)"
  let ?P = "(\<lambda> h. h \<in> ridge_argmin S k)"
  have "\<exists>h. is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) h" using 
      `S \<in> (Samples n D)` ridge_convex1 convex_has_min nnH convH by auto

  have "ridge_argmin S k \<noteq> {}" unfolding ridge_argmin_def using nnH convH 
    using \<open>\<exists>h. is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) h\<close> by blast
  have "\<exists>h. ?P h" unfolding ridge_argmin_def  using nnH
    using \<open>\<exists>h. is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) h\<close> by blast
  have "(ridge_mine S k) \<in> (ridge_argmin S k)" unfolding ridge_mine_def using 
      someI2[of "?P" "(ridge_mine S k)" ?P ]
    by (metis (no_types, lifting) Collect_cong Set.empty_def \<open>ridge_argmin S k \<noteq> {}\<close> mem_Collect_eq ridge_argmin_def verit_sko_ex_indirect)
  then show "(ridge_mine S k) \<in> H" 
    by (simp add: is_arg_min_linorder ridge_argmin_def)
qed


lemma integrable_D:"integrable D (\<lambda> z. l (ridge_mine S k) z)" 
      sorry

lemma integrable_Dn: "integrable (Samples n D)  (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. ((\<lambda> z. l (ridge_mine S k) z) x) \<partial>D))" 
  sorry

lemma integrable_pair: "integrable (pair_pmf (Samples n D) D) (\<lambda> (S,z). l (ridge_mine S k) z)" 
   sorry


lemma truncated_same_min:
  shows "\<forall> S. (ridge_mine (truncated_S S n) k)  =  (ridge_mine  S k)"
proof 
  fix S
  show "(ridge_mine (truncated_S S n) k)  =  (ridge_mine  S k)"
    proof -
      let ?S' = "(S(n:=undefined))"
      have "(ridge_mine ?S' k) = (SOME h. h \<in> {h. is_arg_min (ridge_fun ?S' k) (\<lambda>s. s\<in>H) h})"
        unfolding ridge_mine_def unfolding ridge_argmin_def by auto
      have "(ridge_mine S k) = (SOME h. h \<in> {h. is_arg_min (ridge_fun S k) (\<lambda>s. s\<in>H) h})"
        unfolding ridge_mine_def unfolding ridge_argmin_def by auto

      have "ridge_fun S k = ridge_fun ?S' k" 
      proof 
        fix xa 
        have"train_err_loss S n l xa =  train_err_loss ?S' n l xa"
        proof -
          have "train_err_loss S n l xa = sum (\<lambda>i. l xa (S i) ) {0..<n} / n" 
            unfolding train_err_loss_def by auto
          have "train_err_loss ?S' n l xa = sum (\<lambda>i. l xa (?S' i) ) {0..<n} / n"
            unfolding train_err_loss_def by auto
          then show ?thesis
            using \<open>train_err_loss S n l xa = (\<Sum>i = 0..<n. l xa (S i)) / real n\<close> by auto
        qed
        then show "ridge_fun S k xa = ridge_fun ?S' k xa" by simp
      qed
  then show ?thesis 
        using \<open>ridge_mine (S(n := undefined)) k = (SOME h. h \<in> {h. is_arg_min (ridge_fun (S(n := undefined)) k) (\<lambda>s. s \<in> H) h})\<close> 
              \<open>ridge_mine S k = (SOME h. h \<in> {h. is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) h})\<close> 
        by (metis learning_basics1.truncated_S_def learning_basics1_axioms) 
    qed
  qed

lemma truncated_same_expect: 
    " measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (truncated_S Sz n) k) (Sz n)) =
    measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine  Sz k) (Sz n))"
using truncated_same_min by auto


definition swapped_S1 :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> ('b * 'c))" where
  "swapped_S1 S' i =  S'(i:= S' n, n:= S' i) " 

lemma pmf_swapped_same:
"\<forall> i \<in> {0..<n+1}. pmf (Samples (n+1) D) f  = pmf (Samples (n+1) D) (f(i:=(f n),n:=(f i)))"
proof 
  fix i
  assume "i \<in> {0..<n+1}"
  let ?f' = "(f(i:=(f n),n:=(f i)))"
  have "finite {0..<n+1}" by auto
  have "Samples (n+1) D = Pi_pmf {0..<n+1} undefined (\<lambda>_. D)" unfolding Samples_def by auto
  have "finite {0..<n+1}" by auto
  then  have "pmf  (Pi_pmf {0..<n+1} undefined (\<lambda>_. D)) f = 
       (if (\<forall>x. x \<notin> {0..<n+1} \<longrightarrow> f x = undefined) then
           \<Prod>x\<in>{0..<n+1}. pmf ((\<lambda>_. D) x) (f x) else 0)"
    using pmf_Pi[of "{0..<n+1}" undefined "(\<lambda>_. D)" f] by blast
  then have 1: "pmf (Samples (n+1) D) f = (if (\<forall>x. x \<notin> {0..<n+1} \<longrightarrow> f x = undefined) then
           \<Prod>x\<in>{0..<n+1}. pmf ((\<lambda>_. D) x) (f x) else 0)"
    by (simp add: Samples_def)
   have "pmf  (Pi_pmf {0..<n+1} undefined (\<lambda>_. D)) ?f' = 
       (if (\<forall>x. x \<notin> {0..<n+1} \<longrightarrow> ?f' x = undefined) then
           \<Prod>x\<in>{0..<n+1}. pmf ((\<lambda>_. D) x) (?f' x) else 0)"
    using pmf_Pi[of "{0..<n+1}" undefined "(\<lambda>_. D)" "?f'"] by blast
   then have 2: "pmf (Samples (n+1) D) ?f' = 
        (if (\<forall>x. x \<notin> {0..<n+1} \<longrightarrow> ?f' x = undefined) then
           \<Prod>x\<in>{0..<n+1}. pmf ((\<lambda>_. D) x) (?f' x) else 0)"
     by (simp add: Samples_def)
  show "pmf (Samples (n+1) D) f  = pmf (Samples (n+1) D) ?f'"
  proof (cases "(\<forall>x. x \<notin> {0..<n+1} \<longrightarrow> f x = undefined)")
    case True
    have "pmf (Samples (n+1) D) f = (\<Prod>x\<in>{0..<n+1}. pmf D (f x))" using True 1 by auto
   
     have "(\<forall>x. x \<notin> {0..<n+1} \<longrightarrow>?f' x = undefined)"
    proof
      fix x
      show "x \<notin> {0..<n+1} \<longrightarrow>?f' x = undefined"
      proof
        assume "x \<notin> {0..<n+1}"
        then have " f x = undefined" 
          using True by blast
        have "\<forall> y. y \<noteq> i \<and> y \<noteq> n \<longrightarrow>?f' y = f y" by simp
        then have "x \<noteq> i \<and> x \<noteq> n" using `x \<notin> {0..<n+1}`
        using \<open>i \<in> {0..<n + 1}\<close> by auto
      then show "?f' x = undefined" 
        by (simp add: \<open>f x = undefined\<close>)
    qed
  qed
  then have "pmf (Samples (n+1) D) ?f' =
     (\<Prod>x\<in>{0..<n+1}. pmf D (?f' x))"  using "2" by auto
  have "(\<Prod>x\<in>{0..<n+1}. pmf D (f x)) =
        (\<Prod>x\<in>{0..<n+1}. pmf D (?f' x))"
  proof(cases "i=n")
    case True
    then show ?thesis by auto
  next
    case False
    have " (\<Prod>x\<in>({0..<n+1} - {i,n}). pmf D (?f' x)) * (\<Prod>x\<in>{i,n}.(pmf D (?f' x))) = 
                (\<Prod>x\<in>({0..<n+1} - {i,n}). pmf D (f x)) * (\<Prod>x\<in>{i,n}.(pmf D (f x)))"
      using prod.union_disjoint False by auto
    then show "(\<Prod>x\<in>{0..<n+1}. pmf D (f x)) =
        (\<Prod>x\<in>{0..<n+1}. pmf D (?f' x))"
      by (smt One_nat_def \<open>finite {0..<n + 1}\<close> \<open>i \<in> {0..<n + 1}\<close> add.right_neutral add_Suc_right atLeastLessThan_iff insertE insert_absorb insert_not_empty le_trans lessI n_pos prod.subset_diff subsetI zero_le_one)
  qed
  then show ?thesis
    using \<open>pmf (Samples (n + 1) D) (f(i := f n, n := f i)) = (\<Prod>x = 0..<n + 1. pmf D ((f(i := f n, n := f i)) x))\<close> \<open>pmf (Samples (n + 1) D) f = (\<Prod>x = 0..<n + 1. pmf D (f x))\<close> by linarith
next
  case False
  have "pmf (Samples (n+1) D) f = 0"  using False "1" by auto
  also have "pmf (Samples (n+1) D) ?f' = 0" using 2 False 
    by (metis (no_types, lifting) One_nat_def \<open>i \<in> {0..<n + 1}\<close> add.right_neutral add_Suc_right atLeastLessThan_iff fun_upd_other lessI zero_le)
   finally  show ?thesis  by linarith
 qed
qed

lemma "\<forall>S \<in> (Samples q D).  ennreal (integral\<^sup>L  D (\<lambda> z. l (ridge_mine S k) z)) = 
        (\<integral>\<^sup>+ x. ((\<lambda> z. l (ridge_mine S k) z) x) \<partial>D)"
  oops

lemma inj_swapped: "inj (\<lambda> S. swapped_S1 S i)"
proof (rule)
  fix x
  fix y
  show " x \<in> UNIV \<Longrightarrow> y \<in> UNIV \<Longrightarrow> swapped_S1 x i = swapped_S1 y i \<Longrightarrow> x = y"
  proof
  fix xa
  assume "x \<in> UNIV"
  assume "y \<in> UNIV"
  assume "swapped_S1 x i = swapped_S1 y i"
  have "x (i:= x n, n:= x i) = y(i:= y n, n:= y i)" 
    using \<open>swapped_S1 x i = swapped_S1 y i\<close> swapped_S1_def by auto
  show "x xa = y xa" 
    by (smt \<open>x(i := x n, n := x i) = y(i := y n, n := y i)\<close> fun_upd_eqD fun_upd_triv fun_upd_twist)
qed
qed

lemma map_pmf_swap_same: 
"\<forall>i \<in> {0..<n+1}. pmf (Samples (n+1) D) x = pmf (map_pmf (\<lambda> S. swapped_S1 S i) (Samples (n+1) D)) x" 
proof 
  fix i
  assume "i \<in> {0..<n+1}"
  let ?M = "(Samples (n+1) D)"
  let ?f = "(\<lambda> S. swapped_S1 S i)"
  have "pmf ?M (swapped_S1 x i) = pmf ?M x" using  pmf_swapped_same swapped_S1_def 
    by (metis \<open>i \<in> {0..<n + 1}\<close>)
  have "pmf ?M x = pmf (map_pmf ?f ?M) (?f x)" using inj_swapped pmf_map_inj' by metis
  have "pmf (map_pmf ?f ?M) (?f x) = pmf (map_pmf ?f ?M) (swapped_S1 x i)" by auto
  then have 1: "pmf ?M (swapped_S1 x i) = pmf (map_pmf ?f ?M) (swapped_S1 x i)"  
    using \<open>pmf (Samples (n + 1) D) (swapped_S1 x i) = pmf (Samples (n + 1) D) x\<close> \<open>pmf (Samples (n + 1) D) x = pmf (map_pmf (\<lambda>S. swapped_S1 S i) (Samples (n + 1) D)) (swapped_S1 x i)\<close> by linarith

  have "pmf ?M (swapped_S1 x i) = pmf (map_pmf ?f ?M) (?f (swapped_S1 x i))" 
    using  inj_swapped pmf_map_inj' by metis

  then have " pmf (map_pmf ?f ?M) (swapped_S1 x i) =  pmf (map_pmf ?f ?M) x" 
    by (smt 1 fun_upd_apply fun_upd_triv fun_upd_twist fun_upd_upd swapped_S1_def)

  then show "pmf ?M x = pmf (map_pmf ?f ?M) x" using 1 
  using \<open>pmf (Samples (n + 1) D) x = pmf (map_pmf (\<lambda>S. swapped_S1 S i) (Samples (n + 1) D)) (swapped_S1 x i)\<close> by linarith
qed
  
lemma expect_sample_swap_same:
  fixes f :: "_ \<Rightarrow> real"
  assumes i_le_n: "i \<in> {0..<n+1}"
 shows "measure_pmf.expectation (Samples (n+1) D) f  =
           measure_pmf.expectation (map_pmf (\<lambda> S. swapped_S1 S i) (Samples (n+1) D)) f"
proof -
  let ?M = "(Samples (n+1) D)"
  
  have "measure_pmf.expectation ?M f  = 
        infsetsum (\<lambda>x. pmf ?M x * f x) UNIV" using pmf_expectation_eq_infsetsum by auto
  also have " infsetsum (\<lambda>x. pmf ?M x * f x) UNIV =
             infsetsum (\<lambda>x. pmf  (map_pmf (\<lambda> S. swapped_S1 S i) ?M) x * f x) UNIV"
       using  map_pmf_swap_same i_le_n  by simp
  also have " infsetsum (\<lambda>x. pmf  (map_pmf (\<lambda> S. swapped_S1 S i) ?M) x * f x) UNIV =
        measure_pmf.expectation (map_pmf (\<lambda> S. swapped_S1 S i) ?M) f "
       using pmf_expectation_eq_infsetsum[of "(map_pmf (\<lambda> S. swapped_S1 S i) ?M)" f] by auto   
     finally show ?thesis by auto
   qed

lemma expect_f_swap_same:
  fixes f :: "_ \<Rightarrow> real"
  assumes i_le_n: "i \<in> {0..<n+1}"
 shows "measure_pmf.expectation (Samples (n+1) D) f  =
           measure_pmf.expectation  (Samples (n+1) D) (\<lambda> x. f (swapped_S1 x i))"
proof -
    have "measure_pmf.expectation  (Samples (n+1) D) f =
       measure_pmf.expectation (map_pmf (\<lambda> S. swapped_S1 S i) (Samples (n+1) D)) f"
      using expect_sample_swap_same
      using i_le_n by blast
    also have "measure_pmf.expectation (map_pmf (\<lambda> S. swapped_S1 S i) (Samples (n+1) D)) f = 
        measure_pmf.expectation  (Samples (n+1) D) (\<lambda> x. f (swapped_S1 x i))" using 
        integral_map_pmf[of  "(\<lambda> S. swapped_S1 S i)"  " (Samples (n+1) D)" "f" ] by auto
    finally show ?thesis by auto
  qed



lemma ridge_mine_swap: 
      "\<forall> i\<in>{0..<n+1}. measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine  Sz k) (Sz n)) =
       measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine  (swapped_S1 Sz i) k) (Sz i))"
proof 
  fix i
  assume "i\<in>{0..<n+1}"
      let ?M = " (Samples (n+1) D)"
      let ?f = "(\<lambda> Sz. l (ridge_mine  Sz k) (Sz n))" 
      have 1: " measure_pmf.expectation (Samples (n+1) D) ?f =
       measure_pmf.expectation (Samples (n+1) D) (\<lambda> x. ?f (swapped_S1 x i))" 
        using expect_f_swap_same[of i ?f] `i\<in> {0..<n+1}` by blast
    have "(\<lambda> x. l (ridge_mine (swapped_S1 x i) k ) ((swapped_S1 x i) n)) =  
        (\<lambda> x. l (ridge_mine (swapped_S1 x i) k ) (x  i))" using swapped_S1_def by simp

  then show " measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine  Sz k) (Sz n)) =
       measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine  (swapped_S1 Sz i) k) (Sz i))"
    using expect_f_swap_same 
    by (metis (mono_tags, lifting) "1")
qed

lemma expect_const:
  fixes x :: "real"
  shows "measure_pmf.expectation M (\<lambda> _. x) = x" by auto


lemma 
  shows   "sigma_finite_measure (measure_pmf M )"
  by (simp add: measure_pmf.sigma_finite_measure_axioms)

lemma expect_rearrange:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> real"
  assumes "pair_sigma_finite M N"
  assumes f: "integrable (M \<Otimes>\<^sub>M N) (case_prod f)"
  shows "integral\<^sup>L M (\<lambda> x. integral\<^sup>L N (\<lambda> y. (f x y))) = 
         integral\<^sup>L N (\<lambda> y. integral\<^sup>L M (\<lambda> x. (f x y)))"
  using pair_sigma_finite.Fubini_integral f assms(1) by metis

lemma "pair_sigma_finite D (Samples n D)" 
  by (simp add: measure_pmf.sigma_finite_measure_axioms pair_sigma_finite.intro)


lemma "\<forall>S\<in> (Samples m D). (f S) \<in> borel_measurable (count_space D)"
  using borel_measurable_count_space by auto






lemma 
  fixes f :: "(_ \<times> _ \<Rightarrow> real)"
  fixes m :: nat
  shows " f \<in> borel_measurable (pair_pmf (Samples m D) D)" using borel_measurable_count_space
  by auto

lemma 
  fixes f :: "(_ \<times> _ \<Rightarrow> real)"
  fixes m :: nat
  assumes m_pos: "m>0" 
  assumes f_nn: "AE S in (Samples m D). AE z in D. f (S, z) \<ge> 0"
  assumes "f \<in>  borel_measurable ((Samples m D) \<Otimes>\<^sub>M D)"
  shows "integrable ((Samples m D) \<Otimes>\<^sub>M D) f \<longleftrightarrow> integrable (pair_pmf (Samples m D) D) f"
proof -
  let ?M = " ((Samples m D) \<Otimes>\<^sub>M D)"
  let ?N = "(pair_pmf (Samples m D) D)"
  let ?P = "(\<lambda> z. f z \<ge> 0)"
  let ?Q = "(\<lambda> z. ennreal( norm (f z)) = f z)"
  have pair_pmf_measurable: " f \<in> borel_measurable (pair_pmf (Samples m D) D)" using borel_measurable_count_space
  by auto
  have 1: "\<integral>\<^sup>+ x. f x \<partial> ((Samples m D) \<Otimes>\<^sub>M D) = 
       \<integral>\<^sup>+ x. f x \<partial> (pair_pmf (Samples m D) D)"
  by (smt assms measurable_compose_rev measurable_ennreal measure_pmf.nn_integral_fst nn_integral_cong nn_integral_pair_pmf')
  have "space ?M = space (Samples m D) \<times> space D" using space_pair_measure by blast
  have "pair_sigma_finite (Samples m D) D"
    by (simp add: measure_pmf.sigma_finite_measure_axioms pair_sigma_finite.intro)
 

  have "{x\<in>space ?M. ?P x} \<in> sets ?M"
    using assms(3) by auto

  then have "AE x in ?M. ?P x" 
    using f_nn `pair_sigma_finite (Samples m D) D`
      pair_sigma_finite.AE_pair_measure[of "(Samples m D)" D ?P] by simp
  then have "AE x in ?M. ?Q x" by auto
 
  then have 2:  " \<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?M =  \<integral>\<^sup>+ x. f x \<partial> ?M"
    using  nn_integral_cong_AE by auto


  have " \<integral>\<^sup>+ x. f x \<partial> ?N =  \<integral>\<^sup>+ x. \<integral>\<^sup>+ y.(f (x,y)) \<partial>D \<partial>(Samples m D)"
    using nn_integral_pair_pmf' by auto
  
  then have "\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>D \<partial>(Samples m D)  =  
    \<integral>\<^sup>+ x. \<integral>\<^sup>+ y.(f (x,y)) \<partial>D \<partial>(Samples m D)"
  proof -
   
    have "AE S in (Samples m D). AE z in D. (\<lambda> x. ennreal (norm (f x)) =  f x ) (S,z)"
      using f_nn  by (simp add: AE_measure_pmf_iff)
    then have "AE x in (Samples m D). \<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>D =
          \<integral>\<^sup>+ y.(f (x,y)) \<partial>D" 
    proof
      have "\<forall> x \<in> (Samples m D). 
       (AE z in  D. ennreal (norm (f (x, z))) = ennreal (f (x, z))) \<longrightarrow>
                   \<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial> D =
                   \<integral>\<^sup>+ xa. ennreal (f (x, xa)) \<partial> D"
      proof 
        fix x
        assume "x \<in> (Samples m D)"
        show "(AE z in measure_pmf D. ennreal (norm (f (x, z))) = ennreal (f (x, z))) \<longrightarrow>
                   \<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial>measure_pmf D =
                   \<integral>\<^sup>+ xa. ennreal (f (x, xa)) \<partial>measure_pmf D" 
          using nn_integral_cong_AE by auto
      qed
      then show " AE x in (Samples m D). (AE z in  D. ennreal (norm (f (x, z))) = (f (x, z))) \<longrightarrow>
    \<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial> D = \<integral>\<^sup>+ xa.  (f (x, xa)) \<partial> D"
      using AE_measure_pmf_iff by blast
  qed
  
    then show ?thesis 
      by (simp add: nn_integral_cong_AE)
  qed
  then have "\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial> ?N = \<integral>\<^sup>+ x. f x \<partial> ?N"
    using nn_integral_pair_pmf'  by (smt nn_integral_cong)
   
  then have "\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?M = \<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?N" using 1 2
    by simp
  then have " \<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?M < \<infinity> \<longleftrightarrow>  \<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?N < \<infinity>"
    by auto

  then have " (f \<in> borel_measurable ?M \<and> \<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?M < \<infinity>) \<longleftrightarrow>
       (f \<in> borel_measurable ?N \<and> \<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?N < \<infinity>)" 
   
    using assms(3) pair_pmf_measurable by blast
  then show ?thesis using integrable_iff_bounded by blast
qed

lemma same_integral_restricted:
  fixes f ::"(  _ \<Rightarrow> real)"
  fixes g ::"(  _ \<Rightarrow> real)"
  assumes "\<forall> x \<in> set_pmf M. f x = g x"
  shows "integral\<^sup>L M f = integral\<^sup>L M g"
  by (metis (no_types, lifting) Bochner_Integration.integral_cong assms indicator_simps(2) integral_measure_pmf_real_indicator mult_not_zero)

lemma integrable_pair_pmf:
 fixes f ::"( _ \<times> _ \<Rightarrow> real)"
  fixes m :: "nat"
  assumes m_pos: "m>0" 
  assumes f_nn: "AE S in (Samples m D). AE z in D. f (S, z) \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> (Samples m D). integrable D (\<lambda> x. f (S, x))"
  shows "integrable (Samples m D)  (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) \<longleftrightarrow>
      integrable (pair_pmf (Samples m D) D) f"
proof -
  let ?N = "(pair_pmf (Samples m D) D)"
    have "(\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) \<in> borel_measurable (Samples m D)" by auto
  have "f \<in> borel_measurable ?N" by auto

   have " \<integral>\<^sup>+ x. f x \<partial> ?N =  \<integral>\<^sup>+ x. \<integral>\<^sup>+ y.(f (x,y)) \<partial>D \<partial>(Samples m D)" 
    using nn_integral_pair_pmf' by auto
  
  then have "\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>D \<partial>(Samples m D)  =  
    \<integral>\<^sup>+ x. \<integral>\<^sup>+ y.(f (x,y)) \<partial>D \<partial>(Samples m D)"
  proof -
   
    have "AE S in (Samples m D). AE z in D. (\<lambda> x. ennreal (norm (f x)) =  f x ) (S,z)"
      using f_nn  by (simp add: AE_measure_pmf_iff)
    then have "AE x in (Samples m D). \<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>D =
          \<integral>\<^sup>+ y.(f (x,y)) \<partial>D" 
    proof
      have "\<forall> x \<in> (Samples m D). 
       (AE z in  D. ennreal (norm (f (x, z))) = ennreal (f (x, z))) \<longrightarrow>
                   \<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial> D =
                   \<integral>\<^sup>+ xa. ennreal (f (x, xa)) \<partial> D"
      proof 
        fix x
        assume "x \<in> (Samples m D)"
        show "(AE z in measure_pmf D. ennreal (norm (f (x, z))) = ennreal (f (x, z))) \<longrightarrow>
                   \<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial>measure_pmf D =
                   \<integral>\<^sup>+ xa. ennreal (f (x, xa)) \<partial>measure_pmf D" 
          using nn_integral_cong_AE by auto
      qed
      then show " AE x in (Samples m D). (AE z in  D. ennreal (norm (f (x, z))) = (f (x, z))) \<longrightarrow>
    \<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial> D = \<integral>\<^sup>+ xa.  (f (x, xa)) \<partial> D"
      using AE_measure_pmf_iff by blast
  qed
  
    then show ?thesis 
      by (simp add: nn_integral_cong_AE)
  qed
  then have "\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial> ?N = \<integral>\<^sup>+ x. f x \<partial> ?N"
    using nn_integral_pair_pmf'  by (smt nn_integral_cong)

    have 11:"
     \<forall> S \<in> (Samples m D).   (\<integral>\<^sup>+ x. (f (S,x)) \<partial>D) < top"  
  proof 
    fix S
    assume "S \<in> (Samples m D)"
    have " integrable D (\<lambda> x. f (S, x))" using `S \<in> (Samples m D)`  integrable_D by auto
   
    then show "(\<integral>\<^sup>+ x. (f (S,x)) \<partial>D) < top"
      by (metis (mono_tags, lifting) AE_measure_pmf_iff \<open>S \<in> set_pmf (Samples m D)\<close> ennreal_less_top f_nn nn_integral_cong nn_integral_eq_integral)
  
  qed
   then have "\<forall>S \<in> (Samples m D). ennreal (enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) =
          (\<integral>\<^sup>+ x. f (S,x) \<partial>D) " 
    using ennreal_enn2real by blast

  then have "integral\<^sup>N (Samples m D) (\<lambda> S \<in> (Samples m D). 
         ennreal (enn2real (\<integral>\<^sup>+ x. f (S ,x) \<partial>D)))
          = integral\<^sup>N (Samples m D) (\<lambda> S \<in> (Samples m D).  
            (\<integral>\<^sup>+ x. f (S, x) \<partial>D))"
    using restrict_ext by fastforce

  
  then have "integral\<^sup>N (Samples m D) (restrict (\<lambda> S. 
         ennreal (enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D))) (Samples m D))
          = integral\<^sup>N (Samples m D) (restrict (\<lambda> S. 
        (\<integral>\<^sup>+ x. f (S ,x) \<partial>D)) (Samples m D))"
    by blast

  then have "integral\<^sup>N (Samples m D) (restrict (\<lambda> S. 
         ennreal (enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>D))) (Samples m D)) =
      integral\<^sup>N (Samples m D) ((\<lambda> S. 
         ennreal (enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>D))))" 
    using asd5 
    by (smt AE_measure_pmf_iff nn_integral_cong_AE restrict_apply)

  have "integral\<^sup>N (Samples m D) (restrict (\<lambda> S. 
        (\<integral>\<^sup>+ x. f (S, x) \<partial>D)) (Samples m D)) =
   integral\<^sup>N (Samples m D) (\<lambda> S. 
        (\<integral>\<^sup>+ x. f (S, x) \<partial>D))" 
 using asd5
  by (simp add: AE_measure_pmf_iff nn_integral_cong_AE)

  then have "integral\<^sup>N (Samples m D) ((\<lambda> S. 
         (enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>D)))) =
               integral\<^sup>N (Samples m D) (\<lambda> S. 
        (\<integral>\<^sup>+ x. f (S, x) \<partial>D))"

    using \<open>integral\<^sup>N (measure_pmf (Samples m D)) (\<lambda>S\<in>set_pmf (Samples m D). ennreal (enn2real (\<integral>\<^sup>+ x. ennreal (f (S, x)) \<partial>measure_pmf D))) = \<integral>\<^sup>+ S. ennreal (enn2real (\<integral>\<^sup>+ x. ennreal (f (S, x)) \<partial>measure_pmf D)) \<partial>measure_pmf (Samples m D)\<close> \<open>integral\<^sup>N (measure_pmf (Samples m D)) (\<lambda>S\<in>set_pmf (Samples m D). ennreal (enn2real (\<integral>\<^sup>+ x. ennreal (f (S, x)) \<partial>measure_pmf D))) = integral\<^sup>N (measure_pmf (Samples m D)) (\<lambda>S\<in>set_pmf (Samples m D). \<integral>\<^sup>+ x. ennreal (f (S, x)) \<partial>measure_pmf D)\<close> by auto

  then have 2: "\<integral>\<^sup>+ S. (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) S \<partial>(Samples m D) = 
      \<integral>\<^sup>+ S.  (\<integral>\<^sup>+ x. f (S,x) \<partial>D) \<partial>(Samples m D)" by blast
  then have " \<integral>\<^sup>+ S. (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) S \<partial>(Samples m D) =  \<integral>\<^sup>+ x. f x \<partial> ?N"
    by (simp add: \<open>\<integral>\<^sup>+ x. ennreal (f x) \<partial>measure_pmf (pair_pmf (Samples m D) D) = \<integral>\<^sup>+ x. \<integral>\<^sup>+ xa. ennreal (f (x, xa)) \<partial>measure_pmf D \<partial>measure_pmf (Samples m D)\<close>)

  then have "\<forall> S. enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D) =  (norm (enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)))"
    by auto
  then have "\<integral>\<^sup>+ S. (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) S \<partial>(Samples m D) = 
          \<integral>\<^sup>+ S. ennreal (norm ((\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) S ))\<partial>(Samples m D)"
    by auto
  then have " \<integral>\<^sup>+ S. ennreal (norm ((\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) S ))\<partial>(Samples m D) =
      \<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial> ?N" 
    using \<open>\<integral>\<^sup>+ x. ennreal (enn2real (\<integral>\<^sup>+ xa. ennreal (f (x, xa)) \<partial>measure_pmf D)) \<partial>measure_pmf (Samples m D) = \<integral>\<^sup>+ x. ennreal (f x) \<partial>measure_pmf (pair_pmf (Samples m D) D)\<close> \<open>\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>measure_pmf (pair_pmf (Samples m D) D) = \<integral>\<^sup>+ x. ennreal (f x) \<partial>measure_pmf (pair_pmf (Samples m D) D)\<close> by presburger

  then have " \<integral>\<^sup>+ S. ennreal (norm ((\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) S ))\<partial>(Samples m D) < \<infinity> 
    \<longleftrightarrow>  \<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?N < \<infinity>"
    by auto

  then have " ((\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) \<in> borel_measurable (Samples m D) \<and>
      ( \<integral>\<^sup>+ S. ennreal (norm ((\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) S ))\<partial>(Samples m D)) < \<infinity>) \<longleftrightarrow>
       (f \<in> borel_measurable ?N \<and> (\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?N) < \<infinity>)"
    by auto

  then show ?thesis  using integrable_iff_bounded
    by (metis (mono_tags, lifting) nn_integral_cong)
qed


lemma integrable_pair_pmf1:
 fixes f ::"( _ \<Rightarrow> _ \<Rightarrow> real)"
  fixes m :: "nat"
  assumes m_pos: "m>0" 
  assumes f_nn: "AE S in (Samples m D). AE z in D. f S z \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> (Samples m D). integrable D (f S)"
  shows "integrable (Samples m D)  (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f S x \<partial>D)) \<longleftrightarrow>
      integrable (pair_pmf (Samples m D) D) (\<lambda> (S,z). f S z)"
  using integrable_pair_pmf[of m "(\<lambda> (S,z). f S z)"] assms by auto



lemma add_sample_expectation1:
  fixes f ::"( _  \<Rightarrow> _ \<Rightarrow> real)"
  fixes m :: "nat"
  assumes m_pos: "m>0" 
  assumes f_nn: "\<forall>S\<in> (Samples m D). \<forall>z\<in>D. f S z \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> (Samples m D). integrable D (f S)"
  shows    "measure_pmf.expectation (Samples m D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. f S z)) =
      measure_pmf.expectation (Samples (m+1) D) (\<lambda> Sz. f (truncated_S Sz m) (Sz m))" 
proof -
  let ?pair = "(pair_pmf (Samples m D) D)"
   have 11:"\<forall>S\<in> (Samples m D).  ennreal (integral\<^sup>L  D (f S)) = 
        (\<integral>\<^sup>+ x. (f S x) \<partial>D)"  
  proof 
    fix S
    assume "S \<in> (Samples m D)"
    have " integrable D (f S)" using `S \<in> (Samples m D)`  integrable_D by auto
    then have "AE x in D. 0 \<le> f S x" using `S \<in> (Samples m D)` f_nn  by (simp add: AE_measure_pmf_iff)
    then have "(\<integral>\<^sup>+ x.  (f S x) \<partial>D) =
        (integral\<^sup>L  D (f S))" using  nn_integral_eq_integral ` integrable D (f S)` by blast
    then show "  ennreal (integral\<^sup>L  D (f S)) =  (\<integral>\<^sup>+ x. (f S x) \<partial>D)" by auto
  
  qed

  have 12: "\<forall>S \<in> (Samples m D).  (integral\<^sup>L  D (f S)) = 
        enn2real (\<integral>\<^sup>+ x. (f S x) \<partial>D)" using  
     11 by (metis AE_measure_pmf_iff enn2real_ennreal f_nn integral_nonneg_AE)
 
  then have 15: " (measure_pmf.expectation (Samples m D)
        (\<lambda> S. measure_pmf.expectation D (f S))) =
         (measure_pmf.expectation (Samples m D)  (\<lambda> S. enn2real (\<integral>\<^sup>+ x. f S x \<partial>D)))"
    using pmf_restrict  same_integral_restricted by fastforce 


  have "\<forall>S. enn2real (\<integral>\<^sup>+ x. f S x \<partial>D) \<ge> 0" by auto
  then have 2: "AE S in (Samples m D). (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f S x \<partial>D)) S \<ge> 0" 
    by blast
 
  
    have 16:"integral\<^sup>L (Samples m D) (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. (f S x) \<partial>D)) =
    integral\<^sup>L ?pair (\<lambda> (S,z). f S z)"
  proof (cases "integrable (Samples m D)  (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. (f S x) \<partial>D))")
    case True
    have "AE S in (Samples m D). AE z in D. f S z \<ge> 0" using f_nn 
      by (simp add: AE_measure_pmf_iff)
    then have integrable_pair: "integrable (pair_pmf (Samples m D) D) (\<lambda> (S,z). f S z)"
      using  integrable_pair_pmf1 m_pos integrable_D True by auto 

  then have 13: "integral\<^sup>N (Samples m D) ((\<lambda> S. 
         ennreal (enn2real (\<integral>\<^sup>+ x. ((f S) x) \<partial>D)))) =
               integral\<^sup>N (Samples m D) (\<lambda> S. (\<integral>\<^sup>+ x. ((f S) x) \<partial>D))"
    using asd5 AE_measure_pmf_iff nn_integral_cong_AE ennreal_enn2real restrict_ext 
      using "11" "12" by fastforce 

  have 14: " integral\<^sup>N ?pair (\<lambda> (S,z). f S z) =
         (\<integral>\<^sup>+ S. (\<integral>\<^sup>+ x. (\<lambda> (S,z). f S z) (S,x) \<partial>D) \<partial>(Samples m D))"
    using nn_integral_pair_pmf'[of "(Samples m D)" D "(\<lambda> (S,z). f S z)"]
    by blast


  have "\<forall> Sx \<in> ?pair.  (\<lambda> (S,z). f S z) Sx \<ge> 0" 
    using map_fst_pair_pmf  map_snd_pair_pmf  f_nn by fastforce

  then have "AE Sx in ?pair.  (\<lambda> (S,z). f S z) Sx \<ge> 0"
    using map_fst_pair_pmf  map_snd_pair_pmf  f_nn AE_measure_pmf_iff by blast 

  then have "ennreal (integral\<^sup>L ?pair (\<lambda> (S,z) . f S z)) = 
       \<integral>\<^sup>+ Sx. (\<lambda> (S,z). f S z) Sx \<partial> ?pair"
    using  integrable_pair by (simp add: nn_integral_eq_integral)

  then have " measure_pmf.expectation (Samples m D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. f S z)) =
   measure_pmf.expectation ?pair  (\<lambda> (S,z). f S z)"
    by (metis (mono_tags, lifting) "2" AE_measure_pmf_iff True
        \<open>\<forall>Sx\<in>set_pmf (pair_pmf (Samples m D) D). 0 \<le> (case Sx of (S, z) \<Rightarrow> f S z)\<close> 
          13  14 15
      enn2real_ennreal integral_nonneg_AE nn_integral_cong nn_integral_eq_integral prod.simps(2))

  then show ?thesis  using "15" by linarith

  next
    case False
     have "AE S in (Samples m D). AE z in D. f S z \<ge> 0" using f_nn 
      by (simp add: AE_measure_pmf_iff)
    then have not_integrable_pair: "\<not> integrable ?pair (\<lambda> (S,z). f S z)"
      using integrable_pair_pmf1 m_pos integrable_D False by auto 
    then show ?thesis
      using False integral_eq_cases by blast
  qed
  
  

   have 20: "integral\<^sup>L (map_pmf (\<lambda>(f,y). f(m:=y)) ?pair)
       (\<lambda> Sz. f (Sz(m:=undefined)) (Sz m)) = 
   integral\<^sup>L ?pair (\<lambda>x.  f ((fst x)(m:=undefined))  (snd x))"
    by (simp add: same_integral_restricted) 
 
  have "\<forall>x\<in> ?pair. ((fst x)(m:=undefined)) = (fst x)"
  proof 
    fix x
    assume "x\<in>(pair_pmf (Samples m D) D)"
    have "set_pmf ?pair = set_pmf (Samples m D) \<times> set_pmf D"  using set_pair_pmf by auto

    then have "pmf (Samples m D) (fst x) > 0" using \<open>x \<in> set_pmf (pair_pmf (Samples m D) D)\<close>
      using pmf_positive by fastforce
   
    have "\<forall>y. y \<notin> {0..<m} \<longrightarrow> (fst x) y = undefined"
    proof (rule ccontr)
      assume " \<not> (\<forall>y. y \<notin> {0..<m} \<longrightarrow> (fst x) y = undefined)"
      then have "pmf (Samples m D) (fst x) = 0" unfolding Samples_def 
        by (simp add: pmf_Pi_outside)
      then show False using `pmf (Samples m D) (fst x) > 0` by auto
    qed
   
    then show "((fst x)(m:=undefined)) = (fst x)" by auto
  qed

  then have 21:" integral\<^sup>L (pair_pmf (Samples m D) D) (\<lambda>x.  f ((fst x)(m:=undefined))  (snd x)) =
     integral\<^sup>L (pair_pmf (Samples m D) D) (\<lambda>x.  f (fst x) (snd x))" 
    by (simp add: \<open>\<forall>x\<in>set_pmf (pair_pmf (Samples m D) D). (fst x)(m := undefined) = fst x\<close> same_integral_restricted)

  have "finite {0..<m}" by auto
  have " m \<notin> {0..<m}" by auto



  have "(map_pmf (\<lambda>(f,y). f(m:=y)) ( map_pmf (\<lambda>(x, y). (y, x)) (pair_pmf D (Samples m D)))) =
    (map_pmf (\<lambda>(y,f). f(m:=y)) ((pair_pmf D (Samples m D))))" using map_pmf_comp
    by (smt Pair_inject map_pmf_cong prod.collapse split_beta)

  also have " \<dots> =
      (Pi_pmf (insert m {0..<m}) undefined (\<lambda>_.D))" using `finite {0..<m}` `m \<notin> {0..<m}` 
    Pi_pmf_insert[of "{0..<m}" m undefined "(\<lambda>_. D)"]
    by (metis Samples_def)

  also have "\<dots> =
          Samples (m+1) D" using Samples_def
    by (metis atLeast0LessThan atLeast0_lessThan_Suc  plus_1_eq_Suc semiring_normalization_rules(24))

  then have "measure_pmf.expectation (Samples m D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. f S z)) =
  measure_pmf.expectation (Samples (m+1) D) (\<lambda> Sz. f (Sz(m:=undefined))  (Sz m))"  
   using `finite {0..<m}` `m \<notin> {0..<m}` 
   by (metis (mono_tags, lifting) 20 21  calculation pair_commute_pmf "15"  16  prod.case_eq_if same_integral_restricted)
 
  then show ?thesis using truncated_S_def by auto
qed


lemma integrable_uniform : "\<forall> S \<in> (Samples n D). integrable D (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))"
  by blast




lemma uniform_nn: "\<forall>S\<in> (Samples n D). \<forall>z\<in>D. (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))) z \<ge> 0"
proof (rule)
  fix S
  assume "S\<in> Samples n D"
  have "\<forall> i \<in> {0..<n}. l (ridge_mine S k) (S i) \<ge> 0" 
  using l_pos min_in_H
  using \<open>S \<in> set_pmf (Samples n D)\<close> sample_in_D by blast
  then have " sum (\<lambda>i. l (ridge_mine S k) (S i)) {0..<n} / card {0..<n} \<ge> 0"
    by (meson divide_nonneg_nonneg of_nat_0_le_iff sum_nonneg)
  then show "\<forall>z\<in>D. (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))) z \<ge> 0"
    by (metis (no_types, lifting) Nat.diff_diff_right One_nat_def add_diff_cancel_right' card.empty card_atLeastLessThan diff_is_0_eq' finite_atLeastLessThan integral_pmf_of_set le_trans n_pos plus_1_eq_Suc zero_le_one zero_neq_one)
qed

lemma "measure_pmf.expectation (Samples n D) (\<lambda> S. measure_pmf.expectation D (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))) =
      measure_pmf.expectation (Samples (n+1) D) 
      (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine (truncated_S S n) k)
     ((truncated_S S n) i)))"
proof -
  have "n>0" using n_pos by auto
  then show ?thesis
  using  
    integrable_uniform uniform_nn  add_sample_expectation1[of n " (\<lambda> S. (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))))"] 
  by blast
qed


lemma train_val_diff :
 shows"  measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k) - train_err_loss S n l (ridge_mine S k)) 
            =  measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i. (l (ridge_mine (swapped_S1 S i) k) (S i)) -  (l  (ridge_mine S k) (S i))))" 
proof -

  have "\<forall> i  \<in> {0..<n}. measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k)) =
        measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i))"
  proof 
    fix i
    assume "i\<in> {0..<n}"
  have " measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k)) = 
        measure_pmf.expectation (Samples n D)
          (\<lambda> S. measure_pmf.expectation D (\<lambda> z. (l (ridge_mine S k) z)))"
    unfolding pred_err_loss_def by auto
  also have " measure_pmf.expectation (Samples n D)
          (\<lambda> S. measure_pmf.expectation D (\<lambda> z. (l (ridge_mine S k) z))) =
       measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (truncated_S Sz n) k) (Sz n))"
  proof -
    let ?f = "(\<lambda> S z. l (ridge_mine S k) z)" 
    have "\<forall>S\<in>set_pmf (Samples n D).  \<forall>z\<in>set_pmf D. 0 \<le> ?f S z"
      using l_pos min_in_H by blast
    then show ?thesis
      using integrable_D integrable_Dn integrable_pair add_sample_expectation1 n_pos by auto
  qed
  also  have " measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (truncated_S Sz n) k) (Sz n)) =
       measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine  Sz k) (Sz n))" 
    using truncated_same_expect by auto
  also have " measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine  Sz k) (Sz n)) =
        measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i))"
    using ridge_mine_swap  `i \<in> {0..<n}` by auto

  finally show " measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k)) =
        measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i))"
    by auto
qed
  then have "(\<lambda> i \<in> {0..<n}.   measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k))) = 
             (\<lambda> i \<in> {0..<n}.  measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))"
    by auto
   then have 1: "measure_pmf.expectation (pmf_of_set {0..<n})(\<lambda> i. measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k))) = 
           measure_pmf.expectation (pmf_of_set {0..<n})  (\<lambda> i. 
       measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))"
     using pmf_restrict 
     by (metis (no_types, lifting)  atLeastLessThan_iff empty_iff finite_atLeastLessThan le_add_same_cancel1  lessI n_pos nat_le_iff_add plus_1_eq_Suc set_pmf_of_set)
  

  then have " measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k)) =
        measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda> i.  measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k)))" by auto
  then have " measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k)) =
 measure_pmf.expectation (pmf_of_set {0..<n})  (\<lambda> i. 
       measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))"
    using 1 by linarith



  then have "sum (\<lambda> i. measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k))) {0..<n} = 
      sum (\<lambda> i.  measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))
      {0..<n}" 
    using \<open>\<forall>i\<in>{0..<n}. measure_pmf.expectation (Samples n D) (\<lambda>S. pred_err_loss D l (ridge_mine S k)) = measure_pmf.expectation (Samples (n + 1) D) (\<lambda>Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i))\<close> by auto

  then have " sum (\<lambda> i.  measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))
      {0..<n} =  measure_pmf.expectation (Samples (n+1) D) 
          (\<lambda> Sz. sum (\<lambda> i. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)) {0..<n})" sorry
 
  then have "sum (\<lambda> i.  measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))
      {0..<n} / n = measure_pmf.expectation (Samples (n+1) D) 
          (\<lambda> Sz. sum (\<lambda> i. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)) {0..<n} /n ) " by auto

  then have "sum (\<lambda> i.  measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))
      {0..<n} / n = measure_pmf.expectation (pmf_of_set {0..<n})
     (\<lambda> i.  measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))"
    by (metis (no_types, lifting) card_atLeastLessThan card_empty diff_zero finite_atLeastLessThan integral_pmf_of_set le_zero_eq n_pos zero_neq_one)

  have "measure_pmf.expectation (Samples (n+1) D) 
          (\<lambda> Sz. sum (\<lambda> i. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)) {0..<n} /n ) =
    measure_pmf.expectation (Samples (n+1) D) 
          (\<lambda> Sz. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda> i. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)) )"
    by (metis (no_types, lifting) card_atLeastLessThan card_empty diff_zero finite_atLeastLessThan integral_pmf_of_set le_zero_eq n_pos zero_neq_one)

  then have "measure_pmf.expectation (pmf_of_set {0..<n})
     (\<lambda> i.  measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i))) =
     measure_pmf.expectation (Samples (n+1) D) 
          (\<lambda> Sz. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda> i. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)) )"
    using \<open>(\<Sum>i = 0..<n. measure_pmf.expectation (Samples (n + 1) D) (\<lambda>Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i))) / real n = measure_pmf.expectation (Samples (n + 1) D) (\<lambda>Sz. (\<Sum>i = 0..<n. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)) / real n)\<close> \<open>(\<Sum>i = 0..<n. measure_pmf.expectation (Samples (n + 1) D) (\<lambda>Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i))) / real n = measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. measure_pmf.expectation (Samples (n + 1) D) (\<lambda>Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))\<close> by linarith

  then have 2: "measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k)) =
       measure_pmf.expectation (Samples (n+1) D) 
          (\<lambda> Sz. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda> i. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)) )"
    using \<open>measure_pmf.expectation (Samples n D) (\<lambda>S. pred_err_loss D l (ridge_mine S k)) = measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. measure_pmf.expectation (Samples (n + 1) D) (\<lambda>Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))\<close> by linarith 



  then have "\<forall> Sz. l (ridge_mine  Sz k) (Sz n) =
           measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine Sz k) (Sz n))" by simp



  have "finite {0..<n}" by auto
  have "{0..<n} \<noteq> {}" 
    using n_pos by auto
  have "card {0..<n} = n" by auto
  then have "\<forall> S. integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i) ) =
      (sum (\<lambda>i. l (ridge_mine S k) (S i) ) {0..<n}) / card {0..<n}"
    using integral_pmf_of_set `finite {0..<n}` `{0..<n} \<noteq> {}` by blast
  then have "\<forall> S. integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i) ) =
      (sum (\<lambda>i. l (ridge_mine S k) (S i) ) {0..<n}) /n" using `card {0..<n} = n` by auto
    


  then have "\<forall> S. sum (\<lambda>i. l (ridge_mine S k) (S i) ) {0..<n} / n = 
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))"
    by simp

  then have "\<forall>S.  measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)) =
     (\<lambda> _.  measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))) _" by auto

  then have "\<forall>S.  measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)) =
   measure_pmf.expectation D  (\<lambda> _.  measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))"
    by auto

  then have " (\<lambda> S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))) =
    (\<lambda> S.  measure_pmf.expectation D  (\<lambda> _.  measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))))"
    by auto

  then have " measure_pmf.expectation (Samples n D)   
     (\<lambda> S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))) =
    measure_pmf.expectation (Samples n D) 
     (\<lambda> S.  measure_pmf.expectation D 
     (\<lambda> _.  measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))))"
    by auto

  have "\<forall>S. \<forall>i\<in>{0..<n}. (truncated_S S n) i = S i"  using  truncated_S_def by auto 

  have 1: "\<forall>S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine (truncated_S S n) k)
     ((truncated_S S n) i)) = measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine (truncated_S S n) k)
     (S i))" 
  proof 
    fix S
  have "measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine (truncated_S S n) k)
     ((truncated_S S n) i)) = measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i\<in>{0..<n}. l (ridge_mine (truncated_S S n) k)
     ((truncated_S S n) i))"
    by (metis \<open>finite {0..<n}\<close> \<open>{0..<n} \<noteq> {}\<close> pmf_restrict set_pmf_of_set)

  also have " \<dots> = 
      measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i\<in>{0..<n}. l (ridge_mine (truncated_S S n) k)
     (S i))" using `\<forall>S. \<forall>i\<in>{0..<n}. (truncated_S S n) i = S i`
    by (metis (mono_tags, lifting) restrict_ext)
  also have " \<dots> = 
    measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda> i. l (ridge_mine (truncated_S S n) k)
     (S i))"  by (metis \<open>finite {0..<n}\<close> \<open>{0..<n} \<noteq> {}\<close> pmf_restrict set_pmf_of_set)
  then show "measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine (truncated_S S n) k)
     ((truncated_S S n) i)) = measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine (truncated_S S n) k)
     (S i))"  
    using calculation by linarith
qed
  have "n>0" using n_pos by auto
  then have "measure_pmf.expectation (Samples n D) (\<lambda> S. measure_pmf.expectation D (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))) =
      measure_pmf.expectation (Samples (n+1) D) 
      (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine (truncated_S S n) k)
     ((truncated_S S n) i)))"
  using 
    integrable_uniform uniform_nn  add_sample_expectation1[of n " (\<lambda> S. (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))))"]   by blast

  then have "measure_pmf.expectation (Samples n D) 
      (\<lambda> S. measure_pmf.expectation D 
      (\<lambda> _. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))) =
      measure_pmf.expectation (Samples (n+1) D) 
      (\<lambda> S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine (truncated_S S n) k)
     (S i)))" using 1 by auto
  
  have "\<forall> S. train_err_loss S n l (ridge_mine S k) = 
      measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))" 
    using \<open>\<forall>S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)) = (\<Sum>i = 0..<n. l (ridge_mine S k) (S i)) / real n\<close> train_err_loss_def by force
 
  then have "measure_pmf.expectation (Samples n D)
          (\<lambda> S.  train_err_loss S n l (ridge_mine S k)) =
          measure_pmf.expectation (Samples n D) 
          (\<lambda> S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))" 
    by simp

  then have 3: "measure_pmf.expectation (Samples n D)
          (\<lambda> S.  train_err_loss S n l (ridge_mine S k)) =  measure_pmf.expectation (Samples (n+1) D) 
      (\<lambda> S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine (truncated_S S n) k)
     (S i)))"
    using \<open>measure_pmf.expectation (Samples n D) (\<lambda>S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))) = measure_pmf.expectation (Samples n D) (\<lambda>S. measure_pmf.expectation D (\<lambda>_. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))))\<close> \<open>measure_pmf.expectation (Samples n D) (\<lambda>S. measure_pmf.expectation D (\<lambda>_. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))) = measure_pmf.expectation (Samples (n + 1) D) (\<lambda>S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine (truncated_S S n) k) (S i)))\<close> by linarith

    have "measure_pmf.expectation (Samples (n + 1) D) 
  (\<lambda>S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))) = 
    measure_pmf.expectation (Samples (n + 1) D) (\<lambda>S. measure_pmf.expectation (pmf_of_set {0..<n})
     (\<lambda>i. l (ridge_mine (truncated_S S n) k) (S i)))"
      using truncated_same_min by auto
    then have " measure_pmf.expectation (Samples n D) 
          (\<lambda> S. train_err_loss S n l (ridge_mine S k)) 
            =  measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i.  (l  (ridge_mine S k) (S i))))"
      using 3 \<open>measure_pmf.expectation (Samples n D) (\<lambda>S. train_err_loss S n l (ridge_mine S k)) = measure_pmf.expectation (Samples (n + 1) D) (\<lambda>S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine (truncated_S S n) k) (S i)))\<close> by linarith

    
    then have " measure_pmf.expectation (Samples n D) 
          (\<lambda> S. train_err_loss S n l (ridge_mine S k))  - measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k))  =
      measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i.  (l  (ridge_mine S k) (S i)))) -
         measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i. (l (ridge_mine (swapped_S1 S i) k) (S i))  ))" using 2 by auto

    have "measure_pmf.expectation (Samples n D) 
          (\<lambda> S. train_err_loss S n l (ridge_mine S k))  - measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k)) = 
          measure_pmf.expectation (Samples n D) 
          (\<lambda> S. train_err_loss S n l (ridge_mine S k) -
          pred_err_loss D l (ridge_mine S k))" sorry
    show ?thesis sorry
  qed

lemma train_val_diff2 :
 shows"  measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k) - train_err_loss S n l (ridge_mine S k)) 
            = measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i. measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S.   (l (ridge_mine (swapped_S1 S i) k) (S i)) -  (l  (ridge_mine S k) (S i))))"
  sorry


lemma train_val_diff1 : "\<forall> i \<in> {0..<n}. measure_pmf.expectation (Samples n D) (\<lambda> S.
                       pred_err_loss D l (ridge_mine S k) - train_err_loss S n l (ridge_mine S k)) 
                    =  measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S. (l (ridge_mine (S_index S i (S n))k) (S i)) - 
                         (l  (ridge_mine S k) (S i)))" 
  sorry


end 




end
