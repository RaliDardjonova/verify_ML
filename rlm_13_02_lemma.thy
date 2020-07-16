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
  by (smt Suc_eq_plus1 ab_semigroup_add_class.add_ac(1)
      atLeastLessThan_iff le_eq_less_or_eq sum.atLeastLessThan_concat sum.atLeast_Suc_lessThan)


lemma S_index_eq_without_i : " i \<notin> A \<Longrightarrow>
     sum (\<lambda> j.  l v (S' j)) A = sum (\<lambda> j. l v ((S_index S' i z) j)) A"
  by (metis (mono_tags, lifting) S_index_similar  sum.cong)


lemma restrict_integral: "integral\<^sup>L M f = integral\<^sup>L M   (restrict f (space M))" 
  by (metis Bochner_Integration.integral_cong restrict_apply)

lemma restrict_nn_integral: "integral\<^sup>N M f = integral\<^sup>N M   (restrict f (space M))" 
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
  by (metis UNIV_I asd restrict_integral sets_measure_pmf space_restrict_space2)


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
      `S \<in> (Samples n D)` ridge_convex1 convex_has_min nnH convH k_pos by auto

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





lemma same_integral_restricted:
  fixes f ::"(  _ \<Rightarrow> real)"
  fixes g ::"(  _ \<Rightarrow> real)"
  assumes "\<forall> x \<in> set_pmf M. f x = g x"
  shows "integral\<^sup>L M f = integral\<^sup>L M g"
  by (metis (no_types, lifting) Bochner_Integration.integral_cong assms indicator_simps(2) integral_measure_pmf_real_indicator mult_not_zero)

lemma same_nn_integral_restricted:
  fixes f ::"(  _ \<Rightarrow> real)"
  fixes g ::"(  _ \<Rightarrow> real)"
  assumes "\<forall> x \<in> set_pmf M. f x = g x"
  shows "integral\<^sup>N M f = integral\<^sup>N M g"
  by (metis (mono_tags, lifting) assms ennreal_0 mult_not_zero nn_integral_cong nn_integral_measure_pmf pmf_eq_0_set_pmf)


lemma integrable_pair_pmf:
  fixes f ::"( _ \<times> _ \<Rightarrow> real)"
  assumes f_nn: "AE S in (measure_pmf p). AE z in (measure_pmf q). f (S, z) \<ge> 0"
  assumes integrable_q: "\<forall> S \<in> p. integrable q (\<lambda> x. f (S, x))"
  shows "integrable p  (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>q)) \<longleftrightarrow>
      integrable (pair_pmf p q) f"
proof -
  let ?N = "(pair_pmf p q)"

  have 1:" \<integral>\<^sup>+ x. f x \<partial> ?N =  \<integral>\<^sup>+ x. \<integral>\<^sup>+ y.(f (x,y)) \<partial>q \<partial>p" 
    using nn_integral_pair_pmf' by auto

  have "\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>q \<partial>p  =  
    \<integral>\<^sup>+ x. \<integral>\<^sup>+ y.(f (x,y)) \<partial>q \<partial>p"
  proof -

    have "AE S in p. AE z in q. (\<lambda> x. ennreal (norm (f x)) =  f x ) (S,z)"
      using f_nn  by (simp add: AE_measure_pmf_iff)
    then have "AE x in p. \<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>q =
          \<integral>\<^sup>+ y.(f (x,y)) \<partial>q" 
    proof
      have "\<forall> x \<in> p. 
       (AE z in  q. ennreal (norm (f (x, z))) = ennreal (f (x, z))) \<longrightarrow>
                   \<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial> q =
                   \<integral>\<^sup>+ xa. ennreal (f (x, xa)) \<partial> q" using nn_integral_cong_AE by auto

      then show " AE x in p. (AE z in  q. ennreal (norm (f (x, z))) = (f (x, z))) \<longrightarrow>
    \<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial> q = \<integral>\<^sup>+ xa.  (f (x, xa)) \<partial> q"
        using AE_measure_pmf_iff nn_integral_cong_AE by blast
    qed

    then show ?thesis 
      by (simp add: nn_integral_cong_AE)
  qed
  then have 2: "\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial> ?N = \<integral>\<^sup>+ x. f x \<partial> ?N"
    using nn_integral_pair_pmf'  by (smt nn_integral_cong)

  have "
     \<forall> S \<in> p. (\<integral>\<^sup>+ x. (f (S,x)) \<partial>q) < top"  
    using integrable_q   
    by (metis (mono_tags, lifting) AE_measure_pmf_iff ennreal_less_top
        f_nn nn_integral_cong nn_integral_eq_integral)

  then have "integral\<^sup>N p ((\<lambda> S. 
         (enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q)))) =
               integral\<^sup>N p (\<lambda> S. 
        (\<integral>\<^sup>+ x. f (S, x) \<partial>q))"
    by (simp add:  AE_measure_pmf_iff nn_integral_cong_AE)


  then have " ((\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>q)) \<in> borel_measurable p \<and>
      ( \<integral>\<^sup>+ S. ennreal (norm ((\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>q)) S ))\<partial>p) < \<infinity>) \<longleftrightarrow>
       (f \<in> borel_measurable ?N \<and> (\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?N) < \<infinity>)"
    using 1 2 by auto

  then show ?thesis  using integrable_iff_bounded
    by (metis (mono_tags, lifting) nn_integral_cong)
qed


lemma integrable_pair_pmf2:
  fixes f ::"( _ \<times> _ \<Rightarrow> real)"
  fixes m :: "nat"
  assumes m_pos: "m>0" 
  assumes f_nn: "AE S in (Samples m D). AE z in D. f (S, z) \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> (Samples m D). integrable D (\<lambda> x. f (S, x))"
  shows "integrable (Samples m D)  (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) \<longleftrightarrow>
      integrable (pair_pmf (Samples m D) D) f"
proof -
  let ?N = "(pair_pmf (Samples m D) D)"

  have 1:" \<integral>\<^sup>+ x. f x \<partial> ?N =  \<integral>\<^sup>+ x. \<integral>\<^sup>+ y.(f (x,y)) \<partial>D \<partial>(Samples m D)" 
    using nn_integral_pair_pmf' by auto

  have "\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>D \<partial>(Samples m D)  =  
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
                   \<integral>\<^sup>+ xa. ennreal (f (x, xa)) \<partial> D" using nn_integral_cong_AE by auto

      then show " AE x in (Samples m D). (AE z in  D. ennreal (norm (f (x, z))) = (f (x, z))) \<longrightarrow>
    \<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial> D = \<integral>\<^sup>+ xa.  (f (x, xa)) \<partial> D"
        using AE_measure_pmf_iff nn_integral_cong_AE by blast
    qed

    then show ?thesis 
      by (simp add: nn_integral_cong_AE)
  qed
  then have 2: "\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial> ?N = \<integral>\<^sup>+ x. f x \<partial> ?N"
    using nn_integral_pair_pmf'  by (smt nn_integral_cong)

  have "
     \<forall> S \<in> (Samples m D). (\<integral>\<^sup>+ x. (f (S,x)) \<partial>D) < top"  
    using integrable_D   
    by (metis (mono_tags, lifting) AE_measure_pmf_iff ennreal_less_top
        f_nn nn_integral_cong nn_integral_eq_integral)

  then have "integral\<^sup>N (Samples m D) ((\<lambda> S. 
         (enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>D)))) =
               integral\<^sup>N (Samples m D) (\<lambda> S. 
        (\<integral>\<^sup>+ x. f (S, x) \<partial>D))"
    by (simp add:  AE_measure_pmf_iff nn_integral_cong_AE)


  then have " ((\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) \<in> borel_measurable (Samples m D) \<and>
      ( \<integral>\<^sup>+ S. ennreal (norm ((\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>D)) S ))\<partial>(Samples m D)) < \<infinity>) \<longleftrightarrow>
       (f \<in> borel_measurable ?N \<and> (\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?N) < \<infinity>)"
    using 1 2 by auto

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
  using integrable_pair_pmf2[of m "(\<lambda> (S,z). f S z)"] assms by auto

lemma integrable_pair_pmf3:
  fixes f ::"( _ \<Rightarrow> _ \<Rightarrow> real)"
  assumes f_nn: "AE S in (measure_pmf p) . AE z in (measure_pmf q). f S z \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> p. integrable q (f S)"
  shows "integrable p  (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f S x \<partial>q)) \<longleftrightarrow>
      integrable (pair_pmf p q) (\<lambda> (S,z). f S z)"
  using integrable_pair_pmf[of  "(\<lambda> (S,z). f S z)"] assms by auto


lemma expectation_pair_pmf:
  fixes f ::"( _ \<times> _ \<Rightarrow> real)"
  assumes f_nn: "\<forall> S \<in> (set_pmf p). \<forall> z \<in> (set_pmf q). f (S,z) \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> p. integrable q (\<lambda> z. f (S, z))"
  shows  "measure_pmf.expectation (pair_pmf p q) f
      = measure_pmf.expectation p (\<lambda>x. measure_pmf.expectation q (\<lambda>y. f (x, y)))"
proof -
  let ?pair = "(pair_pmf p q)"
  have 11:"\<forall>S\<in> p.  ennreal (integral\<^sup>L  q (\<lambda> z. f (S, z))) = 
        (\<integral>\<^sup>+ x. f (S, x) \<partial>q)"  
  proof 
    fix S
    assume "S \<in> p"
    have " integrable q (\<lambda> z. f (S,z))" using `S \<in> p`  integrable_D by auto
    then have "AE x in q. 0 \<le> f (S,x)" using `S \<in> p` f_nn  by (simp add: AE_measure_pmf_iff)
    then have "(\<integral>\<^sup>+ x.  f (S,x) \<partial>q) =
        (integral\<^sup>L  q (\<lambda> z. f (S,z)))" using  nn_integral_eq_integral ` integrable q (\<lambda> z. f (S,z))` by blast
    then show "  ennreal (integral\<^sup>L  q (\<lambda> z. f (S,z))) =  (\<integral>\<^sup>+ x. f (S, x) \<partial>q)" by auto

  qed

  have 12: "\<forall>S \<in> p.  (integral\<^sup>L  q (\<lambda> z. f (S,z))) = 
        enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q)" using  
    11 by (metis AE_measure_pmf_iff enn2real_ennreal f_nn integral_nonneg_AE)

  then have 15: " (measure_pmf.expectation p
        (\<lambda> S. measure_pmf.expectation q (\<lambda> z. f (S,z)))) =
         (measure_pmf.expectation p  (\<lambda> S. enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q)))"
    using pmf_restrict  same_integral_restricted by fastforce 


  have "\<forall>S. enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q) \<ge> 0" by auto
  then have 2: "AE S in p. (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q)) S \<ge> 0" 
    by blast



  show ?thesis
  proof(cases "integrable p  (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q))")
    case True
    have "AE S in p. AE z in q. f (S, z) \<ge> 0" using f_nn 
      by (simp add: AE_measure_pmf_iff)
    then have integrable_pair: "integrable ?pair f"
      using  integrable_pair_pmf  integrable_D True  by auto 

    then have 13: "integral\<^sup>N p ((\<lambda> S. 
         ennreal (enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q)))) =
               integral\<^sup>N p (\<lambda> S. (\<integral>\<^sup>+ x. f (S, x) \<partial>q))"
      using asd5 AE_measure_pmf_iff nn_integral_cong_AE ennreal_enn2real restrict_ext 
      using "11" "12" by fastforce 

    have 14: " integral\<^sup>N ?pair f =
         (\<integral>\<^sup>+ S. (\<integral>\<^sup>+ x. f (S,x) \<partial>q) \<partial>p)"
      using nn_integral_pair_pmf'[of "p" q "f"]
      by blast

    have "\<forall> Sx \<in> ?pair.  f Sx \<ge> 0" 
      using map_fst_pair_pmf  map_snd_pair_pmf  f_nn by fastforce

    then  have "AE Sx in ?pair.  f Sx \<ge> 0"

      using map_fst_pair_pmf  map_snd_pair_pmf  f_nn AE_measure_pmf_iff
      by blast

    then have "ennreal (integral\<^sup>L ?pair f) = 
       \<integral>\<^sup>+ Sx. f Sx \<partial> ?pair"
      using  integrable_pair by (simp add: nn_integral_eq_integral)


    then show ?thesis   by (metis (mono_tags, lifting) "2" AE_measure_pmf_iff True
          \<open>\<forall>Sx\<in>set_pmf ?pair. 0 \<le> f Sx\<close> 
          13  14 15
          enn2real_ennreal integral_nonneg_AE nn_integral_cong nn_integral_eq_integral)
  next
    case False
    have "AE S in p. AE z in q. f (S, z) \<ge> 0" using f_nn 
      by (simp add: AE_measure_pmf_iff)
    then have not_integrable_pair: "\<not> integrable ?pair f"
      using integrable_pair_pmf  integrable_D False  by auto 
    then show ?thesis 
      using "15" False integral_eq_cases by auto
  qed
qed

lemma expectation_pair_pmf1:
  fixes f ::"( _ \<Rightarrow> _ \<Rightarrow> real)"
  assumes f_nn: "\<forall> S \<in> (set_pmf p). \<forall> z \<in> (set_pmf q). f S z \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> p. integrable q (\<lambda> z. f S z)"
  shows  "measure_pmf.expectation (pair_pmf p q) (\<lambda> (x,y). f x y)
      = measure_pmf.expectation p (\<lambda>x. measure_pmf.expectation q (\<lambda> y. f x y))"
  using expectation_pair_pmf[of p q "(\<lambda> (x,y). f x y)"] assms by auto


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

  have 11:" measure_pmf.expectation (Samples m D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. f S z)) =
   measure_pmf.expectation ?pair  (\<lambda> (S,z). f S z)" 
    using expectation_pair_pmf1[of "Samples m D" D f] 
    using f_nn integrable_D by linarith

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

    by (metis (mono_tags, lifting) "20" "21" 11 calculation pair_commute_pmf prod.case_eq_if same_integral_restricted)

  then show ?thesis using truncated_S_def by auto
qed



lemma integrable_uniform : "\<forall> S \<in> (Samples n D). integrable D (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))"
  by blast

lemma integrable_train_err : "integrable (Samples n D) 
          (\<lambda> S. train_err_loss S n l (ridge_mine S k))"
  unfolding train_err_loss_def oops


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

lemma not_integrable_sum:
  fixes f ::"( _ \<Rightarrow> _ \<Rightarrow> real)"
  assumes f_nn: "\<forall> S \<in> (set_pmf M). \<forall> i \<in> I. f i S \<ge> 0"
  assumes fin : "finite I"
  assumes not_int: "\<exists> i \<in> I. \<not> integrable M (f i)"
  shows  " \<not> integrable (measure_pmf M) (\<lambda> x. (\<Sum>i\<in>I. f i x))"
proof -
  have 0: "\<forall> i \<in> I. f i \<in> borel_measurable M" by auto

  then have 1:" \<integral>\<^sup>+ x. (\<Sum>i\<in>I. ennreal (f i x))
       \<partial>measure_pmf M =
    (\<Sum>i\<in>I. \<integral>\<^sup>+ x. (f i x) \<partial>measure_pmf M)" using nn_integral_sum[of I f M] by auto
  have "\<forall> x \<in> M. ennreal (\<Sum>i\<in>I. f i x) = (\<Sum>i\<in>I. ennreal (f i x))" 
    using f_nn by auto

  then have 2: " \<integral>\<^sup>+ x. (\<Sum>i\<in>I. f i x) \<partial>M = (\<Sum>i\<in>I. integral\<^sup>N M (f i))"
    using 1 same_nn_integral_restricted 
    by (smt ennreal_mult_left_cong ennreal_neg nn_integral_cong nn_integral_measure_pmf pmf_eq_0_set_pmf)

  have "\<exists> i \<in> I. integral\<^sup>N M (f i) = \<infinity>" 
  proof -

    obtain i where "i\<in>I" and " \<not> integrable M (f i)" using not_int by auto
    have "integrable M (f i) = ((f i) \<in> borel_measurable M \<and> 
                               integral\<^sup>N M (f i) < \<infinity>)" 
      by (smt \<open>i \<in> I\<close> ennreal_0 ennreal_mult_left_cong f_nn integrable_iff_bounded
          nn_integral_cong nn_integral_measure_pmf pmf_eq_0_set_pmf real_norm_def)
    then have "\<not> integral\<^sup>N M (f i) < \<infinity>" using `\<not> integrable M (f i)` 0 `i \<in> I` by auto
    then have "integral\<^sup>N M (f i) = \<infinity>"
      by (metis ennreal_cases ennreal_less_top infinity_ennreal_def)
    then show ?thesis using `i\<in>I` by auto
  qed

  then have "(\<Sum>i\<in>I. integral\<^sup>N M (f i)) = \<infinity>" using sum_Inf[of "(\<lambda> i. enn2ereal ( integral\<^sup>N M (f i)))" I]
      fin  by simp
  then have "\<integral>\<^sup>+ x. (\<Sum>i\<in>I. f i x) \<partial>M = \<infinity>" using 2 by auto

  then show "\<not> integrable M (\<lambda> x. (\<Sum>i\<in>I. f i x))" by auto
qed

lemma pmf_pos:
  fixes m :: nat
  assumes m_pos: "m>0" 
  assumes pmf_pos: "pmf (Samples m D) f > 0"
  shows " \<forall> i. i \<notin> {0..<m} \<longrightarrow> f i = undefined"
proof -
  have "pmf (Pi_pmf {0..<m} undefined (\<lambda> _.D)) f > 0"  using pmf_pos  unfolding Samples_def by auto
  then show ?thesis using pmf_Pi_outside[of "{0..<m}" f undefined "(\<lambda> _. D)"] by auto
qed

lemma integrable_sum_iff:
  fixes f ::"( _ \<Rightarrow> _ \<Rightarrow> real)"
  assumes f_nn: "\<forall> S \<in> (set_pmf M). \<forall> i \<in> I. f i S \<ge> 0"
  assumes fin_I : "finite I"
  shows "(\<forall> i \<in> I.  integrable M (f i)) \<longleftrightarrow> 
      integrable (measure_pmf M) (\<lambda> x. (\<Sum>i\<in>I. f i x))"
proof(cases "(\<forall> i \<in> I.  integrable M (f i))")
  case True
  then show ?thesis using integrable_sum by auto
next
  case False
  then have "\<exists> i \<in> I. \<not> integrable M (f i)" by auto
  then show ?thesis using not_integrable_sum[of M I f] assms by blast
qed

lemma swap_set_expectation:
  fixes f ::"( _ \<Rightarrow> _ \<Rightarrow> real)"
  assumes f_nn: "\<forall> S \<in> (set_pmf M). \<forall> i \<in> I. f i S \<ge> 0"
  assumes fin_I : "finite I"
  assumes non_empty : " I \<noteq> {}"
  assumes I_swap: 
    "\<forall> i\<in> I. \<forall> j \<in> I. measure_pmf.expectation M (\<lambda> S. f i S) =
       measure_pmf.expectation M (\<lambda> S. f j S)"
  shows " integral\<^sup>L M  (\<lambda> S. integral\<^sup>L (pmf_of_set I)  (\<lambda> i. f i S)) =
      integral\<^sup>L (pmf_of_set I) (\<lambda> i. integral\<^sup>L M (\<lambda> S. f i S))"
proof -
  have 1: "(\<forall> i \<in> I.  integrable M (f i)) \<longleftrightarrow> 
      integrable (measure_pmf M) (\<lambda> x. (\<Sum>i\<in>I. f i x))" 
    using f_nn fin_I integrable_sum_iff[of M I f] by auto
  have " integral\<^sup>L M  (\<lambda> S. sum (\<lambda> i. f i S) I) = sum (\<lambda> i. integral\<^sup>L M (\<lambda> S. f i S)) I "
  proof (cases "(\<forall> i \<in> I.  integrable M (f i))")
    case True
    then show ?thesis using integrable_sum by auto
  next
    case False
    have 2: "\<not> integrable ( M) (\<lambda> x. (\<Sum>i\<in>I. f i x))"
      using False 1 by blast
    then have 3: "measure_pmf.expectation M 
          (\<lambda> Sz. sum (\<lambda> i. f i Sz) I) = 0"
      by (simp add: not_integrable_integral_eq)
    then  have "\<forall> i\<in> I. integral\<^sup>L M (f i) = 0" using False

      by (metis "1" I_swap integral_eq_cases)

    then have "sum (\<lambda> i. measure_pmf.expectation M (f i)) I = 0" 

      by simp
    then show ?thesis 
      using 3 by linarith
  qed
  then show ?thesis using  non_empty fin_I
    by (simp add: integral_pmf_of_set)
qed

lemma min_of_Dn1_in_H: "\<forall> S \<in> (Samples (n+1) D). (ridge_mine S k) \<in> H" 
proof 
  let ?M = "(Samples (n+1) D)"
  let ?I = "{0..<n}"
  fix S
  assume "S \<in> ?M" 
  have "finite {0..<n+1}" by auto 
  have "finite ?I" by auto
  then have 1: " pmf ?M S > 0" using pmf_positive_iff `S \<in> ?M` by fast 
  then have "\<forall> i. i \<notin> {0..<n+1} \<longrightarrow> S i = undefined" using pmf_pos[of "(n+1)" S] n_pos by auto
  then have "pmf ?M S = (\<Prod>x\<in>{0..<n+1}. pmf D (S x))"
    using pmf_Pi'[of "{0..<n+1}" S undefined "(\<lambda> _. D)"] `finite {0..<n+1}`  
    by (metis Samples_def)
  then have "\<forall>x \<in> {0..<n+1}.  pmf D (S x) > 0 " 
    by (meson \<open>S \<in> ?M\<close> pmf_positive sample_in_D)
  then have 2: "(\<Prod>x\<in>?I. pmf D (S x)) > 0" 
    by (simp add: prod_pos)
  have "\<And>x. x \<notin> ?I \<Longrightarrow> (truncated_S S n) x = undefined" 
    by (simp add: \<open>\<forall>i. i \<notin> {0..<n + 1} \<longrightarrow> S i = undefined\<close> truncated_S_def)
  then have "pmf (Samples n D) (truncated_S S n) = (\<Prod>x\<in>?I. pmf D (S x))" unfolding Samples_def
    using pmf_Pi'[of ?I "truncated_S S n" undefined "(\<lambda> _. D)"]  `finite ?I` 
    using truncated_S_def by auto
  then have "pmf (Samples n D) (truncated_S S n) > 0" using 2 by auto

  then have "truncated_S S n \<in> Samples n D"
    by (simp add: set_pmf_iff)
  then have "(ridge_mine (truncated_S S n) k) \<in> H" using min_in_H by auto
  then show "(ridge_mine S k) \<in> H" 
    using truncated_same_min by auto
qed

lemma swap_sum: " sum (\<lambda> i.  measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))
      {0..<n} =  measure_pmf.expectation (Samples (n+1) D) 
          (\<lambda> Sz. sum (\<lambda> i. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)) {0..<n})" 
proof -
  let ?f = "(\<lambda> i. (\<lambda> Sz. l (ridge_mine (swapped_S1 Sz i) k) (Sz i)))"
  let ?M = "(Samples (n+1) D)"
  let ?I = "{0..<n}"
  have f_nn : "\<forall> S \<in> (set_pmf ?M). \<forall> i \<in> ?I. ?f i S \<ge> 0" using l_pos min_of_Dn1_in_H
    by (smt  atLeastLessThan_iff le_less_trans learning_basics1.swapped_S1_def learning_basics1_axioms less_add_same_cancel1 less_imp_le_nat less_one pmf_swapped_same sample_in_D set_pmf_iff)
  have fin_I: "finite ?I" by auto
  then have 1: "(\<forall> i \<in> ?I.  integrable ?M (?f i)) \<longleftrightarrow> 
      integrable (measure_pmf ?M) (\<lambda> x. (\<Sum>i\<in>?I. ?f i x))" 
    using f_nn fin_I integrable_sum_iff[of ?M ?I ?f] by auto
  have I_non_empty: " ?I \<noteq> {}" using n_pos by auto
  have "\<forall> i\<in> ?I. \<forall> j \<in> ?I. measure_pmf.expectation ?M (\<lambda> S. ?f i S) =
       measure_pmf.expectation ?M (\<lambda> S. ?f j S)" using ridge_mine_swap 

    by (smt atLeastLessThan_iff le_less_trans le_neq_implies_less
        less_add_same_cancel1 less_imp_le_nat zero_le_one zero_neq_one)

  then show ?thesis 

  proof (cases "(\<forall> i \<in> ?I.  integrable ?M (?f i))")
    case True
    then show ?thesis using integrable_sum by auto
  next
    case False
    have 2: "\<not> integrable ( ?M) (\<lambda> x. (\<Sum>i\<in>?I. ?f i x))"
      using False 1 by blast
    then have 3: "measure_pmf.expectation ?M 
          (\<lambda> Sz. sum (\<lambda> i. ?f i Sz) ?I) = 0"
      by (simp add: not_integrable_integral_eq)
    then  have "\<forall> i\<in> ?I. integral\<^sup>L ?M (?f i) = 0" using False
      by (smt One_nat_def 2  atLeastLessThan_iff integral_eq_cases le_less_trans lessI
          less_add_same_cancel1 less_imp_le_nat ridge_mine_swap)

    then have "sum (\<lambda> i. measure_pmf.expectation ?M (?f i)) {0..<n} = 0" 

      by simp
    then show ?thesis 
      using 3 by linarith
  qed
qed



lemma " integrable (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (truncated_S Sz n) k) (Sz n))"
  oops

lemma train_val_diff :
  assumes integrable_D:"\<forall> S \<in> (Samples n D). integrable D (\<lambda> z. l (ridge_mine S k) z)"
  assumes  pred_err_integrable: "integrable (Samples n D)  (\<lambda> S. pred_err_loss D l (ridge_mine S k))"
  assumes  train_err_integrable: " integrable (Samples n D)  (\<lambda> S. train_err_loss S n l (ridge_mine S k)) "
  assumes integrable_swapped_Si: " integrable (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i.  (l (ridge_mine (swapped_S1 S i) k) (S i))))"
  assumes integrable_Si: " integrable (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i.  (l  (ridge_mine S k) (S i))))"
  shows"  measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k) - train_err_loss S n l (ridge_mine S k)) 
            =  measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i. (l (ridge_mine (swapped_S1 S i) k) (S i)) -  (l  (ridge_mine S k) (S i))))" 
proof -
  let ?Dn = "Samples n D"
  let ?Dn1 = "Samples (n+1) D"
  let ?I = "{0..<n}"
  let ?pmfI = "(pmf_of_set ?I)"
  let ?l_swapped = "(\<lambda> i. (\<lambda> S. l (ridge_mine (swapped_S1 S i) k) (S i)))"
  let ?l_trunc = "(\<lambda> S. (\<lambda> z. l (ridge_mine (truncated_S S n) k) z))"
  let ?l_Si = "(\<lambda> S. (\<lambda>i. l (ridge_mine S k) (S i)))"
  let ?pred_err = "(\<lambda> S. pred_err_loss D l (ridge_mine S k))"
  have fin_I:"finite ?I" by auto
  have non_empty_I:"?I \<noteq> {}" 
    using n_pos by auto

  have pred_err_Dn1: "\<forall> i  \<in> ?I. integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S) =
        integral\<^sup>L ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)"
  proof 
    fix i
    assume "i\<in> ?I"
    have " integral\<^sup>L ?Dn (\<lambda> S. ?pred_err S) = 
        integral\<^sup>L ?Dn (\<lambda> S. integral\<^sup>L D (\<lambda> z. (l (ridge_mine S k) z)))"
      unfolding pred_err_loss_def by auto
    also have " \<dots> = integral\<^sup>L ?Dn1 (\<lambda> S. ?l_trunc S (S n))"
      using l_pos min_in_H  integrable_D add_sample_expectation1 n_pos by auto
    also  have " \<dots> =
       integral\<^sup>L ?Dn1 (\<lambda> S. ?l_Si S n)" 
      using truncated_same_expect by auto
    also have " \<dots> =
        integral\<^sup>L ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)"
      using ridge_mine_swap  `i \<in> ?I` by auto
    finally show " integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S) = integral\<^sup>L ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)"
      by auto
  qed

  then have 1: "integral\<^sup>L ?pmfI (\<lambda> i. integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S)) = 
                integral\<^sup>L ?pmfI (\<lambda> i. integral\<^sup>L ?Dn1 (\<lambda> S. ?l_swapped i S))"
    using pmf_restrict fin_I non_empty_I set_pmf_of_set
    by (smt same_integral_restricted)


  have " integral\<^sup>L ?pmfI  (\<lambda> i.  integral\<^sup>L ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)) =
   integral\<^sup>L ?Dn1  (\<lambda> Sz. integral\<^sup>L ?pmfI (\<lambda> i. ?l_swapped i Sz) )"
  proof -
    have "\<forall> S \<in> (set_pmf ?Dn1). \<forall> i \<in> ?I.(ridge_mine (swapped_S1 S i) k) \<in> H" 
      using min_of_Dn1_in_H 
      by (metis  atLeastLessThan_iff pmf_swapped_same set_pmf_iff swapped_S1_def trans_less_add1)
    then have l_swapped_nn: "\<forall> S \<in> (set_pmf ?Dn1). \<forall> i \<in> ?I. ?l_swapped i S \<ge> 0"
      using l_pos  sample_in_D by auto

    have I_swap: 
      "\<forall> i\<in> ?I. \<forall> j \<in> ?I. measure_pmf.expectation ?Dn1 (\<lambda> S. ?l_swapped i S) =
       measure_pmf.expectation ?Dn1 (\<lambda> S. ?l_swapped j S)" 
      using ridge_mine_swap 
      by (metis (no_types, lifting) pred_err_Dn1)
    then show ?thesis using fin_I non_empty_I 
        l_swapped_nn swap_set_expectation[of ?Dn1 ?I ?l_swapped]
      by linarith
  qed

  then have 2: "integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S) =
       integral\<^sup>L ?Dn1  (\<lambda> Sz. integral\<^sup>L ?pmfI (\<lambda> i. ?l_swapped i Sz) )"
    using 1 by simp


  have "\<forall>S. \<forall>i\<in>?I. (truncated_S S n) i = S i"  using  truncated_S_def by auto 

  then  have 4: "\<forall>S. integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (truncated_S S n i)) =
               integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (S i))" 
    by (metis (no_types, lifting) fin_I non_empty_I same_integral_restricted set_pmf_of_set)

  have "n>0" using n_pos by auto
  then have 5: "integral\<^sup>L ?Dn (\<lambda> S. integral\<^sup>L D (\<lambda> _.  
       integral\<^sup>L ?pmfI (?l_Si S))) =
      integral\<^sup>L ?Dn1  (\<lambda> S.  integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (truncated_S S n i)))"
    using 
      integrable_uniform uniform_nn add_sample_expectation1[of n " (\<lambda> S. (\<lambda> _.  
       integral\<^sup>L ?pmfI (?l_Si S)))"]   by blast

  have "card ?I = n" by auto
  then have "\<forall> S. integral\<^sup>L ?pmfI (\<lambda>i. l (ridge_mine S k) (S i) ) =
      (sum (?l_Si S) ?I) / card ?I"
    using integral_pmf_of_set `finite ?I` `?I \<noteq> {}` by blast
  then have "\<forall> S. train_err_loss S n l (ridge_mine S k) = 
      integral\<^sup>L ?pmfI (?l_Si S)" 
    using `card ?I = n` train_err_loss_def by force

  then have 6:" integral\<^sup>L ?Dn  (\<lambda> S. train_err_loss S n l (ridge_mine S k)) 
            =  integral\<^sup>L ?Dn1  (\<lambda> S.  integral\<^sup>L ?pmfI (?l_Si S))"
    using 4 5 truncated_same_min  by auto 


  

  have "integral\<^sup>L ?Dn 
          (\<lambda> S.   ?pred_err S -train_err_loss S n l (ridge_mine S k)) = 
       integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S) -
       integral\<^sup>L ?Dn  (\<lambda> S. train_err_loss S n l (ridge_mine S k))   "  
    using train_err_integrable  pred_err_integrable by simp

  also have " \<dots>  =
   integral\<^sup>L ?Dn1 (\<lambda> S.  integral\<^sup>L ?pmfI 
   (\<lambda> i. (l (ridge_mine (swapped_S1 S i) k) (S i)))) - 
   integral\<^sup>L ?Dn1 (\<lambda> S.  integral\<^sup>L ?pmfI (?l_Si S))" using 2 6 by auto
  also have " \<dots> =   integral\<^sup>L ?Dn1 (\<lambda> S.  
   integral\<^sup>L ?pmfI (\<lambda> i. (l (ridge_mine (swapped_S1 S i) k) (S i)) ) -
  integral\<^sup>L ?pmfI (?l_Si S)  )" 
    using integrable_Si integrable_swapped_Si  by simp
  also have " \<dots> = 
     integral\<^sup>L ?Dn1 (\<lambda> S.  integral\<^sup>L ?pmfI (\<lambda> i. 
   (l (ridge_mine (swapped_S1 S i) k) (S i)) - (?l_Si S i) ) )"
  proof -
    have "\<forall> S. sum (\<lambda> i. (l (ridge_mine (swapped_S1 S i) k) (S i)) ) ?I -  sum (?l_Si S) ?I  =
    sum (\<lambda> i. (l (ridge_mine (swapped_S1 S i) k) (S i)) - (?l_Si S i) ) ?I"
      by (simp add: sum_subtractf)
    then  have "\<forall> S.
   integral\<^sup>L ?pmfI (\<lambda> i. (l (ridge_mine (swapped_S1 S i) k) (S i)) )  -
 integral\<^sup>L ?pmfI (?l_Si S) =
    integral\<^sup>L ?pmfI (\<lambda> i. 
   (l (ridge_mine (swapped_S1 S i) k) (S i)) -  (?l_Si S i) )" using non_empty_I
      by (metis (no_types, lifting) diff_divide_distrib fin_I integral_pmf_of_set)
    then show ?thesis by auto
  qed
  finally show ?thesis by blast
qed


end
end