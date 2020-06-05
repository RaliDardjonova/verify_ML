theory RLM_learn
  imports  "./providedLibs/verML-1/LearningTheory" "Strong_Convexity"
begin



definition pred_err_loss :: "('a \<times> 'b) pmf \<Rightarrow>  ('c  \<Rightarrow> ('a \<times> 'b) \<Rightarrow>  real)
 \<Rightarrow> 'c \<Rightarrow> real" where
  "pred_err_loss D l h = measure_pmf.expectation D (\<lambda> z. (l h z))"

definition train_err_loss :: " (nat \<Rightarrow> ('a * 'b)) \<Rightarrow> nat \<Rightarrow>
('c \<Rightarrow> ('a \<times> 'b) \<Rightarrow> real) \<Rightarrow> 'c \<Rightarrow>  real" where
  "train_err_loss S n l h = sum (\<lambda>i. l h (S i) ) {0..<n} / n"

lemma train_err_loss_nn: "(\<forall>i\<in>{0..<n}. l h (S i) \<ge>0) \<Longrightarrow> train_err_loss S n l h \<ge> 0"
proof -
  assume "\<forall>i\<in>{0..<n}. 0 \<le> l h (S i)" 
  then have "0 \<le> (\<Sum>i\<in>{0..<n}. l h (S i))" 
    by (meson sum_nonneg) 
  then have " 0 \<le> sum (\<lambda>i. l h (S i) ) {0..<n}" by auto
  then show "train_err_loss S n l h \<ge> 0" unfolding train_err_loss_def  by simp
qed

text\<open>Show L_s(w) is convex over H, when the loss function is convex over H\<close>
lemma train_err_loss_if_convex: "(\<forall>i \<in>{0..<n} . convex_on H (\<lambda> h. l h (S i))) \<Longrightarrow>
   convex_on H (train_err_loss S n l)"
proof -
  assume 1: "(\<forall>i \<in> {0..<n}. convex_on H (\<lambda> h. l h (S i)))" 
  then have 2: "convex_on H (\<Sum>i\<in>{0..<n}. (\<lambda> h. l h (S i)))"
  proof(induct n)
    case 0
    then show ?case 
      by (simp add: convex_on_def zero_fun_def)
  next
    case (Suc n)
    then show  "convex_on H (\<Sum>i = 0..<Suc n.(\<lambda>h. l h (S i)))"
      by (simp add: Suc.hyps Suc.prems convex_fun_add)
  qed
  have "(\<Sum>i = 0..<n.(\<lambda>h. l h (S i))) = (\<lambda>h. \<Sum>i = 0..<n. l h (S i))" 
  proof(induct n)
    case 0
    then show ?case 
      by (simp add: zero_fun_def)
  next
    case (Suc n)
    then show ?case  by (simp add: Suc.hyps Suc.prems)
  qed
  then have 3:" convex_on H (\<lambda>h. \<Sum>i = 0..<n. l h (S i))" using 2 by simp
  have " (1/n)\<ge> 0" by auto
  then have "convex_on H  (\<lambda> h. (1/n)*(sum (\<lambda>i. l h (S i)) {0..<n}) )" using convex_on_cmul 3
    by blast
  then have "convex_on H  (\<lambda> h.(sum (\<lambda>i. l h (S i)) {0..<n})/n )" by auto
  then show "convex_on H (train_err_loss S n l)"  unfolding train_err_loss_def by blast
qed

text\<open>Define a locale for cleaner proofs and definitions\<close>
locale learning_basics1 =
 
 fixes H :: "'a::euclidean_space set"
    and X :: "'b set"
    and Y :: "'c set"
    and D :: "('b \<times> 'c) pmf"
    and n :: "nat"
    and l :: "('a  \<Rightarrow> ('b \<times> 'c) \<Rightarrow> real)"
  assumes nnH: "H \<noteq> {}" 
    and  convH: "convex H"
    and l_pos: "\<forall>h\<in>H. \<forall>z\<in>D. l h z \<ge> 0"
    and convll : "\<forall>z \<in> D. convex_on H (\<lambda> h. l h z)"
    and "set_pmf D \<subseteq> (X\<times>Y)"
    and n_pos: "n\<ge>1"
begin

text \<open>"Regularized Loss Minimization" 
Its learning rule RLMe chooses for a given training set S an Hypothesis h from H
which minimizes the training error + regularisation function. \<close>

definition RLM :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> ('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a::euclidean_space set" where
  "RLM S' r = {h. is_arg_min (train_err_loss S' n l + r) (\<lambda>s. s\<in>H) h}"

definition RLMe :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> ('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a::euclidean_space" where 
  "RLMe S' r = (SOME h. h\<in> RLM S' r)"

definition RLMridge :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> real \<Rightarrow> 'a::euclidean_space" where 
  "RLMridge S' k' = (SOME h. h\<in> RLM S' (\<lambda> x. k' * (norm x)^2))"

fun ridge_fun :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> real)" where
  "ridge_fun S' k' = (train_err_loss S' n l + (\<lambda> w. k' * (norm w)^2))" 

definition ridge_argmin :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> real \<Rightarrow> 'a::euclidean_space set" where
  "ridge_argmin S' k' = {h. is_arg_min (ridge_fun S' k') (\<lambda>s. s\<in>H) h}"

definition ridge_mine :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> real \<Rightarrow> 'a::euclidean_space" where
  "ridge_mine S' k' = (SOME h. h \<in> ridge_argmin S' k')"

definition swapped_S :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> ('b * 'c))" where
  "swapped_S S' i =  S' " 

definition truncated_S :: "(nat \<Rightarrow> ('b * 'c))  \<Rightarrow> (nat \<Rightarrow> ('b * 'c))" where
  "truncated_S S' =  S'(n+1 := undefined) "

lemma sample_in_D: "\<forall>S \<in> (Samples m D). \<forall>i\<in>{0..<m}. S i \<in> set_pmf D" 
  sorry

lemma train_err_loss_convex: "\<forall>S \<in> (Samples n D).convex_on H (train_err_loss S n l)"
  using train_err_loss_if_convex convll sample_in_D  by blast

lemma ridge_strong_convex: "\<forall>S \<in> (Samples n D). strong_convex_on H (ridge_fun S k) (2*k)"
proof 
  fix S
  assume "S \<in> (Samples n D)"
  show "strong_convex_on H (ridge_fun S k) (2*k)" 
  proof -
  have "strong_convex_on H (\<lambda> w. k * (norm w)*(norm w)) (2*k)" using sq_norm_strong_convex 
    by blast
  moreover  have  "(\<lambda> w. k * (norm w)*(norm w)) = (\<lambda> w. k * (norm w)^2)" using power2_eq_square 
    by (simp add: semiring_normalization_rules(17) semiring_normalization_rules(29))

  ultimately  have "strong_convex_on H (\<lambda> w. k * (norm w)^2) (2*k)" using 
      strong_conv_if_eq by auto

  then have "strong_convex_on H (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) (2*k)" 
    using strong_convex_sum train_err_loss_convex add.commute
    by (metis \<open>S \<in> set_pmf (Samples n D)\<close>)
  then show ?thesis by auto
qed
qed

lemma ridge_convex1: "\<forall>S \<in> (Samples n D). convex_on H (ridge_fun S k)"
  sorry

lemma convex_has_min: "convex_on H f \<Longrightarrow> \<exists>x\<in>H. is_arg_min f (\<lambda>z. z\<in>H) x" 
  sorry

lemma in_argmin: "\<forall>S \<in> (Samples n D). (ridge_mine S k) \<in> (ridge_argmin S k)"
proof 
  fix S
  assume " S \<in> Samples n D"
  show "(ridge_mine S k) \<in> (ridge_argmin S k)" 
  proof -
   let ?P = "(\<lambda> h. h \<in> ridge_argmin S k)"
  have "\<exists>h. is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) h" using 
        `S \<in> (Samples n D)` ridge_convex1 convex_has_min nnH convH by auto
  then have "ridge_argmin S k \<noteq> {}" unfolding ridge_argmin_def using nnH convH 
     by blast
  have "\<exists>h. ?P h" unfolding ridge_argmin_def  using nnH
    using \<open>\<exists>h. is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) h\<close> by blast
  show  "(ridge_mine S k) \<in> (ridge_argmin S k)" unfolding ridge_mine_def using 
      someI2[of "?P" "(ridge_mine S k)" ?P ]
    by (metis (no_types, lifting) Collect_cong Set.empty_def \<open>ridge_argmin S k \<noteq> {}\<close> mem_Collect_eq ridge_argmin_def verit_sko_ex_indirect)
qed
qed


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

lemma train_val_diff : "\<forall> i \<in> {0..<n}. measure_pmf.expectation (Samples n D) (\<lambda> S.
                       pred_err_loss D l (ridge_mine S k) - train_err_loss S n l (ridge_mine S k)) 
                    =  measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S. (l (ridge_mine (S_index S i (S n))k) (S i)) - 
                         (l  (ridge_mine S k) (S i)))" 
  sorry
  

end 




end