theory RLM_stable
  imports "./providedLibs/verML-1/LearningTheory" "Strong_Convexity"
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
locale learning_basics =
  fixes X :: "'a set"
    and Y :: "'b set"
    and H :: "'c::euclidean_space set"
    and S :: "(nat \<Rightarrow> ('a \<times> 'b))"
    and n :: "nat"
    and l :: "('c  \<Rightarrow> ('a \<times> 'b) \<Rightarrow>  real)"
    and k :: "real"
  assumes nnH: "H \<noteq> {}" 
    and  convH: "convex H"
    and convl : "\<forall>i \<in>{0..<n} . convex_on H (\<lambda> h. l h (S i))"
    and k_pos : "k>0"
begin

text\<open>S_index is a set where the i-th data point in S is replaced with an arbitrary one\<close>
definition S_index :: " nat \<Rightarrow> ('a \<times> 'b) \<Rightarrow> (nat \<Rightarrow> ('a * 'b))" where
  "S_index i z = S(i := z)"

lemma S_index_similar : "\<forall>i. \<forall> j \<noteq> i. l v (S j) = l v ((S_index i z) j)" 
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
     sum (\<lambda> j.  l v (S j)) A = sum (\<lambda> j. l v ((S_index i z) j)) A"
proof -
  assume  "i \<notin> A" 
  then  show "sum (\<lambda> j.  l v (S j)) A = sum (\<lambda> j. l v ((S_index i z) j)) A" 
    by (metis (mono_tags, lifting) S_index_similar  sum.cong)
qed

text\<open>Show the connection between the loss for S and the loss for S_(i)\<close>
lemma S_index_error : "\<forall>i\<in>{0..<n}. train_err_loss S n l v = 
    train_err_loss (S_index i z) n l v + (l v (S i))/n - (l v z)/n"
proof 
  fix i assume "i \<in> {0..<n}" 
  then show "train_err_loss S n l v = 
    train_err_loss (S_index i z) n l v + (l v (S i))/n - (l v z)/n"
  proof -
    have "(S_index i z) i = z" unfolding S_index_def by auto
    have 1: " sum (\<lambda>j. l v (S j) ) {0..<n} - sum (\<lambda>j. l v ((S_index i z) j) ) {0..<n} =
      sum (\<lambda>j. l v (S j) - l v ((S_index i z) j) ) {0..<n}"
      by (simp add: sum_subtractf)
    then have "sum (\<lambda>j. l v (S j) - l v ((S_index i z) j))  {0..<n} = 
             l v (S i) - l v ((S_index i z) i)" 
      using S_index_similar\<open>i \<in> {0..<n}\<close> sum_split by auto
    then have 2: "sum (\<lambda>j. l v (S j) ) {0..<n} = sum (\<lambda>j. l v ((S_index i z) j) ) {0..<n} 
      +  l v (S i) - l v ((S_index i z) i)" using 1 by auto

    then have "sum (\<lambda>j. l v (S j) ) {0..<n} = sum (\<lambda>j. l v ((S_index i z) j) ) {0..<n} 
      +  (l v (S i)) - (l v z)" using `(S_index i z) i = z` by auto
    then have "sum (\<lambda>j. l v (S j) ) {0..<n}/n = sum (\<lambda>j. l v ((S_index i z) j) ) {0..<n}/n 
      +  (l v (S i))/n - (l v z)/n"
      by (simp add:  add_divide_distrib diff_divide_distrib)

    then show ?thesis by (metis (mono_tags, lifting) sum.cong train_err_loss_def)
  qed
qed

lemma train_err_loss_convex: "convex_on H (train_err_loss S n l)"
  using train_err_loss_if_convex convl by auto

text \<open>"Regularized Loss Minimization" 
Its learning rule RLMe chooses for a given training set S an Hypothesis h from H
which minimizes the training error + regularisation function. \<close>

definition RLM :: "(nat \<Rightarrow> ('a * 'b)) \<Rightarrow> ('c::euclidean_space \<Rightarrow> real) \<Rightarrow> 'c::euclidean_space set" where
  "RLM S' r = {h. is_arg_min (train_err_loss S' n l + r) (\<lambda>s. s\<in>H) h}"

definition RLMe :: "(nat \<Rightarrow> ('a * 'b)) \<Rightarrow> ('c::euclidean_space \<Rightarrow> real) \<Rightarrow> 'c::euclidean_space" where 
  "RLMe S' r = (SOME h. h\<in> RLM S' r)"

definition RLMridge :: "(nat \<Rightarrow> ('a * 'b)) \<Rightarrow> real \<Rightarrow> 'c::euclidean_space" where 
  "RLMridge S' k' = (SOME h. h\<in> RLM S' (\<lambda> x. k' * (norm x)^2))"

fun ridge_fun :: "(nat \<Rightarrow> ('a * 'b)) \<Rightarrow> real \<Rightarrow> ('c \<Rightarrow> real)" where
  "ridge_fun S' k' = (train_err_loss S' n l + (\<lambda> w. k' * (norm w)^2))" 

definition ridge_argmin :: "(nat \<Rightarrow> ('a * 'b)) \<Rightarrow> real \<Rightarrow> 'c::euclidean_space set" where
  "ridge_argmin S' k' = {h. is_arg_min (ridge_fun S' k') (\<lambda>s. s\<in>H) h}"

definition ridge_mine :: "(nat \<Rightarrow> ('a * 'b)) \<Rightarrow> real \<Rightarrow> 'c::euclidean_space" where
  "ridge_mine S' k' = (SOME h. h \<in> ridge_argmin S' k')"


lemma ridge_convex: "strong_convex_on H (ridge_fun S k) (2*k)"
proof -
  have "strong_convex_on H (\<lambda> w. k * (norm w)*(norm w)) (2*k)" using sq_norm_strong_convex 
    by blast
  moreover  have  "(\<lambda> w. k * (norm w)*(norm w)) = (\<lambda> w. k * (norm w)^2)" using power2_eq_square 
    by (simp add: semiring_normalization_rules(17) semiring_normalization_rules(29))

  ultimately  have "strong_convex_on H (\<lambda> w. k * (norm w)^2) (2*k)" using 
      strong_conv_if_eq by auto

  then have "strong_convex_on H (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) (2*k)" 
    using strong_convex_sum train_err_loss_convex add.commute by metis
  then show ?thesis by auto
qed

text\<open>Equation 13.7\<close>
lemma ridge_stable1: "\<forall>v \<in> H. w \<in> (ridge_argmin S k) \<longrightarrow> 
    ridge_fun S k v - ridge_fun S k w \<ge>  k * norm(v - w)^2"
proof
  let ?f = "ridge_fun S k"
  fix v
  assume 1:"v \<in> H"
  show "w \<in> (ridge_argmin S k) \<longrightarrow> 
      ?f v - ?f w \<ge>  k * norm(v - w)^2"
  proof 
    assume "w \<in> (ridge_argmin S k)"
    show "?f v - ?f w \<ge>  k * norm(v - w)^2"
    proof -
      have 2:"is_arg_min ?f (\<lambda>s. s\<in>H) w"  using `w \<in> (ridge_argmin S k)` ridge_argmin_def by blast
      then have 3: "w \<in> H"  by (simp add: is_arg_min_def)
      have 4: "\<forall>y\<in>H. (?f w \<le> ?f y)" using is_arg_min_linorder 2 by metis
      have "?f v - ?f w \<ge>  2*k/2*(norm (v - w))\<^sup>2" 
        using strongly_convex_min[of H ?f "2*k" w v]  ridge_convex 3 4 1 convH   by blast
      then show "?f v - ?f w \<ge> k*norm (v - w)^2" by auto
    qed
  qed
qed

text\<open>Equation 13.8\<close>
lemma ridge_fun_diff: "\<forall>i\<in>{0..<n}. \<forall>v \<in> H. \<forall> u\<in> H. \<forall>z.
    ridge_fun S k v - ridge_fun S k u = 
    ridge_fun (S_index i z) k v - ridge_fun (S_index i z) k u
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n "
proof (rule)+
  fix i assume "i \<in> {0..<n}"
  fix v assume "v \<in> H" 
  fix u assume "u \<in> H" 
  fix z 
  show "ridge_fun S k v - ridge_fun S k u = 
      ridge_fun (S_index i z) k v - ridge_fun (S_index i z) k u
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n " 
  proof -
    have "ridge_fun S k v = (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) v" by simp
    moreover have "ridge_fun S k u = (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) u" by simp

    ultimately  have "ridge_fun S k v - ridge_fun S k u = 
     (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) v - 
      (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) u" by auto
    also have "(train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) v - 
      (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) u = 
      (train_err_loss S n l v - train_err_loss S n l u) +
      k * (norm v)^2  -  k * (norm u)^2" by auto
    also have "(train_err_loss S n l v - train_err_loss S n l u) +
      k * (norm v)^2  -  k * (norm u)^2 = 
       train_err_loss (S_index i z) n l v + (l v (S i))/n - (l v z)/n 
       - (train_err_loss (S_index i z) n l u + (l u (S i))/n - (l u z)/n)   
      +  k * (norm v)^2  -  k * (norm u)^2" using S_index_error
      using \<open>i \<in> {0..<n}\<close> by auto
    also have "train_err_loss (S_index i z) n l v + (l v (S i))/n - (l v z)/n 
       - (train_err_loss (S_index i z) n l u + (l u (S i))/n - (l u z)/n)   
      +  k * (norm v)^2  -  k * (norm u)^2 = 
       (train_err_loss (S_index i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z)/n - (l v z)/n"by simp
    also have "  (train_err_loss (S_index i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z)/n - (l v z)/n =
        (train_err_loss (S_index i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z - l v z)/n"
      by (smt add_divide_distrib)
    also have "  (train_err_loss (S_index i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z - l v z)/n =
  (train_err_loss (S_index i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index i z) n l u) - k * (norm u)^2
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
      by (smt add_divide_distrib)
    finally show ?thesis by auto 
  qed
qed

text\<open>Equation 13.9\<close>
lemma ridge_min_diff : "\<forall>i\<in>{0..<n}. \<forall>z. 
                        v \<in> ridge_argmin (S_index i z) k \<longrightarrow>
                        u \<in> ridge_argmin S k \<longrightarrow>
                        ridge_fun S k v - ridge_fun S k u \<le> 
                        (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
proof (rule)+
  fix i assume " i \<in> {0..<n}"
  fix z
  assume assm1: "v \<in> ridge_argmin (S_index i z) k"
  assume assm2: "u \<in> ridge_argmin S k"
  show "ridge_fun S k v - ridge_fun S k u \<le> 
         (l v (S i) - l u (S i))/n  + (l u z - l v z)/n" 
  proof -
    have "v \<in> H" using assm1 ridge_argmin_def  by (simp add: is_arg_min_def)
    have "u \<in> H" using assm2 ridge_argmin_def  by (simp add: is_arg_min_def)
    have "ridge_fun (S_index i z) k v \<le> ridge_fun (S_index i z) k u"
    proof - 
      have "is_arg_min (ridge_fun (S_index i z) k) (\<lambda>s. s\<in>H) v"
        using `v \<in> ridge_argmin (S_index i z) k` ridge_argmin_def by auto 
      then show ?thesis 
        by (metis \<open>u \<in> H\<close> is_arg_min_linorder)
    qed
    then have 1: " ridge_fun (S_index i z) k v - ridge_fun (S_index i z) k u \<le> 0" by auto
    have "ridge_fun S k v - ridge_fun S k u = 
    ridge_fun (S_index i z) k v - ridge_fun (S_index i z) k u
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
      using ` i \<in> {0..<n}` ridge_fun_diff `v \<in> H` `u \<in> H` by blast
    then show ?thesis using 1 by linarith
  qed
qed

text\<open>Equation 13.10\<close>
lemma ridge_stable: "\<forall>i\<in>{0..<n}. \<forall>z. 
                        v \<in> ridge_argmin (S_index i z) k \<longrightarrow>
                        u \<in> ridge_argmin S k \<longrightarrow>
                k * norm(v - u)^2 \<le> (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
proof (rule)+
  fix i assume " i \<in> {0..<n}"
  fix z
  assume assm1: "v \<in> ridge_argmin (S_index i z) k"
  assume assm2: "u \<in> ridge_argmin S k"
  show "k * norm(v - u)^2 \<le> (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
  proof -
    have "u \<in> H" using assm2 ridge_argmin_def  by (simp add: is_arg_min_def)
    have "v \<in> H" using assm1 ridge_argmin_def  by (simp add: is_arg_min_def)
    then have "  k * norm(v - u)^2 \<le>ridge_fun S k v - ridge_fun S k u" 
      using assm2 ridge_stable1 by blast
    also have " ridge_fun S k v - ridge_fun S k u \<le> 
                        (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
      using `i\<in> {0..<n}` assm1 assm2 ridge_min_diff by blast
    finally show ?thesis by auto
  qed
qed

end