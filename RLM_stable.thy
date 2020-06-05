theory RLM_stable
  imports  "RLM_learn"
begin



locale ridge_and_convex_loss = learning_basics1 + 
  fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
    and k :: "real" 
  assumes convl : "\<forall>y \<in> D. convex_on H (\<lambda> h. l h y)"
    and k_pos : "k>0"
    and S_in_D: "S \<in> Samples n D"
begin


text\<open>Show the connection between the loss for S and the loss for S_(i)\<close>
lemma S_index_error : "\<forall>i\<in>{0..<n}. train_err_loss S n l v = 
    train_err_loss (S_index S i z) n l v + (l v (S i))/n - (l v z)/n"
proof 
  fix i assume "i \<in> {0..<n}" 
  then show "train_err_loss S n l v = 
    train_err_loss (S_index S i z) n l v + (l v (S i))/n - (l v z)/n"
  proof -
    have "(S_index S i z) i = z" unfolding S_index_def by auto
    have 1: " sum (\<lambda>j. l v (S j) ) {0..<n} - sum (\<lambda>j. l v ((S_index S i z) j) ) {0..<n} =
      sum (\<lambda>j. l v (S j) - l v ((S_index S i z) j) ) {0..<n}"
      by (simp add: sum_subtractf)
    then have "sum (\<lambda>j. l v (S j) - l v ((S_index S i z) j))  {0..<n} = 
             l v (S i) - l v ((S_index S i z) i)" 
      using S_index_similar\<open>i \<in> {0..<n}\<close> sum_split by auto
    then have 2: "sum (\<lambda>j. l v (S j) ) {0..<n} = sum (\<lambda>j. l v ((S_index S i z) j) ) {0..<n} 
      +  l v (S i) - l v ((S_index S i z) i)" using 1 by auto

    then have "sum (\<lambda>j. l v (S j) ) {0..<n} = sum (\<lambda>j. l v ((S_index S i z) j) ) {0..<n} 
      +  (l v (S i)) - (l v z)" using `(S_index S i z) i = z` by auto
    then have "sum (\<lambda>j. l v (S j) ) {0..<n}/n = sum (\<lambda>j. l v ((S_index S i z) j) ) {0..<n}/n 
      +  (l v (S i))/n - (l v z)/n"
      by (simp add:  add_divide_distrib diff_divide_distrib)

    then show ?thesis by (metis (mono_tags, lifting) sum.cong train_err_loss_def)
  qed
qed

lemma S_index_is_sample: "\<forall>i\<in>{0..<n}.\<forall>z\<in>D. S_index S i z \<in> Samples n D"
  sorry

lemma train_err_loss_convex: "convex_on H (train_err_loss S n l)"
  using train_err_loss_if_convex convl
  using S_in_D train_err_loss_convex by blast




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
    ridge_fun (S_index S i z) k v - ridge_fun (S_index S i z) k u
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n "
proof (rule)+
  fix i assume "i \<in> {0..<n}"
  fix v assume "v \<in> H" 
  fix u assume "u \<in> H" 
  fix z 
  show "ridge_fun S k v - ridge_fun S k u = 
      ridge_fun (S_index S i z) k v - ridge_fun (S_index S i z) k u
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
       train_err_loss (S_index S i z) n l v + (l v (S i))/n - (l v z)/n 
       - (train_err_loss (S_index S i z) n l u + (l u (S i))/n - (l u z)/n)   
      +  k * (norm v)^2  -  k * (norm u)^2" using S_index_error
      using \<open>i \<in> {0..<n}\<close> by auto
    also have "train_err_loss (S_index S i z) n l v + (l v (S i))/n - (l v z)/n 
       - (train_err_loss (S_index S i z) n l u + (l u (S i))/n - (l u z)/n)   
      +  k * (norm v)^2  -  k * (norm u)^2 = 
       (train_err_loss (S_index S i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index S i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z)/n - (l v z)/n"by simp
    also have "  (train_err_loss (S_index S i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index S i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z)/n - (l v z)/n =
        (train_err_loss (S_index S i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index S i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z - l v z)/n"
      by (smt add_divide_distrib)
    also have "  (train_err_loss (S_index S i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index S i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z - l v z)/n =
  (train_err_loss (S_index S i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index S i z) n l u) - k * (norm u)^2
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
      by (smt add_divide_distrib)
    finally show ?thesis by auto 
  qed
qed

text\<open>Equation 13.9\<close>
lemma ridge_min_diff : "\<forall>i\<in>{0..<n}. \<forall>z. 
                        v \<in> ridge_argmin (S_index S i z) k \<longrightarrow>
                        u \<in> ridge_argmin S k \<longrightarrow>
                        ridge_fun S k v - ridge_fun S k u \<le> 
                        (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
proof (rule)+
  fix i assume " i \<in> {0..<n}"
  fix z
  assume assm1: "v \<in> ridge_argmin (S_index S i z) k"
  assume assm2: "u \<in> ridge_argmin S k"
  show "ridge_fun S k v - ridge_fun S k u \<le> 
         (l v (S i) - l u (S i))/n  + (l u z - l v z)/n" 
  proof -
    have "v \<in> H" using assm1 ridge_argmin_def  by (simp add: is_arg_min_def)
    have "u \<in> H" using assm2 ridge_argmin_def  by (simp add: is_arg_min_def)
    have "ridge_fun (S_index S i z) k v \<le> ridge_fun (S_index S i z) k u"
    proof - 
      have "is_arg_min (ridge_fun (S_index S i z) k) (\<lambda>s. s\<in>H) v"
        using `v \<in> ridge_argmin (S_index S i z) k` ridge_argmin_def by auto 
      then show ?thesis 
        by (metis \<open>u \<in> H\<close> is_arg_min_linorder)
    qed
    then have 1: " ridge_fun (S_index S i z) k v - ridge_fun (S_index S i z) k u \<le> 0" by auto
    have "ridge_fun S k v - ridge_fun S k u = 
    ridge_fun (S_index S i z) k v - ridge_fun (S_index S i z) k u
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
      using ` i \<in> {0..<n}` ridge_fun_diff `v \<in> H` `u \<in> H` by blast
    then show ?thesis using 1 by linarith
  qed
qed


text\<open>Equation 13.10\<close>
lemma ridge_stable: "\<forall>i\<in>{0..<n}. \<forall>z. 
                        v \<in> ridge_argmin (S_index S i z) k \<longrightarrow>
                        u \<in> ridge_argmin S k \<longrightarrow>
                k * norm(v - u)^2 \<le> (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
proof (rule)+
  fix i assume " i \<in> {0..<n}"
  fix z
  assume assm1: "v \<in> ridge_argmin (S_index S i z) k"
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

locale lipschitz_ridge_and_convex_loss =
      ridge_and_convex_loss + 
      assumes lipschitz : "\<forall>y\<in>D . \<rho>-lipschitz_on H  (\<lambda> h. l h y)"
begin

lemma lipschitz_loss_diff_bounded: "\<forall>i\<in>{0..<n}. \<forall>z\<in>D. 
                        (l (ridge_mine (S_index S i z) k)  (S i)) - (l (ridge_mine S k) (S i))
                         \<le> (2*\<rho>^2)/(k*n)"
proof (rule)+
  fix i assume " i \<in> {0..<n}"
  fix z assume " z \<in> D"
  let ?v = "(ridge_mine (S_index S i z) k)"
  let ?u = "ridge_mine S k"
 
  show "(l ?v (S i)) - (l ?u (S i)) \<le> (2*\<rho>^2)/(k*n)"
  proof (cases "?u=?v")
    case True
    then show ?thesis  using k_pos by auto
  next
    case False
    have  assm1: "?v \<in> ridge_argmin (S_index S i z) k" using in_argmin S_index_is_sample
      using \<open>i \<in> {0..<n}\<close> \<open>z \<in> set_pmf D\<close> by blast
    have assm2: "?u \<in> ridge_argmin S k" using in_argmin S_in_D 
        using \<open>i \<in> {0..<n}\<close> \<open>z \<in> set_pmf D\<close> by blast
    let ?loss_zi = "(\<lambda> h. l h (S i))"
    let ?loss_z =  "(\<lambda> h. l h z)"
    have " \<rho> \<ge> 0"  using lipschitz  lipschitz_on_def
      using \<open>z \<in> set_pmf D\<close> by blast
    have assm3: " \<rho>-lipschitz_on H  (\<lambda> h. l h z)" using lipschitz \<open>z \<in> set_pmf D\<close>
      by auto
    have "S i \<in> D" using sample_in_D S_in_D `i \<in> {0..<n}` by simp
    then have assm4:" \<rho>-lipschitz_on H  (\<lambda> h. l h (S i))" using assm3 lipschitz by auto
    have " norm(?v-?u) > 0" using `?u \<noteq> ?v`  by auto
    have "n > 0"  using \<open>i \<in> {0..<n}\<close> by auto
    have "?u \<in> H" using assm2 ridge_argmin_def  by (simp add: is_arg_min_def)
    have "?v \<in> H" using assm1 ridge_argmin_def  by (simp add: is_arg_min_def)
    have " dist (?loss_zi ?v)  (?loss_zi ?u) \<le> \<rho> * dist ?v ?u" 
      using `?v\<in>H` `?u\<in>H` assm4 lipschitz_onD by fastforce
    moreover have "(?loss_zi ?v) - (?loss_zi ?u) \<le> dist (?loss_zi ?v)  (?loss_zi ?u)" 
      by (simp add: dist_norm)
    ultimately  have 1:"(?loss_zi ?v) - (?loss_zi ?u) \<le>  \<rho> * dist ?v ?u" by auto

    have " dist (?loss_z ?u)  (?loss_z ?v) \<le> \<rho> * dist ?u ?v" 
      using `?v\<in>H` `?u\<in>H` assm3 lipschitz_onD by fastforce
    moreover have "(?loss_z ?u) - (?loss_z ?v) \<le> dist (?loss_z ?u)  (?loss_z ?v)" 
      by (simp add: dist_norm)
    ultimately  have 2: "(?loss_z ?u) - (?loss_z ?v) \<le>  \<rho> * dist ?v ?u" 
    proof -
have "l (ridge_mine S k) z - l (ridge_mine (S_index S i z) k) z \<le> \<rho> * dist (ridge_mine S k) (ridge_mine (S_index S i z) k)"
  using \<open>dist (l (ridge_mine S k) z) (l (ridge_mine (S_index S i z) k) z) \<le> \<rho> * dist (ridge_mine S k) (ridge_mine (S_index S i z) k)\<close> \<open>l (ridge_mine S k) z - l (ridge_mine (S_index S i z) k) z \<le> dist (l (ridge_mine S k) z) (l (ridge_mine (S_index S i z) k) z)\<close> dual_order.trans by blast
  then show ?thesis
  by (simp add: dist_commute)
qed

    then have "(?loss_zi ?v) - (?loss_zi ?u) + (?loss_z ?u) - (?loss_z ?v) \<le>
                 2 * \<rho> * dist ?v ?u" using 1 2 by auto
    then have "(((?loss_zi ?v) - (?loss_zi ?u)) + ((?loss_z ?u) - (?loss_z ?v)))/n \<le>
                 (2 * \<rho> * dist ?v ?u)/n" using `n>0` by (simp add: divide_right_mono)

    then have "((?loss_zi ?v) - (?loss_zi ?u))/n + ((?loss_z ?u) - (?loss_z ?v))/n \<le>
                 (2 * \<rho> * dist ?v ?u)/n" by (simp add: add_divide_distrib)
    then have " k * norm(?v - ?u)^2  \<le> (2 * \<rho> * dist ?v ?u)/n" using ridge_stable 
      by (smt \<open>i \<in> {0..<n}\<close> assm1 assm2)
    then have " k * norm(?v - ?u)^2/k \<le> (2 * \<rho> * norm(?v - ?u)/ n)/ k" 
      using k_pos  divide_right_mono dist_norm by smt
    then have  " norm(?v - ?u)^2 \<le> 2 * \<rho> * norm(?v - ?u)/(n * k)"
      using k_pos by auto

    then have "norm(?v - ?u)^2 /norm(?v - ?u) \<le> (2 * \<rho> * norm(?v - ?u)/(n * k))/ norm(?v - ?u)"
      using  `norm(?v-?u) > 0` by (metis divide_le_cancel norm_not_less_zero)
    then have "norm (?v - ?u)* (norm(?v-?u)/norm(?v-?u)) \<le>  2 * \<rho> * (norm(?v-?u)/norm(?v-?u)) / (n*k)"
      by (smt \<open>0 < norm (ridge_mine (S_index S i z) k - ridge_mine S k)\<close> nonzero_mult_div_cancel_left power2_eq_square times_divide_eq_right)
     
    then have "norm (?v - ?u) \<le>  2 * \<rho>  / (n*k)" using \<open>0 < norm (?v - ?u)\<close> by auto
    then have "\<rho> * norm (?v - ?u) \<le> \<rho> * 2 * \<rho>  / (n*k)" using `\<rho> \<ge> 0`
      by (metis mult_left_mono semiring_normalization_rules(18) times_divide_eq_right)
    then have "\<rho> * norm (?v - ?u) \<le>  2 * \<rho> * \<rho>  / (n*k)"
      by (simp add: semiring_normalization_rules(7))
    then have "\<rho> * norm (?v - ?u) \<le>  2 * \<rho> ^2  / (n*k)" using power2_eq_square
      by (metis mult.commute semiring_normalization_rules(19))
    then show " (l ?v (S i)) - (l ?u (S i)) \<le> (2*\<rho>^2)/(k*n)" using 1 
      by (simp add: dist_norm mult.commute)
  qed
qed




end



lemma integral_bellow_const:
  fixes f :: "'a \<Rightarrow> real"
  assumes smaller_a: "AE x in M.  f x \<le> (a::real) "
  assumes pos_a: "a\<ge>0" 
  assumes M_finite: "finite_measure M"
  shows " integral\<^sup>L M f \<le> measure M (space M) *\<^sub>R a"
proof(cases "integrable M f")
  case True
   have 1: "integrable M (\<lambda> y. a)" using finite_measure.integrable_const M_finite by auto
   have "integral\<^sup>L M (\<lambda>y. a) = (\<integral>x. a \<partial>M)" by simp
   then have "integral\<^sup>L M (\<lambda>y. a) = measure M (space M) *\<^sub>R a" using lebesgue_integral_const by auto
   then have "AE x in M.  f x \<le> (\<lambda> y. a) x " using smaller_a 1 by auto
   then have " integral\<^sup>L M f \<le> integral\<^sup>L M (\<lambda>y. a)" using integral_mono_AE 1 
     using True by blast
  then show ?thesis
    using \<open>LINT y|M. a = Sigma_Algebra.measure M (space M) *\<^sub>R a\<close> by linarith
next
  case False
   have "integral\<^sup>L M f = 0" using False 
     by (simp add: not_integrable_integral_eq)
  then show ?thesis 
    by (simp add: pos_a)
qed

lemma univ_to_exist: "A\<noteq>{} \<Longrightarrow> \<forall>x\<in>A. P x \<Longrightarrow> \<exists>x\<in>A. P x" 
  by blast

 

locale arbitrary_S_lipschitz = learning_basics1 +
  fixes k :: "real" 
  assumes convl : "\<forall>y \<in> D. convex_on H (\<lambda> h. l h y)"
    and k_pos : "k>0"
    and lipschitz : "\<forall>y\<in>D . \<rho>-lipschitz_on H  (\<lambda> h. l h y)"
begin
lemma replace_one_stable: "\<forall>i\<in>{0..<n}. 
                        measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S. (l (ridge_mine (S_index S i (S n))k) (S i)) - 
                         (l  (ridge_mine S k) (S i))) \<le> 
                        (2*\<rho>^2)/(k*n)"
proof (rule)
  fix i
  assume " i \<in> {0..<n}"
  show "measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S. (l (ridge_mine (S_index S i (S n))k) (S i)) - 
                         (l  (ridge_mine S k) (S i))) \<le> 
                        (2*\<rho>^2)/(k*n)"
  proof -
    have 1:"\<forall>S\<in> (Samples (n+1) D). (l (ridge_mine (S_index S i (S n))k) (S i)) - 
                         (l  (ridge_mine S k) (S i)) \<le>  (2*\<rho>^2)/(k*(n+1))"
    proof
      fix S
      assume " S \<in> (Samples (n+1) D)"
      have "n \<in> {0..< n+1}" by auto
      then have " S n \<in> D" using sample_in_D[of "n+1"] `S \<in> (Samples (n+1) D)` 
        by blast
      then show " (l (ridge_mine (S_index S i (S n))k) (S i)) - 
                         (l  (ridge_mine S k) (S i)) \<le>  (2*\<rho>^2)/(k*(n+1))"
        using lipschitz_ridge_and_convex_loss.lipschitz_loss_diff_bounded 
            [of H X Y D "n+1" l S k] ` i \<in> {0..<n}`
        by (metis diff_ge_0_iff_ge lipschitz lipschitz_on_def)
    qed

    have finite_M:"finite_measure (Samples (n+1) D)" by simp
    have measure_M:"measure (Samples (n+1) D) (space (Samples (n+1) D)) = 1" by simp
    have pos_const: "(2*\<rho>^2)/(k*n) \<ge> 0" using k_pos by auto

    have "n \<ge> 1" using \<open>i \<in> {0..<n}\<close> by auto
    have "(2*\<rho>^2)/k \<ge> 0" 
      using k_pos by auto
    then have "(2*\<rho>^2)/(k*(n+1)) \<le> (2*\<rho>^2)/(k*n)"  using \<open>1 \<le> n\<close> frac_le by fastforce
    then have "\<forall>S\<in> (Samples (n+1) D). (l (ridge_mine (S_index S i (S n))k) (S i)) - 
                         (l  (ridge_mine S k) (S i)) \<le>  (2*\<rho>^2)/(k*n)" using 1 by auto
    then have "AE S in (Samples (n+1) D).  (l (ridge_mine (S_index S i (S n))k) (S i)) - 
                         (l  (ridge_mine S k) (S i)) \<le>  (2*\<rho>^2)/(k*n) "
      using AE_measure_pmf_iff by blast
    then have "AE S in (Samples (n+1) D).  (\<lambda> S. (l (ridge_mine (S_index S i (S n))k) (S i)) - 
                         (l  (ridge_mine S k) (S i))) S \<le>  (2*\<rho>^2)/(k*n)" 
      by blast

    then have " integral\<^sup>L (Samples (n+1) D) (\<lambda> S. (l (ridge_mine (S_index S i (S n))k) (S i)) - 
                         (l  (ridge_mine S k) (S i))) \<le>  (2*\<rho>^2)/(k*n)" 
      using finite_M measure_M pos_const 
        integral_bellow_const[of "(\<lambda> S. (l (ridge_mine (S_index S i (S n))k) (S i)) - 
                                   (l  (ridge_mine S k) (S i)))"
                                   " (2*\<rho>^2)/(k*n)"
                                  "(Samples (n+1) D)"] by simp
    then show ?thesis by auto
  qed
qed
   
lemma lipschitz_stable: " measure_pmf.expectation (Samples n D) (\<lambda> S.
                       pred_err_loss D l (ridge_mine S k) - train_err_loss S n l (ridge_mine S k))
                        \<le>  (2*\<rho>^2)/(k*n)"
proof -
  have " {0..<n} \<noteq> {}" using n_pos by auto
  have "\<forall> i \<in> {0..<n}. measure_pmf.expectation (Samples n D) (\<lambda> S.
                       pred_err_loss D l (ridge_mine S k) - train_err_loss S n l (ridge_mine S k))
                        \<le>  (2*\<rho>^2)/(k*n)" using train_val_diff replace_one_stable by simp

  then show ?thesis using `{0..<n} \<noteq> {}` by auto
qed



end

end
