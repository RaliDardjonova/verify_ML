theory Strong_Convexity
  imports Main "HOL-Analysis.Analysis" "HOL-Analysis.Convex" 
begin

definition strong_convex_on :: "'a::euclidean_space set\<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "strong_convex_on s f k \<longleftrightarrow>
    (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y - (k/2) *\<^sub>R u *\<^sub>R v *\<^sub>R norm(x-y) *\<^sub>R norm(x-y) )" 


lemma help2_3 : "norm (x+y)^2 = norm x ^ 2 + 2 *\<^sub>R (inner x y) + norm y ^ 2" 
  for x y :: "'a::euclidean_space"
  by (smt inner_commute inner_left_distrib power2_norm_eq_inner scaleR_2)

lemma help2_31 : "norm (x - y)^2 = norm x ^ 2 - 2 *\<^sub>R (inner x y) + norm y ^ 2" 
  for x y :: "'a::euclidean_space"
  using help2_3
  by (simp add: inner_commute inner_diff_right power2_norm_eq_inner)


lemma help2_2 : "(norm (u  *\<^sub>R x +  v  *\<^sub>R y))^2 = norm (u *\<^sub>R x)^2 + (2 * u * v) *\<^sub>R (inner x y) + norm (v *\<^sub>R y)^2 "
  for x y :: "'a::euclidean_space"
  by (simp add: help2_3)

lemma help2_4: "norm (u *\<^sub>R x)^2  = u^2 * norm(x)^2"
proof -
  have "abs(u)^2 = u^2" by simp
  then show "norm (u *\<^sub>R x)^2  = u^2 * norm(x)^2" 
    using norm_scaleR power2_eq_square
    by (simp add: power_mult_distrib)
qed

lemma k_w2_2_convex: "strong_convex_on s (\<lambda> w. k *\<^sub>R norm(w) *\<^sub>R norm(w)) (2*k)"
  for s :: "'a::euclidean_space set"
proof -
  let ?f = "(\<lambda> w. k *\<^sub>R norm(w) *\<^sub>R norm(w))"
  have "\<forall> x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0.( u + v = 1 \<longrightarrow>
     ?f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * ?f x + v * ?f y - (2*k/2) *\<^sub>R u *\<^sub>R v *\<^sub>R norm(x-y) *\<^sub>R norm(x-y) )"
  proof (rule)+
    fix x assume"x\<in>s"
    fix y assume"y\<in>s"
    fix u assume"(u::real) \<ge> 0"
    fix v assume"(v::real) \<ge> 0"
    assume "u+v = 1"
    then show "k *\<^sub>R norm (u *\<^sub>R x + v *\<^sub>R y) *\<^sub>R norm (u *\<^sub>R x + v *\<^sub>R y)
         \<le> u * k *\<^sub>R norm x *\<^sub>R norm x + v * k *\<^sub>R norm y *\<^sub>R norm y - (2 * k / 2) *\<^sub>R u *\<^sub>R  v *\<^sub>R norm (x - y) *\<^sub>R norm (x - y)"
    proof -   
      have  "?f  (u *\<^sub>R x + v *\<^sub>R y) = k*(norm (u  *\<^sub>R x +  v  *\<^sub>R y))^2" 
        by (simp add: power2_eq_square)
      also  have "k*(norm (u  *\<^sub>R x +  v  *\<^sub>R y))^2 =
        k*(norm (u *\<^sub>R x)^2 + (2 * u * v) *\<^sub>R (inner x y) + norm (v *\<^sub>R y)^2)" by (simp add: help2_2)
      also have " k*(norm (u *\<^sub>R x)^2 + (2 * u * v) *\<^sub>R (inner x y) + norm (v *\<^sub>R y)^2) =
             k*(u^2 * norm (x)^2 + (2 * u * v) *\<^sub>R (inner x y) + v^2 * norm (y)^2)" using help2_4 by metis
      also  have "k*(u^2 * norm (x)^2 + (2 * u * v) *\<^sub>R (inner x y) + v^2 * norm (y)^2)  =
                k*u^2 * norm (x)^2 + (2 * k * u * v) *\<^sub>R (inner x y) + k* v^2 * norm (y)^2"
        using `u+v = 1`  by (simp add: distrib_left)
      also have " k*u^2 * norm (x)^2 + (2 * k * u * v) *\<^sub>R (inner x y) + k* v^2 * norm (y)^2 
                            + k * u * v * norm(x)^2 + k * u * v * norm(y)^2 
                            - k * u * v * norm(x)^2 - k * u * v *norm(y)^2 = 
                            k*u*norm(x)^2 + (2 * k * u * v) *\<^sub>R (inner x y) + k* v * norm (y)^2 
                              - k * u * v * norm(x)^2 - k * u * v *norm(y)^2" using `u+v = 1`  by algebra
      also have "k*u*norm(x)^2 + (2 * k * u * v) *\<^sub>R (inner x y) + k* v * norm (y)^2 
                              - k * u * v * norm(x)^2 - k * u * v *norm(y)^2 = 
                                k*u*norm(x)^2  + k* v * norm (y)^2 
                              - (k * u * v) * norm(x)^2  +(k * u * v) * 2  *\<^sub>R (inner x y) -  (k * u * v) *norm(y)^2" by simp
      also have "   k*u*norm(x)^2  + k* v * norm (y)^2 
                              - (k * u * v) * norm(x)^2  +(k * u * v) * 2  *\<^sub>R (inner x y) -  (k * u * v) *norm(y)^2 = 
                               k*u*norm(x)^2  + k* v * norm (y)^2 
                              - (k * u * v) * ( norm(x)^2  -  2  *\<^sub>R (inner x y) + norm(y)^2)" using distrib_left by argo
      also have " k*u*norm(x)^2  + k* v * norm (y)^2 
                              - (k * u * v) * ( norm(x)^2  -  2  *\<^sub>R (inner x y) + norm(y)^2) =
                           k*u*norm(x)^2  + k* v * norm (y)^2  - (k * u * v) * norm(x - y)^2" 
        by (simp add: help2_31)

      finally have "?f  (u *\<^sub>R x + v *\<^sub>R y) =  u * ?f x + v * ?f y - (2*k/2) *\<^sub>R u *\<^sub>R v *\<^sub>R norm(x-y) *\<^sub>R norm(x-y)"
        by  (simp add: power2_eq_square help2_31)

      then show ?thesis   by linarith
    qed
  qed
  then show ?thesis unfolding strong_convex_on_def by blast
qed

instantiation "fun" :: (type, plus) plus
begin

definition fun_plus_def: "A + B = (\<lambda>x. A x + B x)"

lemma minus_apply [simp, code]: "(A + B) x = A x + B x"
  by (simp add: fun_plus_def)

instance ..

end




lemma strong_convex_sum: "strong_convex_on s f k \<and> convex_on s g  \<longrightarrow> 
                            strong_convex_on s ( f + g) k"
proof 
  assume "strong_convex_on s f k \<and> convex_on s g"
  then show "strong_convex_on s (f + g) k"
  proof
    have "strong_convex_on s f k" using `strong_convex_on s f k \<and> convex_on s g` by simp
    have "convex_on s g" using `strong_convex_on s f k \<and> convex_on s g` by simp
    have  "(\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     (f+g) (u *\<^sub>R x + v *\<^sub>R y) \<le> 
      u * (f+g) x + v * (f+g) y - (k/2) *\<^sub>R u *\<^sub>R v *\<^sub>R norm(x-y) *\<^sub>R norm(x-y) )"
    proof (rule)+
      fix x assume"x\<in>s"
      fix y assume"y\<in>s"
      fix u assume"(u::real) \<ge> 0"
      fix v assume"(v::real) \<ge> 0"
      assume "u+v = 1"
      then show "(f+g) (u *\<^sub>R x + v *\<^sub>R y) \<le> 
      u * (f+g) x + v * (f+g) y - (k/2) *\<^sub>R u *\<^sub>R v *\<^sub>R norm(x-y) *\<^sub>R norm(x-y)"
      proof -
        have 1: "f (u *\<^sub>R x + v *\<^sub>R y) \<le> 
           u * f x + v * f y - (k/2) *\<^sub>R u *\<^sub>R v *\<^sub>R norm(x-y) *\<^sub>R norm(x-y)"
          using  \<open>0 \<le> u\<close> \<open>0 \<le> v\<close> \<open>u + v = 1\<close> \<open>x \<in> s\<close> \<open>y \<in> s\<close> `strong_convex_on s f k` unfolding strong_convex_on_def by blast

        have 2: " g (u *\<^sub>R x + v *\<^sub>R y) \<le> u * g x + v * g y" 
          using \<open>0 \<le> u\<close> \<open>0 \<le> v\<close> \<open>u + v = 1\<close> \<open>x \<in> s\<close> \<open>y \<in> s\<close> `convex_on s g ` unfolding convex_on_def by blast

        have 3:"f (u *\<^sub>R x + v *\<^sub>R y)  +  g (u *\<^sub>R x + v *\<^sub>R y) \<le> 
           u * f x + v * f y - (k/2) *\<^sub>R u *\<^sub>R v *\<^sub>R norm(x-y) *\<^sub>R norm(x-y)  + 
       u * g x + v * g y "
          using 1 2 by linarith
         then show ?thesis  by (simp add: distrib_left)
      qed
    qed
    then show ?thesis unfolding strong_convex_on_def by auto
  qed
qed

lemma help7: 
  assumes "(l::real)<0" 
  assumes "\<forall>x. norm (f x - l)< -l"
  shows "\<forall>x. f x < 0"
proof (rule ccontr)
    assume "\<not> (\<forall>x. f x < 0)"
    then show False using assms(2)  real_norm_def by smt
  qed
    
lemma LIM_fun_less_zero1: "f \<midarrow>a\<rightarrow> l \<Longrightarrow> l < 0 \<Longrightarrow> \<exists>r>0. \<forall>x. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow> f x < 0"
for a :: "'b::real_normed_vector" and  l :: "real"
proof -
  assume "f \<midarrow>a\<rightarrow> l" "l < 0" 
  then have "\<exists>r. 0 < r \<and> (\<forall>x. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow> norm (f x - l)< -l)" 
    using LIM_D[of f l a "-l"]
    by (simp add: norm_minus_commute)
  then obtain r where "0 < r" "(\<forall>x. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow> norm (f x - l)< -l)" by auto
  then have "(\<forall>x. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow>  f x < 0)" 
    using `l<0` help7  by auto
  then show ?thesis
    using \<open>0 < r\<close> by blast
qed

lemma metric_LIM_le2:
  fixes a :: "real"
  assumes "f \<midarrow>a\<rightarrow> (l::real)"
  assumes "a\<ge>0"
    and "\<forall>x>a. f x \<ge> 0"
  shows " l \<ge> 0" 
proof (rule ccontr)
  assume "\<not> (l \<ge> 0)"
  then have " l < 0"  by simp
  then have " \<exists>r>0. \<forall>x. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow> f x < 0" using assms(1) LIM_fun_less_zero1
    by blast
  then have "\<exists>r>0. \<forall>x>a. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow> f x < 0 \<and> f x \<ge> 0" using assms(3) by blast
  then have "\<exists>r>0. \<forall>x>a. norm(a - x) < r \<longrightarrow> False" by force
  then have "\<exists>r>0. \<forall>x>a. norm(a - x) \<ge> r" by force
  then obtain r where "r>0" and " \<forall>x>a. norm(a - x) \<ge> r" by auto
  then have 1: "\<forall>x>a. norm(a - x) \<ge> r" by auto
  have  "\<exists>k. k>0 \<and>  k <r " using `r>0`  by (simp add: dense)
  then obtain k where "k>0" and "k < r" by auto
  then have "\<exists> x. x>a \<and> x-a = k" by smt
  then have "\<exists> x>a. norm(x-a) = k" by auto
  then have "\<exists> x>a. norm(x-a) < r" using `k<r` by auto
  then have "\<exists> x>a. norm(a-x) < r \<and> norm(a - x) \<ge> r" using 1 by auto
  then show False using LIM_fun_less_zero1 
    by linarith
qed

lemma metric_LIM_le_zero:
  fixes a :: "real"
  assumes "f \<midarrow>a\<rightarrow> (l::real)"
  assumes "a\<ge>0"
    and "\<exists>r>0. \<forall>x>a. norm(a-x) < r \<longrightarrow> f x \<ge> 0"
  shows " l \<ge> 0" 
proof (rule ccontr)
  assume "\<not> (l \<ge> 0)"
  then have " l < 0"  by simp
  then have " \<exists>r>0. \<forall>x. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow> f x < 0" using assms(1) LIM_fun_less_zero1
    by blast
  then obtain r where "r>0" and 1: "\<forall>x>a. norm(a - x) < r \<longrightarrow> f x < 0" by auto
  obtain r1 where "r1>0" and 2: "\<forall>x>a. norm(a-x) < r1 \<longrightarrow> f x \<ge> 0" using assms(3)
    by auto
  let ?min_r = "min r1 r"
  have 3: " r \<ge> ?min_r " by auto
  have 4: " r1 \<ge> ?min_r " by auto
  have "?min_r>0" using `r>0` `r1>0` by auto
  then have 5: "\<forall>x>a. norm(a - x) < ?min_r \<longrightarrow> f x < 0" using 1 3 by auto
  then have "\<forall>x>a. norm(a - x) < ?min_r \<longrightarrow> f x \<ge> 0" using 2 4 by auto
  then have "\<forall>x>a. norm(a - x) < ?min_r \<longrightarrow> f x < 0 \<and> f x \<ge> 0" using 5 by blast
  then have 6: "\<forall>x>a. norm(a - x) \<ge> ?min_r" by force

  then have  "\<exists>k. k>0 \<and>  k <?min_r " using `?min_r>0` dense by blast 
  then obtain k where "k>0" and "k < ?min_r" by auto
  then have "\<exists> x. x>a \<and> x-a = k" by smt
  then have "\<exists> x>a. norm(x-a) = k" by auto
  then have "\<exists> x>a. norm(x-a) < ?min_r" using `k<?min_r` by auto
  then have "\<exists> x>a. norm(a-x) < ?min_r \<and> norm(a - x) \<ge> ?min_r" using 6 by auto
  then show False using LIM_fun_less_zero1 
    by linarith
qed


lemma help_8: "dist t 0 < ( r/norm(w-x)^2 *\<^sub>R norm(k/2)) \<longrightarrow>
            norm(t) *\<^sub>R norm(w-x)^2 *\<^sub>R norm(k/2) < r" 
proof 
  assume "dist t 0 < ( r/norm(w-x)^2 *\<^sub>R norm(k/2))" 
  then have 1: " norm(t) < (r/norm(w-x)^2 *\<^sub>R norm(k/2))" by auto
  then have 3: "norm(w-x)^2 *\<^sub>R norm(k/2) > 0"
    by (smt div_by_0 norm_ge_zero norm_scaleR power2_less_0 real_scaleR_def)
  have 2: " norm(t) \<ge> 0" by auto
  then have " norm(t) *\<^sub>R norm(w-x)^2 *\<^sub>R norm(k/2) < 
               (r/norm(w-x)^2 *\<^sub>R norm(k/2)) *\<^sub>R norm(w-x)^2 *\<^sub>R norm(k/2)" 
    using 1 2 mult_less_le_imp_less[of "norm t" 
                                      "(r/norm(w-x)^2 *\<^sub>R norm(k/2))" 
                                      "norm(w-x)^2 *\<^sub>R norm(k/2)" 
                                      "norm(w-x)^2 *\<^sub>R norm(k/2)"] by auto
  then show "norm(t) *\<^sub>R norm(w-x)^2 *\<^sub>R norm((k/2)) < r" using 3 
    by (smt nonzero_mult_div_cancel_right real_scaleR_def times_divide_eq_left)
qed

lemma strongly_convex_min: 
  assumes "strong_convex_on s f k"
  assumes "x \<in> s"
  assumes "\<forall>y. (f x \<le> f y)"
  assumes "w \<in> s"
  shows "f w - f x \<ge> (k/2)*norm(w - x)^2"
proof (cases "w = x")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis
  proof(cases "k = 0")
    case True
    then show ?thesis using assms(3) by auto
  next
    case False
    then show ?thesis 
    proof -
      have "(\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y - (k/2) *\<^sub>R u *\<^sub>R v *\<^sub>R norm(x-y)^2)"
        using assms(1)  by (simp add: strong_convex_on_def power2_eq_square)
      then have " \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R w + v *\<^sub>R x) \<le> u * f w + v * f x - (k/2) *\<^sub>R u *\<^sub>R v *\<^sub>R norm(w-x)^2"
        using assms(2) assms(4) by blast
      then have " \<forall>u>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R w + v *\<^sub>R x)/u \<le> (u * f w + v * f x - (k/2) *\<^sub>R u *\<^sub>R v *\<^sub>R norm(w-x) ^2)/u"
        by (meson divide_right_mono less_eq_real_def)
      then have " \<forall>u>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R w + v *\<^sub>R x)/u \<le> (u * f w)/u + (v * f x)/u - ((k/2) *\<^sub>R u *\<^sub>R v *\<^sub>R norm(w-x)^2)/u"
        by (simp add: add_divide_distrib diff_divide_distrib)
      then have " \<forall>u>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R w + v *\<^sub>R x)/u \<le> f w + (v / u)* f x - (k/2) *\<^sub>R v *\<^sub>R norm(w-x)^2" by simp
      then have " \<forall>u>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R w + v *\<^sub>R x)/u \<le> f w +  ((1 - u)/ u)* f x - (k/2) *\<^sub>R v *\<^sub>R norm(w-x)^2" by smt
      then have " \<forall>u>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R w + v *\<^sub>R x)/u  \<le> f w + (1/u + (-u/u)) * f x - (k/2) *\<^sub>R v *\<^sub>R norm(w-x)^2"
        by (simp add: diff_divide_distrib)
      then have " \<forall>u>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R w + v *\<^sub>R x)/u  \<le> f w + (1/u)* f x + (-u/u)*f x - (k/2) *\<^sub>R v *\<^sub>R norm(w-x)^2"
        by (smt distrib_right)
      then have "  \<forall>u>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R w + v *\<^sub>R x)/u  \<le> f w + (1/u)* f x - f x - (k/2) *\<^sub>R v *\<^sub>R norm(w-x)^2"
        by simp
      then have "\<forall>u>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R w + v *\<^sub>R x)/u - (1/u)* f x \<le> f w  - f x - (k/2) *\<^sub>R v *\<^sub>R norm(w-x)^2" 
        by force
      then have "\<forall>u>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     (f (u *\<^sub>R w + v *\<^sub>R x) - f x )/u \<le> f w  - f x - (k/2) *\<^sub>R v *\<^sub>R norm(w-x)^2" 
        by (simp add: diff_divide_distrib)
      then have 1:"\<forall>u>0. u <= 1 \<longrightarrow>
     (\<lambda> t. (f (t *\<^sub>R w + (1-t) *\<^sub>R x) - f x )/t) u \<le> (\<lambda> t. f w  - f x - (k/2) *\<^sub>R (1-t) *\<^sub>R norm(w-x)^2) u" by smt

      have "\<forall>u>0. u <= 1 \<longrightarrow>
    (\<lambda> t. (f (t *\<^sub>R w + (1-t) *\<^sub>R x) - f x )/t) u  \<ge> 0" using assms(3) by auto
      then have 11 : "\<forall>u>0. u <= 1 \<longrightarrow>
    0 \<le> (\<lambda> t. f w  - f x - (k/2) *\<^sub>R (1-t) *\<^sub>R norm(w-x)^2) u" using 1 by fastforce

      let ?f = "(\<lambda> t. f w  - f x - (k/2) *\<^sub>R (1-t) *\<^sub>R norm(w-x)^2)"
      let ?L = "(f w  - f x - (k/2) *\<^sub>R norm(w-x)^2)"
      have "\<forall>t. dist (?f t) ?L = norm(?f t - ?L)"
        using dist_norm by blast
      then have 2: "\<forall>t. norm(?f t - ?L) = norm(t *\<^sub>R(k/2) *\<^sub>R norm(w-x)^2)" 
        by (smt scaleR_collapse scale_left_commute)
      then have 3: "\<forall>t.  norm(t *\<^sub>R(k/2) *\<^sub>R norm(w-x)^2)  =   norm(norm(w-x)^2 *\<^sub>R t *\<^sub>R (k/2))"
        by (smt inner_commute inner_real_def inner_scaleR_right real_scaleR_def)
      have " norm(w-x)^2 \<ge> 0" by auto
      then have "\<forall>t.  norm(norm(w-x)^2 *\<^sub>R t *\<^sub>R (k/2)) =
               norm(w-x)^2 *\<^sub>R norm( t *\<^sub>R (k/2))"
        by (smt norm_scaleR real_scaleR_def)
      then have 4: "\<forall>t. norm(?f t - ?L) =  norm(w-x)^2 *\<^sub>R norm( t *\<^sub>R (k/2))" using 2 3 by simp
      then have  "\<forall>t. norm(w-x)^2 *\<^sub>R norm( t *\<^sub>R (k/2))
           =  norm(w-x)^2 *\<^sub>R norm(t) *\<^sub>R norm((k/2))" 
        by (metis norm_mult real_scaleR_def)
      then have 5:"\<forall>t. norm(?f t - ?L) = norm(t) *\<^sub>R norm(w-x)^2 *\<^sub>R norm((k/2))" using 4 by simp
      then have "\<forall>t. dist t 0 = norm(t)" by auto
      then have "\<forall>r. \<forall>t. t \<noteq> 0 \<and> dist t 0 < ( r/norm(w-x)^2 *\<^sub>R norm((k/2))) \<longrightarrow>
            norm(t) *\<^sub>R norm(w-x)^2 *\<^sub>R norm((k/2)) < r" using help_8 by blast

      then have 6: "\<forall>r. \<forall>t. t \<noteq> 0 \<and> dist t 0 < ( r/norm(w-x)^2 *\<^sub>R norm((k/2))) \<longrightarrow>
            dist (?f t) ?L < r" using 5 dist_norm by metis
      have "norm(w-x)^2 *\<^sub>R norm((k/2)) > 0" using `w \<noteq> x` `k \<noteq> 0` by auto
      then have "\<forall>r>0. (r/norm(w-x)^2 *\<^sub>R norm((k/2))) > 0"
        using divide_pos_pos by blast
      then have "\<forall>r > 0. \<exists>s > 0. \<forall>t. t \<noteq> 0 \<and> dist t 0 < s \<longrightarrow> dist (?f t) ?L < r" using 6 by auto
      then have 7:" ?f \<midarrow>0\<rightarrow> ?L" unfolding LIM_def by auto

      then have "\<forall>u>0. u <= 1 \<longrightarrow> 0 \<le> ?f u" using 11 by simp
      then have "\<exists>r>0. \<forall>u>0.  u \<le> r \<longrightarrow> 0 \<le> ?f u"  using zero_less_one by blast
      then have "\<exists>r>0.\<forall>u>0. norm (0 -u) < r \<longrightarrow> 0 \<le> ?f u" by auto 
      then have "?L \<ge> 0" using metric_LIM_le_zero using 7 by blast

      then show ?thesis by auto
    qed
  qed
qed

end





