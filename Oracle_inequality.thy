theory Oracle_inequality
  imports RLM_stable
begin

context arbitrary_S_lipschitz
begin
  

lemma expect_over_D: 
  shows "\<forall> i \<in> {0..<n}. measure_pmf.expectation (Samples n D) (\<lambda> S.  l h (S i)) =
                      measure_pmf.expectation D (\<lambda> z. l h z)"
proof 
  fix i
  assume "i\<in> {0..<n}" 
  have "\<forall> S \<in> (Samples n D). S i \<in> D"
    using \<open>i \<in> {0..<n}\<close> sample_in_D by blast
  have "\<forall> z \<in> D. \<exists> S \<in> (Samples n D). S i = z" 
    by (meson diff_ge_0_iff_ge le_numeral_extra(2) lipschitz lipschitz_on_def)
  then show "measure_pmf.expectation (Samples n D) (\<lambda> S.  l h (S i)) = 
                      measure_pmf.expectation D (\<lambda> z. l h z)"
    by (smt expect_const lipschitz lipschitz_on_nonneg same_integral_restricted)
qed



lemma expectation_train_err: 
  shows "measure_pmf.expectation (Samples n D)
                              (\<lambda> S. train_err_loss S n l h) =
                            pred_err_loss D l h"
proof -
  let ?I = "{0..<n}"
  let ?Dn = "Samples n D"
  let ?f = "(\<lambda> i. (\<lambda> S. l h (S i)))"
  have fin_I: "finite ?I" by auto
  have non_empty_I: "?I \<noteq> {}" using n_pos by auto


 have "measure_pmf.expectation (Samples n D) 
                              (\<lambda> S. train_err_loss S n l h) = 
   measure_pmf.expectation (Samples n D) 
                              (\<lambda> S.  sum (\<lambda>i. l h (S i) ) {0..<n} / n)"
   unfolding train_err_loss_def by auto

  also have " \<dots> =
  measure_pmf.expectation ?Dn
     (\<lambda>S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l h (S i)))"
     using  non_empty_I   by (simp add: integral_pmf_of_set)

  also have " \<dots> =
    measure_pmf.expectation (pmf_of_set {0..<n})
     (\<lambda>i. measure_pmf.expectation ?Dn (\<lambda>S. l h (S i)))"
  proof -
    have I_swap: 
    "\<forall> i\<in> ?I. \<forall> j \<in> ?I. measure_pmf.expectation ?Dn (\<lambda> S. ?f i S) =
       measure_pmf.expectation ?Dn (\<lambda> S. ?f j S)" using expect_over_D by auto
    have  f_nn: "\<forall> S \<in> (set_pmf ?Dn). \<forall> i \<in> ?I. ?f i S \<ge> 0" 
      using   sample_in_D  using lipschitz lipschitz_on_nonneg by blast

  
   show ?thesis
      using swap_set_expectation[of ?Dn ?I ?f] I_swap f_nn fin_I non_empty_I
      by blast
  qed
  also have "measure_pmf.expectation (pmf_of_set {0..<n})
     (\<lambda>i. measure_pmf.expectation ?Dn (\<lambda>S. l h (S i))) =
  sum  (\<lambda>i. measure_pmf.expectation ?Dn (\<lambda>S. l h (S i))) ?I / card ?I" 
    using integral_pmf_of_set non_empty_I by blast
  also have " \<dots> =  sum (\<lambda> i.  measure_pmf.expectation D (\<lambda> z. l h z)) ?I/ card ?I"
  using expect_over_D by auto
 
 also have "... = measure_pmf.expectation D (\<lambda> z. l h z)" 
   using non_empty_I by auto
   
  finally show ?thesis unfolding pred_err_loss_def  by auto 
qed

lemma "measure_pmf.expectation (Samples n D)
                              (\<lambda> S.  pred_err_loss D l (ridge_mine S k)) =
    measure_pmf.expectation (Samples n D) (\<lambda> S. train_err_loss S n l (ridge_mine S k)) 
   + measure_pmf.expectation (Samples n D)
        (\<lambda> S.  pred_err_loss D l (ridge_mine S k) - train_err_loss S n l (ridge_mine S k))"
  using pred_err_integrable train_err_integrable by simp

lemma
  shows "measure_pmf.expectation (Samples n D)
                              (\<lambda> S.  pred_err_loss D l (ridge_mine S k)) \<le>
    pred_err_loss D l h  + k * norm ( h )^2  + (2*\<rho>^2)/(k*n)"
proof -
  let ?pred_min = "(\<lambda> S. pred_err_loss D l (ridge_mine S k))"
  let ?train_min = "(\<lambda> S.  train_err_loss S n l (ridge_mine S k))"
  let ?Dn = "(Samples n D)"
  have 1: "integral\<^sup>L ?Dn (\<lambda> S. ?pred_min S) =
    integral\<^sup>L ?Dn (\<lambda> S. ?train_min S)  + integral\<^sup>L ?Dn  (\<lambda> S.  ?pred_min S - ?train_min S)"
    using pred_err_integrable train_err_integrable by simp
 
  then have "integral\<^sup>L ?Dn (\<lambda> S. ?train_min S) \<le>
            integral\<^sup>L ?Dn (\<lambda> S.  train_err_loss S n l h) + 
        integral\<^sup>L ?Dn (\<lambda> S. k * norm ( h )^2)"
  by (meson diff_ge_0_iff_ge lipschitz lipschitz_on_nonneg set_pmf_not_empty some_in_eq)
  then have "integral\<^sup>L ?Dn (\<lambda> S. ?train_min S) \<le>
            integral\<^sup>L ?Dn (\<lambda> S.  train_err_loss S n l h) +   k * norm ( h )^2" by simp
  then have "integral\<^sup>L ?Dn (\<lambda> S. ?train_min S) \<le>
             pred_err_loss D l h + k * norm ( h )^2" using expectation_train_err
    by auto
  then have "integral\<^sup>L ?Dn (\<lambda> S. ?pred_min S) \<le>
    pred_err_loss D l h + k * norm ( h )^2  + integral\<^sup>L ?Dn  (\<lambda> S.  ?pred_min S - ?train_min S)"
    using 1 by linarith

  then show ?thesis using lipschitz_stable by smt
qed

end

end