theory svm
  imports "RLM_stable" "Subgradients"
begin


locale soft_svm =
  fixes H :: "'b::euclidean_space set"
    and D :: "('b \<times> real) pmf"
    and n :: "nat"
    and k :: "real"
  fixes S :: "(nat \<Rightarrow> ('b \<times> real))"
    and \<rho> :: "real"
  assumes nnH: "H \<noteq> {}" 
    and  convH: "convex H"
    and n_pos: "n\<ge>1"
    and k_pos : "k>0"
    and rho_pos: "\<rho> > 0"
    and S_in_D: "S \<in> Samples n D" 
    and D_bounded : "\<forall>z \<in> D. norm (fst z) \<le> \<rho>"
    and y_abs : "\<forall>z\<in> D. abs (snd z) = 1"
begin
end


sublocale soft_svm \<subseteq> lipschitz_ridge_and_convex_loss H D n hinge_loss k \<rho>
proof unfold_locales 
  show "H \<noteq> {}" using nnH by auto
  show "convex H" using convH by auto
  show " \<forall>h\<in>H. \<forall>z\<in>set_pmf D. 0 \<le> hinge_loss h z" using hinge_loss_pos by auto
  show "\<forall>z\<in>set_pmf D. convex_on H (\<lambda>h. hinge_loss h z)" using hinge_loss_convex by auto
  show "1 \<le> n" using n_pos by auto
  show "k>0" using k_pos by auto
  show " 0 < \<rho>" using rho_pos by auto
  show " \<forall>y\<in>set_pmf D. \<rho>-lipschitz_on H (\<lambda>h. hinge_loss h y)"
  proof
    fix y 
    assume " y\<in> D" 
    then have "abs (snd y) = 1" using y_abs by auto
    then have "(norm (fst y))-lipschitz_on H (\<lambda> z. hinge_loss z y)" 
      using abv by auto
    then show "\<rho>-lipschitz_on H (\<lambda> z. hinge_loss z y)" using D_bounded `y\<in>D`
      using lipschitz_on_le by blast
  qed

  show "\<forall> h \<in> H. integrable D (\<lambda> z. hinge_loss h z)"
proof
  fix h
  assume "h\<in>H" 
  have "integrable D (\<lambda> z. 0)" by auto
  have "integrable D (\<lambda> z. (1 - (snd z) * inner h (fst z)))"
  proof 
    show "integrable D (\<lambda>x. 1)" by auto

    have 6: "integrable D (\<lambda> x. snd x *\<^sub>R fst x)"
    proof -
      have 1:"(\<lambda> x. 1) \<in> borel_measurable D" by auto
      have 2:"\<rho> \<noteq> \<infinity>" by auto
      have "integrable D (\<lambda>x. 1)" by auto
      then have "integral\<^sup>N D (\<lambda> x. 1) < \<infinity>" by simp
      have "AE x in D. norm (snd x *\<^sub>R fst x) \<le> \<rho> * ((\<lambda> x. 1) x)"
        using D_bounded y_abs
        by (simp add: AE_measure_pmf_iff)
      then have 3: "(\<integral>\<^sup>+x. norm (snd x *\<^sub>R fst x) \<partial>D) < \<infinity>" using D_bounded 
          nn_integral_mult_bounded_inf[of "(\<lambda> x. 1)" D \<rho> "(\<lambda> x. norm (snd x *\<^sub>R fst x))"] 1 2
        using rho_pos by auto
      have 4:"(\<lambda> x. snd x *\<^sub>R fst x) \<in> borel_measurable D" by auto
      show "integrable D (\<lambda> x. snd x *\<^sub>R fst x)" using 3 4
        using integrableI_bounded by blast
    qed


    have 5: "integrable D (\<lambda>x. (h \<bullet> snd x *\<^sub>R fst x))"
    proof(cases "h=0")
      case True
      then show ?thesis
        by simp
    next
      case False
     
      then show "integrable D (\<lambda>x. h \<bullet> snd x *\<^sub>R fst x)" 
        using integrable_inner_right[of h D "(\<lambda> x. snd x *\<^sub>R fst x)"] 6 
          `h \<noteq> 0` by auto
    qed
    have "(\<lambda> x. h \<bullet> snd x *\<^sub>R fst x) = (\<lambda> x.  snd x * (h \<bullet> fst x))" 
      by simp
    then show "integrable D (\<lambda>x. snd x * (h \<bullet> fst x))" using 5 by simp
  qed
  then show "integrable D (hinge_loss h)" unfolding hinge_loss.simps
    by auto
qed
qed

context soft_svm
begin
fun soft_svm :: "(nat \<Rightarrow> real)  \<Rightarrow> ('b \<Rightarrow> real)" where
  "soft_svm ksi  = (\<lambda> w. k * norm w^2 + (1/n)* (\<Sum>i\<in>{0..<n}. (ksi i)))"




lemma 
  fixes w :: "'b::euclidean_space"
  fixes ksi :: "(nat \<Rightarrow> real)"
  assumes "w\<in>H" 
  assumes "\<forall> i\<in>{0..<n}. ksi i \<ge> 0"
  assumes "\<forall>i\<in>{0..<n}. snd (S i) * (inner w (fst (S i))) \<ge> 1 - (ksi i)"
  shows"ridge_mine S k =  (SOME h. is_arg_min (soft_svm ksi) (\<lambda>s. s\<in>H) h)"
proof -

  oops

end