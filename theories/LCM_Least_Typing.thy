theory LCM_Least_Typing
  imports LCM_EventTyping
begin

section \<open>Closure and genuine leastness of event typing\<close>

text \<open>\<open>\<Gamma>*\<close> is the least solution of the seed and propagation constraints.\<close>

definition typing_solution ::
  "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> ('e \<Rightarrow> etype) \<Rightarrow> bool"
where
  "typing_solution G \<beta> \<Gamma> \<longleftrightarrow>
    (\<forall>e. base_val \<beta> e \<sqsubseteq>\<^sub>e \<Gamma> e) \<and>
    (\<forall>x y. (x,y) \<in> rf G \<union> data G \<longrightarrow>
       \<Gamma> x \<sqsubseteq>\<^sub>e \<Gamma> y) \<and>
    (\<forall>x y. (x,y) \<in> rfx G \<longrightarrow> snd (\<Gamma> x) \<le> snd (\<Gamma> y))"

lemma typesA_iff_least_arch:
  "(G, \<beta> \<turnstile>A e : l) \<longleftrightarrow> l \<le> least_arch G \<beta> e"
  by (cases l) (auto simp: least_arch_def typesA_Low split: if_splits)

lemma typesT_iff_least_tgt:
  "(G, \<beta> \<turnstile>T e : l) \<longleftrightarrow> l \<le> least_tgt G \<beta> e"
  by (cases l) (auto simp: least_tgt_def typesT_Low split: if_splits)

lemma least_arch_derivable:
  "G, \<beta> \<turnstile>A e : least_arch G \<beta> e"
  by (simp add: typesA_iff_least_arch)

lemma least_tgt_derivable:
  "G, \<beta> \<turnstile>T e : least_tgt G \<beta> e"
  by (simp add: typesT_iff_least_tgt)

lemma least_arch_seed:
  "fst (base_val \<beta> e) \<le> least_arch G \<beta> e"
proof -
  have "G, \<beta> \<turnstile>A e : fst (base_val \<beta> e)"
    by (rule typesA.BaseA) simp
  thus ?thesis by (simp add: typesA_iff_least_arch)
qed

lemma least_tgt_seed:
  "snd (base_val \<beta> e) \<le> least_tgt G \<beta> e"
proof -
  have "G, \<beta> \<turnstile>T e : snd (base_val \<beta> e)"
    by (rule typesT.BaseT) simp
  thus ?thesis by (simp add: typesT_iff_least_tgt)
qed

lemma least_arch_edge:
  assumes "(x,y) \<in> rf G \<union> data G"
  shows "least_arch G \<beta> x \<le> least_arch G \<beta> y"
proof -
  from assms have "G, \<beta> \<turnstile>A y : least_arch G \<beta> x"
  proof (elim UnE)
    assume edge: "(x,y) \<in> rf G"
    show ?thesis by (rule typesA.RFA[OF edge least_arch_derivable])
  next
    assume edge: "(x,y) \<in> data G"
    show ?thesis by (rule typesA.DataA[OF edge least_arch_derivable])
  qed
  thus ?thesis by (simp add: typesA_iff_least_arch)
qed

lemma least_tgt_edge:
  assumes "(x,y) \<in> rf G \<union> data G \<union> rfx G"
  shows "least_tgt G \<beta> x \<le> least_tgt G \<beta> y"
proof -
  from assms have "G, \<beta> \<turnstile>T y : least_tgt G \<beta> x"
  proof (elim UnE)
    assume edge: "(x,y) \<in> rf G"
    show ?thesis by (rule typesT.RFT[OF edge least_tgt_derivable])
  next
    assume edge: "(x,y) \<in> data G"
    show ?thesis by (rule typesT.DataT[OF edge least_tgt_derivable])
  next
    assume edge: "(x,y) \<in> rfx G"
    show ?thesis by (rule typesT.T_RFX[OF edge least_tgt_derivable])
  qed
  thus ?thesis by (simp add: typesT_iff_least_tgt)
qed

theorem gamma_star_solution:
  "typing_solution G \<beta> (gamma_star G \<beta>)"
  unfolding typing_solution_def
proof (intro conjI)
  show "\<forall>e. base_val \<beta> e \<sqsubseteq>\<^sub>e gamma_star G \<beta> e"
    by (simp add: etype_leq_def gamma_star_def least_arch_seed least_tgt_seed)
next
  show "\<forall>x y. (x,y) \<in> rf G \<union> data G \<longrightarrow>
      gamma_star G \<beta> x \<sqsubseteq>\<^sub>e gamma_star G \<beta> y"
  proof (intro allI impI)
    fix x y assume edge: "(x,y) \<in> rf G \<union> data G"
    have a: "least_arch G \<beta> x \<le> least_arch G \<beta> y"
      by (rule least_arch_edge[OF edge])
    have t: "least_tgt G \<beta> x \<le> least_tgt G \<beta> y"
      by (rule least_tgt_edge) (rule UnI1[OF edge])
    from a t show "gamma_star G \<beta> x \<sqsubseteq>\<^sub>e gamma_star G \<beta> y"
      by (simp add: etype_leq_def gamma_star_def)
  qed
next
  show "\<forall>x y. (x,y) \<in> rfx G \<longrightarrow>
      snd (gamma_star G \<beta> x) \<le> snd (gamma_star G \<beta> y)"
  proof (intro allI impI)
    fix x y assume edge: "(x,y) \<in> rfx G"
    have "least_tgt G \<beta> x \<le> least_tgt G \<beta> y"
      by (rule least_tgt_edge) (rule UnI2[OF edge])
    then show "snd (gamma_star G \<beta> x) \<le> snd (gamma_star G \<beta> y)"
      by (simp add: gamma_star_def)
  qed
qed

lemma solution_seed_arch:
  "typing_solution G \<beta> \<Gamma> \<Longrightarrow>
    fst (base_val \<beta> e) \<le> fst (\<Gamma> e)"
  unfolding typing_solution_def etype_leq_def by blast

lemma solution_seed_tgt:
  "typing_solution G \<beta> \<Gamma> \<Longrightarrow>
    snd (base_val \<beta> e) \<le> snd (\<Gamma> e)"
  unfolding typing_solution_def etype_leq_def by blast

lemma solution_rf_arch:
  assumes edge: "(x,y) \<in> rf G" and bound: "l \<le> fst (\<Gamma> x)"
    and sol: "typing_solution G \<beta> \<Gamma>"
  shows "l \<le> fst (\<Gamma> y)"
proof -
  have "fst (\<Gamma> x) \<le> fst (\<Gamma> y)"
    using edge sol unfolding typing_solution_def etype_leq_def by blast
  from bound this show ?thesis by (rule order_trans)
qed

lemma solution_data_arch:
  assumes edge: "(x,y) \<in> data G" and bound: "l \<le> fst (\<Gamma> x)"
    and sol: "typing_solution G \<beta> \<Gamma>"
  shows "l \<le> fst (\<Gamma> y)"
proof -
  have "fst (\<Gamma> x) \<le> fst (\<Gamma> y)"
    using edge sol unfolding typing_solution_def etype_leq_def by blast
  from bound this show ?thesis by (rule order_trans)
qed

lemma solution_rf_tgt:
  assumes edge: "(x,y) \<in> rf G" and bound: "l \<le> snd (\<Gamma> x)"
    and sol: "typing_solution G \<beta> \<Gamma>"
  shows "l \<le> snd (\<Gamma> y)"
proof -
  have "snd (\<Gamma> x) \<le> snd (\<Gamma> y)"
    using edge sol unfolding typing_solution_def etype_leq_def by blast
  from bound this show ?thesis by (rule order_trans)
qed

lemma solution_data_tgt:
  assumes edge: "(x,y) \<in> data G" and bound: "l \<le> snd (\<Gamma> x)"
    and sol: "typing_solution G \<beta> \<Gamma>"
  shows "l \<le> snd (\<Gamma> y)"
proof -
  have "snd (\<Gamma> x) \<le> snd (\<Gamma> y)"
    using edge sol unfolding typing_solution_def etype_leq_def by blast
  from bound this show ?thesis by (rule order_trans)
qed

lemma solution_rfx_tgt:
  assumes edge: "(x,y) \<in> rfx G" and bound: "l \<le> snd (\<Gamma> x)"
    and sol: "typing_solution G \<beta> \<Gamma>"
  shows "l \<le> snd (\<Gamma> y)"
proof -
  have "snd (\<Gamma> x) \<le> snd (\<Gamma> y)"
    using edge sol unfolding typing_solution_def by blast
  from bound this show ?thesis by (rule order_trans)
qed

lemma typesA_bounded_by_solution:
  "G, \<beta> \<turnstile>A e : l \<Longrightarrow>
   typing_solution G \<beta> \<Gamma> \<Longrightarrow> l \<le> fst (\<Gamma> e)"
proof (induction rule: typesA.induct)
  case BaseA
  from BaseA.hyps solution_seed_arch[OF BaseA.prems]
  show ?case by (rule order_trans)
next
  case RFA
  show ?case
    by (rule solution_rf_arch[OF RFA.hyps(1) RFA.IH[OF RFA.prems] RFA.prems])
next
  case DataA
  show ?case
    by (rule solution_data_arch[OF DataA.hyps(1) DataA.IH[OF DataA.prems] DataA.prems])
qed

lemma typesT_bounded_by_solution:
  "G, \<beta> \<turnstile>T e : l \<Longrightarrow>
   typing_solution G \<beta> \<Gamma> \<Longrightarrow> l \<le> snd (\<Gamma> e)"
proof (induction rule: typesT.induct)
  case BaseT
  from BaseT.hyps solution_seed_tgt[OF BaseT.prems]
  show ?case by (rule order_trans)
next
  case RFT
  show ?case
    by (rule solution_rf_tgt[OF RFT.hyps(1) RFT.IH[OF RFT.prems] RFT.prems])
next
  case DataT
  show ?case
    by (rule solution_data_tgt[OF DataT.hyps(1) DataT.IH[OF DataT.prems] DataT.prems])
next
  case T_RFX
  show ?case
    by (rule solution_rfx_tgt[OF T_RFX.hyps(1) T_RFX.IH[OF T_RFX.prems] T_RFX.prems])
qed

theorem gamma_star_least:
  assumes "typing_solution G \<beta> \<Gamma>"
  shows "gamma_star G \<beta> e \<sqsubseteq>\<^sub>e \<Gamma> e"
  unfolding gamma_star_def etype_leq_def
  using typesA_bounded_by_solution[OF least_arch_derivable assms]
        typesT_bounded_by_solution[OF least_tgt_derivable assms]
  by simp

theorem gamma_star_unique_least:
  assumes sol: "typing_solution G \<beta> \<Gamma>"
    and least: "\<And>\<Delta>. typing_solution G \<beta> \<Delta> \<Longrightarrow>
      \<forall>e. \<Gamma> e \<sqsubseteq>\<^sub>e \<Delta> e"
  shows "\<Gamma> = gamma_star G \<beta>"
proof (rule ext)
  fix e
  have lower: "gamma_star G \<beta> e \<sqsubseteq>\<^sub>e \<Gamma> e"
    by (rule gamma_star_least[OF sol])
  have upper: "\<Gamma> e \<sqsubseteq>\<^sub>e gamma_star G \<beta> e"
    using least[OF gamma_star_solution] by blast
  from lower upper show "\<Gamma> e = gamma_star G \<beta> e"
    unfolding etype_leq_def by (metis antisym prod_eqI)
qed

corollary unique_least_well_formed_typing:
  assumes "wf_base \<beta>"
  shows "typing_solution G \<beta> (gamma_star G \<beta>) \<and>
    (\<forall>e. fst (gamma_star G \<beta> e) \<le> snd (gamma_star G \<beta> e)) \<and>
    (\<forall>\<Gamma>. typing_solution G \<beta> \<Gamma> \<longrightarrow>
       (\<forall>e. gamma_star G \<beta> e \<sqsubseteq>\<^sub>e \<Gamma> e))"
proof (intro conjI)
  show "typing_solution G \<beta> (gamma_star G \<beta>)"
    by (rule gamma_star_solution)
next
  show "\<forall>e. fst (gamma_star G \<beta> e) \<le> snd (gamma_star G \<beta> e)"
    by (intro allI) (rule least_typing_invariant[OF assms])
next
  show "\<forall>\<Gamma>. typing_solution G \<beta> \<Gamma> \<longrightarrow>
       (\<forall>e. gamma_star G \<beta> e \<sqsubseteq>\<^sub>e \<Gamma> e)"
    by (intro allI impI) (erule gamma_star_least)
qed

end
