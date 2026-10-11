theory LCM_EventTyping
  imports LCM_Graph
begin

section \<open>Event Typing\<close>

text \<open>Each rule gives a lower bound on an event's value-flow label. With \<open>\<le>\<close>
  in the base rule, \<open>Low\<close> is always derivable.\<close>

subsection \<open>Architectural typing judgment\<close>

inductive typesA ::
    "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e \<Rightarrow> label \<Rightarrow> bool"
    ("_,_ \<turnstile>A _ : _" [60,60,60,60] 61)
where
  BaseA:
    "l \<le> fst (base_val \<beta> e) \<Longrightarrow>
     G, \<beta> \<turnstile>A e : l"
| RFA:
    "(w, r) \<in> rf G \<Longrightarrow>
     G, \<beta> \<turnstile>A w : l \<Longrightarrow>
     G, \<beta> \<turnstile>A r : l"
| DataA:
    "(x, y) \<in> data G \<Longrightarrow>
     G, \<beta> \<turnstile>A x : l \<Longrightarrow>
     G, \<beta> \<turnstile>A y : l"

subsection \<open>Target typing judgment\<close>

inductive typesT ::
    "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e \<Rightarrow> label \<Rightarrow> bool"
    ("_,_ \<turnstile>T _ : _" [60,60,60,60] 61)
where
  BaseT:
    "l \<le> snd (base_val \<beta> e) \<Longrightarrow>
     G, \<beta> \<turnstile>T e : l"
| RFT:
    "(w, r) \<in> rf G \<Longrightarrow>
     G, \<beta> \<turnstile>T w : l \<Longrightarrow>
     G, \<beta> \<turnstile>T r : l"
| DataT:
    "(x, y) \<in> data G \<Longrightarrow>
     G, \<beta> \<turnstile>T x : l \<Longrightarrow>
     G, \<beta> \<turnstile>T y : l"
| T_RFX:
    "(w, r) \<in> rfx G \<Longrightarrow>
     G, \<beta> \<turnstile>T w : l \<Longrightarrow>
     G, \<beta> \<turnstile>T r : l"

subsection \<open>Low is always derivable\<close>

lemma typesA_Low: "G, \<beta> \<turnstile>A e : Low"
  by (rule BaseA) simp

lemma typesT_Low: "G, \<beta> \<turnstile>T e : Low"
  by (rule BaseT) simp

subsection \<open>A-derivations lift to T-derivations\<close>

lemma typesA_implies_typesT_aux:
  "G, \<beta> \<turnstile>A e : l \<Longrightarrow> wf_base \<beta> \<Longrightarrow> G, \<beta> \<turnstile>T e : l"
proof (induction rule: typesA.induct)
  case (BaseA l \<beta> e)
  from BaseA.hyps have H1: "l \<le> fst (base_val \<beta> e)" .
  from BaseA.prems have H2: "fst (base_val \<beta> e) \<le> snd (base_val \<beta> e)"
    by (rule wf_base_val)
  from H1 H2 have "l \<le> snd (base_val \<beta> e)" by (rule order_trans)
  thus ?case by (rule typesT.BaseT)
next
  case RFA
  thus ?case by (blast intro: typesT.RFT)
next
  case DataA
  thus ?case by (blast intro: typesT.DataT)
qed

lemma typesA_implies_typesT:
  assumes wf: "wf_base \<beta>" and ty: "G, \<beta> \<turnstile>A e : l"
  shows "G, \<beta> \<turnstile>T e : l"
  by (rule typesA_implies_typesT_aux[OF ty wf])

subsection \<open>Least event typing\<close>

text \<open>On two labels the least type is \<open>High\<close> iff \<open>High\<close> is derivable.\<close>

definition least_arch ::
    "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e \<Rightarrow> label" where
  "least_arch G \<beta> e \<equiv>
     if G, \<beta> \<turnstile>A e : High then High else Low"

definition least_tgt ::
    "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e \<Rightarrow> label" where
  "least_tgt G \<beta> e \<equiv>
     if G, \<beta> \<turnstile>T e : High then High else Low"

definition gamma_star ::
    "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e \<Rightarrow> etype"
    ("\<Gamma>*") where
  "\<Gamma>* G \<beta> e \<equiv> (least_arch G \<beta> e, least_tgt G \<beta> e)"

subsection \<open>Pair-type invariant\<close>

theorem least_typing_invariant:
  assumes wf: "wf_base \<beta>"
  shows "fst (\<Gamma>* G \<beta> e) \<le> snd (\<Gamma>* G \<beta> e)"
proof -
  have arch_to_tgt: "G, \<beta> \<turnstile>A e : High \<Longrightarrow> G, \<beta> \<turnstile>T e : High"
    by (rule typesA_implies_typesT[OF wf])
  show ?thesis
  proof (cases "G, \<beta> \<turnstile>A e : High")
    case True
    hence "G, \<beta> \<turnstile>T e : High" by (rule arch_to_tgt)
    thus ?thesis by (simp add: gamma_star_def least_arch_def least_tgt_def)
  next
    case False
    thus ?thesis by (simp add: gamma_star_def least_arch_def least_tgt_def)
  qed
qed

subsection \<open>Monotonicity in rfx\<close>

lemma typesT_mono_rfx_aux:
  "G0, \<beta> \<turnstile>T e : l \<Longrightarrow>
   rfx G0 \<subseteq> rfx G \<Longrightarrow> rf G0 = rf G \<Longrightarrow> data G0 = data G \<Longrightarrow>
   G, \<beta> \<turnstile>T e : l"
proof (induction arbitrary: G rule: typesT.induct)
  case BaseT
  thus ?case by (blast intro: typesT.BaseT)
next
  case RFT
  thus ?case by (metis typesT.RFT)
next
  case DataT
  thus ?case by (metis typesT.DataT)
next
  case T_RFX
  thus ?case by (meson typesT.T_RFX subsetD)
qed

lemma typesT_mono_rfx:
  assumes "G', \<beta> \<turnstile>T e : l"
    and rfx_sub: "rfx G' \<subseteq> rfx G"
    and rf_eq:   "rf G'   = rf G"
    and data_eq: "data G'  = data G"
  shows "G, \<beta> \<turnstile>T e : l"
  using typesT_mono_rfx_aux[OF assms(1) rfx_sub rf_eq data_eq] .

lemma typesA_replace_graph:
  "G0, \<beta> \<turnstile>A e : l \<Longrightarrow>
   rf G0 = rf G \<Longrightarrow> data G0 = data G \<Longrightarrow>
   G, \<beta> \<turnstile>A e : l"
proof (induction arbitrary: G rule: typesA.induct)
  case BaseA
  thus ?case by (blast intro: typesA.BaseA)
next
  case RFA
  thus ?case by (metis typesA.RFA)
next
  case DataA
  thus ?case by (metis typesA.DataA)
qed

lemma typesA_independent_rfx:
  assumes rf_eq:   "rf G'   = rf G"
    and data_eq: "data G'  = data G"
  shows "G, \<beta> \<turnstile>A e : l \<longleftrightarrow> G', \<beta> \<turnstile>A e : l"
proof
  assume "G, \<beta> \<turnstile>A e : l"
  thus "G', \<beta> \<turnstile>A e : l"
    using typesA_replace_graph[of G \<beta> e l G'] rf_eq data_eq by simp
next
  assume "G', \<beta> \<turnstile>A e : l"
  thus "G, \<beta> \<turnstile>A e : l"
    using typesA_replace_graph[of G' \<beta> e l G] rf_eq data_eq by simp
qed

theorem gamma_star_mono_rfx:
  assumes sub: "G' \<preceq>\<^sub>G G"
    and wf: "wf_base \<beta>"
  shows "\<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e"
proof -
  have rfx_sub: "rfx G' \<subseteq> rfx G" using sub by blast
  have rf_eq:   "rf G'   = rf G"   using sub by blast
  have data_eq: "data G' = data G"  using sub by blast
  (* Architectural component is unchanged *)
  have arch_eq:
    "G', \<beta> \<turnstile>A e : High \<longleftrightarrow> G, \<beta> \<turnstile>A e : High"
    using typesA_independent_rfx[OF rf_eq data_eq] by blast
  (* Target: derivable in G' \<Rightarrow> derivable in G (G has more edges) *)
  have tgt_mono:
    "G', \<beta> \<turnstile>T e : High \<Longrightarrow> G, \<beta> \<turnstile>T e : High"
    using typesT_mono_rfx[OF _ rfx_sub rf_eq data_eq] by blast
  show ?thesis
  proof (cases "G', \<beta> \<turnstile>T e : High")
    case True
    have "G, \<beta> \<turnstile>T e : High" using True tgt_mono by blast
    thus ?thesis
      by (simp add: gamma_star_def least_arch_def least_tgt_def
                    etype_leq_def arch_eq)
  next
    case False
    thus ?thesis
      by (simp add: gamma_star_def least_arch_def least_tgt_def
                    etype_leq_def arch_eq less_eq_label_def)
  qed
qed

end
