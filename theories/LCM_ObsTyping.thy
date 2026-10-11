theory LCM_ObsTyping
  imports LCM_EventTyping
begin

section \<open>Observation Typing\<close>

datatype 'e obs =
    ValObs   'e
  | AddrObs  'e
  | StoreObs 'e
  | PredObs  'e
  | CtrlObs  'e
  | TxObs    'e

type_synonym 'e view_fn = "'e \<Rightarrow> 'e obs"

subsection \<open>Observation typing rules\<close>

text \<open>One rule instance per predecessor edge; the observation type joins all
  instances.\<close>

inductive obs_types ::
    "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e view_fn \<Rightarrow>
     'e obs \<Rightarrow> etype \<Rightarrow> bool"
    ("_,_,_ \<turnstile>O _ : _" [60,60,60,60,60] 61)
where
  OVal:
    "G, \<beta>, V \<turnstile>O ValObs e : \<Gamma>* G \<beta> e"
| OAddrBase:
    "G, \<beta>, V \<turnstile>O AddrObs m : base_addr \<beta> m"
| OAddr:
    "(e, m) \<in> addr G \<Longrightarrow>
     G, \<beta>, V \<turnstile>O AddrObs m : \<Gamma>* G \<beta> e"
| OStore:
    "(e, w) \<in> data G \<Longrightarrow>
     G, \<beta>, V \<turnstile>O StoreObs w : \<Gamma>* G \<beta> e"
| OPred:
    "(e, b) \<in> data G \<Longrightarrow>
     G, \<beta>, V \<turnstile>O PredObs b : \<Gamma>* G \<beta> e"
| OCtrl:
    "(b, u) \<in> ctrl G \<Longrightarrow>
     G, \<beta>, V \<turnstile>O PredObs b : \<tau> \<Longrightarrow>
     G, \<beta>, V \<turnstile>O CtrlObs u : \<tau>"
| OExport:
    "V \<chi> = ob \<Longrightarrow>
     G, \<beta>, V \<turnstile>O ob : \<tau> \<Longrightarrow>
     G, \<beta>, V \<turnstile>O TxObs \<chi> : \<tau>"

subsection \<open>Final observation type\<close>

definition obs_type_arch ::
    "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e view_fn \<Rightarrow> 'e obs \<Rightarrow> label"
  where
  "obs_type_arch G \<beta> V ob \<equiv>
     if \<exists>\<tau>. G, \<beta>, V \<turnstile>O ob : \<tau> \<and> fst \<tau> = High
     then High else Low"

definition obs_type_tgt ::
    "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e view_fn \<Rightarrow> 'e obs \<Rightarrow> label"
  where
  "obs_type_tgt G \<beta> V ob \<equiv>
     if \<exists>\<tau>. G, \<beta>, V \<turnstile>O ob : \<tau> \<and> snd \<tau> = High
     then High else Low"

definition obs_ty ::
    "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e view_fn \<Rightarrow> 'e obs \<Rightarrow> etype"
  where
  "obs_ty G \<beta> V ob \<equiv> (obs_type_arch G \<beta> V ob, obs_type_tgt G \<beta> V ob)"

subsection \<open>Stability\<close>

definition obs_stable ::
    "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e view_fn \<Rightarrow> 'e obs \<Rightarrow> bool"
  where
  "obs_stable G \<beta> V ob \<equiv> stable (obs_ty G \<beta> V ob)"

lemma obs_stable_iff:
  "obs_stable G \<beta> V ob \<longleftrightarrow>
   obs_type_arch G \<beta> V ob = obs_type_tgt G \<beta> V ob"
  by (simp add: obs_stable_def obs_ty_def stable_def)

lemma not_obs_stable_iff:
  "\<not> obs_stable G \<beta> V ob \<longleftrightarrow>
   obs_type_arch G \<beta> V ob \<noteq> obs_type_tgt G \<beta> V ob"
  by (simp add: obs_stable_iff)

subsection \<open>rfx-independence of the architectural component\<close>

lemma fst_gamma_star_rfx_indep:
  assumes rf_eq:   "rf G' = rf G"
    and data_eq: "data G' = data G"
  shows "fst (\<Gamma>* G' \<beta> e) = fst (\<Gamma>* G \<beta> e)"
proof -
  have "G', \<beta> \<turnstile>A e : High \<longleftrightarrow> G, \<beta> \<turnstile>A e : High"
    using typesA_independent_rfx[OF rf_eq data_eq] by blast
  thus ?thesis by (simp add: gamma_star_def least_arch_def)
qed

lemma obs_types_graph_swap_fst:
  "G0, \<beta>, V \<turnstile>O ob : \<tau> \<Longrightarrow>
   (\<And>e. fst (\<Gamma>* G0 \<beta> e) = fst (\<Gamma>* G \<beta> e)) \<Longrightarrow>
   addr G0 = addr G \<Longrightarrow> data G0 = data G \<Longrightarrow> ctrl G0 = ctrl G \<Longrightarrow>
   \<exists>\<tau>'. G, \<beta>, V \<turnstile>O ob : \<tau>' \<and> fst \<tau>' = fst \<tau>"
proof (induction rule: obs_types.induct)
  case (OVal G0' \<beta>' V' e)
  have "G, \<beta>', V' \<turnstile>O ValObs e : \<Gamma>* G \<beta>' e" by (rule obs_types.OVal)
  moreover have "fst (\<Gamma>* G \<beta>' e) = fst (\<Gamma>* G0' \<beta>' e)"
    using OVal.prems(1)[of e] by simp
  ultimately show ?case by blast
next
  case (OAddrBase G0' \<beta>' V' m)
  have "G, \<beta>', V' \<turnstile>O AddrObs m : base_addr \<beta>' m" by (rule obs_types.OAddrBase)
  thus ?case by blast
next
  case (OAddr e m G0' \<beta>' V')
  have em_G: "(e, m) \<in> addr G" using OAddr.hyps OAddr.prems(2) by simp
  have "G, \<beta>', V' \<turnstile>O AddrObs m : \<Gamma>* G \<beta>' e" by (rule obs_types.OAddr[OF em_G])
  moreover have "fst (\<Gamma>* G \<beta>' e) = fst (\<Gamma>* G0' \<beta>' e)"
    using OAddr.prems(1)[of e] by simp
  ultimately show ?case by blast
next
  case (OStore e w G0' \<beta>' V')
  have ew_G: "(e, w) \<in> data G" using OStore.hyps OStore.prems(3) by simp
  have "G, \<beta>', V' \<turnstile>O StoreObs w : \<Gamma>* G \<beta>' e" by (rule obs_types.OStore[OF ew_G])
  moreover have "fst (\<Gamma>* G \<beta>' e) = fst (\<Gamma>* G0' \<beta>' e)"
    using OStore.prems(1)[of e] by simp
  ultimately show ?case by blast
next
  case (OPred e b G0' \<beta>' V')
  have eb_G: "(e, b) \<in> data G" using OPred.hyps OPred.prems(3) by simp
  have "G, \<beta>', V' \<turnstile>O PredObs b : \<Gamma>* G \<beta>' e" by (rule obs_types.OPred[OF eb_G])
  moreover have "fst (\<Gamma>* G \<beta>' e) = fst (\<Gamma>* G0' \<beta>' e)"
    using OPred.prems(1)[of e] by simp
  ultimately show ?case by blast
next
  case (OCtrl b u G0' \<beta>' V' \<tau>)
  have bu_G: "(b, u) \<in> ctrl G" using OCtrl.hyps(1) OCtrl.prems(4) by simp
  from OCtrl.IH[OF OCtrl.prems(1) OCtrl.prems(2) OCtrl.prems(3) OCtrl.prems(4)]
  obtain \<tau>' where t1: "G, \<beta>', V' \<turnstile>O PredObs b : \<tau>'" and t2: "fst \<tau>' = fst \<tau>" by blast
  have "G, \<beta>', V' \<turnstile>O CtrlObs u : \<tau>'" by (rule obs_types.OCtrl[OF bu_G t1])
  thus ?case using t2 by blast
next
  case (OExport V' \<chi> ob' G0' \<beta>' \<tau>)
  from OExport.IH[OF OExport.prems(1) OExport.prems(2) OExport.prems(3) OExport.prems(4)]
  obtain \<tau>' where t1: "G, \<beta>', V' \<turnstile>O ob' : \<tau>'" and t2: "fst \<tau>' = fst \<tau>" by blast
  have "G, \<beta>', V' \<turnstile>O TxObs \<chi> : \<tau>'" by (rule obs_types.OExport[OF OExport.hyps(1) t1])
  thus ?case using t2 by blast
qed

lemma obs_type_arch_rfx_indep:
  assumes rf_eq:   "rf G' = rf G"
    and data_eq: "data G' = data G"
    and addr_eq: "addr G' = addr G"
    and ctrl_eq: "ctrl G' = ctrl G"
  shows "obs_type_arch G' \<beta> V ob = obs_type_arch G \<beta> V ob"
proof -
  have fst_eq: "\<And>e. fst (\<Gamma>* G' \<beta> e) = fst (\<Gamma>* G \<beta> e)"
    using fst_gamma_star_rfx_indep[OF rf_eq data_eq] by blast
  have fst_eq_sym: "\<And>e. fst (\<Gamma>* G \<beta> e) = fst (\<Gamma>* G' \<beta> e)"
    using fst_eq by simp
  have equiv:
    "(\<exists>\<tau>. G', \<beta>, V \<turnstile>O ob : \<tau> \<and> fst \<tau> = High) \<longleftrightarrow>
     (\<exists>\<tau>. G,  \<beta>, V \<turnstile>O ob : \<tau> \<and> fst \<tau> = High)"
  proof
    assume "\<exists>\<tau>. G', \<beta>, V \<turnstile>O ob : \<tau> \<and> fst \<tau> = High"
    then obtain \<tau> where typed': "G', \<beta>, V \<turnstile>O ob : \<tau>" and fhigh: "fst \<tau> = High"
      by blast
    from obs_types_graph_swap_fst[OF typed' fst_eq addr_eq data_eq ctrl_eq]
    obtain \<tau>' where a1: "G, \<beta>, V \<turnstile>O ob : \<tau>'" and a2: "fst \<tau>' = fst \<tau>" by blast
    from a2 fhigh have "fst \<tau>' = High" by simp
    with a1 show "\<exists>\<tau>. G, \<beta>, V \<turnstile>O ob : \<tau> \<and> fst \<tau> = High" by blast
  next
    assume "\<exists>\<tau>. G, \<beta>, V \<turnstile>O ob : \<tau> \<and> fst \<tau> = High"
    then obtain \<tau> where typed: "G, \<beta>, V \<turnstile>O ob : \<tau>" and fhigh: "fst \<tau> = High"
      by blast
    from obs_types_graph_swap_fst[OF typed fst_eq_sym
           addr_eq[symmetric] data_eq[symmetric] ctrl_eq[symmetric]]
    obtain \<tau>' where b1: "G', \<beta>, V \<turnstile>O ob : \<tau>'" and b2: "fst \<tau>' = fst \<tau>" by blast
    from b2 fhigh have "fst \<tau>' = High" by simp
    with b1 show "\<exists>\<tau>. G', \<beta>, V \<turnstile>O ob : \<tau> \<and> fst \<tau> = High" by blast
  qed
  thus ?thesis unfolding obs_type_arch_def by simp
qed

subsection \<open>Obs-type invariant and monotonicity\<close>

lemma obs_types_invariant_aux:
  "G, \<beta>, V \<turnstile>O ob : \<tau> \<Longrightarrow> wf_base \<beta> \<Longrightarrow> fst \<tau> \<le> snd \<tau>"
proof (induction rule: obs_types.induct)
  case (OVal G \<beta> V e)
  from OVal.prems have "wf_base \<beta>" .
  thus ?case by (rule least_typing_invariant)
next
  case (OAddrBase G \<beta> V m)
  from OAddrBase.prems have "wf_base \<beta>" .
  thus ?case by (rule wf_base_addr)
next
  case (OAddr e m G \<beta> V)
  from OAddr.prems have "wf_base \<beta>" .
  thus ?case by (rule least_typing_invariant)
next
  case (OStore e w G \<beta> V)
  from OStore.prems have "wf_base \<beta>" .
  thus ?case by (rule least_typing_invariant)
next
  case (OPred e b G \<beta> V)
  from OPred.prems have "wf_base \<beta>" .
  thus ?case by (rule least_typing_invariant)
next
  case OCtrl thus ?case by simp
next
  case OExport thus ?case by simp
qed

lemma obs_types_invariant:
  assumes ty: "G, \<beta>, V \<turnstile>O ob : \<tau>"
    and wf: "wf_base \<beta>"
  shows "fst \<tau> \<le> snd \<tau>"
  by (rule obs_types_invariant_aux[OF ty wf])

lemma obs_ty_invariant:
  assumes wf: "wf_base \<beta>"
  shows "fst (obs_ty G \<beta> V ob) \<le> snd (obs_ty G \<beta> V ob)"
proof (cases "obs_type_arch G \<beta> V ob")
  case Low thus ?thesis by (simp add: obs_ty_def)
next
  case High
  hence "\<exists>\<tau>. G, \<beta>, V \<turnstile>O ob : \<tau> \<and> fst \<tau> = High"
    unfolding obs_type_arch_def by (auto split: if_splits)
  then obtain \<tau> where typed: "G, \<beta>, V \<turnstile>O ob : \<tau>" and fhigh: "fst \<tau> = High"
    by blast
  have snd_high: "snd \<tau> = High"
    using obs_types_invariant[OF typed wf] fhigh
    by (cases "snd \<tau>"; simp add: less_eq_label_def)
  from typed snd_high have "\<exists>\<tau>. G, \<beta>, V \<turnstile>O ob : \<tau> \<and> snd \<tau> = High" by blast
  hence "obs_type_tgt G \<beta> V ob = High"
    unfolding obs_type_tgt_def by auto
  thus ?thesis using High by (simp add: obs_ty_def)
qed

subsection \<open>Removing rfx edges\<close>

lemma obs_types_gamma_mono_aux:
  "G, \<beta>, V \<turnstile>O ob : \<tau> \<Longrightarrow>
   (\<And>e. \<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e) \<Longrightarrow>
   addr G' = addr G \<Longrightarrow> data G' = data G \<Longrightarrow> ctrl G' = ctrl G \<Longrightarrow>
   \<exists>\<tau>'. G', \<beta>, V \<turnstile>O ob : \<tau>' \<and> \<tau>' \<sqsubseteq>\<^sub>e \<tau>"
proof (induction rule: obs_types.induct)
  case (OVal G \<beta> V e)
  have "G', \<beta>, V \<turnstile>O ValObs e : \<Gamma>* G' \<beta> e" by (rule obs_types.OVal)
  moreover have "\<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e" using OVal.prems(1) by blast
  ultimately show ?case by blast
next
  case (OAddrBase G \<beta> V m)
  have "G', \<beta>, V \<turnstile>O AddrObs m : base_addr \<beta> m" by (rule obs_types.OAddrBase)
  thus ?case using etype_leq_refl by blast
next
  case (OAddr e m G \<beta> V)
  have em: "(e, m) \<in> addr G'" using OAddr.hyps OAddr.prems(2) by simp
  have "G', \<beta>, V \<turnstile>O AddrObs m : \<Gamma>* G' \<beta> e" by (rule obs_types.OAddr[OF em])
  moreover have "\<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e" using OAddr.prems(1) by blast
  ultimately show ?case by blast
next
  case (OStore e w G \<beta> V)
  have ew: "(e, w) \<in> data G'" using OStore.hyps OStore.prems(3) by simp
  have "G', \<beta>, V \<turnstile>O StoreObs w : \<Gamma>* G' \<beta> e" by (rule obs_types.OStore[OF ew])
  moreover have "\<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e" using OStore.prems(1) by blast
  ultimately show ?case by blast
next
  case (OPred e b G \<beta> V)
  have eb: "(e, b) \<in> data G'" using OPred.hyps OPred.prems(3) by simp
  have "G', \<beta>, V \<turnstile>O PredObs b : \<Gamma>* G' \<beta> e" by (rule obs_types.OPred[OF eb])
  moreover have "\<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e" using OPred.prems(1) by blast
  ultimately show ?case by blast
next
  case (OCtrl b u G \<beta> V \<tau>)
  have bu: "(b, u) \<in> ctrl G'" using OCtrl.hyps(1) OCtrl.prems(4) by simp
  from OCtrl.IH[OF OCtrl.prems(1) OCtrl.prems(2) OCtrl.prems(3) OCtrl.prems(4)]
  obtain \<tau>' where t1: "G', \<beta>, V \<turnstile>O PredObs b : \<tau>'" and t2: "\<tau>' \<sqsubseteq>\<^sub>e \<tau>" by blast
  have "G', \<beta>, V \<turnstile>O CtrlObs u : \<tau>'" by (rule obs_types.OCtrl[OF bu t1])
  thus ?case using t2 by blast
next
  case (OExport V \<chi> ob' G \<beta> \<tau>)
  from OExport.IH[OF OExport.prems(1) OExport.prems(2) OExport.prems(3) OExport.prems(4)]
  obtain \<tau>' where t1: "G', \<beta>, V \<turnstile>O ob' : \<tau>'" and t2: "\<tau>' \<sqsubseteq>\<^sub>e \<tau>" by blast
  have "G', \<beta>, V \<turnstile>O TxObs \<chi> : \<tau>'" by (rule obs_types.OExport[OF OExport.hyps(1) t1])
  thus ?case using t2 by blast
qed

lemma obs_types_gamma_mono:
  assumes typed: "G, \<beta>, V \<turnstile>O ob : \<tau>"
    and gamma_leq: "\<And>e. \<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e"
    and addr_eq: "addr G' = addr G"
    and data_eq: "data G' = data G"
    and ctrl_eq: "ctrl G' = ctrl G"
  shows "\<exists>\<tau>'. G', \<beta>, V \<turnstile>O ob : \<tau>' \<and> \<tau>' \<sqsubseteq>\<^sub>e \<tau>"
  using obs_types_gamma_mono_aux[OF typed _ addr_eq data_eq ctrl_eq] gamma_leq by blast

subsection \<open>Adding rfx edges\<close>

lemma obs_types_mono_rfx_aux:
  "G', \<beta>, V \<turnstile>O ob : \<tau> \<Longrightarrow>
   (\<And>e. \<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e) \<Longrightarrow>
   addr G' = addr G \<Longrightarrow> data G' = data G \<Longrightarrow> ctrl G' = ctrl G \<Longrightarrow>
   \<exists>\<tau>'. G, \<beta>, V \<turnstile>O ob : \<tau>' \<and> \<tau> \<sqsubseteq>\<^sub>e \<tau>'"
proof (induction rule: obs_types.induct)
  case (OVal G' \<beta> V e)
  have "G, \<beta>, V \<turnstile>O ValObs e : \<Gamma>* G \<beta> e" by (rule obs_types.OVal)
  moreover have "\<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e" using OVal.prems(1) by blast
  ultimately show ?case by blast
next
  case (OAddrBase G' \<beta> V m)
  have "G, \<beta>, V \<turnstile>O AddrObs m : base_addr \<beta> m" by (rule obs_types.OAddrBase)
  thus ?case using etype_leq_refl by blast
next
  case (OAddr e m G' \<beta> V)
  have em: "(e, m) \<in> addr G" using OAddr.hyps OAddr.prems(2) by simp
  have "G, \<beta>, V \<turnstile>O AddrObs m : \<Gamma>* G \<beta> e" by (rule obs_types.OAddr[OF em])
  moreover have "\<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e" using OAddr.prems(1) by blast
  ultimately show ?case by blast
next
  case (OStore e w G' \<beta> V)
  have ew: "(e, w) \<in> data G" using OStore.hyps OStore.prems(3) by simp
  have "G, \<beta>, V \<turnstile>O StoreObs w : \<Gamma>* G \<beta> e" by (rule obs_types.OStore[OF ew])
  moreover have "\<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e" using OStore.prems(1) by blast
  ultimately show ?case by blast
next
  case (OPred e b G' \<beta> V)
  have eb: "(e, b) \<in> data G" using OPred.hyps OPred.prems(3) by simp
  have "G, \<beta>, V \<turnstile>O PredObs b : \<Gamma>* G \<beta> e" by (rule obs_types.OPred[OF eb])
  moreover have "\<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e" using OPred.prems(1) by blast
  ultimately show ?case by blast
next
  case (OCtrl b u G' \<beta> V \<tau>)
  have bu: "(b, u) \<in> ctrl G" using OCtrl.hyps(1) OCtrl.prems(4) by simp
  from OCtrl.IH[OF OCtrl.prems(1) OCtrl.prems(2) OCtrl.prems(3) OCtrl.prems(4)]
  obtain \<tau>' where t1: "G, \<beta>, V \<turnstile>O PredObs b : \<tau>'" and t2: "\<tau> \<sqsubseteq>\<^sub>e \<tau>'" by blast
  have "G, \<beta>, V \<turnstile>O CtrlObs u : \<tau>'" by (rule obs_types.OCtrl[OF bu t1])
  thus ?case using t2 by blast
next
  case (OExport V \<chi> ob' G' \<beta> \<tau>)
  from OExport.IH[OF OExport.prems(1) OExport.prems(2) OExport.prems(3) OExport.prems(4)]
  obtain \<tau>' where t1: "G, \<beta>, V \<turnstile>O ob' : \<tau>'" and t2: "\<tau> \<sqsubseteq>\<^sub>e \<tau>'" by blast
  have "G, \<beta>, V \<turnstile>O TxObs \<chi> : \<tau>'" by (rule obs_types.OExport[OF OExport.hyps(1) t1])
  thus ?case using t2 by blast
qed

lemma obs_types_mono_rfx:
  assumes typed: "G', \<beta>, V \<turnstile>O ob : \<tau>"
    and gamma_mono: "\<And>e. \<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e"
    and addr_eq: "addr G' = addr G"
    and data_eq: "data G' = data G"
    and ctrl_eq: "ctrl G' = ctrl G"
  shows "\<exists>\<tau>'. G, \<beta>, V \<turnstile>O ob : \<tau>' \<and> \<tau> \<sqsubseteq>\<^sub>e \<tau>'"
  using obs_types_mono_rfx_aux[OF typed _ addr_eq data_eq ctrl_eq] gamma_mono by blast

section \<open>Refinement\<close>

text \<open>A fact lowers the target component of one observation to its architectural
  component. Event types are untouched.\<close>

definition refine :: "'e obs set \<Rightarrow> 'e obs \<Rightarrow> etype \<Rightarrow> etype" where
  "refine \<Phi> ob \<tau> \<equiv> if ob \<in> \<Phi> then (fst \<tau>, fst \<tau>) else \<tau>"

definition robs_ty ::
    "'e obs set \<Rightarrow> 'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e view_fn \<Rightarrow> 'e obs \<Rightarrow> etype"
  where
  "robs_ty \<Phi> G \<beta> V ob \<equiv> refine \<Phi> ob (obs_ty G \<beta> V ob)"

lemma fst_refine [simp]: "fst (refine \<Phi> ob \<tau>) = fst \<tau>"
  by (simp add: refine_def)

lemma fst_robs_ty [simp]:
  "fst (robs_ty \<Phi> G \<beta> V ob) = obs_type_arch G \<beta> V ob"
  by (simp add: robs_ty_def obs_ty_def)

lemma robs_ty_empty [simp]: "robs_ty {} G \<beta> V ob = obs_ty G \<beta> V ob"
  by (simp add: robs_ty_def refine_def)

lemma robs_ty_no_fact:
  "ob \<notin> \<Phi> \<Longrightarrow> robs_ty \<Phi> G \<beta> V ob = obs_ty G \<beta> V ob"
  by (simp add: robs_ty_def refine_def)

lemma robs_ty_fact:
  "ob \<in> \<Phi> \<Longrightarrow>
   robs_ty \<Phi> G \<beta> V ob = (obs_type_arch G \<beta> V ob, obs_type_arch G \<beta> V ob)"
  by (simp add: robs_ty_def refine_def obs_ty_def)

lemma refine_invariant:
  assumes "fst \<tau> \<le> snd \<tau>"
  shows "fst (refine \<Phi> ob \<tau>) \<le> snd (refine \<Phi> ob \<tau>)"
  using assms by (simp add: refine_def)

lemma robs_ty_invariant:
  assumes wf: "wf_base \<beta>"
  shows "fst (robs_ty \<Phi> G \<beta> V ob) \<le> snd (robs_ty \<Phi> G \<beta> V ob)"
  unfolding robs_ty_def
  by (rule refine_invariant[OF obs_ty_invariant[OF wf]])

lemma robs_ty_leq_obs_ty:
  assumes wf: "wf_base \<beta>"
  shows "robs_ty \<Phi> G \<beta> V ob \<sqsubseteq>\<^sub>e obs_ty G \<beta> V ob"
proof (cases "ob \<in> \<Phi>")
  case True
  have inv: "fst (obs_ty G \<beta> V ob) \<le> snd (obs_ty G \<beta> V ob)"
    by (rule obs_ty_invariant[OF wf])
  from True have lhs:
    "robs_ty \<Phi> G \<beta> V ob =
     (fst (obs_ty G \<beta> V ob), fst (obs_ty G \<beta> V ob))"
    by (simp add: robs_ty_def refine_def)
  show ?thesis by (simp add: lhs etype_leq_def inv)
next
  case False
  thus ?thesis by (simp add: robs_ty_def refine_def)
qed

lemma robs_ty_mono_facts:
  assumes wf: "wf_base \<beta>" and sub: "\<Phi> \<subseteq> \<Phi>'"
  shows "robs_ty \<Phi>' G \<beta> V ob \<sqsubseteq>\<^sub>e robs_ty \<Phi> G \<beta> V ob"
proof (cases "ob \<in> \<Phi>")
  case True
  with sub have "ob \<in> \<Phi>'" by blast
  with True show ?thesis by (simp add: robs_ty_fact etype_leq_def)
next
  case False
  hence rhs: "robs_ty \<Phi> G \<beta> V ob = obs_ty G \<beta> V ob"
    by (rule robs_ty_no_fact)
  show ?thesis
  proof (cases "ob \<in> \<Phi>'")
    case True
    have inv: "fst (obs_ty G \<beta> V ob) \<le> snd (obs_ty G \<beta> V ob)"
      by (rule obs_ty_invariant[OF wf])
    from True have lhs:
      "robs_ty \<Phi>' G \<beta> V ob =
       (fst (obs_ty G \<beta> V ob), fst (obs_ty G \<beta> V ob))"
      by (simp add: robs_ty_def refine_def)
    show ?thesis by (simp add: lhs rhs etype_leq_def inv)
  next
    case False
    thus ?thesis by (simp add: rhs robs_ty_no_fact)
  qed
qed

end
