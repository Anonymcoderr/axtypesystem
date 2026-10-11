theory LCM_Soundness
  imports LCM_ObsTyping
begin

section \<open>Containment\<close>

text \<open>Containment is checked on refined observation types.\<close>

definition containment_r ::
    "'e obs set \<Rightarrow> 'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e view_fn \<Rightarrow>
     'e obs set \<Rightarrow> bool"
  where
  "containment_r \<Phi> G \<beta> V obs_set \<equiv>
     \<forall>ob \<in> obs_set. stable (robs_ty \<Phi> G \<beta> V ob)"

abbreviation containment ::
    "'e graph \<Rightarrow> 'e base_labels \<Rightarrow> 'e view_fn \<Rightarrow> 'e obs set \<Rightarrow> bool"
  where
  "containment G \<beta> V obs_set \<equiv> containment_r {} G \<beta> V obs_set"

subsection \<open>Stability bookkeeping\<close>

lemma stable_arch_eq_tgt:
  assumes contain: "containment_r \<Phi> G \<beta> V obs_set"
    and obs_in: "ob \<in> obs_set" and no_fact: "ob \<notin> \<Phi>"
  shows "obs_type_arch G \<beta> V ob = obs_type_tgt G \<beta> V ob"
proof -
  from contain obs_in have "stable (robs_ty \<Phi> G \<beta> V ob)"
    unfolding containment_r_def by blast
  with no_fact show ?thesis
    by (simp add: robs_ty_no_fact obs_ty_def stable_def)
qed

lemma stable_tgt_to_arch:
  assumes "containment_r \<Phi> G \<beta> V obs_set" "ob \<in> obs_set" "ob \<notin> \<Phi>"
    and "obs_type_tgt G \<beta> V ob = High"
  shows "obs_type_arch G \<beta> V ob = High"
  using stable_arch_eq_tgt[OF assms(1,2,3)] assms(4) by simp

subsection \<open>Monotonicity\<close>

theorem mono_gamma_star:
  assumes "G' \<preceq>\<^sub>G G" "wf_base \<beta>"
  shows "\<Gamma>* G' \<beta> e \<sqsubseteq>\<^sub>e \<Gamma>* G \<beta> e"
  by (rule gamma_star_mono_rfx[OF assms(1) assms(2)])

theorem mono_obs_ty:
  assumes sub: "G' \<preceq>\<^sub>G G" and wf: "wf_base \<beta>"
  shows "obs_ty G' \<beta> V ob \<sqsubseteq>\<^sub>e obs_ty G \<beta> V ob"
proof (unfold etype_leq_def obs_ty_def; simp; intro conjI)
  show "obs_type_arch G' \<beta> V ob \<le> obs_type_arch G \<beta> V ob"
  proof -
    have "obs_type_arch G' \<beta> V ob = obs_type_arch G \<beta> V ob"
      using obs_type_arch_rfx_indep[of G' G \<beta> V ob]
            graph_rfx_leq_rf[OF sub]   graph_rfx_leq_data[OF sub]
            graph_rfx_leq_addr[OF sub] graph_rfx_leq_ctrl[OF sub]
      by blast
    thus ?thesis by simp
  qed
next
  show "obs_type_tgt G' \<beta> V ob \<le> obs_type_tgt G \<beta> V ob"
  proof (cases "obs_type_tgt G' \<beta> V ob")
    case Low thus ?thesis by simp
  next
    case High
    then obtain \<tau> where typed': "G', \<beta>, V \<turnstile>O ob : \<tau>" and shigh: "snd \<tau> = High"
      unfolding obs_type_tgt_def by (auto split: if_splits)
    from obs_types_mono_rfx[OF typed'
            mono_gamma_star[OF sub wf]
            graph_rfx_leq_addr[OF sub] graph_rfx_leq_data[OF sub]
            graph_rfx_leq_ctrl[OF sub]]
    obtain \<tau>'' where typed'': "G, \<beta>, V \<turnstile>O ob : \<tau>''" and leq: "\<tau> \<sqsubseteq>\<^sub>e \<tau>''"
      by blast
    have snd_high: "snd \<tau>'' = High"
      using leq shigh unfolding etype_leq_def
      by (cases "snd \<tau>''"; simp add: less_eq_label_def)
    from typed'' snd_high
    have "\<exists>\<tau>. G, \<beta>, V \<turnstile>O ob : \<tau> \<and> snd \<tau> = High" by blast
    hence "obs_type_tgt G \<beta> V ob = High"
      unfolding obs_type_tgt_def by auto
    thus ?thesis using High by simp
  qed
qed

theorem mono_robs_ty:
  assumes sub: "G' \<preceq>\<^sub>G G" and wf: "wf_base \<beta>"
  shows "robs_ty \<Phi> G' \<beta> V ob \<sqsubseteq>\<^sub>e robs_ty \<Phi> G \<beta> V ob"
proof (cases "ob \<in> \<Phi>")
  case True
  have arch_eq: "obs_type_arch G' \<beta> V ob = obs_type_arch G \<beta> V ob"
    using obs_type_arch_rfx_indep[of G' G \<beta> V ob]
          graph_rfx_leq_rf[OF sub]   graph_rfx_leq_data[OF sub]
          graph_rfx_leq_addr[OF sub] graph_rfx_leq_ctrl[OF sub]
    by blast
  from True show ?thesis
    by (simp add: robs_ty_fact arch_eq etype_leq_def)
next
  case False
  show ?thesis
    using mono_obs_ty[OF sub wf]
    by (simp add: robs_ty_no_fact[OF False])
qed

theorem mono_facts:
  assumes "wf_base \<beta>" "\<Phi> \<subseteq> \<Phi>'"
  shows "robs_ty \<Phi>' G \<beta> V ob \<sqsubseteq>\<^sub>e robs_ty \<Phi> G \<beta> V ob"
  by (rule robs_ty_mono_facts[OF assms])

subsection \<open>Containment monotonicity\<close>

lemma stable_ob_mono:
  assumes sub: "G' \<preceq>\<^sub>G G"
    and wf: "wf_base \<beta>"
    and st: "stable (obs_ty G \<beta> V ob)"
  shows "stable (obs_ty G' \<beta> V ob)"
proof -
  have eq_G: "obs_type_arch G \<beta> V ob = obs_type_tgt G \<beta> V ob"
    using st by (simp add: obs_ty_def stable_def)
  have arch_eq: "obs_type_arch G' \<beta> V ob = obs_type_arch G \<beta> V ob"
    using obs_type_arch_rfx_indep[of G' G \<beta> V ob]
          graph_rfx_leq_rf[OF sub]   graph_rfx_leq_data[OF sub]
          graph_rfx_leq_addr[OF sub] graph_rfx_leq_ctrl[OF sub]
    by blast
  have tgt_leq: "obs_type_tgt G' \<beta> V ob \<le> obs_type_tgt G \<beta> V ob"
    using mono_obs_ty[OF sub wf]
    unfolding etype_leq_def obs_ty_def by simp
  have inv: "obs_type_arch G' \<beta> V ob \<le> obs_type_tgt G' \<beta> V ob"
    using obs_ty_invariant[OF wf] unfolding obs_ty_def by simp
  have tgt_leq_arch: "obs_type_tgt G' \<beta> V ob \<le> obs_type_arch G' \<beta> V ob"
    using tgt_leq eq_G arch_eq by simp
  show ?thesis
    unfolding obs_ty_def stable_def
    using antisym[OF inv tgt_leq_arch] by simp
qed

corollary containment_mono:
  assumes sub: "G' \<preceq>\<^sub>G G"
    and wf: "wf_base \<beta>"
    and contain_G: "containment_r \<Phi> G \<beta> V obs_set"
  shows "containment_r \<Phi> G' \<beta> V obs_set"
proof (unfold containment_r_def; intro ballI)
  fix ob assume in_obs: "ob \<in> obs_set"
  show "stable (robs_ty \<Phi> G' \<beta> V ob)"
  proof (cases "ob \<in> \<Phi>")
    case True
    thus ?thesis by (simp add: robs_ty_fact stable_def)
  next
    case False
    have "stable (robs_ty \<Phi> G \<beta> V ob)"
      using contain_G in_obs unfolding containment_r_def by blast
    hence "stable (obs_ty G \<beta> V ob)"
      using False by (simp add: robs_ty_no_fact)
    from stable_ob_mono[OF sub wf this] show ?thesis
      by (simp add: robs_ty_no_fact[OF False])
  qed
qed

section \<open>Semantic locale\<close>

text \<open>Two low-equivalent executions contained in \<open>G\<close> are described by the
  divergence predicates \<open>vdiv\<close>, \<open>adiv\<close>, \<open>pdiv\<close>, \<open>gdiv\<close> on event payloads,
  addresses, predicates, and guards. \<open>FO\<close> is fetch order. The assumptions are
  the containment and seed conditions of an adequate instance.\<close>

subsection \<open>Aspects of observations\<close>

fun ev0 :: "'e obs \<Rightarrow> 'e" where
  "ev0 (ValObs e)   = e"
| "ev0 (AddrObs m)  = m"
| "ev0 (StoreObs w) = w"
| "ev0 (PredObs b)  = b"
| "ev0 (CtrlObs u)  = u"
| "ev0 (TxObs \<chi>)    = \<chi>"

fun obs_div0 ::
    "('e \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> bool) \<Rightarrow>
     'e obs \<Rightarrow> bool"
  where
  "obs_div0 vd ad pd gd (ValObs e)   = vd e"
| "obs_div0 vd ad pd gd (AddrObs m)  = ad m"
| "obs_div0 vd ad pd gd (StoreObs w) = vd w"
| "obs_div0 vd ad pd gd (PredObs b)  = pd b"
| "obs_div0 vd ad pd gd (CtrlObs u)  = gd u"
| "obs_div0 vd ad pd gd (TxObs \<chi>)    = False"

definition event_of :: "'e view_fn \<Rightarrow> 'e obs \<Rightarrow> 'e" where
  "event_of V ob = (case ob of TxObs \<chi> \<Rightarrow> ev0 (V \<chi>) | _ \<Rightarrow> ev0 ob)"

definition obs_div ::
    "'e view_fn \<Rightarrow> ('e \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> bool) \<Rightarrow>
     ('e \<Rightarrow> bool) \<Rightarrow> 'e obs \<Rightarrow> bool"
  where
  "obs_div V vd ad pd gd ob =
     (case ob of TxObs \<chi> \<Rightarrow> obs_div0 vd ad pd gd (V \<chi>)
               | _ \<Rightarrow> obs_div0 vd ad pd gd ob)"

lemma event_of_simps [simp]:
  "event_of V (ValObs e)   = e"
  "event_of V (AddrObs m)  = m"
  "event_of V (StoreObs w) = w"
  "event_of V (PredObs b)  = b"
  "event_of V (CtrlObs u)  = u"
  "event_of V (TxObs \<chi>)    = ev0 (V \<chi>)"
  by (simp_all add: event_of_def)

lemma obs_div_simps [simp]:
  "obs_div V vd ad pd gd (ValObs e)   = vd e"
  "obs_div V vd ad pd gd (AddrObs m)  = ad m"
  "obs_div V vd ad pd gd (StoreObs w) = vd w"
  "obs_div V vd ad pd gd (PredObs b)  = pd b"
  "obs_div V vd ad pd gd (CtrlObs u)  = gd u"
  "obs_div V vd ad pd gd (TxObs \<chi>)    = obs_div0 vd ad pd gd (V \<chi>)"
  by (simp_all add: obs_div_def)

subsection \<open>Helper lemmas on the typing side\<close>

lemma snd_gamma_star_High:
  "G, \<beta> \<turnstile>T e : High \<Longrightarrow> snd (\<Gamma>* G \<beta> e) = High"
  by (simp add: gamma_star_def least_tgt_def)

lemma obs_type_tgt_HighI:
  "G, \<beta>, V \<turnstile>O ob : \<tau> \<Longrightarrow> snd \<tau> = High \<Longrightarrow> obs_type_tgt G \<beta> V ob = High"
  unfolding obs_type_tgt_def by (cases \<tau>) auto

subsection \<open>The semantic locale\<close>

locale lcm_semantics =
  fixes G :: "'e graph"
    and \<beta> :: "'e base_labels"
    and V :: "'e view_fn"
    and obs_set :: "'e obs set"     \<comment> \<open>checked observations\<close>
    and \<Phi> :: "'e obs set"           \<comment> \<open>refinement facts\<close>
    and MemEvt :: "'e set"          \<comment> \<open>memory events\<close>
    and FO :: "('e \<times> 'e) set"       \<comment> \<open>fetch order\<close>
    and vdiv adiv pdiv gdiv :: "'e \<Rightarrow> bool"
  assumes wf_FO: "wf FO"
    and trans_FO: "trans FO"
    and wf_seed: "wf_base \<beta>"
    and prim_view: "\<And>\<chi> \<chi>'. V \<chi> \<noteq> TxObs \<chi>'"
    and flow_complete:
      "\<And>m. m \<in> MemEvt \<Longrightarrow> AddrObs m \<in> obs_set \<and> CtrlObs m \<in> obs_set"
    \<comment> \<open>a diverging payload has a diverging source, a High seed, or an
        earlier address or guard divergence at a memory event\<close>
    and Hcar:
      "\<And>e. vdiv e \<Longrightarrow>
         (\<exists>w. (w, e) \<in> rf G \<union> data G \<union> rfx G \<and> (w, e) \<in> FO \<and> vdiv w)
       \<or> snd (base_val \<beta> e) = High
       \<or> (\<exists>m \<in> MemEvt. (m, e) \<in> FO \<and> (adiv m \<or> gdiv m))"
    and Haddr:
      "\<And>m. adiv m \<Longrightarrow>
         (\<exists>e. (e, m) \<in> addr G \<and> (e, m) \<in> FO \<and> vdiv e)
       \<or> snd (base_addr \<beta> m) = High"
    and Hpred:
      "\<And>b. pdiv b \<Longrightarrow> (\<exists>e. (e, b) \<in> data G \<and> (e, b) \<in> FO \<and> vdiv e)"
    and Hguard:
      "\<And>u. gdiv u \<Longrightarrow> (\<exists>b. (b, u) \<in> ctrl G \<and> (b, u) \<in> FO \<and> pdiv b)"
    \<comment> \<open>checked stores: residuals are public constants\<close>
    and Hstore:
      "\<And>w. StoreObs w \<in> obs_set \<or>
            (\<exists>\<chi>. TxObs \<chi> \<in> obs_set \<and> V \<chi> = StoreObs w) \<Longrightarrow>
            vdiv w \<Longrightarrow>
            (\<exists>e. (e, w) \<in> data G \<and> (e, w) \<in> FO \<and> vdiv e)"
    \<comment> \<open>certified observations do not diverge\<close>
    and fact_sound:
      "\<And>ob. ob \<in> \<Phi> \<Longrightarrow> \<not> obs_div V vdiv adiv pdiv gdiv ob"
begin

abbreviation odiv :: "'e obs \<Rightarrow> bool" where
  "odiv \<equiv> obs_div V vdiv adiv pdiv gdiv"

abbreviation eof :: "'e obs \<Rightarrow> 'e" where
  "eof \<equiv> event_of V"

definition fo_le :: "'e \<Rightarrow> 'e \<Rightarrow> bool" where
  "fo_le x y \<equiv> x = y \<or> (x, y) \<in> FO"

lemma fo_le_refl [simp]: "fo_le x x"
  by (simp add: fo_le_def)

lemma fo_le_step:
  assumes "(x, y) \<in> FO" and "fo_le y z"
  shows "(x, z) \<in> FO"
  using assms trans_FO unfolding fo_le_def by (auto dest: transD)

lemma fo_leI: "(x, z) \<in> FO \<Longrightarrow> fo_le x z"
  by (simp add: fo_le_def)

subsection \<open>Earliest-divergence induction\<close>

text \<open>Earliest-divergence argument. \<open>u0\<close> is the event of the fetch-earliest
  diverging checked observation.\<close>

lemma carrier_typed_High:
  assumes min: "\<And>ob. ob \<in> obs_set \<Longrightarrow> odiv ob \<Longrightarrow> (eof ob, u0) \<notin> FO"
  shows "fo_le e u0 \<Longrightarrow> vdiv e \<Longrightarrow> G, \<beta> \<turnstile>T e : High"
proof (induction e rule: wf_induct_rule[OF wf_FO, case_names less])
  case (less e)
  note le_e = less.prems(1) and dv_e = less.prems(2)
  from Hcar[OF dv_e] consider
      (edge) "\<exists>w. (w, e) \<in> rf G \<union> data G \<union> rfx G \<and> (w, e) \<in> FO \<and> vdiv w"
    | (seed) "snd (base_val \<beta> e) = High"
    | (med)  "\<exists>m \<in> MemEvt. (m, e) \<in> FO \<and> (adiv m \<or> gdiv m)"
    by blast
  then show ?case
  proof cases
    case edge
    then obtain w where wedge: "(w, e) \<in> rf G \<union> data G \<union> rfx G"
      and wfo: "(w, e) \<in> FO" and wdv: "vdiv w" by blast
    have wle: "fo_le w u0" by (rule fo_leI[OF fo_le_step[OF wfo le_e]])
    have wHigh: "G, \<beta> \<turnstile>T w : High"
      by (rule less.IH[OF wfo wle wdv])
    from wedge show ?thesis
    proof (elim UnE)
      assume "(w, e) \<in> rf G"
      thus ?thesis by (rule typesT.RFT[OF _ wHigh])
    next
      assume "(w, e) \<in> data G"
      thus ?thesis by (rule typesT.DataT[OF _ wHigh])
    next
      assume "(w, e) \<in> rfx G"
      thus ?thesis by (rule typesT.T_RFX[OF _ wHigh])
    qed
  next
    case seed
    show ?thesis by (rule typesT.BaseT) (simp add: seed)
  next
    case med
    then obtain m where mM: "m \<in> MemEvt" and mfo: "(m, e) \<in> FO"
      and mdv: "adiv m \<or> gdiv m" by blast
    have mu0: "(m, u0) \<in> FO" by (rule fo_le_step[OF mfo le_e])
    from flow_complete[OF mM]
    have inA: "AddrObs m \<in> obs_set" and inC: "CtrlObs m \<in> obs_set" by auto
    from mdv have False
    proof
      assume am: "adiv m"
      have "(eof (AddrObs m), u0) \<notin> FO"
        by (rule min[OF inA]) (simp add: am)
      thus False using mu0 by simp
    next
      assume gm: "gdiv m"
      have "(eof (CtrlObs m), u0) \<notin> FO"
        by (rule min[OF inC]) (simp add: gm)
      thus False using mu0 by simp
    qed
    thus ?thesis ..
  qed
qed

lemma pred_obs_High:
  assumes min: "\<And>ob. ob \<in> obs_set \<Longrightarrow> odiv ob \<Longrightarrow> (eof ob, u0) \<notin> FO"
    and ble: "fo_le b u0" and bdv: "pdiv b"
  shows "\<exists>\<tau>. G, \<beta>, V \<turnstile>O PredObs b : \<tau> \<and> snd \<tau> = High"
proof -
  from Hpred[OF bdv] obtain e where
    edata: "(e, b) \<in> data G" and efo: "(e, b) \<in> FO" and edv: "vdiv e" by blast
  have ele: "fo_le e u0" by (rule fo_leI[OF fo_le_step[OF efo ble]])
  have eHigh: "G, \<beta> \<turnstile>T e : High"
    by (rule carrier_typed_High[OF min ele edv])
  have "G, \<beta>, V \<turnstile>O PredObs b : \<Gamma>* G \<beta> e"
    by (rule obs_types.OPred[OF edata])
  moreover have "snd (\<Gamma>* G \<beta> e) = High"
    by (rule snd_gamma_star_High[OF eHigh])
  ultimately show ?thesis by blast
qed

lemma prim_obs_High:
  assumes min: "\<And>ob. ob \<in> obs_set \<Longrightarrow> odiv ob \<Longrightarrow> (eof ob, u0) \<notin> FO"
    and pdv: "obs_div0 vdiv adiv pdiv gdiv p"
    and ple: "fo_le (ev0 p) u0"
    and chk: "p \<in> obs_set \<or> (\<exists>\<chi>. TxObs \<chi> \<in> obs_set \<and> V \<chi> = p)"
  shows "\<exists>\<tau>. G, \<beta>, V \<turnstile>O p : \<tau> \<and> snd \<tau> = High"
proof (cases p)
  case (ValObs e)
  with pdv ple have "vdiv e" "fo_le e u0" by simp_all
  hence eHigh: "G, \<beta> \<turnstile>T e : High"
    using carrier_typed_High[OF min] by blast
  have "G, \<beta>, V \<turnstile>O ValObs e : \<Gamma>* G \<beta> e" by (rule obs_types.OVal)
  with snd_gamma_star_High[OF eHigh] ValObs show ?thesis by blast
next
  case (AddrObs m)
  with pdv ple have mdv: "adiv m" and mle: "fo_le m u0" by simp_all
  from Haddr[OF mdv] show ?thesis
  proof
    assume "\<exists>e. (e, m) \<in> addr G \<and> (e, m) \<in> FO \<and> vdiv e"
    then obtain e where eaddr: "(e, m) \<in> addr G"
      and efo: "(e, m) \<in> FO" and edv: "vdiv e" by blast
    have ele: "fo_le e u0" by (rule fo_leI[OF fo_le_step[OF efo mle]])
    have eHigh: "G, \<beta> \<turnstile>T e : High"
      by (rule carrier_typed_High[OF min ele edv])
    have "G, \<beta>, V \<turnstile>O AddrObs m : \<Gamma>* G \<beta> e"
      by (rule obs_types.OAddr[OF eaddr])
    with snd_gamma_star_High[OF eHigh] AddrObs show ?thesis by blast
  next
    assume sh: "snd (base_addr \<beta> m) = High"
    have "G, \<beta>, V \<turnstile>O AddrObs m : base_addr \<beta> m"
      by (rule obs_types.OAddrBase)
    with sh AddrObs show ?thesis by blast
  qed
next
  case (StoreObs w)
  with chk have chkw:
    "StoreObs w \<in> obs_set \<or> (\<exists>\<chi>. TxObs \<chi> \<in> obs_set \<and> V \<chi> = StoreObs w)"
    by simp
  from StoreObs pdv ple have wdv: "vdiv w" and wle: "fo_le w u0" by simp_all
  from Hstore[OF chkw wdv] obtain e where
    edata: "(e, w) \<in> data G" and efo: "(e, w) \<in> FO" and edv: "vdiv e" by blast
  have ele: "fo_le e u0" by (rule fo_leI[OF fo_le_step[OF efo wle]])
  have eHigh: "G, \<beta> \<turnstile>T e : High"
    by (rule carrier_typed_High[OF min ele edv])
  have "G, \<beta>, V \<turnstile>O StoreObs w : \<Gamma>* G \<beta> e"
    by (rule obs_types.OStore[OF edata])
  with snd_gamma_star_High[OF eHigh] StoreObs show ?thesis by blast
next
  case (PredObs b)
  with pdv ple have "pdiv b" "fo_le b u0" by simp_all
  with pred_obs_High[OF min] PredObs show ?thesis by blast
next
  case (CtrlObs u)
  with pdv ple have udv: "gdiv u" and ule: "fo_le u u0" by simp_all
  from Hguard[OF udv] obtain b where
    bctrl: "(b, u) \<in> ctrl G" and bfo: "(b, u) \<in> FO" and bdv: "pdiv b" by blast
  have ble: "fo_le b u0" by (rule fo_leI[OF fo_le_step[OF bfo ule]])
  from pred_obs_High[OF min ble bdv] obtain \<tau> where
    pty: "G, \<beta>, V \<turnstile>O PredObs b : \<tau>" and sh: "snd \<tau> = High" by blast
  have "G, \<beta>, V \<turnstile>O CtrlObs u : \<tau>"
    by (rule obs_types.OCtrl[OF bctrl pty])
  with sh CtrlObs show ?thesis by blast
next
  case (TxObs \<chi>)
  with pdv show ?thesis by simp
qed

subsection \<open>Soundness, label level\<close>

theorem thm1_label_level:
  assumes contain: "containment_r \<Phi> G \<beta> V obs_set"
    and dist: "\<exists>ob \<in> obs_set. odiv ob"
  shows "\<exists>ob \<in> obs_set. odiv ob \<and> obs_type_arch G \<beta> V ob = High"
proof -
  \<comment> \<open>pick a diverging checked observation with fetch-minimal event\<close>
  define Q where "Q = eof ` {ob \<in> obs_set. odiv ob}"
  from dist obtain ob1 where "ob1 \<in> obs_set" "odiv ob1" by blast
  hence "eof ob1 \<in> Q" unfolding Q_def by blast
  from wfE_min[OF wf_FO this] obtain u0 where
    u0Q: "u0 \<in> Q" and u0min: "\<And>y. (y, u0) \<in> FO \<Longrightarrow> y \<notin> Q" by blast
  from u0Q obtain ob0 where
    ob0_in: "ob0 \<in> obs_set" and ob0_dv: "odiv ob0" and ob0_ev: "eof ob0 = u0"
    unfolding Q_def by blast
  have min: "(eof ob, u0) \<notin> FO" if "ob \<in> obs_set" and "odiv ob" for ob
  proof
    assume fo: "(eof ob, u0) \<in> FO"
    have "eof ob \<in> Q" using that unfolding Q_def by blast
    with u0min[OF fo] show False by blast
  qed
  \<comment> \<open>the minimal diverging checked observation is target-typed High\<close>
  have tgt_high: "obs_type_tgt G \<beta> V ob0 = High"
  proof (cases ob0)
    case (TxObs \<chi>)
    have pdv: "obs_div0 vdiv adiv pdiv gdiv (V \<chi>)"
      using ob0_dv TxObs by simp
    have ple: "fo_le (ev0 (V \<chi>)) u0"
      using ob0_ev TxObs by simp
    have chk: "V \<chi> \<in> obs_set \<or> (\<exists>\<chi>'. TxObs \<chi>' \<in> obs_set \<and> V \<chi>' = V \<chi>)"
      using ob0_in TxObs by blast
    from prim_obs_High[OF min pdv ple chk] obtain \<tau> where
      vty: "G, \<beta>, V \<turnstile>O V \<chi> : \<tau>" and sh: "snd \<tau> = High" by blast
    have "G, \<beta>, V \<turnstile>O TxObs \<chi> : \<tau>"
      by (rule obs_types.OExport[OF refl vty])
    from this sh show ?thesis
      unfolding TxObs by (rule obs_type_tgt_HighI)
  next
    case (ValObs e)
    have pdv: "obs_div0 vdiv adiv pdiv gdiv ob0"
      using ob0_dv ValObs by simp
    have ple: "fo_le (ev0 ob0) u0"
      using ob0_ev ValObs by simp
    from prim_obs_High[OF min pdv ple] ob0_in obtain \<tau> where
      "G, \<beta>, V \<turnstile>O ob0 : \<tau>" and "snd \<tau> = High" by blast
    then show ?thesis by (rule obs_type_tgt_HighI)
  next
    case (AddrObs m)
    have pdv: "obs_div0 vdiv adiv pdiv gdiv ob0"
      using ob0_dv AddrObs by simp
    have ple: "fo_le (ev0 ob0) u0"
      using ob0_ev AddrObs by simp
    from prim_obs_High[OF min pdv ple] ob0_in obtain \<tau> where
      "G, \<beta>, V \<turnstile>O ob0 : \<tau>" and "snd \<tau> = High" by blast
    then show ?thesis by (rule obs_type_tgt_HighI)
  next
    case (StoreObs w)
    have pdv: "obs_div0 vdiv adiv pdiv gdiv ob0"
      using ob0_dv StoreObs by simp
    have ple: "fo_le (ev0 ob0) u0"
      using ob0_ev StoreObs by simp
    from prim_obs_High[OF min pdv ple] ob0_in obtain \<tau> where
      "G, \<beta>, V \<turnstile>O ob0 : \<tau>" and "snd \<tau> = High" by blast
    then show ?thesis by (rule obs_type_tgt_HighI)
  next
    case (PredObs b)
    have pdv: "obs_div0 vdiv adiv pdiv gdiv ob0"
      using ob0_dv PredObs by simp
    have ple: "fo_le (ev0 ob0) u0"
      using ob0_ev PredObs by simp
    from prim_obs_High[OF min pdv ple] ob0_in obtain \<tau> where
      "G, \<beta>, V \<turnstile>O ob0 : \<tau>" and "snd \<tau> = High" by blast
    then show ?thesis by (rule obs_type_tgt_HighI)
  next
    case (CtrlObs u)
    have pdv: "obs_div0 vdiv adiv pdiv gdiv ob0"
      using ob0_dv CtrlObs by simp
    have ple: "fo_le (ev0 ob0) u0"
      using ob0_ev CtrlObs by simp
    from prim_obs_High[OF min pdv ple] ob0_in obtain \<tau> where
      "G, \<beta>, V \<turnstile>O ob0 : \<tau>" and "snd \<tau> = High" by blast
    then show ?thesis by (rule obs_type_tgt_HighI)
  qed
  \<comment> \<open>the diverging observation carries no fact\<close>
  have no_fact: "ob0 \<notin> \<Phi>"
    using fact_sound ob0_dv by blast
  \<comment> \<open>containment forces the architectural component to High\<close>
  have "obs_type_arch G \<beta> V ob0 = High"
    using stable_tgt_to_arch[OF contain ob0_in no_fact tgt_high] .
  with ob0_in ob0_dv show ?thesis by blast
qed

corollary thm1_label_level_refined:
  assumes "containment_r \<Phi> G \<beta> V obs_set"
    and "\<exists>ob \<in> obs_set. odiv ob"
  shows "\<exists>ob \<in> obs_set. odiv ob \<and> fst (robs_ty \<Phi> G \<beta> V ob) = High"
  using thm1_label_level[OF assms] by simp

subsection \<open>Speculative constant time\<close>

theorem thm1_sct:
  assumes contain: "containment_r \<Phi> G \<beta> V obs_set"
    and all_low: "\<forall>ob \<in> obs_set. obs_type_arch G \<beta> V ob = Low"
  shows "\<forall>ob \<in> obs_set. \<not> odiv ob"
proof (rule ccontr)
  assume "\<not> (\<forall>ob \<in> obs_set. \<not> odiv ob)"
  hence "\<exists>ob \<in> obs_set. odiv ob" by blast
  from thm1_label_level[OF contain this] obtain ob where
    "ob \<in> obs_set" "obs_type_arch G \<beta> V ob = High" by blast
  with all_low show False by auto
qed

end  \<comment> \<open>locale lcm_semantics\<close>

subsection \<open>Consistency witness\<close>

lemma lcm_semantics_consistent:
  "lcm_semantics G ((\<lambda>_. LL, \<lambda>_. LL) :: 'e base_labels) ValObs obs_set {} {} {}
     (\<lambda>_. False) (\<lambda>_. False) (\<lambda>_. False) (\<lambda>_. False)"
  by unfold_locales
     (auto simp: wf_base_def base_val_def base_addr_def trans_def wf_def)

subsection \<open>Cache observer: flow completeness by construction\<close>

text \<open>Flow completeness of the cache observer holds by construction.\<close>

definition cache_obs_set :: "'e set \<Rightarrow> 'e obs set" where
  "cache_obs_set MemEvt \<equiv> AddrObs ` MemEvt \<union> CtrlObs ` MemEvt"

lemma cache_flow_complete:
  "m \<in> MemEvt \<Longrightarrow>
   AddrObs m \<in> cache_obs_set MemEvt \<and> CtrlObs m \<in> cache_obs_set MemEvt"
  by (auto simp: cache_obs_set_def)

end
