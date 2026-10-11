theory LCM_Aspect_Soundness
  imports LCM_Soundness
begin

section \<open>Soundness with same-event address and guard mediation\<close>

text \<open>As \<open>lcm_semantics\<close>, except that a memory event's own address or guard may
  mediate its payload divergence. The induction uses fetch order refined by
  aspect: guard, then address, then payload.\<close>

fun observation_position0 :: "'e obs \<Rightarrow> 'e \<times> nat" where
  "observation_position0 (ValObs e) = (e, 2)"
| "observation_position0 (AddrObs e) = (e, 1)"
| "observation_position0 (StoreObs e) = (e, 2)"
| "observation_position0 (PredObs e) = (e, 2)"
| "observation_position0 (CtrlObs e) = (e, 0)"
| "observation_position0 (TxObs e) = (e, 2)"

definition observation_position :: "'e view_fn \<Rightarrow> 'e obs \<Rightarrow> 'e \<times> nat" where
  "observation_position V ob =
    (case ob of TxObs e \<Rightarrow> observation_position0 (V e)
      | _ \<Rightarrow> observation_position0 ob)"

lemma observation_position_simps [simp]:
  "observation_position V (ValObs e) = (e, 2)"
  "observation_position V (AddrObs e) = (e, 1)"
  "observation_position V (StoreObs e) = (e, 2)"
  "observation_position V (PredObs e) = (e, 2)"
  "observation_position V (CtrlObs e) = (e, 0)"
  "observation_position V (TxObs e) = observation_position0 (V e)"
  by (simp_all add: observation_position_def)

definition aspect_order :: "('e \<times> 'e) set \<Rightarrow>
    (('e \<times> nat) \<times> ('e \<times> nat)) set" where
  "aspect_order FO = FO <*lex*> less_than"

lemma aspect_order_iff [simp]:
  "((x, i), (y, j)) \<in> aspect_order FO \<longleftrightarrow>
    (x, y) \<in> FO \<or> (x = y \<and> i < j)"
  by (simp add: aspect_order_def lex_prod_def)

locale lcm_aspect_semantics =
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
        address or guard divergence at the same or an earlier memory event\<close>
    and Hcar:
      "\<And>e. vdiv e \<Longrightarrow>
         (\<exists>w. (w, e) \<in> rf G \<union> data G \<union> rfx G \<and> (w, e) \<in> FO \<and> vdiv w)
       \<or> snd (base_val \<beta> e) = High
       \<or> (\<exists>m \<in> MemEvt. (m = e \<or> (m, e) \<in> FO) \<and> (adiv m \<or> gdiv m))"
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
abbreviation opos :: "'e obs \<Rightarrow> 'e \<times> nat" where
  "opos \<equiv> observation_position V"
abbreviation AFO :: "(('e \<times> nat) \<times> ('e \<times> nat)) set" where
  "AFO \<equiv> aspect_order FO"

lemma wf_AFO: "wf AFO"
  unfolding aspect_order_def by (rule wf_lex_prod[OF wf_FO wf_less_than])

lemma trans_AFO: "trans AFO"
  unfolding aspect_order_def
  by (rule trans_lex_prod[OF trans_FO trans_less_than])

definition aspect_le :: "('e \<times> nat) \<Rightarrow> ('e \<times> nat) \<Rightarrow> bool" where
  "aspect_le x y \<equiv> x = y \<or> (x, y) \<in> AFO"
lemma aspect_le_refl [simp]: "aspect_le x x"
  by (simp add: aspect_le_def)
lemma aspect_leI: "(x, y) \<in> AFO \<Longrightarrow> aspect_le x y"
  by (simp add: aspect_le_def)
lemma aspect_le_step:
  assumes "(x, y) \<in> AFO" and "aspect_le y z"
  shows "(x, z) \<in> AFO"
  using assms trans_AFO unfolding aspect_le_def by (auto dest: transD)
lemma earlier_event:
  assumes "(x, y) \<in> FO"
  shows "((x, i), (y, j)) \<in> AFO"
  using assms by simp

subsection \<open>Earliest-divergence induction over event aspects\<close>

lemma carrier_typed_High:
  assumes min: "\<And>ob. ob \<in> obs_set \<Longrightarrow> odiv ob \<Longrightarrow> (opos ob, u0) \<notin> AFO"
  shows "aspect_le (e, 2) u0 \<Longrightarrow> vdiv e \<Longrightarrow> G, \<beta> \<turnstile>T e : High"
proof (induction e rule: wf_induct_rule[OF wf_FO, case_names less])
  case (less e)
  note le_e = less.prems(1) and dv_e = less.prems(2)
  from Hcar[OF dv_e] consider
      (edge) "\<exists>w. (w, e) \<in> rf G \<union> data G \<union> rfx G \<and> (w, e) \<in> FO \<and> vdiv w"
    | (seed) "snd (base_val \<beta> e) = High"
    | (med)  "\<exists>m \<in> MemEvt. (m = e \<or> (m, e) \<in> FO) \<and> (adiv m \<or> gdiv m)"
    by blast
  then show ?case
  proof cases
    case edge
    then obtain w where wedge: "(w, e) \<in> rf G \<union> data G \<union> rfx G"
      and wfo: "(w, e) \<in> FO" and wdv: "vdiv w" by blast
    have wle: "aspect_le (w, 2) u0" by (rule aspect_leI[OF aspect_le_step[OF earlier_event[OF wfo] le_e]])
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
    then obtain m where mM: "m \<in> MemEvt" and mfo: "m = e \<or> (m, e) \<in> FO"
      and mdv: "adiv m \<or> gdiv m" by blast
    have ma: "((m, 1), (e, 2)) \<in> AFO" using mfo by auto
    have mg: "((m, 0), (e, 2)) \<in> AFO" using mfo by auto
    have au0: "((m, 1), u0) \<in> AFO"
      by (rule aspect_le_step[OF ma le_e])
    have gu0: "((m, 0), u0) \<in> AFO"
      by (rule aspect_le_step[OF mg le_e])
    from flow_complete[OF mM]
    have inA: "AddrObs m \<in> obs_set" and inC: "CtrlObs m \<in> obs_set" by auto
    from mdv have False
    proof
      assume am: "adiv m"
      have "(opos (AddrObs m), u0) \<notin> AFO"
        by (rule min[OF inA]) (simp add: am)
      thus False using au0 by simp
    next
      assume gm: "gdiv m"
      have "(opos (CtrlObs m), u0) \<notin> AFO"
        by (rule min[OF inC]) (simp add: gm)
      thus False using gu0 by simp
    qed
    thus ?thesis ..
  qed
qed

lemma pred_obs_High:
  assumes min: "\<And>ob. ob \<in> obs_set \<Longrightarrow> odiv ob \<Longrightarrow> (opos ob, u0) \<notin> AFO"
    and ble: "aspect_le (b, 2) u0" and bdv: "pdiv b"
  shows "\<exists>\<tau>. G, \<beta>, V \<turnstile>O PredObs b : \<tau> \<and> snd \<tau> = High"
proof -
  from Hpred[OF bdv] obtain e where
    edata: "(e, b) \<in> data G" and efo: "(e, b) \<in> FO" and edv: "vdiv e" by blast
  have ele: "aspect_le (e, 2) u0" by (rule aspect_leI[OF aspect_le_step[OF earlier_event[OF efo] ble]])
  have eHigh: "G, \<beta> \<turnstile>T e : High"
    by (rule carrier_typed_High[OF min ele edv])
  have "G, \<beta>, V \<turnstile>O PredObs b : \<Gamma>* G \<beta> e"
    by (rule obs_types.OPred[OF edata])
  moreover have "snd (\<Gamma>* G \<beta> e) = High"
    by (rule snd_gamma_star_High[OF eHigh])
  ultimately show ?thesis by blast
qed

lemma prim_obs_High:
  assumes min: "\<And>ob. ob \<in> obs_set \<Longrightarrow> odiv ob \<Longrightarrow> (opos ob, u0) \<notin> AFO"
    and pdv: "obs_div0 vdiv adiv pdiv gdiv p"
    and ple: "aspect_le (observation_position0 p) u0"
    and chk: "p \<in> obs_set \<or> (\<exists>\<chi>. TxObs \<chi> \<in> obs_set \<and> V \<chi> = p)"
  shows "\<exists>\<tau>. G, \<beta>, V \<turnstile>O p : \<tau> \<and> snd \<tau> = High"
proof (cases p)
  case (ValObs e)
  with pdv ple have "vdiv e" "aspect_le (e, 2) u0" by simp_all
  hence eHigh: "G, \<beta> \<turnstile>T e : High"
    using carrier_typed_High[OF min] by blast
  have "G, \<beta>, V \<turnstile>O ValObs e : \<Gamma>* G \<beta> e" by (rule obs_types.OVal)
  with snd_gamma_star_High[OF eHigh] ValObs show ?thesis by blast
next
  case (AddrObs m)
  with pdv ple have mdv: "adiv m" and mle: "aspect_le (m, 1) u0" by simp_all
  from Haddr[OF mdv] show ?thesis
  proof
    assume "\<exists>e. (e, m) \<in> addr G \<and> (e, m) \<in> FO \<and> vdiv e"
    then obtain e where eaddr: "(e, m) \<in> addr G"
      and efo: "(e, m) \<in> FO" and edv: "vdiv e" by blast
    have ele: "aspect_le (e, 2) u0" by (rule aspect_leI[OF aspect_le_step[OF earlier_event[OF efo] mle]])
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
  from StoreObs pdv ple have wdv: "vdiv w" and wle: "aspect_le (w, 2) u0" by simp_all
  from Hstore[OF chkw wdv] obtain e where
    edata: "(e, w) \<in> data G" and efo: "(e, w) \<in> FO" and edv: "vdiv e" by blast
  have ele: "aspect_le (e, 2) u0" by (rule aspect_leI[OF aspect_le_step[OF earlier_event[OF efo] wle]])
  have eHigh: "G, \<beta> \<turnstile>T e : High"
    by (rule carrier_typed_High[OF min ele edv])
  have "G, \<beta>, V \<turnstile>O StoreObs w : \<Gamma>* G \<beta> e"
    by (rule obs_types.OStore[OF edata])
  with snd_gamma_star_High[OF eHigh] StoreObs show ?thesis by blast
next
  case (PredObs b)
  with pdv ple have "pdiv b" "aspect_le (b, 2) u0" by simp_all
  with pred_obs_High[OF min] PredObs show ?thesis by blast
next
  case (CtrlObs u)
  with pdv ple have udv: "gdiv u" and ule: "aspect_le (u, 0) u0" by simp_all
  from Hguard[OF udv] obtain b where
    bctrl: "(b, u) \<in> ctrl G" and bfo: "(b, u) \<in> FO" and bdv: "pdiv b" by blast
  have ble: "aspect_le (b, 2) u0" by (rule aspect_leI[OF aspect_le_step[OF earlier_event[OF bfo] ule]])
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
  \<comment> \<open>pick a diverging checked observation with minimal event-aspect position\<close>
  define Q where "Q = opos ` {ob \<in> obs_set. odiv ob}"
  from dist obtain ob1 where "ob1 \<in> obs_set" "odiv ob1" by blast
  hence "opos ob1 \<in> Q" unfolding Q_def by blast
  from wfE_min[OF wf_AFO this] obtain u0 where
    u0Q: "u0 \<in> Q" and u0min: "\<And>y. (y, u0) \<in> AFO \<Longrightarrow> y \<notin> Q" by blast
  from u0Q obtain ob0 where
    ob0_in: "ob0 \<in> obs_set" and ob0_dv: "odiv ob0" and ob0_ev: "opos ob0 = u0"
    unfolding Q_def by blast
  have min: "(opos ob, u0) \<notin> AFO" if "ob \<in> obs_set" and "odiv ob" for ob
  proof
    assume fo: "(opos ob, u0) \<in> AFO"
    have "opos ob \<in> Q" using that unfolding Q_def by blast
    with u0min[OF fo] show False by blast
  qed
  \<comment> \<open>the minimal diverging checked observation is target-typed High\<close>
  have tgt_high: "obs_type_tgt G \<beta> V ob0 = High"
  proof (cases ob0)
    case (TxObs \<chi>)
    have pdv: "obs_div0 vdiv adiv pdiv gdiv (V \<chi>)"
      using ob0_dv TxObs by simp
    have ple: "aspect_le (observation_position0 (V \<chi>)) u0"
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
    have ple: "aspect_le (observation_position0 ob0) u0"
      using ob0_ev ValObs by simp
    from prim_obs_High[OF min pdv ple] ob0_in obtain \<tau> where
      "G, \<beta>, V \<turnstile>O ob0 : \<tau>" and "snd \<tau> = High" by blast
    then show ?thesis by (rule obs_type_tgt_HighI)
  next
    case (AddrObs m)
    have pdv: "obs_div0 vdiv adiv pdiv gdiv ob0"
      using ob0_dv AddrObs by simp
    have ple: "aspect_le (observation_position0 ob0) u0"
      using ob0_ev AddrObs by simp
    from prim_obs_High[OF min pdv ple] ob0_in obtain \<tau> where
      "G, \<beta>, V \<turnstile>O ob0 : \<tau>" and "snd \<tau> = High" by blast
    then show ?thesis by (rule obs_type_tgt_HighI)
  next
    case (StoreObs w)
    have pdv: "obs_div0 vdiv adiv pdiv gdiv ob0"
      using ob0_dv StoreObs by simp
    have ple: "aspect_le (observation_position0 ob0) u0"
      using ob0_ev StoreObs by simp
    from prim_obs_High[OF min pdv ple] ob0_in obtain \<tau> where
      "G, \<beta>, V \<turnstile>O ob0 : \<tau>" and "snd \<tau> = High" by blast
    then show ?thesis by (rule obs_type_tgt_HighI)
  next
    case (PredObs b)
    have pdv: "obs_div0 vdiv adiv pdiv gdiv ob0"
      using ob0_dv PredObs by simp
    have ple: "aspect_le (observation_position0 ob0) u0"
      using ob0_ev PredObs by simp
    from prim_obs_High[OF min pdv ple] ob0_in obtain \<tau> where
      "G, \<beta>, V \<turnstile>O ob0 : \<tau>" and "snd \<tau> = High" by blast
    then show ?thesis by (rule obs_type_tgt_HighI)
  next
    case (CtrlObs u)
    have pdv: "obs_div0 vdiv adiv pdiv gdiv ob0"
      using ob0_dv CtrlObs by simp
    have ple: "aspect_le (observation_position0 ob0) u0"
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

end \<comment> \<open>locale lcm_aspect_semantics\<close>

context lcm_semantics
begin
lemma aspect_semantics_instance:
  "lcm_aspect_semantics G \<beta> V obs_set \<Phi> MemEvt FO vdiv adiv pdiv gdiv"
  apply unfold_locales
  subgoal by (rule wf_FO)
  subgoal by (rule trans_FO)
  subgoal by (rule wf_seed)
  subgoal by (rule prim_view)
  subgoal by (rule flow_complete; assumption)
  subgoal for e using Hcar[of e] by blast
  subgoal by (rule Haddr; assumption)
  subgoal by (rule Hpred; assumption)
  subgoal by (rule Hguard; assumption)
  subgoal by (rule Hstore; assumption)
  subgoal by (rule fact_sound; assumption)
  done
end

end
