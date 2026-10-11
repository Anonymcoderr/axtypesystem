theory LCM_Semantic_Examples
  imports LCM_Execution_Bridge
begin

section \<open>Concrete public-table executions\<close>

text \<open>A secret index, a read from a fixed public table, and a probe addressed by
  the value read.\<close>

datatype example_event = SecretIndex | TableRead | LaterProbe

fun example_rank :: "example_event \<Rightarrow> nat" where
  "example_rank SecretIndex = 0"
| "example_rank TableRead = 1"
| "example_rank LaterProbe = 2"

definition example_order :: "(example_event \<times> example_event) set" where
  "example_order = measure example_rank"

lemma example_order_wf: "wf example_order"
  by (simp add: example_order_def)

lemma example_order_trans: "trans example_order"
  by (auto simp: example_order_def trans_def intro: less_trans)

definition example_memory :: "example_event set" where
  "example_memory = {TableRead, LaterProbe}"

definition address_graph :: "('e \<times> 'e) set \<Rightarrow> 'e graph" where
  "address_graph A = \<lparr>rf = {}, rfx = {}, data = {}, addr = A, ctrl = {}\<rparr>"

lemma address_graph_typesA:
  "typesA (address_graph A) \<beta> e l \<longleftrightarrow> l \<le> fst (base_val \<beta> e)"
  by (auto simp: address_graph_def elim: typesA.cases intro: typesA.BaseA)

lemma address_graph_typesT:
  "typesT (address_graph A) \<beta> e l \<longleftrightarrow> l \<le> snd (base_val \<beta> e)"
  by (auto simp: address_graph_def elim: typesT.cases intro: typesT.BaseT)

lemma address_graph_gamma:
  "\<Gamma>* (address_graph A) \<beta> e = base_val \<beta> e"
proof -
  have arch: "least_arch (address_graph A) \<beta> e = fst (base_val \<beta> e)"
    by (cases "fst (base_val \<beta> e)")
       (simp_all add: least_arch_def address_graph_typesA)
  have target: "least_tgt (address_graph A) \<beta> e = snd (base_val \<beta> e)"
    by (cases "snd (base_val \<beta> e)")
       (simp_all add: least_tgt_def address_graph_typesT)
  show ?thesis by (simp add: gamma_star_def arch target)
qed

definition table_graph :: "example_event graph" where
  "table_graph = address_graph {(SecretIndex, TableRead), (TableRead, LaterProbe)}"

definition table_seeds :: "example_event base_labels" where
  "table_seeds = ((\<lambda>e. if e = SecretIndex then LH else LL), (\<lambda>_. LL))"

lemma table_graph_fields [simp]:
  "rf table_graph = {}" "rfx table_graph = {}" "data table_graph = {}"
  "addr table_graph = {(SecretIndex, TableRead), (TableRead, LaterProbe)}"
  "ctrl table_graph = {}"
  by (simp_all add: table_graph_def address_graph_def)

lemma table_address_seed [simp]: "base_addr table_seeds e = LL"
  by (simp add: table_seeds_def base_addr_def)

definition table_execution ::
  "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (example_event, nat, nat) lcm_execution" where
  "table_execution B h =
    \<lparr>exec_payload = (\<lambda>e. case e of SecretIndex \<Rightarrow> h
                                    | TableRead \<Rightarrow> B h
                                    | LaterProbe \<Rightarrow> 0),
     exec_address = (\<lambda>e. case e of SecretIndex \<Rightarrow> 0
                                    | TableRead \<Rightarrow> h
                                    | LaterProbe \<Rightarrow> B h),
     exec_predicate = (\<lambda>_. False), exec_executed = (\<lambda>_. True)\<rparr>"

lemma table_wf_seeds: "wf_base table_seeds"
  by (auto simp: wf_base_def table_seeds_def base_val_def base_addr_def
           split: if_splits)

interpretation table_semantics: lcm_aspect_semantics
  table_graph table_seeds AddrObs "cache_obs_set example_memory" "{}"
  example_memory example_order
  "payload_div (table_execution B h1) (table_execution B h2)"
  "address_div (table_execution B h1) (table_execution B h2)"
  "predicate_div (table_execution B h1) (table_execution B h2)"
  "guard_div (table_execution B h1) (table_execution B h2)"
  for B h1 h2
  apply unfold_locales
  subgoal by (rule example_order_wf)
  subgoal by (rule example_order_trans)
  subgoal by (rule table_wf_seeds)
  subgoal by simp
  subgoal by (rule cache_flow_complete)
  subgoal for e
    by (cases e)
       (auto simp: table_execution_def payload_div_def address_div_def guard_div_def
                   table_graph_def address_graph_def table_seeds_def base_val_def
                   example_memory_def example_order_def)
  subgoal for m
    by (cases m)
       (auto simp: table_execution_def payload_div_def address_div_def
                   table_graph_def address_graph_def table_seeds_def base_addr_def
                   example_order_def)
  subgoal by (simp add: predicate_div_def table_execution_def)
  subgoal by (simp add: guard_div_def table_execution_def)
  subgoal by (auto simp: cache_obs_set_def)
  subgoal by simp
  done

lemma table_event_types [simp]:
  "\<Gamma>* table_graph table_seeds SecretIndex = LH"
  "\<Gamma>* table_graph table_seeds TableRead = LL"
  "\<Gamma>* table_graph table_seeds LaterProbe = LL"
  by (simp_all add: table_graph_def address_graph_gamma table_seeds_def base_val_def)

lemma table_address_derivations:
  "obs_types table_graph table_seeds V (AddrObs TableRead) \<tau>
     \<longleftrightarrow> \<tau> = LL \<or> \<tau> = LH"
proof
  assume "obs_types table_graph table_seeds V (AddrObs TableRead) \<tau>"
  then show "\<tau> = LL \<or> \<tau> = LH"
    by (cases rule: obs_types.cases) auto
next
  assume alternatives: "\<tau> = LL \<or> \<tau> = LH"
  have low: "obs_types table_graph table_seeds V (AddrObs TableRead) LL"
    using obs_types.OAddrBase[of table_graph table_seeds V TableRead]
    by (simp add: table_seeds_def base_addr_def)
  have high: "obs_types table_graph table_seeds V (AddrObs TableRead)
      (\<Gamma>* table_graph table_seeds SecretIndex)"
    by (rule obs_types.OAddr) (simp add: table_graph_def address_graph_def)
  from alternatives low high show "obs_types table_graph table_seeds V (AddrObs TableRead) \<tau>"
    by auto
qed

lemma table_address_type:
  "obs_ty table_graph table_seeds V (AddrObs TableRead) = LH"
  by (simp add: obs_ty_def obs_type_arch_def obs_type_tgt_def
                table_address_derivations)

lemma table_containment_fails:
  "\<not> containment_r {} table_graph table_seeds V (cache_obs_set example_memory)"
  using table_address_type[of V]
  by (auto simp: containment_r_def cache_obs_set_def example_memory_def stable_def)

text \<open>For the identity table the \<open>LL\<close>-typed read returns the secret; its address is
  checked and has type \<open>LH\<close>.\<close>

lemma identity_table_payload_diverges:
  assumes "h1 \<noteq> h2"
  shows "payload_div (table_execution id h1) (table_execution id h2) TableRead"
  using assms by (simp add: payload_div_def table_execution_def)

lemma identity_table_cache_traces_differ:
  assumes "h1 \<noteq> h2"
  shows "cache_trace id (table_execution id h1) [TableRead, LaterProbe]
       \<noteq> cache_trace id (table_execution id h2) [TableRead, LaterProbe]"
  using assms by (simp add: table_execution_def cache_event_def)

lemma identity_table_64_byte_lines_differ:
  "cache_trace (\<lambda>a. a div 64) (table_execution id 0) [TableRead, LaterProbe]
   \<noteq> cache_trace (\<lambda>a. a div 64) (table_execution id 64) [TableRead, LaterProbe]"
  by (simp add: table_execution_def cache_event_def)

text \<open>Equal cache lines at the read do not give equal exact addresses; the probe
  separates them.\<close>

lemma same_line_read_can_feed_different_line_probe:
  "cache_event (\<lambda>a. a div 64) (table_execution (\<lambda>i. 64 * i) 0) TableRead =
   cache_event (\<lambda>a. a div 64) (table_execution (\<lambda>i. 64 * i) 1) TableRead"
  "cache_event (\<lambda>a. a div 64) (table_execution (\<lambda>i. 64 * i) 0) LaterProbe \<noteq>
   cache_event (\<lambda>a. a div 64) (table_execution (\<lambda>i. 64 * i) 1) LaterProbe"
  "address_div (table_execution (\<lambda>i. 64 * i) 0)
               (table_execution (\<lambda>i. 64 * i) 1) TableRead"
  by (simp_all add: cache_event_def address_div_def table_execution_def)

text \<open>\<open>lcm_semantics\<close> cannot interpret this instance: the address divergence
  belongs to the read itself.\<close>

lemma identity_table_needs_same_event_mediation:
  assumes different: "h1 \<noteq> h2"
  shows "\<not> lcm_semantics table_graph table_seeds AddrObs
    (cache_obs_set example_memory) {} example_memory example_order
    (payload_div (table_execution id h1) (table_execution id h2))
    (address_div (table_execution id h1) (table_execution id h2))
    (predicate_div (table_execution id h1) (table_execution id h2))
    (guard_div (table_execution id h1) (table_execution id h2))"
proof
  assume old: "lcm_semantics table_graph table_seeds AddrObs
    (cache_obs_set example_memory) {} example_memory example_order
    (payload_div (table_execution id h1) (table_execution id h2))
    (address_div (table_execution id h1) (table_execution id h2))
    (predicate_div (table_execution id h1) (table_execution id h2))
    (guard_div (table_execution id h1) (table_execution id h2))"
  from lcm_semantics.Hcar[OF old, of TableRead] different show False
    by (auto simp: table_execution_def payload_div_def address_div_def guard_div_def
                   table_graph_def address_graph_def table_seeds_def base_val_def
                   example_memory_def example_order_def)
qed

section \<open>Secret internal data with fixed observations\<close>

definition safe_graph :: "example_event graph" where
  "safe_graph = address_graph {}"

definition safe_seeds :: "example_event base_labels" where
  "safe_seeds = ((\<lambda>e. if e = SecretIndex then HH else LL), (\<lambda>_. LL))"

definition safe_execution :: "nat \<Rightarrow> (example_event, nat, nat) lcm_execution" where
  "safe_execution h =
    \<lparr>exec_payload = (\<lambda>e. if e = SecretIndex then h else 0),
     exec_address = (\<lambda>_. 0), exec_predicate = (\<lambda>_. False),
     exec_executed = (\<lambda>_. True)\<rparr>"

lemma safe_wf_seeds: "wf_base safe_seeds"
  by (auto simp: wf_base_def safe_seeds_def base_val_def base_addr_def
           split: if_splits)

interpretation safe_semantics: lcm_aspect_semantics
  safe_graph safe_seeds AddrObs "cache_obs_set example_memory" "{}"
  example_memory example_order
  "payload_div (safe_execution h1) (safe_execution h2)"
  "address_div (safe_execution h1) (safe_execution h2)"
  "predicate_div (safe_execution h1) (safe_execution h2)"
  "guard_div (safe_execution h1) (safe_execution h2)"
  for h1 h2
  apply unfold_locales
  subgoal by (rule example_order_wf)
  subgoal by (rule example_order_trans)
  subgoal by (rule safe_wf_seeds)
  subgoal by simp
  subgoal by (rule cache_flow_complete)
  subgoal for e
    by (auto simp: safe_execution_def payload_div_def safe_seeds_def base_val_def
             split: if_splits)
  subgoal by (simp add: address_div_def safe_execution_def)
  subgoal by (simp add: predicate_div_def safe_execution_def)
  subgoal by (simp add: guard_div_def safe_execution_def)
  subgoal by (auto simp: cache_obs_set_def)
  subgoal by simp
  done

lemma safe_secret_type:
  "\<Gamma>* safe_graph safe_seeds SecretIndex = HH"
  by (simp add: safe_graph_def address_graph_gamma safe_seeds_def base_val_def)

lemma safe_internal_divergence:
  assumes "h1 \<noteq> h2"
  shows "payload_div (safe_execution h1) (safe_execution h2) SecretIndex"
  using assms by (simp add: payload_div_def safe_execution_def)

lemma safe_address_derivations:
  "obs_types safe_graph safe_seeds V (AddrObs e) \<tau> \<longleftrightarrow> \<tau> = LL"
  using obs_types.OAddrBase[of safe_graph safe_seeds V e]
  by (auto elim: obs_types.cases
           simp: safe_graph_def address_graph_def safe_seeds_def base_addr_def)

lemma safe_no_control_derivations:
  "\<not> obs_types safe_graph safe_seeds V (CtrlObs e) \<tau>"
  by (auto elim: obs_types.cases simp: safe_graph_def address_graph_def)

lemma safe_checked_type:
  assumes "ob \<in> cache_obs_set example_memory"
  shows "obs_ty safe_graph safe_seeds V ob = LL"
  using assms
  by (auto simp: cache_obs_set_def obs_ty_def obs_type_arch_def obs_type_tgt_def
                 safe_address_derivations safe_no_control_derivations)

lemma safe_containment:
  "containment_r {} safe_graph safe_seeds V (cache_obs_set example_memory)"
  using safe_checked_type[of _ V]
  by (simp add: containment_r_def stable_def)

theorem safe_cache_trace_noninterference:
  assumes "set es \<subseteq> example_memory"
  shows "cache_trace line (safe_execution h1) es =
         cache_trace line (safe_execution h2) es"
proof -
  have all_low:
    "\<forall>ob \<in> cache_obs_set example_memory.
      obs_type_arch safe_graph safe_seeds AddrObs ob = Low"
    using safe_checked_type[of _ AddrObs] by (simp add: obs_ty_def)
  show ?thesis
    by (rule safe_semantics.cache_trace_noninterference[OF
          safe_containment all_low refl refl refl refl assms])
qed

corollary safe_cache_SCT:
  assumes "set es \<subseteq> example_memory"
  shows "cache_SCT (range safe_execution) (\<lambda>_ _. True) line es"
  using safe_cache_trace_noninterference[OF assms]
  by (auto simp: cache_SCT_def)

end
