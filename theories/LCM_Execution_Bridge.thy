theory LCM_Execution_Bridge
  imports LCM_Aspect_Soundness
begin

section \<open>Executions and concrete observation equality\<close>

text \<open>Divergence predicates as inequalities between two execution records over
  the same events. Addresses are exact, before cache-line projection.\<close>

record ('e, 'v, 'a) lcm_execution =
  exec_payload :: "'e \<Rightarrow> 'v"
  exec_address :: "'e \<Rightarrow> 'a"
  exec_predicate :: "'e \<Rightarrow> bool"
  exec_executed :: "'e \<Rightarrow> bool"

definition payload_div ::
  "('e, 'v, 'a) lcm_execution \<Rightarrow> ('e, 'v, 'a) lcm_execution \<Rightarrow> 'e \<Rightarrow> bool"
  where "payload_div s t e \<longleftrightarrow> exec_payload s e \<noteq> exec_payload t e"

definition address_div ::
  "('e, 'v, 'a) lcm_execution \<Rightarrow> ('e, 'v, 'a) lcm_execution \<Rightarrow> 'e \<Rightarrow> bool"
  where "address_div s t e \<longleftrightarrow> exec_address s e \<noteq> exec_address t e"

definition predicate_div ::
  "('e, 'v, 'a) lcm_execution \<Rightarrow> ('e, 'v, 'a) lcm_execution \<Rightarrow> 'e \<Rightarrow> bool"
  where "predicate_div s t e \<longleftrightarrow> exec_predicate s e \<noteq> exec_predicate t e"

definition guard_div ::
  "('e, 'v, 'a) lcm_execution \<Rightarrow> ('e, 'v, 'a) lcm_execution \<Rightarrow> 'e \<Rightarrow> bool"
  where "guard_div s t e \<longleftrightarrow> exec_executed s e \<noteq> exec_executed t e"

datatype ('v, 'a) execution_observation_value =
    PayloadValue 'v
  | AddressValue 'a
  | PredicateValue bool
  | GuardValue bool
  | Unexported

fun primitive_observation ::
  "('e, 'v, 'a) lcm_execution \<Rightarrow> 'e obs \<Rightarrow> ('v, 'a) execution_observation_value"
  where
  "primitive_observation s (ValObs e) = PayloadValue (exec_payload s e)"
| "primitive_observation s (AddrObs e) = AddressValue (exec_address s e)"
| "primitive_observation s (StoreObs e) = PayloadValue (exec_payload s e)"
| "primitive_observation s (PredObs e) = PredicateValue (exec_predicate s e)"
| "primitive_observation s (CtrlObs e) = GuardValue (exec_executed s e)"
| "primitive_observation s (TxObs e) = Unexported"

definition execution_observation ::
  "'e view_fn \<Rightarrow> ('e, 'v, 'a) lcm_execution \<Rightarrow> 'e obs \<Rightarrow>
    ('v, 'a) execution_observation_value"
  where
  "execution_observation V s ob =
    (case ob of TxObs e \<Rightarrow> primitive_observation s (V e)
      | _ \<Rightarrow> primitive_observation s ob)"

lemma obs_div0_execution_iff:
  "obs_div0 (payload_div s t) (address_div s t)
      (predicate_div s t) (guard_div s t) ob \<longleftrightarrow>
    primitive_observation s ob \<noteq> primitive_observation t ob"
  by (cases ob)
     (simp_all add: payload_div_def address_div_def predicate_div_def guard_div_def)

lemma obs_div_execution_iff:
  "obs_div V (payload_div s t) (address_div s t)
      (predicate_div s t) (guard_div s t) ob \<longleftrightarrow>
    execution_observation V s ob \<noteq> execution_observation V t ob"
  by (cases ob)
     (simp_all add: obs_div_def execution_observation_def obs_div0_execution_iff
       payload_div_def address_div_def predicate_div_def guard_div_def)

section \<open>Cache observations and traces\<close>

definition cache_event ::
  "('a \<Rightarrow> 'l) \<Rightarrow> ('e, 'v, 'a) lcm_execution \<Rightarrow> 'e \<Rightarrow> 'l option"
  where
  "cache_event line s e =
    (if exec_executed s e then Some (line (exec_address s e)) else None)"

definition cache_view ::
  "('a \<Rightarrow> 'l) \<Rightarrow> ('e, 'v, 'a) lcm_execution \<Rightarrow>
    'e set \<Rightarrow> 'e \<Rightarrow> 'l option"
  where
  "cache_view line s M e = (if e \<in> M then cache_event line s e else None)"

fun cache_trace ::
  "('a \<Rightarrow> 'l) \<Rightarrow> ('e, 'v, 'a) lcm_execution \<Rightarrow> 'e list \<Rightarrow> 'l list"
  where
  "cache_trace line s [] = []"
| "cache_trace line s (e # es) =
    (case cache_event line s e of None \<Rightarrow> cache_trace line s es
      | Some l \<Rightarrow> l # cache_trace line s es)"

lemma cache_event_eq:
  assumes "\<not> address_div s t e" "\<not> guard_div s t e"
  shows "cache_event line s e = cache_event line t e"
  using assms by (simp add: address_div_def guard_div_def cache_event_def)

lemma cache_trace_cong:
  assumes "\<And>e. e \<in> set es \<Longrightarrow> cache_event line s e = cache_event line t e"
  shows "cache_trace line s es = cache_trace line t es"
  using assms
  by (induction es) (auto split: option.splits)

lemma checked_divergence_cache_event_eq:
  assumes covered: "AddrObs e \<in> S" "CtrlObs e \<in> S"
    and no_div: "\<forall>ob \<in> S.
      \<not> obs_div V (payload_div s t) (address_div s t)
        (predicate_div s t) (guard_div s t) ob"
  shows "cache_event line s e = cache_event line t e"
proof (rule cache_event_eq)
  show "\<not> address_div s t e" using no_div covered(1) by auto
  show "\<not> guard_div s t e" using no_div covered(2) by auto
qed

lemma checked_divergence_cache_view_eq:
  assumes coverage: "\<And>e. e \<in> M \<Longrightarrow> AddrObs e \<in> S \<and> CtrlObs e \<in> S"
    and no_div: "\<forall>ob \<in> S.
      \<not> obs_div V (payload_div s t) (address_div s t)
        (predicate_div s t) (guard_div s t) ob"
  shows "cache_view line s M = cache_view line t M"
proof (rule ext)
  fix e
  show "cache_view line s M e = cache_view line t M e"
  proof (cases "e \<in> M")
    case True
    have "cache_event line s e = cache_event line t e"
      using coverage[OF True] no_div
      by (blast intro: checked_divergence_cache_event_eq)
    with True show ?thesis by (simp add: cache_view_def)
  next
    case False
    then show ?thesis by (simp add: cache_view_def)
  qed
qed

lemma checked_divergence_cache_trace_eq:
  assumes coverage: "\<And>e. e \<in> M \<Longrightarrow> AddrObs e \<in> S \<and> CtrlObs e \<in> S"
    and no_div: "\<forall>ob \<in> S.
      \<not> obs_div V (payload_div s t) (address_div s t)
        (predicate_div s t) (guard_div s t) ob"
    and memory_events: "set es \<subseteq> M"
  shows "cache_trace line s es = cache_trace line t es"
proof (rule cache_trace_cong)
  fix e assume "e \<in> set es"
  with memory_events have "e \<in> M" by blast
  from coverage[OF this] no_div show "cache_event line s e = cache_event line t e"
    by (blast intro: checked_divergence_cache_event_eq)
qed

corollary cache_trace_difference_checked_divergence:
  assumes coverage: "\<And>e. e \<in> M \<Longrightarrow> AddrObs e \<in> S \<and> CtrlObs e \<in> S"
    and memory_events: "set es \<subseteq> M"
    and different: "cache_trace line s es \<noteq> cache_trace line t es"
  shows "\<exists>ob \<in> S.
    obs_div V (payload_div s t) (address_div s t)
      (predicate_div s t) (guard_div s t) ob"
  using checked_divergence_cache_trace_eq[OF coverage _ memory_events] different
  by blast

section \<open>Conditional execution-level result\<close>

context lcm_aspect_semantics
begin

theorem checked_execution_observations_eq:
  assumes contain: "containment_r \<Phi> G \<beta> V obs_set"
    and all_low: "\<forall>ob \<in> obs_set. obs_type_arch G \<beta> V ob = Low"
    and vd: "vdiv = payload_div s t"
    and ad: "adiv = address_div s t"
    and pd: "pdiv = predicate_div s t"
    and gd: "gdiv = guard_div s t"
  shows "\<forall>ob \<in> obs_set. execution_observation V s ob = execution_observation V t ob"
  using thm1_sct[OF contain all_low]
  by (simp add: vd ad pd gd obs_div_execution_iff)

theorem cache_view_noninterference:
  assumes contain: "containment_r \<Phi> G \<beta> V obs_set"
    and all_low: "\<forall>ob \<in> obs_set. obs_type_arch G \<beta> V ob = Low"
    and vd: "vdiv = payload_div s t"
    and ad: "adiv = address_div s t"
    and pd: "pdiv = predicate_div s t"
    and gd: "gdiv = guard_div s t"
  shows "cache_view line s MemEvt = cache_view line t MemEvt"
proof -
  have no_div: "\<forall>ob \<in> obs_set.
    \<not> obs_div V (payload_div s t) (address_div s t)
      (predicate_div s t) (guard_div s t) ob"
    using thm1_sct[OF contain all_low] by (simp add: vd ad pd gd)
  show ?thesis
    by (rule checked_divergence_cache_view_eq[OF flow_complete no_div])
qed

theorem cache_trace_noninterference:
  assumes contain: "containment_r \<Phi> G \<beta> V obs_set"
    and all_low: "\<forall>ob \<in> obs_set. obs_type_arch G \<beta> V ob = Low"
    and vd: "vdiv = payload_div s t"
    and ad: "adiv = address_div s t"
    and pd: "pdiv = predicate_div s t"
    and gd: "gdiv = guard_div s t"
    and memory_events: "set es \<subseteq> MemEvt"
  shows "cache_trace line s es = cache_trace line t es"
proof -
  have no_div: "\<forall>ob \<in> obs_set.
    \<not> obs_div V (payload_div s t) (address_div s t)
      (predicate_div s t) (guard_div s t) ob"
    using thm1_sct[OF contain all_low] by (simp add: vd ad pd gd)
  show ?thesis
    by (rule checked_divergence_cache_trace_eq[OF flow_complete no_div memory_events])
qed

end

section \<open>Quantifying over related executions\<close>

definition cache_SCT ::
  "('e, 'v, 'a) lcm_execution set \<Rightarrow>
    (('e, 'v, 'a) lcm_execution \<Rightarrow> ('e, 'v, 'a) lcm_execution \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'l) \<Rightarrow> 'e list \<Rightarrow> bool"
  where
  "cache_SCT executions low_equiv line es \<longleftrightarrow>
    (\<forall>s \<in> executions. \<forall>t \<in> executions.
      low_equiv s t \<longrightarrow> cache_trace line s es = cache_trace line t es)"

text \<open>\<open>low_equiv\<close> is an instance parameter; the adequacy obligations are required
  for every related pair.\<close>

theorem cache_SCT_from_adequacy:
  assumes adequate: "\<And>s t. s \<in> executions \<Longrightarrow> t \<in> executions \<Longrightarrow>
      low_equiv s t \<Longrightarrow>
      lcm_aspect_semantics G \<beta> V S \<Phi> M FO
        (payload_div s t) (address_div s t) (predicate_div s t) (guard_div s t)"
    and contain: "containment_r \<Phi> G \<beta> V S"
    and all_low: "\<forall>ob \<in> S. obs_type_arch G \<beta> V ob = Low"
    and memory_events: "set es \<subseteq> M"
  shows "cache_SCT executions low_equiv line es"
proof (unfold cache_SCT_def; intro ballI impI)
  fix s t
  assume s: "s \<in> executions" and t: "t \<in> executions"
    and related: "low_equiv s t"
  interpret pair: lcm_aspect_semantics G \<beta> V S \<Phi> M FO
    "payload_div s t" "address_div s t" "predicate_div s t" "guard_div s t"
    by (rule adequate[OF s t related])
  show "cache_trace line s es = cache_trace line t es"
    by (rule pair.cache_trace_noninterference[OF contain all_low refl refl refl refl memory_events])
qed

end
