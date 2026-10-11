theory LCM_Graph
  imports LCM_Lattice
begin

section \<open>Execution Graphs\<close>

record 'e graph =
  rf   :: "('e \<times> 'e) set"   \<comment> \<open>reads-from (architectural)\<close>
  rfx  :: "('e \<times> 'e) set"   \<comment> \<open>extra-architectural reads-from\<close>
  data :: "('e \<times> 'e) set"   \<comment> \<open>data dependency\<close>
  addr :: "('e \<times> 'e) set"   \<comment> \<open>address dependency\<close>
  ctrl :: "('e \<times> 'e) set"   \<comment> \<open>control dependency\<close>

section \<open>Base (seed) labels\<close>

text \<open>Seed labels for residual sources: \<open>base_val\<close> for an event's value,
  \<open>base_addr\<close> for a memory event's address.\<close>

type_synonym 'e base_labels = "('e \<Rightarrow> etype) \<times> ('e \<Rightarrow> etype)"

definition base_val  :: "'e base_labels \<Rightarrow> 'e \<Rightarrow> etype" where
  "base_val  \<beta> e \<equiv> fst \<beta> e"

definition base_addr :: "'e base_labels \<Rightarrow> 'e \<Rightarrow> etype" where
  "base_addr \<beta> e \<equiv> snd \<beta> e"

definition wf_base :: "'e base_labels \<Rightarrow> bool" where
  "wf_base \<beta> \<equiv>
     (\<forall>e. fst (base_val  \<beta> e) \<le> snd (base_val  \<beta> e)) \<and>
     (\<forall>m. fst (base_addr \<beta> m) \<le> snd (base_addr \<beta> m))"

lemma wf_base_val:
  assumes "wf_base \<beta>"
  shows "fst (base_val \<beta> e) \<le> snd (base_val \<beta> e)"
  using assms unfolding wf_base_def by blast

lemma wf_base_addr:
  assumes "wf_base \<beta>"
  shows "fst (base_addr \<beta> m) \<le> snd (base_addr \<beta> m)"
  using assms unfolding wf_base_def by blast

section \<open>Graph subgraph ordering\<close>

text \<open>\<open>G1 \<preceq>\<^sub>G G2\<close>: the same graph except that \<open>G1\<close> has fewer \<open>rfx\<close> edges.\<close>

definition graph_rfx_leq :: "'e graph \<Rightarrow> 'e graph \<Rightarrow> bool"
    (infix "\<preceq>\<^sub>G" 50) where
  "G1 \<preceq>\<^sub>G G2 \<equiv>
     rfx  G1 \<subseteq> rfx  G2 \<and>
     rf   G1 = rf   G2 \<and>
     data G1 = data G2 \<and>
     addr G1 = addr G2 \<and>
     ctrl G1 = ctrl G2"

lemma graph_rfx_leq_refl [simp]: "G \<preceq>\<^sub>G G"
  by (simp add: graph_rfx_leq_def)

lemma graph_rfx_leq_trans:
  "G1 \<preceq>\<^sub>G G2 \<Longrightarrow> G2 \<preceq>\<^sub>G G3 \<Longrightarrow> G1 \<preceq>\<^sub>G G3"
  by (auto simp: graph_rfx_leq_def)

(* Projection lemmas *)
lemma graph_rfx_leq_rfx  [dest]: "G1 \<preceq>\<^sub>G G2 \<Longrightarrow> rfx  G1 \<subseteq> rfx  G2"
  by (simp add: graph_rfx_leq_def)
lemma graph_rfx_leq_rf   [dest]: "G1 \<preceq>\<^sub>G G2 \<Longrightarrow> rf   G1 = rf   G2"
  by (simp add: graph_rfx_leq_def)
lemma graph_rfx_leq_data [dest]: "G1 \<preceq>\<^sub>G G2 \<Longrightarrow> data G1 = data G2"
  by (simp add: graph_rfx_leq_def)
lemma graph_rfx_leq_addr [dest]: "G1 \<preceq>\<^sub>G G2 \<Longrightarrow> addr G1 = addr G2"
  by (simp add: graph_rfx_leq_def)
lemma graph_rfx_leq_ctrl [dest]: "G1 \<preceq>\<^sub>G G2 \<Longrightarrow> ctrl G1 = ctrl G2"
  by (simp add: graph_rfx_leq_def)

end
