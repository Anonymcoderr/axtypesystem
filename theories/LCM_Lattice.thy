theory LCM_Lattice
  imports Main
begin

section \<open>Security Lattice\<close>

text \<open>Two-point lattice and pair types. \<open>stable \<tau>\<close> says that the two labels
  agree, nothing more.\<close>

datatype label = Low | High

subsection \<open>Order on label\<close>

instantiation label :: order
begin

definition less_eq_label :: "label \<Rightarrow> label \<Rightarrow> bool" where
  "less_eq_label a b \<equiv> a = Low \<or> a = b"

definition less_label :: "label \<Rightarrow> label \<Rightarrow> bool" where
  "less_label a b \<equiv> a \<le> b \<and> \<not> b \<le> a"

instance
proof
  fix a b c :: label
  show "a \<le> a"
    by (simp add: less_eq_label_def)
  show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
    by (cases a; cases b; cases c; simp add: less_eq_label_def)
  show "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b"
    by (cases a; cases b; simp add: less_eq_label_def)
  show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
    by (simp add: less_label_def)
qed

end

lemma Low_leq [simp]: "Low \<le> l"
  by (simp add: less_eq_label_def)

lemma leq_High [simp]: "l \<le> High"
  by (cases l) (simp_all add: less_eq_label_def)

lemma High_leq_iff [simp]: "High \<le> l \<longleftrightarrow> l = High"
  by (cases l) (simp_all add: less_eq_label_def)

lemma label_cases: "l = Low \<or> l = High"
  by (cases l) auto

subsection \<open>Lattice on label\<close>

instantiation label :: lattice
begin

fun inf_label :: "label \<Rightarrow> label \<Rightarrow> label" where
  "inf_label Low  b = Low"
| "inf_label High b = b"

fun sup_label :: "label \<Rightarrow> label \<Rightarrow> label" where
  "sup_label Low  b = b"
| "sup_label High b = High"

instance
proof
  fix a b c :: label
  show "inf a b \<le> a"
    by (cases a; cases b; simp add: less_eq_label_def)
  show "inf a b \<le> b"
    by (cases a; cases b; simp add: less_eq_label_def)
  show "c \<le> a \<Longrightarrow> c \<le> b \<Longrightarrow> c \<le> inf a b"
    by (cases a; cases b; cases c; simp add: less_eq_label_def)
  show "a \<le> sup a b"
    by (cases a; cases b; simp add: less_eq_label_def)
  show "b \<le> sup a b"
    by (cases a; cases b; simp add: less_eq_label_def)
  show "a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> sup a b \<le> c"
    by (cases a; cases b; cases c; simp add: less_eq_label_def)
qed

end

lemma sup_Low_left [simp]:  "sup Low  b    = b"    by simp
lemma sup_High_left [simp]: "sup High b    = High" by simp
lemma sup_Low_right [simp]: "sup a    Low  = a"    by (cases a) simp_all
lemma sup_High_right [simp]: "sup a    High = High" by (cases a) simp_all
lemma sup_self [simp]:      "sup (a::label) a    = a"    by (cases a) simp_all

section \<open>Pair-valued event types\<close>

type_synonym etype = "label \<times> label"

definition stable :: "etype \<Rightarrow> bool" where
  "stable \<tau> \<equiv> fst \<tau> = snd \<tau>"

definition etype_leq :: "etype \<Rightarrow> etype \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>e" 50) where
  "\<tau>1 \<sqsubseteq>\<^sub>e \<tau>2 \<equiv> fst \<tau>1 \<le> fst \<tau>2 \<and> snd \<tau>1 \<le> snd \<tau>2"

definition ejoin :: "etype \<Rightarrow> etype \<Rightarrow> etype" where
  "ejoin \<tau>1 \<tau>2 \<equiv> (sup (fst \<tau>1) (fst \<tau>2), sup (snd \<tau>1) (snd \<tau>2))"

abbreviation LL :: etype where "LL \<equiv> (Low,  Low)"
abbreviation LH :: etype where "LH \<equiv> (Low,  High)"
abbreviation HH :: etype where "HH \<equiv> (High, High)"

subsection \<open>Stability lemmas\<close>

lemma stable_LL [simp]: "stable LL" by (simp add: stable_def)
lemma stable_HH [simp]: "stable HH" by (simp add: stable_def)
lemma not_stable_LH [simp]: "\<not> stable LH" by (simp add: stable_def)

lemma stable_cases:
  assumes "stable \<tau>"
  obtains "fst \<tau> = Low  \<and> snd \<tau> = Low"
        | "fst \<tau> = High \<and> snd \<tau> = High"
  using assms by (cases "fst \<tau>"; cases "snd \<tau>"; auto simp: stable_def)

subsection \<open>etype_leq lemmas\<close>

lemma etype_leq_refl [simp]: "\<tau> \<sqsubseteq>\<^sub>e \<tau>"
  by (simp add: etype_leq_def)

lemma etype_leq_trans:
  "\<tau>1 \<sqsubseteq>\<^sub>e \<tau>2 \<Longrightarrow> \<tau>2 \<sqsubseteq>\<^sub>e \<tau>3 \<Longrightarrow> \<tau>1 \<sqsubseteq>\<^sub>e \<tau>3"
  by (auto simp: etype_leq_def intro: order_trans)

lemma ejoin_leq_left: "\<tau>1 \<sqsubseteq>\<^sub>e ejoin \<tau>1 \<tau>2"
  by (cases "fst \<tau>1"; cases "snd \<tau>1"; simp add: etype_leq_def ejoin_def)

lemma ejoin_leq_right: "\<tau>2 \<sqsubseteq>\<^sub>e ejoin \<tau>1 \<tau>2"
  by (cases "fst \<tau>2"; cases "snd \<tau>2"; cases "fst \<tau>1"; cases "snd \<tau>1";
      simp add: etype_leq_def ejoin_def)

lemma ejoin_least:
  "\<tau>1 \<sqsubseteq>\<^sub>e \<tau> \<Longrightarrow> \<tau>2 \<sqsubseteq>\<^sub>e \<tau> \<Longrightarrow> ejoin \<tau>1 \<tau>2 \<sqsubseteq>\<^sub>e \<tau>"
  by (cases "fst \<tau>1"; cases "fst \<tau>2"; cases "snd \<tau>1"; cases "snd \<tau>2";
      simp add: etype_leq_def ejoin_def less_eq_label_def)

lemma stable_ejoin:
  "stable \<tau>1 \<Longrightarrow> stable \<tau>2 \<Longrightarrow> stable (ejoin \<tau>1 \<tau>2)"
  by (cases "fst \<tau>1"; cases "snd \<tau>1"; cases "fst \<tau>2"; cases "snd \<tau>2";
      auto simp: stable_def ejoin_def)

end
