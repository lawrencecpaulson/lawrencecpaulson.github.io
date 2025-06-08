section \<open>Simple example of an inductive definition: Prolog append\<close>

theory Append
imports Main
begin

inductive Append :: "['a list, 'a list, 'a list] \<Rightarrow> bool" where
    Append_Nil:  "Append [] X X"
  | Append_Cons: "Append Y Z W \<Longrightarrow> Append (X#Y) Z (X#W)"

lemma Append_function: "\<lbrakk>Append X Y Z; Append X Y Z'\<rbrakk> \<Longrightarrow> Z' = Z"
proof (induction arbitrary: Z' rule: Append.induct)
  show "\<And>X Z'. Append [] X Z' \<Longrightarrow> Z' = X"
    using Append.cases by blast
  show "\<And>Y Z W X Z'. \<lbrakk>\<And>Z'. Append Y Z Z' \<Longrightarrow> Z'=W; Append (X#Y) Z Z'\<rbrakk>
       \<Longrightarrow> Z' = X#W"
    by (metis Append.cases list.inject neq_Nil_conv)
qed

inductive_simps Append_Nil_simp [simp]: "Append [] X Y"
inductive_simps Append_Cons_simp [simp]: "Append (X#Y) Z V"

lemma "\<lbrakk>Append X Y Z; Append X Y Z'\<rbrakk> \<Longrightarrow> Z' = Z"
proof (induction arbitrary: Z' rule: Append.induct)
  case Append_Nil
  then show ?case
    by simp
next
  case Append_Cons
  then show ?case
    by (metis Append_Cons_simp)
qed

lemma Append_function2: "\<lbrakk>Append X Y Z; Append X Y' Z\<rbrakk> \<Longrightarrow> Y' = Y"
  by (induction rule: Append.induct) auto

lemma Append_assoc: "\<lbrakk>Append T U V; Append V W X; Append U W Y\<rbrakk> \<Longrightarrow> Append T Y X"
  by (induction arbitrary: X rule: Append.induct) (auto simp add: Append_function)

lemma Append_imp_append: "Append X Y Z \<Longrightarrow> Z = X@Y"
proof (induction rule: Append.induct)
  show "\<And>X. X = [] @ X" 
    by simp
  show "\<And>Y Z W X. W = Y@Z \<Longrightarrow> X # W = (X # Y) @ Z"
    by simp
qed

lemma Append_append: "Append X Y (X@Y)"
proof (induction X)
  show "Append [] Y ([] @ Y)"
    by (auto simp: Append.intros)
  show "\<And>U X. Append X Y (X @ Y) \<Longrightarrow> Append (U # X) Y ((U # X) @ Y)"
    by (auto simp: Append.intros)
qed

text \<open>As above but in one line\<close>
lemma "Append X Y Z \<Longrightarrow> Z = X@Y"
  by (induction rule: Append.induct) auto

lemma "Append X Y (X@Y)"
  by (induction X) (auto simp: Append.intros)

lemma Append_iff_append: "Append X Y Z \<longleftrightarrow> Z = X@Y"
  using Append_append Append_imp_append by blast

lemma Append_function1: "\<lbrakk>Append X Y Z; Append X' Y Z\<rbrakk> \<Longrightarrow> X' = X"
  by (simp add: Append_iff_append)

end
