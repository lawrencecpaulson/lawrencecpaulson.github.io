section \<open>Simple example of an inductive definition: Prolog append\<close>

theory Append
imports Main
begin

inductive Append :: "['a list, 'a list, 'a list] \<Rightarrow> bool" where
    Append_Nil:  "Append [] X X"
  | Append_Cons: "Append Y Z W \<Longrightarrow> Append (X#Y) Z (X#W)"

lemma Append_function: "\<lbrakk>Append X Y Z; Append X Y Z'\<rbrakk> \<Longrightarrow> Z' = Z"
proof (induction arbitrary: Z' rule: Append.induct)
  show "\<And>Y Z'. Append [] Y Z' \<Longrightarrow> Z' = Y"
    using Append.cases by blast
  show "\<And>X Y W A Z'. \<lbrakk>\<And>Z'. Append X Y Z' \<Longrightarrow> Z'=W; Append (A#X) Y Z'\<rbrakk>
       \<Longrightarrow> Z' = A#W"
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
  show "\<And>Y. Y = [] @ Y" 
    by simp
  show "\<And>X Y Z A. Z = X@Y \<Longrightarrow> A # Z = (A # X) @ Y"
    by simp
qed

lemma Append_append: "Append X Y (X@Y)"
proof (induction X)
  show "Append [] Y ([] @ Y)"
    by (auto simp: Append.intros)
  show "\<And>A X. Append X Y (X @ Y) \<Longrightarrow> Append (A # X) Y ((A # X) @ Y)"
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
