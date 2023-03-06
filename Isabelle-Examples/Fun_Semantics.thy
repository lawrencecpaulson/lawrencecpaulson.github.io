theory Fun_Semantics
imports Main
begin

datatype exp = T | F | Zero | Succ exp | IF exp exp exp | EQ exp exp

inductive Eval :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Rrightarrow>" 50) where
    IF_T:    "IF T x y \<Rrightarrow> x"
  | IF_F:    "IF F x y \<Rrightarrow> y"
  | IF_Eval: "p \<Rrightarrow> q \<Longrightarrow> IF p x y \<Rrightarrow> IF q x y"
  | Succ_Eval: "x \<Rrightarrow> y \<Longrightarrow> Succ x \<Rrightarrow> Succ y"
  | EQ_same: "EQ x x \<Rrightarrow> T"
  | EQ_S0:   "EQ (Succ x) Zero \<Rrightarrow> F"
  | EQ_0S:   "EQ Zero (Succ y) \<Rrightarrow> F"
  | EQ_SS:   "EQ (Succ x) (Succ y) \<Rrightarrow> EQ x y"
  | EQ_Eval1: "x \<Rrightarrow> z \<Longrightarrow> EQ x y \<Rrightarrow> EQ z y"
  | EQ_Eval2: "y \<Rrightarrow> z \<Longrightarrow> EQ x y \<Rrightarrow> EQ x z"

inductive_simps T_simp [simp]: "T \<Rrightarrow> z"
inductive_simps F_simp [simp]: "F \<Rrightarrow> z"
inductive_simps Zero_simp [simp]: "Zero \<Rrightarrow> z"
inductive_simps Succ_simp [simp]: "Succ x \<Rrightarrow> z"
inductive_simps IF_simp [simp]: "IF p x y \<Rrightarrow>  z"
inductive_simps EQ_simp [simp]: "EQ x y \<Rrightarrow> z"

datatype tp = bool | num

inductive TP :: "exp \<Rightarrow> tp \<Rightarrow> bool" where
  T:    "TP T bool"
| F:    "TP F bool"
| Zero: "TP Zero num"
| IF:   "\<lbrakk>TP p bool; TP x t; TP y t\<rbrakk> \<Longrightarrow> TP (IF p x y) t"
| Succ: "TP x num \<Longrightarrow> TP (Succ x) num"
| EQ:   "\<lbrakk>TP x t; TP y t\<rbrakk> \<Longrightarrow> TP (EQ x y) bool"

inductive_simps TP_IF [simp]: "TP (IF p x y) t"
inductive_simps TP_Succ [simp]: "TP (Succ x) t"
inductive_simps TP_EQ [simp]: "TP (EQ x y) t"

proposition type_preservation:
  assumes "x \<Rrightarrow> y" "TP x t" shows "TP y t"
  using assms
  by (induction x y arbitrary: t rule: Eval.induct) (auto simp: TP.intros)

fun evl :: "exp \<Rightarrow> nat"
  where
    "evl T = 1"
  | "evl F = 0"
  | "evl Zero = 0"
  | "evl (Succ x) = evl x + 1"
  | "evl (IF x y z) = (if evl x = 1 then evl y else evl z)"
  | "evl (EQ x y) = (if evl x = evl y then 1 else 0)"

lemma
  assumes "TP x t" "t = bool" shows "evl x < 2"
  using assms by (induction x t; force)

proposition value_preservation:
  assumes "x \<Rrightarrow> y" shows "evl x = evl y"
  using assms by (induction x y; force)


text \<open>This doesn't hold\<close>
lemma
  assumes "x \<Rrightarrow> y" "x \<Rrightarrow> z" shows "\<exists>u. y \<Rrightarrow> u \<and> z \<Rrightarrow> u"
  nitpick
  oops

inductive EvalStar :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Rrightarrow>*" 50) where
    Id: "x \<Rrightarrow>* x"
  | Step: "x \<Rrightarrow> y \<Longrightarrow> y \<Rrightarrow>* z \<Longrightarrow> x \<Rrightarrow>* z"

proposition type_preservation_Star:
  assumes "x \<Rrightarrow>* y" "TP x t" shows "TP y t"
  using assms by (induction x y) (auto simp: type_preservation)

lemma Succ_EvalStar:
  assumes "x \<Rrightarrow>* y" shows "Succ x \<Rrightarrow>* Succ y"
  using assms by induction (auto intro: Succ_Eval EvalStar.intros)

lemma IF_EvalStar:
  assumes "p \<Rrightarrow>* q" shows "IF p x y \<Rrightarrow>* IF q x y"
  using assms by induction (auto intro: IF_Eval EvalStar.intros)

lemma EQ_EvalStar1:
  assumes "x \<Rrightarrow>* z" shows "EQ x y \<Rrightarrow>* EQ z y"
  using assms by induction (auto intro: EQ_Eval1 EvalStar.intros)

lemma EQ_EvalStar2:
  assumes "y \<Rrightarrow>* z" shows "EQ x y \<Rrightarrow>* EQ x z "
  using assms by induction (auto intro: EQ_Eval2 EvalStar.intros)

proposition diamond:
  assumes "x \<Rrightarrow> y" "x \<Rrightarrow> z" shows "\<exists>u. y \<Rrightarrow>* u \<and> z \<Rrightarrow>* u"
  using assms
proof (induction x y arbitrary: z)
  case (IF_Eval p q x y)
  then show ?case
    by (simp; meson F_simp IF_EvalStar T_simp)
next
  case (EQ_SS x y)
  then show ?case
    by (simp; meson Eval.intros EvalStar.intros)
next
  case (EQ_Eval1 x u y)
  then show ?case
    by (auto; meson EQ_EvalStar1 Eval.intros EvalStar.intros)+
next
    case (EQ_Eval2 y u x)
    then show ?case
    by (auto; meson EQ_EvalStar2 Eval.intros EvalStar.intros)+
qed (force intro: Succ_EvalStar Eval.intros EvalStar.intros)+

end
