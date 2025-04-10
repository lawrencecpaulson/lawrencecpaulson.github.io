(*Run with 
  isabelle jedit -l CTT  CTT_Examples.thy
*)
theory CTT_Examples
imports "CTT.CTT"
begin

schematic_goal "?A type"
  apply (rule form_rls)
  back
   apply (rule form_rls)
  apply (rule form_rls)
  done

schematic_goal "<0, succ(0)> : ?A"
  apply (rule intr_rls)
   apply (rule intr_rls)
  apply (rule intr_rls)
  apply (rule intr_rls)
  done

lemma "<0, succ(0)> : N \<times> N"
  by (rule intr_rls)+

text "typechecking the addition function"

schematic_goal "\<^bold>\<lambda>n. \<^bold>\<lambda>m. rec(n, m, \<lambda>x y. succ(y)) : ?A"
  apply (rule intr_rls form_rls elim_rls | assumption)+
  done


text "This finds the functions fst and snd!"

schematic_goal "A type \<Longrightarrow> ?a : (A \<times> A) \<longrightarrow> A"
  apply (rule intr_rls form_rls | erule elim_rls | assumption)+
  back
  done

text "Double negation of the Excluded Middle"
schematic_goal "A type \<Longrightarrow> ?a : ((A + (A\<longrightarrow>F)) \<longrightarrow> F) \<longrightarrow> F"
  apply intr
  apply (rule ProdE)
   apply assumption
  apply pc
  done

(*Experiment: the proof above in Isar*)
lemma
  assumes "A type" shows "(\<^bold>\<lambda>f. f ` inr(\<^bold>\<lambda>y. f ` inl(y))) : ((A + (A\<longrightarrow>F)) \<longrightarrow> F) \<longrightarrow> F"
proof intr
  fix f
  assume f: "f : A + (A \<longrightarrow> F) \<longrightarrow> F" 
  with assms have "inr(\<^bold>\<lambda>y. f ` inl(y)) : A + (A \<longrightarrow> F)"
    by pc
  then show "f ` inr(\<^bold>\<lambda>y. f ` inl(y)) : F" 
    by (rule ProdE [OF f])
qed (rule assms)+

text "Binary sums and products"
schematic_goal "\<lbrakk>A type; B type; C type\<rbrakk> \<Longrightarrow> ?a : (A + B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C) \<times> (B \<longrightarrow> C)"
  apply pc
  done

(*A distributive law*)
schematic_goal
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x. x:A \<Longrightarrow> C(x) type"
  shows "?a : (\<Sum>x:A. B(x) + C(x)) \<longrightarrow> (\<Sum>x:A. B(x)) + (\<Sum>x:A. C(x))"
  apply (pc assms)
  done

text "Construction of the currying functional"
schematic_goal
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>z. z: (\<Sum>x:A. B(x)) \<Longrightarrow> C(z) type"
  shows "?a : \<Prod>f: (\<Prod>z : (\<Sum>x:A . B(x)) . C(z)).
                      (\<Prod>x:A . \<Prod>y:B(x) . C(<x,y>))"
  apply (pc assms)
  done

text "Martin-Löf (1984), page 48: axiom of sum-elimination (uncurry)"
schematic_goal
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>z. z: (\<Sum>x:A . B(x)) \<Longrightarrow> C(z) type"
  shows "?a : (\<Prod>x:A . \<Prod>y:B(x) . C(<x,y>))
        \<longrightarrow> (\<Prod>z : (\<Sum>x:A . B(x)) . C(z))"
  apply (pc assms)
  done

text "Basic test of quantifier reasoning"
schematic_goal
  assumes "A type"
    and "B type"
    and "\<And>x y. \<lbrakk>x:A; y:B\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows
    "?a :     (\<Sum>y:B . \<Prod>x:A . C(x,y))
          \<longrightarrow> (\<Prod>x:A . \<Sum>y:B . C(x,y))"
  apply (pc assms)
  done

text "Martin-Löf (1984) pages 36-7: the combinator S"
schematic_goal
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows "?a :    (\<Prod>x:A. \<Prod>y:B(x). C(x,y))
             \<longrightarrow> (\<Prod>f: (\<Prod>x:A. B(x)). \<Prod>x:A. C(x, f`x))"
  apply (pc assms)
  done

text "Martin-Löf (1984) page 58: the axiom of disjunction elimination"
schematic_goal
  assumes "A type"
    and "B type"
    and "\<And>z. z: A+B \<Longrightarrow> C(z) type"
  shows "?a : (\<Prod>x:A. C(inl(x))) \<longrightarrow> (\<Prod>y:B. C(inr(y)))
          \<longrightarrow> (\<Prod>z: A+B. C(z))"
  apply (pc assms)
  done


(*Martin-Löf (1984) page 50*)
text "AXIOM OF CHOICE!  Delicate use of elimination rules"
lemma Axiom_of_Choice:
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows "(\<^bold>\<lambda>f. <\<^bold>\<lambda>x. fst(f`x), \<^bold>\<lambda>x. snd(f`x)>) 
        : (\<Prod>x:A. \<Sum>y:B(x). C(x,y)) \<longrightarrow> (\<Sum>f: (\<Prod>x:A. B(x)). \<Prod>x:A. C(x, f`x))"
proof (intr assms)
  fix f a
  assume f: "f : \<Prod>x:A. Sum(B(x), C(x))" and "a : A" 
  then have fa: "f`a : Sum(B(a), C(a))"
    by (rule ProdE)
  then show "fst(f ` a) : B(a)" 
    by (rule SumE_fst)
  have "snd(f ` a) : C(a, fst(f ` a))"
    by (rule SumE_snd [OF fa]) (typechk SumE_fst assms \<open>a : A\<close>)
  moreover have "(\<^bold>\<lambda>x. fst(f ` x)) ` a = fst(f ` a) : B(a)"
    by (rule ProdC [OF \<open>a : A\<close>]) (typechk SumE_fst f)
  ultimately show "snd(f`a) : C(a, (\<^bold>\<lambda>x. fst(f ` x)) ` a)"
    by (intro replace_type [OF subst_eqtyparg]) (typechk SumE_fst assms \<open>a : A\<close>)
qed

end
