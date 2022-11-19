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

schematic_goal "\<Prod>z:?A . N + ?B(z) type"
  apply (rule form_rls)
   apply (rule form_rls)
  apply (rule form_rls)
   apply (rule form_rls)
  apply (rule form_rls)
  done

schematic_goal "<0, succ(0)> : ?A"
  apply intr done

schematic_goal "\<Prod>w:N . Eq(?A,w,w) type"
  apply typechk done

schematic_goal "\<Prod>x:N . \<Prod>y:N . Eq(?A,x,y) type"
  apply typechk done

text "typechecking an application of fst"
schematic_goal "(\<^bold>\<lambda>u. split(u, \<lambda>v w. v)) ` <0, succ(0)> : ?A"
  apply typechk done

text "typechecking the predecessor function"
schematic_goal "\<^bold>\<lambda>n. rec(n, 0, \<lambda>x y. x) : ?A"
  apply typechk done

text "typechecking the addition function"
schematic_goal "\<^bold>\<lambda>n. \<^bold>\<lambda>m. rec(n, m, \<lambda>x y. succ(y)) : ?A"
  apply typechk done

text \<open>Proofs involving arbitrary types.
  For concreteness, every type variable left over is forced to be @{term N}\<close>
method_setup N =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (TRYALL (resolve_tac ctxt @{thms NF})))\<close>

schematic_goal "\<^bold>\<lambda>w. <w,w> : ?A"
  apply typechk
  apply N
  done

schematic_goal "\<^bold>\<lambda>x. \<^bold>\<lambda>y. x : ?A"
  apply typechk
   apply N
  done

text "typechecking fst (as a function object)"
schematic_goal "\<^bold>\<lambda>i. split(i, \<lambda>j k. j) : ?A"
  apply typechk 
   apply N
  done


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
