section \<open>Tim Gowers' Example: A Characterisation of Bijections\<close>

theory Gowers_Bijection imports Main
   
begin

text \<open>Isabelle's default syntax for set difference is nonstandard.\<close>
abbreviation set_difference :: "['a set,'a set] \<Rightarrow> 'a set" (infixl "\<setminus>" 65)
  where "A \<setminus> B \<equiv> A-B"

text \<open>The one-line proof found by sledgehammer\<close>
lemma "bij_betw f X Y \<longleftrightarrow> (\<forall>A. A\<subseteq>X \<longrightarrow> f ` (X\<setminus>A) = Y \<setminus> f`A)"
  by (metis Diff_empty Diff_eq_empty_iff Diff_subset bij_betw_def image_is_empty 
            inj_on_image_set_diff subset_antisym subset_image_inj)

text \<open>A more detailed proof. Note use of variables for the left and right sides\<close>
lemma "bij_betw f X Y \<longleftrightarrow> (\<forall>A. A\<subseteq>X \<longrightarrow> f ` (X\<setminus>A) = Y \<setminus> f`A)"  (is "?L=?R")
proof
  show "?L \<Longrightarrow> ?R"
    by (metis Diff_subset bij_betw_def inj_on_image_set_diff)
  assume ?R
  then have "inj_on f X" "f ` X = Y"
    by (auto simp: inj_on_def)
  then show ?L
    by (simp add: bij_betw_def)
qed

end
