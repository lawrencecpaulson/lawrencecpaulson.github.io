section \<open>Tim Gowers' Example: A Characterisation of Bijections\<close>

theory Gowers_Bijection imports Complex_Main
   
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

text \<open>Bonus: an example due to Terrence Tao\<close>

lemma
  fixes a :: "nat \<Rightarrow> real"
  assumes a: "decseq a" and D: "\<And>k. D k \<ge> 0" and aD: "\<And>k. a k \<le> D k - D(Suc k)"
  shows "a k \<le> D 0 / (Suc k)"
proof -
  have "a k = (\<Sum>i\<le>k. a k) / (Suc k)"
    by simp
  also have "\<dots> \<le> (\<Sum>i\<le>k. a i) / (Suc k)"
    using a sum_mono[of "{..k}" "\<lambda>i. a k" a] 
    by (simp add: monotone_def divide_simps mult.commute)
  also have "\<dots> \<le> (\<Sum>i\<le>k. D i - D(Suc i)) / (Suc k)"
    by (simp add: aD divide_right_mono sum_mono)
  also have "\<dots> \<le> D 0 / (Suc k)"
    by (simp add: sum_telescope D divide_right_mono)
  finally show ?thesis .
qed

end
