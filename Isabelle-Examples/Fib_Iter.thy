section \<open>Iterative Fibonacci and Code Generation \<close>

theory Fib_Iter
  imports Complex_Main  \<comment> \<open>allows implicit coercions\<close>
begin

text \<open>The type of integers banishes the successor function\<close>
fun itfib :: "[int,int,int] \<Rightarrow> int" where
  "itfib n j k = (if n\<le>1 then k else itfib (n-1) k (j+k))"

text \<open>Simplification alone can compute this colossal number
   in a fraction of a second\<close>
lemma "itfib 200 0 1 = 280571172992510140037611932413038677189525"
  by simp

fun fib :: "nat \<Rightarrow> int" where
    "fib 0 = 0"
  | "fib (Suc 0) = 1"
  | "fib (Suc (Suc n)) = fib n + fib (Suc n)"

text \<open>The two functions are closely related\<close>
lemma itfib_fib: "n > 0 \<Longrightarrow> itfib n (fib k) (fib(k+1)) = fib (k+n)"
proof (induction n arbitrary: k)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  have "n > 0 \<Longrightarrow> itfib n (fib (k+1)) (fib k + fib (k+1)) = fib (k+n+1)"
    by (metis Suc.IH Suc_eq_plus1 add.commute add_Suc_right fib.simps(3))
  with Suc show ?case
    by simp
qed

text \<open>Direct recursive evaluation is exponential and slow\<close>
value "fib 44"

declare fib.simps [code del]

text \<open>New code equation for @{term fib}\<close>
lemma fib_eq_itfib[code]: "fib n = (if n=0 then 0 else itfib (int n) 0 1)"
  using itfib_fib [of n 0] by simp

text \<open>FAST\<close>
value "fib 200"

end
