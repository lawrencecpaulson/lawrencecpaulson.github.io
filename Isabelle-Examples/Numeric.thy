section \<open>Numerical experiments\<close>

theory Numeric imports
  "HOL-Decision_Procs.Approximation" "HOL-Computational_Algebra.Primes"
   
begin

text \<open>Addition of polymorphic numerals actually works, 
though nobody should rely on this\<close>
lemma "2+2=4"
  by auto

text \<open>Multiplication of polymorphic numerals does not work\<close>
lemma "2*3=6"
  oops

text \<open>These do not work because the group identity law is not available.\<close>
lemma "0+2=2" "1*3=3"
  oops

text \<open>Works because of the type constraint. And multiplcation is fast!\<close>
lemma "123456789 * (987654321::int) = 121932631112635269"
  by simp

text \<open>The function @{term Suc} implies type @{typ nat}\<close>
lemma "Suc (Suc 0) * n = n*2"
  by simp

text \<open>We have to expand 5 into Suc-notation.\<close>
lemma "x^5 = x*x*x*x*(x::real)"
  by (simp add: eval_nat_numeral)

text \<open>Decimal notation and arithmetic on complex numbers\<close>
lemma "(1 - 0.3*\<i>) * (2.7 + 5*\<i>) = 4.2 + 4.19*\<i>"
  by (simp add: algebra_simps)

text \<open>Applying a function to a numeral argument via eval. 
      But only if this has been set up.\<close>
lemma "fact 20 < (2432902008176640001::nat)"
  by eval

text \<open>Testing primality via eval, takes a couple of seconds. 
      The type constraint is necessary!\<close>
lemma "prime (179424673::nat)"
  by eval

text \<open>A simple demonstration of the approximation method\<close>
lemma "\<bar>pi - 355/113\<bar> < 1/10^6"
  by (approximation 25)

text \<open>Ditto, the approximation method\<close>
lemma "\<bar>sqrt 2 - 1.4142135624\<bar> < 1/10^10"
  by (approximation 35)

text \<open>The approximation method on a *closed* interval (SLOW). Must avoid zero!\<close>
lemma
  fixes x::real
  assumes "x \<in> {0.1 .. 1}"
  shows "x * ln(x) \<ge> -0.368"
  using assms by (approximation 17 splitting: x=13) 

text \<open>A little more accuracy makes it MUCH slower 
  (the exact answer is -1/e = 0.36787944117144233)\<close>
lemma
  fixes x::real
  assumes "x \<in> {0.1 .. 1}"
  shows "x * ln(x) \<ge> -0.3679"
using assms
  by (approximation 18 splitting: x=16) 

end
