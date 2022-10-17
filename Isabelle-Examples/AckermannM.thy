(*  Title:      HOL/Examples/AckermannM.thy
    Author:     Larry Paulson
*)

section \<open>A Tail-Recursive, Stack-Based Ackermann's Function\<close>

text \<open>Unlike the other Ackermann example, this termination proof uses the argument from
Nachum Dershowitz and Zohar Manna. Proving termination with multiset orderings.
Communications of the ACM 22 (8) 1979, 465–476.\<close>

theory AckermannM imports "HOL-Library.Multiset_Order" "HOL-Library.Product_Lexorder"

begin

text\<open>This theory investigates a stack-based implementation of Ackermann's function.
Let's recall the traditional definition,
as modified by R{\'o}zsa P\'eter and Raphael Robinson.\<close>

fun ack :: "[nat,nat] \<Rightarrow> nat" where
  "ack 0 n             = Suc n"
| "ack (Suc m) 0       = ack m 1"
| "ack (Suc m) (Suc n) = ack m (ack (Suc m) n)"

text\<open>Setting up the termination proof for the stack-based version.\<close>

fun ack_mset :: "nat list \<Rightarrow> (nat\<times>nat) multiset" where
  "ack_mset [] = {#}"
| "ack_mset [x] = {#}"
| "ack_mset (z#y#l) =  mset ((y,z) # map (\<lambda>x. (Suc x, 0)) l)"

lemma case1: "ack_mset (Suc n # l) < add_mset (0, n) {#(Suc x, 0). x \<in># mset l#}"
proof (cases l)
  case (Cons m list)
  have "{#(m, Suc n)#} < {#(Suc m, 0)#}"
    by auto
  also have "\<dots> \<le> {#(Suc m, 0), (0,n)#}"
    by auto
  finally show ?thesis
    by (simp add: Cons)
qed auto

text\<open>Here is the stack-based version, which uses lists.\<close>

function ackloop :: "nat list \<Rightarrow> nat" where
  "ackloop (n # 0 # l)         = ackloop (Suc n # l)"
| "ackloop (0 # Suc m # l)     = ackloop (1 # m # l)"
| "ackloop (Suc n # Suc m # l) = ackloop (n # Suc m # m # l)"
| "ackloop [m] = m"
| "ackloop [] =  0"
  by pat_completeness auto

termination
  by (relation "inv_image {(x,y). x<y} ack_mset") (auto simp: wf case1)

text \<open>Unlike the other Ackermann theory, no extra function is needed to prove equivalence\<close>
lemma ackloop_ack: "ackloop (n # m # l) = ackloop (ack m n # l)"
  by (induction m n arbitrary: l rule: ack.induct) auto

theorem ack: "ack m n = ackloop [n,m]"
  by (simp add: ackloop_ack)

end
