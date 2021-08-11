---
layout: post
title:  "test post II"
date:   2021-08-10 12:04:21 +0100
usemathjax: true 
categories: general
---

Test blogpost II

$$E=mc^2$$

$$\alpha\longrightarrow (\beta, \gamma)^n \label{DD}$$ 

you can refer to it as \ref{DD}.
 
But you can use inline equations too, with one dollar sign, like this: $ J(x) = \int{L(t, x, \dot{x}) dt} \$. 

[prev post]({% post_url 2021-08-09-welcome %})

```{.isabelle}
lemma disj_wf: "disj_wf r ⟷ (∃T. ∃n::nat. (∀i<n. wf(T i)) ∧ r ⊆ (⋃i<n. T i))"
proof -
  have *: "⋀T n. ⟦∀i<n. wf (T i); r ⊆ ⋃ (T ` {..<n})⟧
           ⟹ (∀i<n. wf (T i ∩ r)) ∧ r = (⋃i<n. T i ∩ r)"
    by (force simp add: wf_Int1)
  show ?thesis
    unfolding disj_wf_def by auto (metis "*")
qed
```

{% highlight isabelle %}
theorem trans_disj_wf_implies_wf:
  assumes "trans r"
    and "disj_wf r"
  shows "wf r"
proof (simp only: wf_iff_no_infinite_down_chain, rule notI)
  assume "\<exists>s. \<forall>i. (s (Suc i), s i) \<in> r"
  then obtain s where sSuc: "\<forall>i. (s (Suc i), s i) \<in> r" ..
  from \<open>disj_wf r\<close> obtain T and n :: nat where wfT: "\<forall>k<n. wf(T k)" and r: "r = (\<Union>k<n. T k)"
    by (auto simp add: disj_wf_def)
  have s_in_T: "\<exists>k. (s j, s i) \<in> T k \<and> k<n" if "i < j" for i j
  proof -
    from \<open>i < j\<close> have "(s j, s i) \<in> r"
    proof (induct rule: less_Suc_induct)
      case 1
      then show ?case by (simp add: sSuc)
    next
      case 2
      with \<open>trans r\<close> show ?case
        unfolding trans_def by blast
    qed
    then show ?thesis by (auto simp add: r)
  qed
  have "i < j \<Longrightarrow> transition_idx s T {i, j} < n" for i j
    using s_in_T transition_idx_less by blast
  then have trless: "i \<noteq> j \<Longrightarrow> transition_idx s T {i, j} < n" for i j
    by (metis doubleton_eq_iff less_linear)
  have "\<exists>K k. K \<subseteq> UNIV \<and> infinite K \<and> k < n \<and>
      (\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> transition_idx s T {i, j} = k)"
    by (rule Ramsey2) (auto intro: trless infinite_UNIV_nat)
  then obtain K and k where infK: "infinite K" and "k < n"
    and allk: "\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> transition_idx s T {i, j} = k"
    by auto
  have "(s (enumerate K (Suc m)), s (enumerate K m)) \<in> T k" for m :: nat
  proof -
    let ?j = "enumerate K (Suc m)"
    let ?i = "enumerate K m"
    have ij: "?i < ?j" by (simp add: enumerate_step infK)
    have "?j \<in> K" "?i \<in> K" by (simp_all add: enumerate_in_set infK)
    with ij have k: "k = transition_idx s T {?i, ?j}" by (simp add: allk)
    from s_in_T [OF ij] obtain k' where "(s ?j, s ?i) \<in> T k'" "k'<n" by blast
    then show "(s ?j, s ?i) \<in> T k" by (simp add: k transition_idx_in ij)
  qed
  then have "\<not> wf (T k)"
    unfolding wf_iff_no_infinite_down_chain by iprover
  with wfT \<open>k < n\<close> show False by blast
qed
{% endhighlight %}
