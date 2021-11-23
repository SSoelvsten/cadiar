section \<open>Negation procedure\<close>
theory Negation
imports Data Evaluate
begin

text \<open>To compute the negation of a function f one merely needs to flip the values in the leaves.
      Hence, one should be able to merely lazily remap the original BDD nodes into the same with
      leaves negated.\<close>

fun negate :: \<open>'l node \<Rightarrow> 'l node\<close> where
  \<open>negate (N u l h) = (let l' = (case l of Leaf b \<Rightarrow> Leaf (\<not>b) | _ \<Rightarrow> l)
                         ; h' = (case h of Leaf b \<Rightarrow> Leaf (\<not>b) | _ \<Rightarrow> h)
                        in N u l' h')\<close>

fun bdd_not :: \<open>'l bdd \<Rightarrow> 'l bdd\<close> where
  \<open>bdd_not (Constant b) = (Constant (\<not>b))\<close>
| \<open>bdd_not (Nodes ns)   = (Nodes (map negate ns))\<close>

lemma bdd_not_correct_aux:
  assumes \<open>closed ns\<close> \<open>tgt \<in> uid ` set ns\<close>
  shows \<open>\<not>bdd_eval_node ns a tgt \<longleftrightarrow> bdd_eval_node (map negate ns) a tgt\<close>
  using assms by (induction ns arbitrary: tgt rule: nl_induct) (auto split: ptr.splits)

theorem bdd_not_correct:
  assumes \<open>well_formed bdd\<close>
  shows \<open>\<not>bdd_eval bdd a \<longleftrightarrow> bdd_eval (bdd_not bdd) a\<close>
  using assms bdd_not_correct_aux
  by (cases bdd rule: bdd_cases; force split:ptr.splits dest!: closed_if_well_formed_nl)

end