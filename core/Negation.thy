section\<open>Core data structures\<close>
theory Negation
imports Data Evaluate
begin
  
fun negate :: \<open>'l node \<Rightarrow> 'l node\<close> where
  \<open>negate (N u l h) = (let l' = (case l of Leaf b \<Rightarrow> Leaf (\<not>b) | _ \<Rightarrow> l)
                         ; h' = (case h of Leaf b \<Rightarrow> Leaf (\<not>b) | _ \<Rightarrow> h)
                        in N u l' h')\<close>

fun bdd_not :: \<open>'l bdd \<Rightarrow> 'l bdd\<close> where
  \<open>bdd_not (Constant b) = (Constant (\<not>b))\<close>
| \<open>bdd_not (Nodes ns)   = (Nodes (map negate ns))\<close>

lemma bdd_not_correct_aux:
  assumes \<open>well_formed_nl ns\<close> \<open>t \<in> uid ` set ns\<close>
  shows \<open>\<not>bdd_eval_aux ns a t \<longleftrightarrow> bdd_eval_aux (map negate ns) a t\<close>
  using assms by (induction ns arbitrary: t rule: nl_induct) (auto split: ptr.splits)

theorem bdd_not_correct:
  assumes \<open>well_formed bdd\<close>
  shows \<open>\<not>bdd_eval bdd a \<longleftrightarrow> bdd_eval (bdd_not bdd) a\<close>
  using assms bdd_not_correct_aux by (cases bdd rule: bdd_cases) (auto split:ptr.splits)

end