section\<open>Evaluate procedure\<close>
theory Evaluate
imports ROBDD.BDT Data
begin
text \<open> Stream-like evaluation of Adiar's BDD representation \<close>

fun bdd_eval_node :: \<open>'l node list \<Rightarrow> 'l assignment \<Rightarrow> 'l uid \<Rightarrow> bool\<close> where
  \<open>bdd_eval_node []     _ _ = undefined\<close>
| \<open>bdd_eval_node (n#ns) a t = (if uid n = t
                              then let child = (if a (label t) then high n else low n)
                                   in (case child of Leaf b \<Rightarrow> b
                                                   | Node t' \<Rightarrow> bdd_eval_node ns a t' )
                              else bdd_eval_node ns a t)\<close>

fun bdd_eval :: \<open>'l bdd \<Rightarrow> 'l assignment \<Rightarrow> bool\<close> where
  \<open>bdd_eval (Constant b)        _ = b\<close>
| \<open>bdd_eval (Nodes (root#ns))   a = bdd_eval_node (root#ns) a (uid root)\<close>
| \<open>bdd_eval (Nodes [])          _ = undefined\<close>

text \<open> Linking to Binary Decision Tree \<close>

abbreviation Ifleaf_of_leaf :: \<open>bool \<Rightarrow> 'l ifex\<close> where
  \<open>Ifleaf_of_leaf b \<equiv> (if b then Trueif else Falseif)\<close>

fun bdt_of_bdd_node :: \<open>'l node list \<Rightarrow> 'l uid \<Rightarrow> 'l ifex\<close> where
  \<open>bdt_of_bdd_node []     _ = undefined\<close>
| \<open>bdt_of_bdd_node (n#ns) t = (if uid n = t
                               then let high_subtree = (case high n of Leaf b \<Rightarrow> Ifleaf_of_leaf b
                                                                    | Node t' \<Rightarrow> bdt_of_bdd_node ns t')
                                      ; low_subtree = (case low n of Leaf b \<Rightarrow> Ifleaf_of_leaf b
                                                                  | Node t' \<Rightarrow> bdt_of_bdd_node ns t')
                                     in IF (label t) high_subtree low_subtree
                               else bdt_of_bdd_node ns t)\<close>

fun bdt_of_bdd :: \<open>'l bdd \<Rightarrow> 'l ifex\<close> where
  \<open>bdt_of_bdd (Constant b) = Ifleaf_of_leaf b\<close>
| \<open>bdt_of_bdd (Nodes (root#ns)) = bdt_of_bdd_node (root#ns) (uid root)\<close>
| \<open>bdt_of_bdd (Nodes []) = undefined\<close>


lemma bdd_eval_node_iff_val_ifex_aux:
  assumes \<open>well_formed_nl ns\<close> \<open>t \<in> uid ` set ns\<close>
  shows \<open>bdd_eval_node ns a t \<longleftrightarrow> val_ifex (bdt_of_bdd_node ns t) a\<close>
  using assms
proof (induction ns arbitrary: t rule: nl_induct)
  case (Cons i t e ns)
  then show ?case
    by (cases \<open>ns = []\<close>; auto split:ptr.splits)
qed simp

theorem bdd_eval_iff_val_ifex:
  assumes \<open>well_formed bdd\<close>
  shows \<open>bdd_eval bdd a \<longleftrightarrow> val_ifex (bdt_of_bdd bdd) a\<close>
proof (cases bdd rule: bdd_cases)
  case (Nodes i t e ns)
  with assms show ?thesis
    by (auto split:ptr.splits
             dest:imageI[where f = uid] bdd_eval_node_iff_val_ifex_aux[where a = a])
qed (use assms in auto)

text \<open>Evaluation of pointers, this comes in handy later.\<close>
fun bdd_eval_ptr :: \<open>'l node list \<Rightarrow> 'l assignment \<Rightarrow> 'l ptr \<Rightarrow> bool\<close> where
  \<open>bdd_eval_ptr ns a (Leaf b) = b\<close>
| \<open>bdd_eval_ptr ns a (Node t) = bdd_eval_node ns a t\<close>

lemma bdd_eval_node_Cons_alt:
  \<open>bdd_eval_node (n#ns) a t = (if uid n = t
                              then let child = (if a (label t) then high n else low n)
                                   in bdd_eval_ptr ns a child
                              else bdd_eval_node ns a t)\<close>
  unfolding bdd_eval_node.simps by (simp split: ptr.splits)

end