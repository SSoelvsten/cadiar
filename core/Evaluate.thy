section\<open>Evaluate procedure\<close>
theory Evaluate
imports "../afp-robdd/BDT" Data
begin
text \<open> Stream-like evaluation of Adiar's BDD representation \<close>

fun bdd_eval_aux :: \<open>'l node list \<Rightarrow> 'l assignment \<Rightarrow> 'l uid \<Rightarrow> bool\<close> where
  \<open>bdd_eval_aux []     _ _ = undefined\<close>
| \<open>bdd_eval_aux (n#ns) a t = (if uid n = t
                              then let child = (if a (label t) then high n else low n)
                                   in (case child of Leaf b \<Rightarrow> b
                                                   | Node t' \<Rightarrow> bdd_eval_aux ns a t' )
                              else bdd_eval_aux ns a t)\<close>

fun bdd_eval :: \<open>'l bdd \<Rightarrow> 'l assignment \<Rightarrow> bool\<close> where
  \<open>bdd_eval (Constant b)        _ = b\<close>
| \<open>bdd_eval (Nodes (root#ns))   a = bdd_eval_aux (root#ns) a (uid root)\<close>
| \<open>bdd_eval (Nodes [])          _ = undefined\<close>

text \<open> Linking to Binary Decision Tree \<close>

abbreviation Ifleaf_of_leaf :: \<open>bool \<Rightarrow> 'l ifex\<close> where
  \<open>Ifleaf_of_leaf b \<equiv> (if b then Trueif else Falseif)\<close>

fun bdt_of_bdd_aux :: \<open>'l node list \<Rightarrow> 'l uid \<Rightarrow> 'l ifex\<close> where
  \<open>bdt_of_bdd_aux []     _ = undefined\<close>
| \<open>bdt_of_bdd_aux (n#ns) t = (if uid n = t
                              then let high_subtree = (case high n of Leaf b \<Rightarrow> Ifleaf_of_leaf b
                                                                    | Node t' \<Rightarrow> bdt_of_bdd_aux ns t')
                                     ; low_subtree = (case low n of Leaf b \<Rightarrow> Ifleaf_of_leaf b
                                                                  | Node t' \<Rightarrow> bdt_of_bdd_aux ns t')
                                    in IF (label t) high_subtree low_subtree
                              else bdt_of_bdd_aux ns t)\<close>

fun bdt_of_bdd :: \<open>'l bdd \<Rightarrow> 'l ifex\<close> where
  \<open>bdt_of_bdd (Constant b) = Ifleaf_of_leaf b\<close>
| \<open>bdt_of_bdd (Nodes (root#ns)) = bdt_of_bdd_aux (root#ns) (uid root)\<close>
| \<open>bdt_of_bdd (Nodes []) = undefined\<close>

lemma bdd_eval_aux_iff_val_ifex_aux:
  assumes \<open>well_formed_nl ns\<close> \<open>t \<in> uid ` set ns\<close>
  shows \<open>bdd_eval_aux ns a t \<longleftrightarrow> val_ifex (bdt_of_bdd_aux ns t) a\<close>
  using assms
proof (induction ns arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  then show ?case
    by (cases \<open>ns = []\<close>; cases n; auto split:ptr.splits)
qed

theorem bdd_eval_iff_val_ifex:
  assumes \<open>well_formed bdd\<close>
  shows \<open>bdd_eval bdd a \<longleftrightarrow> val_ifex (bdt_of_bdd bdd) a\<close>
proof (cases bdd rule: bdt_of_bdd.cases)
  case (1 b)
  then show ?thesis by auto
next
  case (2 root ns)
  with assms show ?thesis
    by (cases root)
       (auto split:ptr.splits
             dest:imageI[where f = uid] bdd_eval_aux_iff_val_ifex_aux[where a = a])
next
  case 3
  with assms show ?thesis by auto
qed

end