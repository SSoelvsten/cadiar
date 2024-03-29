section\<open>Evaluate procedure\<close>
theory Evaluate
imports ROBDD.BDT Data
begin

text \<open>To evaluate a BDD for a function \<open>f\<close> given as assignment a, i.e. to compute \<open>f(a)\<close>, one should
      start at the root and then follow pointers until one reaches a leaf.\<close>

fun bdd_eval_node :: \<open>'l node list \<Rightarrow> 'l assignment \<Rightarrow> 'l uid \<Rightarrow> bool\<close>
and bdd_eval_ptr :: \<open>'l node list \<Rightarrow> 'l assignment \<Rightarrow> 'l ptr \<Rightarrow> bool\<close>
  where
  \<open>bdd_eval_node []     _ _ = undefined\<close>
| \<open>bdd_eval_node (N i t e # ns) a tgt = (if i = tgt
                                         then bdd_eval_ptr ns a (if a (label i) then t else e)
                                         else bdd_eval_node ns a tgt)\<close>
| \<open>bdd_eval_ptr ns a (Leaf b) = b\<close>
| \<open>bdd_eval_ptr ns a (Node u) = bdd_eval_node ns a u\<close>

fun bdd_eval :: \<open>'l bdd \<Rightarrow> 'l assignment \<Rightarrow> bool\<close> where
  \<open>bdd_eval (Constant b)          _ = b\<close>
| \<open>bdd_eval (Nodes (root # ns))   a = bdd_eval_node (root#ns) a (uid root)\<close>
| \<open>bdd_eval (Nodes [])            _ = undefined\<close>

subsection \<open>Linking to Binary Decision Tree\<close>

text \<open>To prove that @{term bdd_eval} above establishes a semantics for our BDD data structure,
      we will map our BDDs to the Binary Decision Trees in @{cite Michaelis2016}
      and prove that @{term bdd_eval} is equivalent to the recursive semantics on the tree.\<close>

abbreviation Ifleaf_of_leaf :: \<open>bool \<Rightarrow> 'l ifex\<close> where
  \<open>Ifleaf_of_leaf b \<equiv> (if b then Trueif else Falseif)\<close>

fun bdt_of_node :: \<open>'l node list \<Rightarrow> 'l uid \<Rightarrow> 'l ifex\<close>
and bdt_of_ptr :: \<open>'l node list \<Rightarrow> 'l ptr \<Rightarrow> 'l ifex\<close>
where
  \<open>bdt_of_node []     _ = undefined\<close>
| \<open>bdt_of_node (N i t e # ns) tgt = (if i = tgt
                                     then IF (label tgt) (bdt_of_ptr ns t) (bdt_of_ptr ns e)
                               else bdt_of_node ns tgt)\<close>
| \<open>bdt_of_ptr ns (Leaf b) = Ifleaf_of_leaf b\<close>
| \<open>bdt_of_ptr ns (Node u) = bdt_of_node ns u\<close>

fun bdt_of_bdd :: \<open>'l bdd \<Rightarrow> 'l ifex\<close> where
  \<open>bdt_of_bdd (Constant b)        = Ifleaf_of_leaf b\<close>
| \<open>bdt_of_bdd (Nodes (root # ns)) = bdt_of_node (root # ns) (uid root)\<close>
| \<open>bdt_of_bdd (Nodes [])          = undefined\<close>

lemma bdd_eval_node_iff_val_ifex_aux:
  assumes \<open>closed ns\<close> \<open>tgt \<in> uid ` set ns\<close>
  shows \<open>bdd_eval_node ns a tgt \<longleftrightarrow> val_ifex (bdt_of_node ns tgt) a\<close>
  using assms
proof (induction ns arbitrary: tgt rule: nl_induct)
  case (Cons i t e ns)
  then show ?case
    by (cases \<open>ns = []\<close>; auto split: ptr.splits)
qed simp

theorem bdd_eval_iff_val_ifex:
  assumes \<open>well_formed bdd\<close>
  shows \<open>bdd_eval bdd a \<longleftrightarrow> val_ifex (bdt_of_bdd bdd) a\<close>
proof (cases bdd rule: bdd_cases)
  case (Nodes i t e ns)
  with assms show ?thesis
    by (auto split: ptr.splits
             dest:  imageI[where f = uid] bdd_eval_node_iff_val_ifex_aux[where a = a]
             dest!: closed_if_well_formed_nl)
qed (use assms in auto)

subsubsection \<open>Variable domain of Binary Decision Diagrams and Trees\<close>

fun vars_of_bdt where
  "vars_of_bdt (IF i t e) = insert i (vars_of_bdt t \<union> vars_of_bdt e)"
| "vars_of_bdt _ = {}"


definition dom_bounded_vars where
  "dom_bounded_vars S a \<equiv> \<forall>x. x \<notin> S \<longrightarrow> a x = False"

definition
  "vars_of_bdd bdd = vars_of_bdt (bdt_of_bdd bdd)"

definition
  "vars_of_node ns node = vars_of_bdt (bdt_of_node ns node)"

definition
  "vars_of_ptr ns ptr = vars_of_bdt (bdt_of_ptr ns ptr)"

definition
  "num_assignments_vars bdd = card {a. bdd_eval bdd a \<and> dom_bounded_vars (vars_of_bdd bdd) a}"

definition
  "num_assignments_vars_ptr ns ptr =
    card {a. bdd_eval_ptr ns a ptr \<and> dom_bounded_vars (vars_of_ptr ns ptr) a}"

definition
  "num_assignments_vars_node ns node =
    card {a. bdd_eval_node ns a node \<and> dom_bounded_vars (vars_of_node ns node) a}"

lemma vars_of_bdd_to_node[simp]:
  "vars_of_bdd (Nodes (N i t e # ns)) = vars_of_node (N i t e # ns) i"
  unfolding vars_of_bdd_def vars_of_node_def by simp

lemma num_assignments_vars_to_node[simp]:
  "num_assignments_vars (Nodes (N i t e # ns)) = num_assignments_vars_node (N i t e # ns) i"
  unfolding num_assignments_vars_def num_assignments_vars_node_def by simp

end