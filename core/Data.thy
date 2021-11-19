section\<open>Core data structures\<close>
theory Data
imports Main
begin

datatype 'l uid = U (label:\<open>'l\<close>) (id:\<open>nat\<close>)

instantiation uid :: (linorder) linorder
begin
definition less_uid where
   \<open>less_uid \<equiv> \<lambda>(U i1 id1) \<Rightarrow> \<lambda>(U i2 id2) \<Rightarrow> (i1 < i2 \<or> (i1 = i2 \<and> id1 < id2))\<close>

definition less_eq_uid where
   \<open>less_eq_uid \<equiv> \<lambda>(U i1 id1) \<Rightarrow> \<lambda>(U i2 id2) \<Rightarrow> (i1 < i2 \<or> (i1 = i2 \<and> id1 \<le> id2))\<close>

instance
  by standard (auto simp: less_uid_def less_eq_uid_def split: uid.splits)

end

lemma less_uid_simp[simp]:
  \<open>(U i1 id1) < (U i2 id2) = (i1 < i2 \<or> (i1 = i2 \<and> id1 < id2))\<close>
  unfolding less_uid_def by simp

lemma less_eq_uid_simp[simp]:
  \<open>(U i1 id1) \<le> (U i2 id2) = (i1 < i2 \<or> (i1 = i2 \<and> id1 \<le> id2))\<close>
  unfolding less_eq_uid_def by simp

datatype 'l ptr = Leaf \<open>bool\<close> | Node \<open>'l uid\<close>

instantiation ptr :: (linorder) linorder
begin
fun less_ptr where
  \<open>less_ptr (Node u1) (Node u2) \<longleftrightarrow> u1 < u2\<close>
| \<open>less_ptr (Node _) (Leaf _) \<longleftrightarrow> True\<close>
| \<open>less_ptr (Leaf _) (Node _) \<longleftrightarrow> False\<close>
| \<open>less_ptr (Leaf b1) (Leaf b2) \<longleftrightarrow> b1 < b2\<close>

lemma less_ptr_alt_def:
  "(ptr1 :: ('b :: linorder) ptr) < (ptr2 :: ('b :: linorder) ptr) = (case (ptr1, ptr2) of
    (Node u1, Node u2) \<Rightarrow> u1 < u2
  | (Node _, Leaf _) \<Rightarrow> True
  | (Leaf _, Node _) \<Rightarrow> False
  | (Leaf b1, Leaf b2) \<Rightarrow> b1 < b2
)"
  by (cases "(ptr1, ptr2)" rule: less_ptr.cases) auto

definition less_eq_ptr where
  "less_eq_ptr (ptr1 :: ('b :: linorder) ptr) (ptr2 :: ('b :: linorder) ptr) = (case (ptr1, ptr2) of
    (Node u1, Node u2) \<Rightarrow> u1 \<le> u2
  | (Node _, Leaf _) \<Rightarrow> True
  | (Leaf _, Node _) \<Rightarrow> False
  | (Leaf b1, Leaf b2) \<Rightarrow> b1 \<le> b2
)"

instance
  by standard
     (auto split: ptr.splits simp del: less_ptr.simps simp add: less_ptr_alt_def less_eq_ptr_def)
end

datatype 'l node = N (uid:\<open>'l uid\<close>) (low:\<open>'l ptr\<close>) (high:\<open>'l ptr\<close>)

instantiation node :: (linorder) linorder
begin
definition less_node where
  \<open>less_node \<equiv> \<lambda>(N i1 t1 e1) \<Rightarrow> \<lambda>(N i2 t2 e2) \<Rightarrow>
    (i1 < i2 \<or> i1 = i2 \<and> e1 < e2 \<or> i1 = i2 \<and> e1 = e2 \<and> t1 < t2)\<close>

definition less_eq_node where
  \<open>less_eq_node \<equiv> \<lambda>(N i1 t1 e1) \<Rightarrow> \<lambda>(N i2 t2 e2) \<Rightarrow>
    (i1 < i2 \<or> i1 = i2 \<and> e1 < e2 \<or> i1 = i2 \<and> e1 = e2 \<and> t1 \<le> t2)\<close>

instance
  by standard (auto simp: less_node_def less_eq_node_def split: node.splits)

end

lemma less_node_simp[simp]:
  \<open>(N i1 t1 e1) < (N i2 t2 e2) =
    (i1 < i2 \<or> i1 = i2 \<and> e1 < e2 \<or> i1 = i2 \<and> e1 = e2 \<and> t1 < t2)\<close>
  unfolding less_node_def by simp

lemma less_eq_node_simp[simp]:
  \<open>(N i1 t1 e1) \<le> (N i2 t2 e2) \<longleftrightarrow>
    (i1 < i2 \<or> i1 = i2 \<and> e1 < e2 \<or> i1 = i2 \<and> e1 = e2 \<and> t1 \<le> t2)\<close>
  unfolding less_eq_node_def by simp


datatype 'l bdd = Constant \<open>bool\<close> | Nodes \<open>'l node list\<close>

type_synonym 'l assignment = \<open>'l \<Rightarrow> bool\<close>

fun closed :: \<open>'l node list \<Rightarrow> bool\<close> where
  \<open>closed []             = True\<close>
| \<open>closed (N i t e # ns) = (closed ns
                          \<and> (case t of Leaf b \<Rightarrow> True | Node l_uid \<Rightarrow> \<exists>n \<in> set ns . uid n = l_uid)
                          \<and> (case e of Leaf b \<Rightarrow> True | Node h_uid \<Rightarrow> \<exists>n \<in> set ns . uid n = h_uid))\<close>

definition
  "ptr_lb i \<equiv> \<lambda>Node n \<Rightarrow> i < label n | _ \<Rightarrow> True"

fun inc_labels :: \<open>('l::linorder) node list \<Rightarrow> bool\<close> where
  \<open>inc_labels []             \<longleftrightarrow> True\<close>
| \<open>inc_labels (N i t e # ns) \<longleftrightarrow> inc_labels ns \<and> ptr_lb (label i) t \<and> ptr_lb (label i) e\<close>

definition
  "well_formed_nl ns \<equiv> closed ns \<and> inc_labels ns \<and> sorted ns"

lemma closed_if_well_formed_nl[intro,simp]:
  "closed ns" if "well_formed_nl ns"
  using that unfolding well_formed_nl_def ..

lemma inc_labels_if_well_formed_nl[intro,simp]:
  "inc_labels ns" if "well_formed_nl ns"
  using that unfolding well_formed_nl_def by (elim conjE)

lemma sorted_if_well_formed_nl[intro,simp]:
  "sorted ns" if "well_formed_nl ns"
  using that unfolding well_formed_nl_def by (elim conjE)

lemma nl_induct[case_names Nil Cons]:
  fixes P :: "'a node list \<Rightarrow> bool"
    and ns :: "'a node list"
  assumes "P []"
    and "\<And>i t e ns. P ns \<Longrightarrow> P (N i t e # ns)"
  shows "P ns"
  using assms by (rule closed.induct)

fun well_formed :: \<open>('l::linorder) bdd \<Rightarrow> bool\<close> where
  \<open>well_formed (Constant _) = True\<close>
| \<open>well_formed (Nodes [])   = False\<close>
| \<open>well_formed (Nodes ns)   = well_formed_nl ns\<close>


fun bdd_cases where
  Const: "bdd_cases (Constant b) = undefined"
| Empty: "bdd_cases (Nodes [])   = undefined"
| Nodes: "bdd_cases (Nodes (N i t e # ns)) = undefined"

lemma bdd_cases:
  fixes bdd :: "'c bdd"
  obtains 
      (Const) b :: "bool" where "bdd = Constant b"
    | (Empty) "bdd = Nodes []"
    | (Nodes) i :: "'c uid" and t :: "'c ptr" and e :: "'c ptr" and ns :: "'c node list"
    where "bdd = Nodes (N i t e # ns)"
  by (rule bdd_cases.cases)

lemma ptr_cases:
  fixes ptr :: "'a ptr"
  obtains
    (True)  "ptr = Leaf True"
  | (False) "ptr = Leaf False"
  | (Node)  u :: "'a uid" where "ptr = Node u"
  by (cases ptr) auto

end