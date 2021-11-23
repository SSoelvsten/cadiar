section\<open>Core data structures\<close>
theory Data
imports Main
begin

subsection \<open>Data types\<close>

subsubsection \<open>Unique identifier\<close>

text \<open>Every node of a BDD is uniquely identified by its label and a level-identifer. The prior is
      the input variable in \<open>'l\<close> that it represents, while the second is supposed to induce a total
      ordering within a level.\<close>

datatype 'l uid = U (label:\<open>'l\<close>) (id:\<open>nat\<close>)

text \<open>All algorithms are based on a level-by-level processing of all nodes. This requires nodes to
      be topologically ordered. Secondly, these algorithms need to know when they are going to see
      a node within the level, so secondarily they are sorted on the identifier.

      Hence, the uid is sorted lexicographically on the above tuple.\<close>

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

subsubsection \<open>Pointer\<close>

text \<open>The above encapsulates identification of an internal node of a BDD. We also need nodes to be
      able to reference leaves in the BDD, i.e. the True and the False Boolean values.

      Hence, a pointer can either refer to a leaf or to an internal node. To this end, we lift the
      ordering from both the ordering of Boolean values (\<open>False < True\<close>) and the ordering of uids up
      to pointers.\<close>

datatype 'l ptr = Leaf \<open>bool\<close> | Node \<open>'l uid\<close>

instantiation ptr :: (linorder) linorder
begin
definition less_ptr where
   \<open>less_ptr \<equiv> \<lambda>ptr1 \<Rightarrow> \<lambda>ptr2 \<Rightarrow> (case (ptr1, ptr2) of
      (Node u1, Node u2) \<Rightarrow> u1 < u2
    | (Node _, Leaf _) \<Rightarrow> True
    | (Leaf _, Node _) \<Rightarrow> False
    | (Leaf b1, Leaf b2) \<Rightarrow> b1 < b2)\<close>

definition less_eq_ptr where
   \<open>less_eq_ptr \<equiv> \<lambda>ptr1 \<Rightarrow> \<lambda>ptr2 \<Rightarrow> (case (ptr1, ptr2) of
      (Node u1, Node u2) \<Rightarrow> u1 \<le> u2
    | (Node _, Leaf _) \<Rightarrow> True
    | (Leaf _, Node _) \<Rightarrow> False
    | (Leaf b1, Leaf b2) \<Rightarrow> b1 \<le> b2
)\<close>

instance
  by standard (auto simp: less_ptr_def less_eq_ptr_def split: ptr.splits)
end

text \<open>And a simple rule to simplify case distinction on pointers within our proofs.\<close>

lemma ptr_cases:
  fixes ptr :: "'a ptr"
  obtains
    (True)  "ptr = Leaf True"
  | (False) "ptr = Leaf False"
  | (Node)  u :: "'a uid" where "ptr = Node u"
  by (cases ptr) auto

subsubsection \<open>Node data type\<close>

text \<open>A node is a triple that consists of its unique identifier, i.e. its label and its
      level-identifier, together with a pointer to its high child, i.e. where to go to in the 'then'
      case on the input variable, and finally the pointer to its low child, i.e. where to go to when
      the input variable evaluates to false.\<close>

datatype 'l node = N (uid:\<open>'l uid\<close>) (high:\<open>'l ptr\<close>) (low:\<open>'l ptr\<close>)

text \<open>Nodes are sorted lexicographically on the above triple. This makes nodes first and foremost
      sorted by their unique identifiers, which makes them topologically ordered.

      At this point, we are not (yet) going to use the ordering on children. See Reduce.thy for how
      we actually can guarantee this ordering is fully satisfied.\<close>

instantiation node :: (linorder) linorder
begin
definition less_node where
  \<open>less_node \<equiv> \<lambda>(N i1 t1 e1) \<Rightarrow> \<lambda>(N i2 t2 e2) \<Rightarrow>
    (i1 < i2 \<or> i1 = i2 \<and> t1 < t2 \<or> i1 = i2 \<and> t1 = t2 \<and> e1 < e2)\<close>

definition less_eq_node where
  \<open>less_eq_node \<equiv> \<lambda>(N i1 t1 e1) \<Rightarrow> \<lambda>(N i2 t2 e2) \<Rightarrow>
    (i1 < i2 \<or> i1 = i2 \<and> t1 < t2 \<or> i1 = i2 \<and> t1 = t2 \<and> e1 \<le> e2)\<close>

instance
  by standard (auto simp: less_node_def less_eq_node_def split: node.splits)

end

lemma less_node_simp[simp]:
  \<open>(N i1 t1 e1) < (N i2 t2 e2) =
    (i1 < i2 \<or> i1 = i2 \<and> t1 < t2 \<or> i1 = i2 \<and> t1 = t2 \<and> e1 < e2)\<close>
  unfolding less_node_def by simp

lemma less_eq_node_simp[simp]:
  \<open>(N i1 t1 e1) \<le> (N i2 t2 e2) \<longleftrightarrow>
    (i1 < i2 \<or> i1 = i2 \<and> t1 < t2 \<or> i1 = i2 \<and> t1 = t2 \<and> e1 \<le> e2)\<close>
  unfolding less_eq_node_def by simp

subsection \<open>Binary Decision Diagram\<close>

text \<open>A BDD is then either immediately a leaf, thereby representing a constant function. Otherwise,
      it a (non-empty) stream of nodes, where the first node is to be interpreted as the root.\<close>

datatype 'l bdd = Constant \<open>bool\<close> | Nodes \<open>'l node list\<close>

text \<open>All algorithms rely on the nodes in the Binary Decision Diagram are well-formed in some way.
      Specifically, we need them to

      (a) be 'closed', i.e. every node mentioned actually exists,
      (b) be sorted
      (c) the levels are always (strictly) increasing, i.e. a node may not mention any other node on
          the same level or above.
      (d) the node list is non-empty

      TODO: (e) Every node mentioned is transitively reachable from the root?\<close>

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

fun well_formed :: \<open>('l::linorder) bdd \<Rightarrow> bool\<close> where
  \<open>well_formed (Constant _) = True\<close>
| \<open>well_formed (Nodes [])   = False\<close>
| \<open>well_formed (Nodes ns)   = well_formed_nl ns\<close>

lemma well_formed_nl_ConsD[intro?]:
  \<open>well_formed_nl ns\<close> if \<open>well_formed_nl (n # ns)\<close>
  using that unfolding well_formed_nl_def by (cases n, simp)

lemma high_lb:
  "ptr_lb (label (uid n)) (high n)" if "inc_labels (n # ns)"
  using that by (cases n; simp)

lemma low_lb:
  "ptr_lb (label (uid n)) (low n)" if "inc_labels (n # ns)"
  using that by (cases n; simp)

lemma ptr_lb_trans:
  "ptr_lb l n" if "ptr_lb k n" "(l :: 'a :: order) \<le> k"
  using that unfolding ptr_lb_def by (auto split: ptr.splits)

text \<open>Finally we have here a few ease-of-life lemmas for later proofs.\<close>

lemma nl_induct[case_names Nil Cons]:
  fixes P :: "'a node list \<Rightarrow> bool"
    and ns :: "'a node list"
  assumes "P []"
    and "\<And>i t e ns. P ns \<Longrightarrow> P (N i t e # ns)"
  shows "P ns"
  using assms by (rule closed.induct)

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

subsection \<open>Assignment\<close>

text \<open>For assignments we are going to reuse the definition from @{cite Michaelis2016} of a function
      from the set of labels to the Boolean values they were assigned.

      While this is not (yet) reflective of the definition in Adiar it is planned to implement it
      exactly like this (cf. Issue #147 on 'github.com/SSoelvsten/adiar/').\<close>

type_synonym 'l assignment = \<open>'l \<Rightarrow> bool\<close>

end