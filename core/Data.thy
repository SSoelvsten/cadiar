section\<open>Core data structures\<close>
theory Data
imports Main
begin

datatype 'l uid = U (label:\<open>'l\<close>) (id:\<open>nat\<close>)

instantiation uid :: (linorder) linorder
begin
fun less_uid where
   \<open>less_uid (U i1 id1) (U i2 id2) = (i1 < i2 \<or> (i1 = i2 \<and> id1 < id2))\<close>
instance sorry
end

datatype 'l ptr = Leaf \<open>bool\<close> | Node \<open>'l uid\<close>

datatype 'l node = N (uid:\<open>'l uid\<close>) (low:\<open>'l ptr\<close>) (high:\<open>'l ptr\<close>)

datatype 'l bdd = Constant \<open>bool\<close> | Nodes \<open>'l node list\<close>

type_synonym 'l assignment = \<open>'l \<Rightarrow> bool\<close>

fun well_formed_nl :: \<open>'l node list \<Rightarrow> bool\<close> where
  \<open>well_formed_nl []             = True\<close>
| \<open>well_formed_nl (N i t e # ns) = (well_formed_nl ns
                                    \<and> (case t of Leaf b \<Rightarrow> True | Node l_uid \<Rightarrow> \<exists>n \<in> set ns . uid n = l_uid)
                                    \<and> (case e of Leaf b \<Rightarrow> True | Node h_uid \<Rightarrow> \<exists>n \<in> set ns . uid n = h_uid))\<close>

theorem nl_induct[case_names Nil Cons]:
  fixes P :: "'a node list \<Rightarrow> bool"
    and ns :: "'a node list"
  assumes "P []"
    and "\<And>i t e ns. P ns \<Longrightarrow> P (N i t e # ns)"
  shows "P ns"
  using assms by (rule Data.well_formed_nl.induct)

fun well_formed :: \<open>'l bdd \<Rightarrow> bool\<close> where
  \<open>well_formed (Constant _) = True\<close>
| \<open>well_formed (Nodes [])   = False\<close>
| \<open>well_formed (Nodes ns)   = well_formed_nl ns\<close>


fun bdd_cases where
  Const: "bdd_cases (Constant b) = undefined"
| Empty: "bdd_cases (Nodes [])   = undefined"
| Nodes: "bdd_cases (Nodes (N i t e # ns)) = undefined"

theorem bdd_cases:
  fixes bdd :: "'c bdd"
  obtains 
      (Const) b :: "bool" where "bdd = Constant b"
    | (Empty) "bdd = Nodes []"
    | (Nodes) i :: "'c uid" and t :: "'c ptr" and e :: "'c ptr" and ns :: "'c node list"
    where "bdd = Nodes (N i t e # ns)"
  by (rule bdd_cases.cases)

end