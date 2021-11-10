section\<open>Core data structures\<close>
theory Data
imports Main
begin

datatype 'l uid = U (label:\<open>'l\<close>) (id:\<open>nat\<close>)
datatype 'l ptr = Leaf \<open>bool\<close> | Node \<open>'l uid\<close>

datatype 'l node = N (uid:\<open>'l uid\<close>) (low:\<open>'l ptr\<close>) (high:\<open>'l ptr\<close>)

datatype 'l bdd = Constant \<open>bool\<close> | Nodes \<open>'l node list\<close>

type_synonym 'l assignment = \<open>'l \<Rightarrow> bool\<close>

fun well_formed_nl :: \<open>'l node list \<Rightarrow> bool\<close> where
  \<open>well_formed_nl []             = True\<close>
| \<open>well_formed_nl (N _ l h # ns) = (well_formed_nl ns
                                    \<and> (case l of Leaf b \<Rightarrow> True | Node l_uid \<Rightarrow> \<exists>n \<in> set ns . uid n = l_uid)
                                    \<and> (case h of Leaf b \<Rightarrow> True | Node h_uid \<Rightarrow> \<exists>n \<in> set ns . uid n = h_uid))\<close>

fun well_formed :: \<open>'l bdd \<Rightarrow> bool\<close> where
  \<open>well_formed (Constant _) = True\<close>
| \<open>well_formed (Nodes [])   = False\<close>
| \<open>well_formed (Nodes ns)   = well_formed_nl ns\<close>

end