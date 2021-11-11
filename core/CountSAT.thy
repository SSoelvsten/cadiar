section\<open>CountSAT procedure\<close>
theory CountSAT
imports Data Evaluate "HOL-Library.Multiset"
begin

text \<open> 
  TODO:
   - Priority Queue (multi-set)
   - Auxiliary functions:
     - Forwarding to out-going edges of a node
         return result_inc * PQ
     - Combine all in-going to a node
         return sum * levels * PQ
     - While loop
         return result
 \<close>

datatype 'l pq_item = Request (target: \<open>'l uid\<close>) (sum: \<open>nat\<close>) (levels_visited: \<open>nat\<close>)

instantiation pq_item :: (linorder) linorder
begin
fun less_pq_item where
   \<open>less_pq_item (Request t1 s1 l1) (Request t2 s2 l2) = (t1 < t2
                                     \<or> (t1 = t2 \<and> l1 < l2)
                                     \<or> (t1 = t2 \<and> l1 = l2 \<and> s1 < s2))\<close>
instance sorry
end

type_synonym 'l pq = \<open>('l pq_item) multiset\<close>

definition top :: \<open>('l :: linorder) pq \<Rightarrow> 'l pq_item option\<close> where
  \<open>top pq = (if pq = {#} then None else Some (Min(set_mset pq)))\<close>

context
fixes varcount :: nat
begin
fun forward_paths :: \<open>'l pq \<Rightarrow> 'l ptr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat * 'l pq\<close> where
  \<open>forward_paths pq (Leaf False) s v = (0, pq)\<close>
| \<open>forward_paths pq (Leaf True)  s v = (2^(varcount - v), pq)\<close>
| \<open>forward_paths pq (Node u)     s v = (0, {# Request u s v #} \<union># pq)\<close>

fun combine_paths :: \<open>'l pq \<Rightarrow> 'l uid \<Rightarrow> nat * nat * 'l pq\<close> where
  \<open>combine_paths pq t = undefined\<close>

fun bdd_satcount :: \<open>'l bdd \<Rightarrow> nat\<close> where
  \<open>bdd_satcount (Constant False)    = 0\<close>
| \<open>bdd_satcount (Constant True)     = 2^varcount\<close>
| \<open>bdd_satcount (Nodes (root # ns)) = undefined\<close>
end

end