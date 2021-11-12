section\<open>CountSAT procedure\<close>
theory CountSAT
imports Data Evaluate "HOL-Library.Multiset"
begin

datatype 'l pq_item = Request (target: \<open>'l uid\<close>) (sum: \<open>nat\<close>) (levels_visited: \<open>nat\<close>)

instantiation pq_item :: (linorder) linorder
begin

definition less_pq_item where
  \<open>less_pq_item \<equiv> \<lambda>(Request t1 s1 l1) \<Rightarrow> \<lambda>(Request t2 s2 l2) \<Rightarrow>
    (t1 < t2 \<or> t1 = t2 \<and> l1 < l2 \<or> t1 = t2 \<and> l1 = l2 \<and> s1 < s2)\<close>

definition less_eq_pq_item where
  \<open>less_eq_pq_item \<equiv> \<lambda>(Request t1 s1 l1) \<Rightarrow> \<lambda>(Request t2 s2 l2) \<Rightarrow>
    (t1 < t2 \<or> t1 = t2 \<and> l1 < l2 \<or> t1 = t2 \<and> l1 = l2 \<and> s1 \<le> s2)\<close>

instance
  by standard (auto simp: less_pq_item_def less_eq_pq_item_def split: pq_item.splits)

end

lemma less_pq_item_simp[simp]:
  "Request t1 s1 l1 < Request t2 s2 l2 \<longleftrightarrow>
    (t1 < t2 \<or> t1 = t2 \<and> l1 < l2 \<or> t1 = t2 \<and> l1 = l2 \<and> s1 < s2)"
  unfolding less_pq_item_def by simp

lemma less_eq_pq_item_simp[simp]:
  "Request t1 s1 l1 \<le> Request t2 s2 l2 \<longleftrightarrow>
    (t1 < t2 \<or> t1 = t2 \<and> l1 < l2 \<or> t1 = t2 \<and> l1 = l2 \<and> s1 \<le> s2)"
  unfolding less_eq_pq_item_def by simp


type_synonym 'l pq = \<open>('l pq_item) multiset\<close>

definition top :: \<open>('l :: linorder) pq \<Rightarrow> 'l pq_item option\<close> where
  \<open>top pq = (if pq = {#} then None else Some (Min_mset pq))\<close>

lemma top_in[termination_simp]:
  "x \<in># pq" if "top pq = Some x"
  by (metis Min_in finite_set_mset not_None_eq option.inject set_mset_eq_empty_iff that top_def)

lemma top_eq_None_iff:
  "top pq = None \<longleftrightarrow> pq = {#}"
  unfolding top_def by simp

lemma top_Min:
  "x \<le> y" if "top pq = Some x" "y \<in># pq"
  by (metis Min_le finite_set_mset option.discI option.sel that top_def)


context
  fixes varcount :: nat
begin
fun forward_paths :: \<open>'l pq \<Rightarrow> 'l ptr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat * 'l pq\<close> where
  \<open>forward_paths pq (Leaf False) s v = (0, pq)\<close>
| \<open>forward_paths pq (Leaf True)  s v = (2^(varcount - v), pq)\<close>
| \<open>forward_paths pq (Node u)     s v = (0, {# Request u s v #} \<union># pq)\<close>


lemma size_Diff1_less_iff[termination_simp]:
  "size (ms - {#x#}) < size ms \<longleftrightarrow> x \<in># ms"
  by (metis diff_single_trivial less_irrefl size_Diff1_less)

fun combine_paths_acc :: \<open>('l :: linorder) pq \<Rightarrow> 'l uid \<Rightarrow> nat * nat \<Rightarrow> nat * nat * 'l pq\<close> where
  \<open>combine_paths_acc pq t (s_acc, v_acc) =
    (case top pq of None                  \<Rightarrow> (s_acc, v_acc, pq)
                  | Some (Request t' s v) \<Rightarrow> (if t' = t
                                              then (let acc' = (s_acc * 2^(v-v_acc) + s, v)
                                                      ; pq'  = (pq - {# Request t' s v #})
                                                    in combine_paths_acc pq' t acc')
                                              else (s_acc, v_acc, pq) ))\<close>

fun combine_paths :: \<open>('l :: linorder) pq \<Rightarrow> 'l uid \<Rightarrow> nat * nat * 'l pq\<close> where
  \<open>combine_paths pq t = combine_paths_acc pq t (0,0)\<close>

fun bdd_satcount_acc :: \<open>('l :: linorder) node list => 'l pq \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bdd_satcount_acc [] pq result_acc =
    (case top pq of None \<Rightarrow> result_acc
                  | _    \<Rightarrow> undefined)\<close>
| \<open>bdd_satcount_acc ((N i t e) # ns) pq result_acc =
    (case top pq of None                   \<Rightarrow> result_acc
                  | Some (Request tgt _ _) \<Rightarrow> (if i = tgt
                                               then let (s, lvls, pq') = combine_paths pq tgt
                                                      ; (rt, pq'') = forward_paths pq' t s (lvls+1)
                                                      ; (re, pq''') = forward_paths pq'' e s (lvls+1)
                                                     in bdd_satcount_acc ns pq''' (result_acc + rt + re)
                                               else bdd_satcount_acc ns pq result_acc))\<close>

fun bdd_satcount :: \<open>('l :: linorder) bdd \<Rightarrow> nat\<close> where
  \<open>bdd_satcount (Constant False)    = 0\<close>
| \<open>bdd_satcount (Constant True)     = 2^varcount\<close>
| \<open>bdd_satcount (Nodes ((N i t e) # ns)) =
    (let (rt, pq)  = forward_paths {#} t 1 1
       ; (re, pq') = forward_paths pq e 1 1
     in bdd_satcount_acc ns pq' (rt + re))\<close>
end

end