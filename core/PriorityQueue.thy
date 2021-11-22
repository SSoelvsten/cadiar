section\<open>Priority Queue\<close>
theory PriorityQueue
imports Main "HOL-Library.Multiset"
begin

type_synonym 'e pq = \<open>'e multiset\<close>

definition top :: \<open>('e :: linorder) pq \<Rightarrow> 'e option\<close> where
  \<open>top pq = (if pq = {#} then None else Some (Min_mset pq))\<close>

definition pop :: \<open>('e :: linorder) pq \<Rightarrow> 'e pq\<close> where
  \<open>pop pq = (pq - {# Min_mset pq #})\<close>

lemma top_in[termination_simp]:
  "x \<in># pq" if "top pq = Some x"
  by (metis Min_in finite_set_mset not_None_eq option.inject set_mset_eq_empty_iff that top_def)

lemma top_eq_None_iff:
  "top pq = None \<longleftrightarrow> pq = {#}"
  unfolding top_def by simp

lemma top_Min:
  "x \<le> y" if "top pq = Some x" "y \<in># pq"
  by (metis Min_le finite_set_mset option.discI option.sel that top_def)

lemma size_Diff1_less_iff[termination_simp]:
  "size (ms - {#x#}) < size ms \<longleftrightarrow> x \<in># ms"
  by (metis diff_single_trivial less_irrefl size_Diff1_less)

end