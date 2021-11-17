section\<open>CountSAT procedure\<close>
theory CountSAT
imports Data Evaluate "HOL-Library.Multiset"
begin

subsection \<open>Requests and Priority Queues\<close>

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


subsection \<open>Definition from Adiar\<close>

context
  fixes varcount :: nat
begin
fun forward_paths :: \<open>'l pq \<Rightarrow> 'l ptr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat * 'l pq\<close> where
  \<open>forward_paths pq (Leaf False) s v = (0, pq)\<close>
| \<open>forward_paths pq (Leaf True)  s v = (s * 2^(varcount - v), pq)\<close>
| \<open>forward_paths pq (Node u)     s v = (0, add_mset (Request u s v) pq)\<close>

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


subsection \<open>Simplified definition\<close>

fun bdd_satcount_acc' :: \<open>('l :: linorder) node list => 'l pq \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bdd_satcount_acc' [] pq result_acc =
    (case top pq of None \<Rightarrow> result_acc
                  | _    \<Rightarrow> undefined)\<close>
| \<open>bdd_satcount_acc' ((N i t e) # ns) pq result_acc =
    (case top pq of None                   \<Rightarrow> result_acc
                  | Some (Request tgt _ v) \<Rightarrow> (if i = tgt
                                               then let (s, lvls, pq') = (0, v, pq)\<^cancel>\<open>combine_paths pq tgt\<close>
                                                      ; (rt, pq'') = forward_paths pq' t s (lvls+1)
                                                      ; (re, pq''') = forward_paths pq'' e s (lvls+1)
                                                     in bdd_satcount_acc' ns pq''' (result_acc + rt + re)
                                               else bdd_satcount_acc' ns pq result_acc))\<close>

fun bdd_satcount' :: \<open>('l :: linorder) bdd \<Rightarrow> nat\<close> where
  \<open>bdd_satcount' (Constant False)    = 0\<close>
| \<open>bdd_satcount' (Constant True)     = 2^varcount\<close>
| \<open>bdd_satcount' (Nodes ((N i t e) # ns)) =
    (let (rt, pq)  = forward_paths {#} t 1 1
       ; (re, pq') = forward_paths pq e 1 1
     in bdd_satcount_acc' ns pq' (rt + re))\<close>

abbreviation
  "dom_bounded n a \<equiv> a ` (UNIV - {0..<n}) \<subseteq> {False}"

definition
  "num_assignments n bdd = card {a. bdd_eval bdd a \<and> dom_bounded n a}"

definition
  "num_assignments_nl n u ns = card {a. bdd_eval_node ns a u \<and> dom_bounded n a}"

definition
  "num_assignments_nl_ptr n ptr ns = card {a. bdd_eval_ptr ns a ptr \<and> dom_bounded n a}"


subsection \<open>Properties of bounded Boolean functions\<close>

lemma dom_bounded_alt_def:
  "dom_bounded n a \<longleftrightarrow> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> a i = False)"
  by blast

lemma dom_bounded_0:
  "dom_bounded (0::nat) a \<longleftrightarrow> a = (\<lambda>_. False)"
  unfolding dom_bounded_alt_def by auto

lemma dom_bounded_minus_1_iff:
  "dom_bounded n a \<and> a (n - 1) = False \<longleftrightarrow> dom_bounded (n - 1) a" if "n > 0" for n :: nat
proof -
  have "{0..<n} = {0..<n-1} \<union> {n-1}"
    using that by auto
  show ?thesis
    unfolding dom_bounded_alt_def \<open>{0..<n} = _\<close> by force
qed

lemma dom_bounded_Suc_iff:
  "dom_bounded (Suc n) a \<longleftrightarrow> dom_bounded n a \<or> dom_bounded (Suc n) a \<and> a n"
  unfolding dom_bounded_alt_def using less_Suc_eq by auto

lemma card_dom_bounded_flip:
  "card {a. dom_bounded (Suc n) a \<and> a n} = card {a. dom_bounded n a}"
  apply (intro card_bij_eq[where f = "\<lambda>a. a(n := False)" and g = "\<lambda>a. a(n := True)"])
  subgoal inj_on_f
    by (smt (verit, del_insts) fun_upd_triv fun_upd_upd inj_onI mem_Collect_eq)
  subgoal subs_A
    by (auto split: if_split_asm simp: dom_bounded_alt_def)
  subgoal inj_on_g
    by (rule inj_onI)
       (smt (z3) Diff_iff UNIV_I atLeastLessThan_iff fun_upd_triv
            fun_upd_upd image_subset_iff mem_Collect_eq nat_less_le singletonD)
  subgoal subs_B
    by (auto split: if_split_asm simp: dom_bounded_alt_def)
  subgoal finite_A \<comment> \<open>Finiteness\<close>
    sorry
  subgoal finite_B \<comment> \<open>Finiteness\<close>
    by (rule inj_on_finite, rule inj_on_g, rule subs_B, rule finite_A)
  done

lemma card_dom_bounded:
  "card {a. dom_bounded n a} = 2 ^ n"
proof (induction n)
  case 0
  then show ?case
    unfolding dom_bounded_0 by simp
next
  case (Suc n)
  let ?S = "{a. dom_bounded (Suc n) a}"
  and ?Sf = "{a. dom_bounded n a}" and ?St = "{a. dom_bounded (Suc n) a \<and> a n}"
  have "?S = ?Sf \<union> ?St"
    by (subst dom_bounded_Suc_iff) auto
  have "?Sf \<inter> ?St = {}"
    unfolding dom_bounded_alt_def by auto
  have "card ?S = card ?Sf + card ?St"
    unfolding \<open>?S = _\<close> apply (rule card_Un_disjoint)
    subgoal \<comment> \<open>Finiteness\<close>
      sorry
    subgoal \<comment> \<open>Finiteness\<close>
      sorry
    by (rule \<open>?Sf \<inter> ?St = {}\<close>)
  also have "\<dots> = card ?Sf + card ?Sf"
    unfolding card_dom_bounded_flip ..
  also have "\<dots> = 2 ^ n + 2 ^ n"
    unfolding Suc.IH ..
  also have "\<dots> = 2 ^ (Suc n)"
    by simp
  finally show ?case .
qed


subsection \<open>Properties of assignment counting\<close>

lemma num_assignments_nl_ptr_Node_eq[simp]:
  "num_assignments_nl_ptr n (Node u) ns = num_assignments_nl n u ns"
  unfolding num_assignments_nl_ptr_def num_assignments_nl_def by simp

lemma num_assignments_nl_ptr_alt_def:
  "num_assignments_nl_ptr n ptr ns = (
      case ptr of
        Leaf False \<Rightarrow> 0
      | Leaf True  \<Rightarrow> 2 ^ n
      | Node u \<Rightarrow> num_assignments_nl n u ns
  )"
  unfolding num_assignments_nl_ptr_def num_assignments_nl_def
  by (simp split: ptr.splits bool.splits add: card_dom_bounded)

lemma num_assignments_Const_True:
  "num_assignments n (Constant True) = 2 ^ n"
  unfolding num_assignments_def by (simp add: card_dom_bounded)

lemma num_assignments_Const_False:
  "num_assignments n (Constant False) = 0"
  unfolding num_assignments_def by simp


subsection \<open>An additional well-formedness condition on BDDs\<close>

definition well_formed_node where
  "well_formed_node \<equiv> \<lambda>N i t e \<Rightarrow>
    (case t of Node i1 \<Rightarrow> label i < label i1 | _ \<Rightarrow> True)
  \<and> (case t of Node i2 \<Rightarrow> label i < label i2 | _ \<Rightarrow> True)
  "

fun well_formed_nodes :: \<open>('l :: linorder) bdd \<Rightarrow> bool\<close> where
  \<open>well_formed_nodes (Constant _) = True\<close>
| \<open>well_formed_nodes (Nodes ns)   = list_all well_formed_node ns\<close>


subsection \<open>The central property of recursive counting of assignments\<close>

lemma num_assignments_split:
  "num_assignments varcount (Nodes (N i t e # ns)) =
   num_assignments_nl_ptr (varcount - 1) t ns + num_assignments_nl_ptr (varcount - 1) e ns"
  (is "?l = ?r")
  if "well_formed bdd" "well_formed_nodes bdd"
proof -
  \<comment> \<open>Need to prove these from the well-formedness assumptions\<close>
  have "0 < varcount" "label i = varcount - 1"
    sorry
  have 1: "{a. (a (label i) \<longrightarrow>
          bdd_eval_ptr ns a e \<and> dom_bounded varcount a) \<and>
         (\<not> a (label i) \<longrightarrow>
          bdd_eval_ptr ns a t \<and> dom_bounded varcount a)}
  = {a. a (label i) \<and> bdd_eval_ptr ns a e \<and> dom_bounded varcount a}
  \<union> {a. \<not> a (label i) \<and> bdd_eval_ptr ns a t \<and> dom_bounded varcount a}" (is "?S = ?Se \<union> ?St")
    by auto
  \<comment> \<open>Because \<open>e\<close> cannot refer to \<open>label i\<close>.\<close>
  have "bdd_eval_ptr ns a e \<longleftrightarrow> bdd_eval_ptr ns (a(label i := b)) e" for a b
    sorry
  then have "card ?Se
      = card {a. \<not> a (label i) \<and> bdd_eval_ptr ns a e \<and> dom_bounded varcount a}" (is "_ = card ?Se'")
    apply (intro card_bij_eq[where f = "\<lambda>a. a(label i := False)" and g = "\<lambda>a. a(label i := True)"])
    subgoal inj_on_f
      by (smt (verit, del_insts) fun_upd_triv fun_upd_upd inj_onI mem_Collect_eq)
    subgoal subs_A
      by (auto simp: \<open>label i = _\<close> split: if_split_asm)
    subgoal inj_on_g
      by (smt (verit, del_insts) fun_upd_triv fun_upd_upd inj_onI mem_Collect_eq)
    subgoal subs_B
      by (auto simp: \<open>label i = _\<close> \<open>varcount > 0\<close> split: if_split_asm)
    subgoal finite_A \<comment> \<open>Finiteness\<close>
      sorry
    subgoal finite_B \<comment> \<open>Finiteness\<close>
      by (rule inj_on_finite, rule inj_on_g, assumption, rule subs_B, assumption, rule finite_A)
    done
  have "?St = {a. bdd_eval_ptr ns a t \<and> dom_bounded (varcount - Suc 0) a}"
    using dom_bounded_minus_1_iff[OF \<open>varcount > 0\<close>] \<open>label i = _\<close>
    by simp (metis (no_types, hide_lams))
  have "?Se' = {a. bdd_eval_ptr ns a e \<and> dom_bounded (varcount - Suc 0) a}"
    using dom_bounded_minus_1_iff[OF \<open>varcount > 0\<close>] \<open>label i = _\<close>
    by simp (metis (no_types, hide_lams))
  have disjoint: "?Se \<inter> ?St = {}"
    by auto
  have finite: "finite ?Se" "finite ?St" \<comment> \<open>Proofs of finiteness are annoying but routine.\<close>
    sorry
  have "?l = num_assignments_nl varcount i (N i t e # ns)"
    unfolding num_assignments_def num_assignments_nl_def by simp
  also have "\<dots> = card ?S"
    unfolding num_assignments_nl_def bdd_eval_node_Cons_alt num_assignments_nl_ptr_def by simp
  also have "\<dots> = ?r"
    unfolding num_assignments_nl_def bdd_eval_node_Cons_alt num_assignments_nl_ptr_def 1
    by (subst card_Un_disjoint, rule finite, rule finite, rule disjoint)
       (simp add: \<open>?St = _\<close> \<open>card ?Se = _\<close> \<open>?Se' = _\<close>)
  finally show ?thesis .
qed


subsection \<open>Assigning an assignment count to priority queues\<close>

definition
  "num_request ns \<equiv> \<lambda>Request u s l \<Rightarrow> s * num_assignments_nl (varcount - l) u ns"

definition
  "num_pq ns pq \<equiv> \<Sum>r \<in># pq. num_request ns r"

lemma num_pq_Mempty_eq_0[simp]:
  "num_pq ns {#} = 0"
  unfolding num_pq_def by simp

lemma num_request_alt_def:
  "num_request ns (Request u s l) = s * num_assignments_nl (varcount - l) u ns"
  unfolding num_request_def by simp


subsection \<open>Proving correctness of @{term bdd_satcount'}}\<close>

lemma forward_pathsE:
  obtains s' pq' where
    "forward_paths pq ptr s l = (s', pq')"
    "num_pq ns pq' + s' = num_pq ns pq + s * num_assignments_nl_ptr (varcount - l) ptr ns"
  by (cases ptr rule: ptr_cases; simp add: num_assignments_nl_ptr_alt_def num_pq_def num_request_def)

lemma bdd_satcount_acc'_correct:
  "bdd_satcount_acc' ns pq s = s + num_pq ns pq"
  sorry

theorem bdd_satcount'_correct:
  assumes "well_formed bdd" "well_formed_nodes bdd"
  shows "bdd_satcount' bdd = num_assignments varcount bdd"
proof (cases bdd rule: bdd_satcount'.cases)
  case (3 i t e ns)
  obtain rt pq where 1:
    "forward_paths {#} t 1 1 = (rt, pq)"
    "num_pq ns pq + rt = num_pq ns {#} + 1 * num_assignments_nl_ptr (varcount - 1) t ns"
    by (rule forward_pathsE[of "{#}" t 1 1 ns])
  obtain re pq' where 2:
    "forward_paths pq e 1 1 = (re, pq')"
    "num_pq ns pq' + re = num_pq ns pq + 1 * num_assignments_nl_ptr (varcount - 1) e ns"
    by (rule forward_pathsE)
  have "bdd_satcount' bdd = bdd_satcount_acc' ns pq' (rt + re)"
    using 1 2 by (simp add: \<open>bdd = _\<close>)
  also have "\<dots> = rt + re + num_pq ns pq'"
    by (rule bdd_satcount_acc'_correct)
  also have "\<dots> = num_assignments_nl_ptr (varcount - 1) t ns + num_assignments_nl_ptr (varcount - 1) e ns"
    using 1(2) 2(2) by simp
  also have "\<dots> = num_assignments varcount (Nodes (N i t e # ns))"
    using assms by (rule num_assignments_split[symmetric])
  also have "\<dots> = num_assignments varcount bdd"
    unfolding \<open>bdd = _\<close> ..
  finally show ?thesis .
qed (use assms in \<open>simp_all add: num_assignments_Const_True num_assignments_Const_False\<close>)

end

end