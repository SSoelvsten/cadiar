section\<open>CountSAT procedure\<close>
theory CountSAT
imports Data Evaluate PriorityQueue "~/Isabelle/isabelle-finite/Finiteness"
begin

subsection \<open>Priority Queue requests\<close>

text \<open>The type of the priority queue elements have to be defined before the 'varcount' variable
      fixed below.\<close>

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
  \<open>Request t1 s1 l1 < Request t2 s2 l2 \<longleftrightarrow>
    (t1 < t2 \<or> t1 = t2 \<and> l1 < l2 \<or> t1 = t2 \<and> l1 = l2 \<and> s1 < s2)\<close>
  unfolding less_pq_item_def by simp

lemma less_eq_pq_item_simp[simp]:
  \<open>Request t1 s1 l1 \<le> Request t2 s2 l2 \<longleftrightarrow>
    (t1 < t2 \<or> t1 = t2 \<and> l1 < l2 \<or> t1 = t2 \<and> l1 = l2 \<and> s1 \<le> s2)\<close>
  unfolding less_eq_pq_item_def by simp

subsection \<open>Bounded domain boolean functions\<close>

text \<open>To be able to count the number of satisfying assignments, we first need to know the number of
      input variables. That is, we need to work with boolean functions with a bounded domain.\<close>

context
  fixes varcount :: nat
begin

definition
  \<open>dom_bounded n a \<equiv> a ` (UNIV - {n..<varcount}) \<subseteq> {False}\<close>

definition
  "num_assignments n bdd = card {a. bdd_eval bdd a \<and> dom_bounded n a}"

definition
  "num_assignments_node n u ns = card {a. bdd_eval_node ns a u \<and> dom_bounded n a}"

definition
  "num_assignments_ptr n ptr ns = card {a. bdd_eval_ptr ns a ptr \<and> dom_bounded n a}"

subsubsection \<open>Basic properties of bounded Boolean functions\<close>

lemma dom_bounded_alt_def:
  "dom_bounded n a \<longleftrightarrow> (\<forall>i. i \<notin> {n..<varcount} \<longrightarrow> a i = False)"
  unfolding dom_bounded_def by blast

lemma dom_bounded_max:
  "dom_bounded (n::nat) a \<longleftrightarrow> a = (\<lambda>_. False)" if "n \<ge> varcount"
  using that unfolding dom_bounded_alt_def by auto

lemma dom_bounded_plus_1_iff:
  "dom_bounded n a \<and> a n = False \<longleftrightarrow> dom_bounded (n + 1) a" for n :: nat
  unfolding dom_bounded_alt_def
  apply auto
  subgoal for i
    apply (cases "i = n")
     apply auto
    done
  done

lemma dom_bounded_Suc_iff:
  "dom_bounded n a \<longleftrightarrow> dom_bounded n a \<and> a n \<or> dom_bounded (Suc n) a"
  unfolding dom_bounded_alt_def
  apply auto
  subgoal for i
    by (cases "i = n") auto
  done

lemma finite_dom_bounded[simp]:
  "finite {a. dom_bounded n a}"
proof (induction n rule: nat_descend_induct[where n = varcount])
  case (base k)
  then show ?case
    by - (rule finite_subset[where B = "{\<lambda>_. False}"], auto simp: dom_bounded_alt_def)
next
  case (descend k)
  have "{a. dom_bounded k a \<and> a k} \<subseteq> (\<lambda>a. a(k:=True)) ` {a. dom_bounded (Suc k) a}" (is "?S \<subseteq> ?T")
  proof safe
    fix a assume "dom_bounded k a" "a k"
    let ?a = "a(k:=False)"
    from \<open>dom_bounded k a\<close> have "dom_bounded (Suc k) ?a"
      unfolding dom_bounded_alt_def by auto
    moreover from \<open>a k\<close> have "?a(k:=True) = a"
      by (intro ext; simp)
    ultimately show "a \<in> ?T"
      by (intro image_eqI) auto
  qed
  then have "{a. dom_bounded k a} \<subseteq> ?T \<union> {a. dom_bounded (Suc k) a}"
    by (subst dom_bounded_Suc_iff) blast
  moreover have "finite \<dots>"
    using descend.IH by simp
  ultimately show ?case
    by (rule finite_subset)
qed

lemma card_dom_bounded_flip:
  "card {a. dom_bounded n a \<and> a n} = card {a. dom_bounded (Suc n) a}" if "n < varcount"
  apply (intro card_bij_eq[where f = "\<lambda>a. a(n := False)" and g = "\<lambda>a. a(n := True)"])
  subgoal inj_on_f
    by (smt (verit, del_insts) fun_upd_triv fun_upd_upd inj_onI mem_Collect_eq)
  subgoal subs_A
    by (auto split: if_split_asm simp: dom_bounded_alt_def)
  subgoal inj_on_g
    apply (rule inj_onI)
    by (smt (verit, del_insts) CountSAT.dom_bounded_alt_def Diff_iff atLeastLessThan_singleton fun_upd_triv fun_upd_upd insertCI ivl_diff less_Suc_eq_le mem_Collect_eq nat_less_le not_le)
  subgoal subs_B
    by (auto split: if_split_asm simp: dom_bounded_alt_def that)
  subgoal finite_A
    by simp
  subgoal finite_B
    by simp
  done

lemma card_dom_bounded:
  "card {a. dom_bounded (varcount - n) a} = 2 ^ n" if "n \<le> varcount"
  using that
proof (induction n)
  case 0
  then show ?case
    by (subst dom_bounded_max; simp)
next
  case (Suc n)
  let ?n = "varcount - n" and ?n1 = "varcount - Suc n"
  let ?S = "{a. dom_bounded ?n1 a}"
  and ?Sf = "{a. dom_bounded ?n a}" and ?St = "{a. dom_bounded ?n1 a \<and> a ?n1}"
  from \<open>Suc n \<le> varcount\<close> have [simp]: "Suc ?n1 = ?n"
    by simp
  have "?S = ?Sf \<union> ?St"
    by (subst dom_bounded_Suc_iff) auto
  from \<open>Suc n \<le> varcount\<close> have "?Sf \<inter> ?St = {}"
    unfolding dom_bounded_alt_def by auto
  from \<open>?Sf \<inter> ?St = {}\<close> have "card ?S = card ?Sf + card ?St"
    unfolding \<open>?S = _\<close> by (intro card_Un_disjoint; simp)
  also have "\<dots> = card ?Sf + card ?Sf"
    using \<open>Suc n \<le> varcount\<close> by (simp add: card_dom_bounded_flip)
  also have "\<dots> = 2 ^ n + 2 ^ n"
    using \<open>Suc n \<le> varcount\<close> by (simp add: Suc.IH)
  also have "\<dots> = 2 ^ (Suc n)"
    by simp
  finally show ?case .
qed

lemma card_dom_bounded':
  "card {a. dom_bounded n a} = 2 ^ (varcount - n)" if "n \<le> varcount"
  using card_dom_bounded[of "varcount - n"] that by simp

subsubsection \<open>Properties of assignment counting\<close>

lemma num_assignments_ptr_Node_eq[simp]:
  "num_assignments_ptr n (Node u) ns = num_assignments_node n u ns"
  unfolding num_assignments_ptr_def num_assignments_node_def by simp

lemma num_assignments_ptr_alt_def:
  "num_assignments_ptr n ptr ns = (
      case ptr of
        Leaf False \<Rightarrow> 0
      | Leaf True  \<Rightarrow> 2 ^ (varcount - n)
      | Node u \<Rightarrow> num_assignments_node n u ns
  )" if "n \<le> varcount"
  using that unfolding num_assignments_ptr_def num_assignments_node_def
  by (simp split: ptr.splits bool.splits add: card_dom_bounded')

lemma num_assignments_Const_True[simp]:
  "num_assignments n (Constant True) = 2 ^ (varcount - n)" if "n \<le> varcount"
  using that unfolding num_assignments_def by (simp add: card_dom_bounded')

lemma num_assignments_Const_False[simp]:
  "num_assignments n (Constant False) = 0"
  unfolding num_assignments_def by simp

lemma num_assignments_ptr_leaf_eq_num_assignments[simp]:
  "num_assignments_ptr n (Leaf b) ns = num_assignments n (Constant b)"
  unfolding num_assignments_def num_assignments_ptr_def by simp

lemma num_assignments_nodes_eq[simp]:
  "num_assignments n (Nodes (N i t e # ns)) = num_assignments_node n i (N i t e # ns)"
  unfolding num_assignments_def num_assignments_node_def by simp

lemma num_assignments_restrict:
  "num_assignments n bdd = num_assignments_vars bdd * 2 ^ (n - card (vars_of_bdd bdd))"
  oops


subsubsection \<open>The central property of recursive counting of assignments\<close>

lemma dom_bounded_upd_False:
  "dom_bounded n (a(l := False))" if "dom_bounded n a"
  using that unfolding dom_bounded_alt_def by auto

lemma dom_bounded_upd_iff:
  "dom_bounded n (a(l := b)) \<longleftrightarrow> dom_bounded n a" if "n \<le> l" "l < varcount"
  using that unfolding dom_bounded_alt_def by auto

lemma
  fixes ns :: "nat node list"
  assumes "well_formed_nl ns"
  shows bdd_eval_node_upd_iff:
    "l < label u \<Longrightarrow> bdd_eval_node ns (a(l := b)) u = bdd_eval_node ns a u"
  and bdd_eval_ptr_upd_iff:
    "ptr_lb l ptr \<Longrightarrow> bdd_eval_ptr ns (a(l := b)) ptr = bdd_eval_ptr ns a ptr"
  using assms
proof (induction ns a u and ns a ptr rule: bdd_eval_node_bdd_eval_ptr.induct)
  case (2 i t e ns a tgt)
  from \<open>well_formed_nl (N i t e # ns)\<close> have \<open>well_formed_nl ns\<close>
    by (rule well_formed_nl_ConsD)
  have [simp]: "(\<lambda>x. (x = l \<longrightarrow> b) \<and> (x \<noteq> l \<longrightarrow> a x)) = a(l:=b)" \<comment> \<open>XXX\<close>
    by auto
  show ?case
  proof (cases "i = tgt")
    case True
    moreover have "ptr_lb l t" "ptr_lb l e"
      using \<open>well_formed_nl (N i t e # ns)\<close> \<open>l < label tgt\<close> True
      by (auto intro: ptr_lb_trans elim: high_lb low_lb dest!: inc_labels_if_well_formed_nl)
    ultimately show ?thesis
      using 2(1-) \<open>well_formed_nl ns\<close> by (simp add: 2(1))
  next
    case False
    with 2(3-) \<open>well_formed_nl ns\<close> show ?thesis
      by (simp add: 2(2))
  qed
qed (simp add: ptr_lb_def)+

lemma dom_bounded_swap_var_card_eq:
  "card {a. \<not> a l \<and> bdd_eval_ptr ns a t \<and> dom_bounded n a}
 = card {a. bdd_eval_ptr ns a t \<and> dom_bounded (n + 1) a}"
  if [simp]: "well_formed_nl ns" "ptr_lb l t" "ptr_lb n t"
 and bounds: \<open>l < varcount\<close> \<open>n \<le> l\<close>
  unfolding dom_bounded_plus_1_iff[symmetric]
  apply simp
  apply (intro card_bij_eq[where f = "\<lambda>a. a(l := a n,n := False)"
                             and g = "\<lambda>a. a(n:= a l,l := False)"])
  subgoal inj_on_f
    apply (rule inj_onI)
    apply simp
    by (smt (z3) fun_upd_idem_iff fun_upd_twist fun_upd_upd)
  subgoal subs_A
    using bounds by (auto simp: dom_bounded_upd_iff bdd_eval_ptr_upd_iff)
  subgoal inj_on_g
    apply (rule inj_onI)
    apply simp
    by (smt (z3) fun_upd_idem_iff fun_upd_twist fun_upd_upd)
  subgoal subs_B
    using bounds by (auto simp: dom_bounded_upd_iff bdd_eval_ptr_upd_iff)
  subgoal finite_A
    by simp
  subgoal finite_B
    by simp
  done

lemma num_assignments_split:
  "num_assignments_node n i (N i t e # ns) =
   num_assignments_ptr (n + 1) t ns + num_assignments_ptr (n + 1) e ns"
  (is "?l = ?r")
  if "well_formed_nl (N i t e # ns)" and bounds: \<open>label i < varcount\<close> \<open>n \<le> label i\<close>
proof -
  have 1: "{a. (a (label i) \<longrightarrow> bdd_eval_ptr ns a t \<and> dom_bounded n a) \<and>
             (\<not> a (label i) \<longrightarrow> bdd_eval_ptr ns a e \<and> dom_bounded n a)}
  = {a. a (label i) \<and> bdd_eval_ptr ns a t \<and> dom_bounded n a}
  \<union> {a. \<not> a (label i) \<and> bdd_eval_ptr ns a e \<and> dom_bounded n a}" (is "?S = ?St \<union> ?Se")
    by auto
  from \<open>well_formed_nl _\<close> \<open>n \<le> label i\<close> have [simp]:
    "ptr_lb n t" "ptr_lb n e" "ptr_lb (label i) t" "ptr_lb (label i) e"
    by (auto intro: ptr_lb_trans elim: high_lb low_lb dest!: inc_labels_if_well_formed_nl)
  from \<open>well_formed_nl _\<close> have [simp]: "well_formed_nl ns"
    by (rule well_formed_nl_ConsD)
  have "bdd_eval_ptr ns (a(label i := b)) t \<longleftrightarrow> bdd_eval_ptr ns a t" for a b
    by (rule bdd_eval_ptr_upd_iff; simp)
  then have "card ?St
      = card {a. \<not> a (label i) \<and> bdd_eval_ptr ns a t \<and> dom_bounded n a}" (is "_ = card ?St'")
    apply (intro card_bij_eq[where f = "\<lambda>a. a(label i := False)" and g = "\<lambda>a. a(label i := True)"])
    subgoal inj_on_f
      by (smt (verit, del_insts) fun_upd_triv fun_upd_upd inj_onI mem_Collect_eq)
    subgoal subs_A
      by (auto split: if_split_asm intro: dom_bounded_upd_False)
    subgoal inj_on_g
      by (smt (verit, del_insts) fun_upd_triv fun_upd_upd inj_onI mem_Collect_eq)
    subgoal subs_B
      by (auto simp: bounds dom_bounded_upd_iff split: if_split_asm)
    subgoal finite_A
      by simp
    subgoal finite_B
      by simp
    done
  have "card ?Se = card {a. bdd_eval_ptr ns a e \<and> dom_bounded (n + 1) a}"
    by (rule dom_bounded_swap_var_card_eq; simp add: bounds)
  have "card ?St' = card {a. bdd_eval_ptr ns a t \<and> dom_bounded (n + 1) a}"
    by (rule dom_bounded_swap_var_card_eq; simp add: bounds)
  have "?St \<inter> ?Se = {}"
    by auto
  have "?l = card ?S"
    unfolding num_assignments_node_def num_assignments_ptr_def by simp
  also have "\<dots> = ?r"
    unfolding num_assignments_node_def num_assignments_ptr_def 1
    by (simp add: card_Un_disjoint \<open>card ?St = _\<close> \<open>card ?Se = _\<close> \<open>card ?St' = _\<close> \<open>?St \<inter> ?Se = {}\<close>)
  finally show ?thesis .
qed

subsection \<open>Algorithm Definition\<close>

text \<open>The core idea of the time-forwarded CountSAT algorithm is to keep track of the number of
      input variables that have been fixed on a path going from the root to a node. Any input
      variable (regardless of which one) not fixed can be set to any value.

      The forward_paths function takes care of the 'base cases' by either forwarding a request
      to an internal node or to return a value to be added to the total; the value accounts the
      number of 'unbound' variables by multiplying the number of assignments on the 'bound'
      variables with the number of possible assignments to the rest.\<close>

fun forward_paths :: \<open>('l pq_item) pq \<Rightarrow> 'l ptr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat * ('l pq_item) pq\<close> where
  \<open>forward_paths pq (Leaf False) s v = (0, pq)\<close>
| \<open>forward_paths pq (Leaf True)  s v = (s * 2^(varcount - v), pq)\<close>
| \<open>forward_paths pq (Node u)     s v = (0, add_mset (Request u s v) pq)\<close>

subsubsection \<open>Simplified definition\<close>

function bdd_satcount_acc' :: \<open>('l :: linorder) node list => ('l pq_item) pq \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bdd_satcount_acc' [] pq racc =
    (case top pq of None \<Rightarrow> racc
                  | _    \<Rightarrow> undefined)\<close>
| \<open>bdd_satcount_acc' ((N i t e) # ns) pq racc =
    (case top pq of None                      \<Rightarrow> racc
                  | Some (Request tgt s lvls) \<Rightarrow> (if i = tgt
                                               then let pq' = pop pq
                                                      ; (rt, pq'') = forward_paths pq' t s (lvls+1)
                                                      ; (re, pq''') = forward_paths pq'' e s (lvls+1)
                                                     in bdd_satcount_acc' ((N i t e) # ns) pq''' (racc + rt + re)
                                               else bdd_satcount_acc' ns pq racc))\<close>
  by pat_completeness auto

termination
  sorry

fun bdd_satcount' :: \<open>('l :: linorder) bdd \<Rightarrow> nat\<close> where
  \<open>bdd_satcount' (Constant False)    = 0\<close>
| \<open>bdd_satcount' (Constant True)     = 2^varcount\<close>
| \<open>bdd_satcount' (Nodes ((N i t e) # ns)) =
    (let (rt, pq)  = forward_paths {#} t 1 1
       ; (re, pq') = forward_paths pq e 1 1
     in bdd_satcount_acc' ((N i t e) # ns) pq' (rt + re))\<close>

subsubsection \<open>Definition from Adiar\<close>

text \<open>We need to only forward a single request in the priority queue, if we want to keep the running
      time to be O(N log N). To this end, we need to combine all in-going requests to the same node
      while also accounting for any differences in the number of input variables that were bound to
      some value.

      Luckily, due to the simple solution in @{term forward_paths} this is quite simple. It is also
      important to remember, that we had sorted the @{term pq_item} such that it was secondarily
      sorted in ascending order by the number 'bound' variables. So, we can accumulate the sum of
      ingoing paths and compensate for any nodes that were skipped on one path, but not the other.\<close>

fun combine_paths_acc :: \<open>(('l :: linorder) pq_item) pq \<Rightarrow> 'l uid \<Rightarrow> nat * nat \<Rightarrow> nat * nat * ('l pq_item) pq\<close> where
  \<open>combine_paths_acc pq t (s_acc, v_acc) =
    (case top pq of None                  \<Rightarrow> (s_acc, v_acc, pq)
                  | Some (Request t' s v) \<Rightarrow> (if t' = t
                                              then (let acc' = (s_acc * 2^(v-v_acc) + s, v)
                                                      ; pq'  = (pq - {# Request t' s v #})
                                                    in combine_paths_acc pq' t acc')
                                              else (s_acc, v_acc, pq) ))\<close>

fun combine_paths :: \<open>(('l :: linorder) pq_item) pq \<Rightarrow> 'l uid \<Rightarrow> nat * nat * ('l pq_item) pq\<close> where
  \<open>combine_paths pq t = combine_paths_acc pq t (0,0)\<close>

text \<open>Combining the two functions above, we get the main loop of the CountSAT function. Here all
      in-going requests are combined to then forward them to their children and then go to the
      next node.\<close>

fun bdd_satcount_acc :: \<open>('l :: linorder) node list => ('l pq_item) pq \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bdd_satcount_acc [] pq racc =
    (case top pq of None \<Rightarrow> racc
                  | _    \<Rightarrow> undefined)\<close>
| \<open>bdd_satcount_acc (N i t e # ns) pq racc =
    (case top pq of None                   \<Rightarrow> racc
                  | Some (Request tgt _ _) \<Rightarrow> (if i = tgt
                                               then let (s, lvls, pq') = combine_paths pq tgt
                                                      ; (rt, pq'') = forward_paths pq' t s (lvls+1)
                                                      ; (re, pq''') = forward_paths pq'' e s (lvls+1)
                                                     in bdd_satcount_acc ns pq''' (racc + rt + re)
                                               else bdd_satcount_acc ns pq racc))\<close>

fun bdd_satcount :: \<open>('l :: linorder) bdd \<Rightarrow> nat\<close> where
  \<open>bdd_satcount (Constant False)    = 0\<close>
| \<open>bdd_satcount (Constant True)     = 2^varcount\<close>
| \<open>bdd_satcount (Nodes ((N i t e) # ns)) =
    (let (rt, pq)  = forward_paths {#} t 1 1
       ; (re, pq') = forward_paths pq e 1 1
     in bdd_satcount_acc ns pq' (rt + re))\<close>

text \<open>TODO: make the proofs in the following work for this one instead\<close>

subsection \<open>Proof of correctness\<close>

subsubsection \<open>Assigning an assignment count to priority queues\<close>

definition
  "num_request ns \<equiv> \<lambda>Request u s l \<Rightarrow> s * num_assignments_node l u ns"

definition
  "num_pq ns pq \<equiv> \<Sum>r \<in># pq. num_request ns r"

lemma num_pq_Mempty_eq_0[simp]:
  "num_pq ns {#} = 0"
  unfolding num_pq_def by simp

lemma num_request_alt_def:
  "num_request ns (Request u s l) = s * num_assignments_node l u ns"
  unfolding num_request_def by simp

lemma top_pop_split:
  "pq = add_mset r (pop pq)" if "top pq = Some r"
  using that unfolding pop_def top_def by (auto split: if_split_asm)

lemma num_pq_top_pop_split:
  "num_pq ns pq = num_pq ns (pop pq) + num_request ns r" if "top pq = Some r"
  by (subst top_pop_split, rule that) (simp add: algebra_simps num_pq_def)

lemma top_Min_target:
  assumes "top pq = Some r"
  shows "\<forall>r' \<in># pq. target r \<le> target r'"
  using top_Min[OF assms] by (metis eq_iff less_eq_pq_item_simp less_imp_le pq_item.exhaust_sel)

subsubsection \<open>Correctness of @{term combine_paths}\<close>

text \<open>TODO\<close>

subsubsection \<open>Correctness of @{term bdd_satcount'}}\<close>

lemma forward_pathsE:
  assumes "l \<le> varcount"
  obtains s' pq' where
    "forward_paths pq ptr s l = (s', pq')"
    "num_pq ns pq' + s' = num_pq ns pq + s * num_assignments_ptr l ptr ns"
  using assms
  by (cases ptr rule: ptr_cases; simp add: num_assignments_ptr_alt_def num_pq_def num_request_def)

definition
  "pq_wf ns pq \<equiv> target ` set_mset pq \<subseteq> uid ` set ns
               \<and> (\<forall>r \<in># pq. levels_visited r \<le> label (target r))"

lemma pq_wf_empty_nodes_iff:
  "pq_wf [] pq \<longleftrightarrow> pq = {#}"
  unfolding pq_wf_def by auto

lemma pq_wf_empty:
  "pq_wf ns {#}"
  unfolding pq_wf_def by simp

lemma bdd_eval_ptr_drop_node:
  fixes n :: "('a :: linorder) node"
  assumes "ptr_lb (label (uid n)) ptr"
  shows "bdd_eval_ptr (n # ns) a ptr = bdd_eval_ptr ns a ptr"
  using assms by (cases n; cases ptr; auto simp: ptr_lb_def)

lemma num_assignments_ptr_drop_parent:
  assumes "inc_labels (N i t e # ns)"
  shows "num_assignments_ptr lvl e (N i t e # ns) = num_assignments_ptr lvl e ns"
    and "num_assignments_ptr lvl t (N i t e # ns) = num_assignments_ptr lvl t ns"
  using assms unfolding num_assignments_ptr_def by (simp add: bdd_eval_ptr_drop_node)+

lemma num_assignments_node_drop:
  \<open>num_assignments_node lvl u (N i t e # ns) = num_assignments_node lvl u ns\<close> if \<open>i \<noteq> u\<close>
  using that unfolding num_assignments_node_def by simp

lemma num_pq_drop:
  assumes "\<forall>r \<in># pq. target r \<noteq> i"
  shows "num_pq (N i t e # ns) pq = num_pq ns pq"
proof -
  have "num_request (N i t e # ns) r = num_request ns r" if "r \<in># pq" for r
    unfolding num_request_def using that assms
    by (auto simp: num_assignments_node_drop split: pq_item.splits)
  then show ?thesis
    unfolding num_pq_def by (simp cong: image_mset_cong)
qed

definition nodes_bounded where
  "nodes_bounded ns = (label ` uid ` set ns \<subseteq> {0..<varcount})"

lemma forward_paths_pq_preserves_pq_wf:
  assumes "forward_paths pq ptr s l = (s', pq')" "pq_wf ns pq"
    "case ptr of Node u \<Rightarrow> u \<in> uid ` set ns \<and> l \<le> label u | _ \<Rightarrow> True"
  shows "pq_wf ns pq'"
  using assms by (cases ptr rule: ptr_cases; force simp: pq_wf_def)

lemma pq_wf_pop:
  "pq_wf ns (pop pq)" if "pq_wf ns pq"
  using that unfolding pq_wf_def pop_def by (meson image_subset_iff in_diffD)

lemma bdd_satcount_acc'_correct:
  "bdd_satcount_acc' ns pq s = s + num_pq ns pq"
  if "pq_wf ns pq" "well_formed_nl ns" "nodes_bounded ns"
  using that
proof (induction ns pq s rule: bdd_satcount_acc'.induct)
  case (1 pq racc)
  then show ?case
    by (auto split: option.splits simp: top_eq_None_iff pq_wf_empty_nodes_iff dest: top_in)
next
  case (2 i t e ns pq racc)
  note IH_match = 2(1) and IH_no_match = 2(2)
  show ?case
  proof (cases "top pq")
    case None
    then show ?thesis
      by simp (simp add: top_eq_None_iff)
  next
    case [simp]: (Some r)
    obtain tgt s lvl where [simp]: "r = Request tgt s lvl"
      by (cases r)
    show ?thesis
    proof (cases "tgt = i")
      case [simp]: True
      have bounds: "label i < varcount" "lvl \<le> label i"
        using \<open>nodes_bounded (_ #_)\<close> \<open>pq_wf (_ #_) pq\<close> top_in[OF Some]
        unfolding nodes_bounded_def well_formed_nl_def pq_wf_def
        by auto
      then have "Suc lvl \<le> varcount"
        by simp
      then obtain rt pq'' where rt:
        "forward_paths (pop pq) t s (Suc lvl) = (rt, pq'')"
        "num_pq (N i t e # ns) pq'' + rt =
         num_pq (N i t e # ns) (pop pq) + s * num_assignments_ptr (Suc lvl) t (N i t e # ns)"
        by (rule forward_pathsE[of "Suc lvl" "pop pq" t s "N i t e # ns"])
      from \<open>Suc lvl \<le> _\<close> obtain re pq''' where re:
        "forward_paths pq'' e s (Suc lvl) = (re, pq''')"
        "num_pq (N i t e # ns) pq''' + re =
         num_pq (N i t e # ns) pq'' + s * num_assignments_ptr (Suc lvl) e (N i t e # ns)"
        by (rule forward_pathsE[of "Suc lvl" pq'' e s "N i t e # ns"])
      have "pq_wf (N i t e # ns) pq'''"
        using re(1) rt(1) \<open>pq_wf _ pq\<close> \<open>well_formed_nl (_ # _)\<close> bounds
        by (elim forward_paths_pq_preserves_pq_wf pq_wf_pop)
           (auto 4 4 simp: ptr_lb_def split: ptr.splits
                     dest: inc_labels_if_well_formed_nl closed_if_well_formed_nl)
      moreover have "rt + (re + num_pq (N i t e # ns) pq''') = num_pq (N i t e # ns) pq"
        (is "?l = ?r")
      proof -
        let ?n = "Suc lvl" and ?ns = "(N i t e # ns)"
        have "?l = s * num_assignments_ptr ?n e ?ns + num_pq (N i t e # ns) (pop pq)
                 + s * num_assignments_ptr ?n t ?ns"
          using rt(2) re(2) by simp
        also have "\<dots> = s * (num_assignments_ptr ?n e ?ns + num_assignments_ptr ?n t ?ns)
                      + num_pq (N i t e # ns) (pop pq)"
          by algebra
        also have "\<dots> = s * (num_assignments_ptr ?n e ns + num_assignments_ptr ?n t ns)
                      + num_pq (N i t e # ns) (pop pq)"
          using \<open>well_formed_nl ?ns\<close>
          by (simp del: inc_labels.simps add: num_assignments_ptr_drop_parent)
        also have "\<dots> = s * (num_assignments_node lvl i ?ns) + num_pq (N i t e # ns) (pop pq)"
          using bounds \<open>well_formed_nl (_ # ns)\<close> by (simp add: num_assignments_split)
        also have "\<dots> = ?r"
          by (simp add: num_request_def True num_pq_top_pop_split)
        finally show ?thesis .
      qed
      ultimately show ?thesis
        using \<open>well_formed_nl (_ # ns)\<close> \<open>nodes_bounded (_ # ns)\<close>
        by (subst bdd_satcount_acc'.simps)
           (auto simp del: bdd_satcount_acc'.simps simp add: rt(1) re(1) IH_match)
    next
      case False
      have i_not_in_pq: "\<forall>r \<in># pq. target r \<noteq> i"
      proof -
        from \<open>pq_wf _ pq\<close> Some \<open>r = _\<close> have "tgt \<in> uid ` set (N i t e # ns)"
          by (metis image_subset_iff pq_item.sel(1) pq_wf_def top_in)
        moreover from \<open>well_formed_nl (_ # ns)\<close> have \<open>sorted (N i t e # ns)\<close> ..
        ultimately have "i \<le> tgt"
          apply safe
          subgoal for x
            by (cases x) fastforce
          done
        then show ?thesis
          using top_Min_target[OF Some] False \<open>r = _\<close> by auto
      qed
      have "num_pq (N i t e # ns) pq = num_pq ns pq"
        using i_not_in_pq by (auto intro!: num_pq_drop)
      moreover have "pq_wf ns pq"
        using \<open>pq_wf _ pq\<close> i_not_in_pq
        unfolding pq_wf_def
        by auto
      moreover from \<open>well_formed_nl (_ # ns)\<close> have "well_formed_nl ns" ..
      moreover from \<open>nodes_bounded (_ # ns)\<close> have "nodes_bounded ns"
        unfolding nodes_bounded_def by auto
      ultimately show ?thesis
        using False by (simp add: IH_no_match)
    qed
  qed
qed

theorem bdd_satcount'_correct:
  assumes "well_formed bdd" "case bdd of Nodes ns \<Rightarrow> nodes_bounded ns | _ \<Rightarrow> True"
  shows "bdd_satcount' bdd = num_assignments 0 bdd"
proof (cases bdd rule: bdd_satcount'.cases)
  case [simp]: (3 i t e ns)
  then have "bdd_satcount' bdd = bdd_satcount_acc' ((N i t e) # ns) {# Request i 1 0 #} 0"
    by (subst bdd_satcount_acc'.simps) (simp del: bdd_satcount_acc'.simps add: top_def pop_def)
  also have "\<dots> = num_pq (N i t e # ns) {#Request i 1 0#}"
  proof -
    have "pq_wf (N i t e # ns) {#Request i 1 0#}"
      unfolding pq_wf_def by auto
    then show ?thesis
      using assms by (subst bdd_satcount_acc'_correct; simp)
  qed
  also have "\<dots> = num_assignments_node 0 i (N i t e # ns)"
    by (simp add: num_pq_def num_request_def)
  also have "\<dots> = num_assignments 0 bdd"
    by simp
  finally show ?thesis .
qed (use assms(1) in simp_all)

end (* context fixes varcount :: int *)

end