theory LinearTemporalProperties
  imports Main LinearTemporalLogic HOL.Topological_Spaces
begin


definition cS :: \<open>'a infinite_trace set \<Rightarrow> 'a infinite_trace set\<close> where
\<open>cS X \<equiv> infinites (\<up>\<^sub>s ((\<down>\<^sub>d Infinite ` X) \<inter> range Finite))\<close>


definition liveness :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>liveness X = (range Finite \<subseteq> \<down>\<^sub>s Infinite ` X)\<close>

definition coliveness :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>coliveness X = (range Finite \<subseteq> \<down>\<^sub>s Infinite ` (- X))\<close>

definition cosafety :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>cosafety X = (infinites (\<up>\<^sub>s ((\<down>\<^sub>d Infinite ` X) \<inter> range Finite)) = X)\<close>

definition safety :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>safety X = (infinites (\<up>\<^sub>s ((\<down>\<^sub>d Infinite ` (- X)) \<inter> range Finite)) = - X)\<close>


lemma cosafety_alt:
\<open>cosafety X = (cS X = X)\<close>
  unfolding cosafety_def cS_def by simp


lemma safety_alt:
\<open>safety X = (cS (-X) = (-X))\<close>
  unfolding safety_def cS_def by simp

lemma cS_subset : \<open>cS P \<subseteq> P\<close>
  unfolding cS_def
proof (rule subsetI)
  fix x assume X: \<open>x \<in> infinites  (\<up>\<^sub>s ((\<down>\<^sub>d Infinite ` P) \<inter> range Finite))\<close>
  show \<open>x \<in> P\<close>
    using infinites_alt_in[THEN iffD1,OF X, simplified extensions_closure_def, simplified]
    by (metis IntE dprefixes_contains_extensions dprefixes_infinite infinites_alt 
              infinites_dprefixes_Infinite infinites_alt_in subset_iff)
qed

lemma cS_idem: \<open>cS (cS P) = cS P\<close> 
proof
  show \<open>cS (cS P) \<subseteq> cS P\<close> by (rule cS_subset)
next
  show \<open>cS (cS P) \<supseteq> cS P\<close>
  unfolding cS_def
  apply (clarsimp simp add: infinites_alt_subset infinites_alt dprefixes_extensions_closure extensions_closure_def)
  apply (rule bexI, simp, clarsimp simp: dprefixes_inter_distrib)
  unfolding dprefixes_def
  using prefix_closure_subset by fastforce
qed

lemma cS_UNIV: \<open>cS UNIV = UNIV\<close> 
  unfolding cS_def
  apply (rule, simp, rule subsetI, simp add: infinites_alt_in)
  by (metis UNIV_I UN_I \<epsilon>_def extensions_closure_def extensions_empty range_eqI)

lemma cS_union: \<open>cS P \<union> cS Q \<subseteq> cS (P \<union> Q)\<close>
  unfolding cS_def
  by (meson Int_mono Un_least Un_upper1 Un_upper2 dprefixes_mono extensions_closure_mono image_mono infinites_alt_subset top.extremum_unique)

lemma infinites_inter: \<open>infinites P \<inter> infinites Q = infinites (P \<inter> Q)\<close>
  by (auto simp add: infinites_alt_in infinites_alt_subset)

lemma cS_mono: \<open>P \<subseteq> Q \<Longrightarrow> cS P \<subseteq> cS Q\<close>
  unfolding cS_def
  by (metis dprefixes_mono dual_order.refl extensions_closure_mono 
            inf_mono infinites_alt infinites_alt_subset infinites_dprefixes_Infinite)

lemma cS_inter': \<open>cS P \<inter> cS Q \<supseteq> cS (P \<inter> Q)\<close>
  by (simp add: cS_mono)

lemma cS_inter: \<open>cS P \<inter> cS Q \<subseteq> cS (P \<inter> Q)\<close>
proof -
  { fix xb xe inf 
    assume \<open>Finite xb \<in> \<down> Infinite inf\<close>
     and \<open>Finite xe \<in> \<down> Infinite inf\<close>
     and \<open>Finite xb \<in> \<down>\<^sub>d Infinite ` P\<close>
     and \<open>Finite xe \<in> \<down>\<^sub>d Infinite ` Q\<close>
    note A = this have \<open>\<exists>x\<in>\<down>\<^sub>d (Infinite ` P \<inter> Infinite ` Q) \<inter> range Finite. x \<in> \<down> Infinite inf\<close>
    proof -
      { assume \<open>Finite xe \<in> \<down> Finite xb\<close> with A have ?thesis
          apply (rule_tac x = \<open>Finite xb\<close> in bexI, simp)
          apply (clarsimp simp: dprefixes_inter_distrib)
          using dprefixes_contains_extensions prefixes_extensions by blast
      }
      also 
      { assume \<open>Finite xb \<in> \<down> Finite xe\<close> with A have ?thesis
          apply (rule_tac x = \<open>Finite xe\<close> in bexI, simp)
          apply (clarsimp simp: dprefixes_inter_distrib)
          using dprefixes_contains_extensions prefixes_extensions by blast 
      }
      ultimately show ?thesis using A prefixes_directed by blast
    qed
  }
  then show ?thesis
  unfolding cS_def
  by (clarsimp simp add: infinites_inter extensions_closure_def infinites_alt_subset 
                         prefixes_extensions[THEN sym])
qed

lemma cS_inter_eq: \<open>cS (P \<inter> Q) = cS P \<inter> cS Q\<close>
  using cS_inter cS_inter' by blast

lemma cS_Union: \<open>\<Union> (cS ` K) \<subseteq> cS (\<Union> K)\<close>
  unfolding cS_def
  apply (clarsimp simp add: infinites_alt_in extensions_closure_def)
  by (meson IntI Sup_upper dprefixes_mono image_mono range_eqI subsetD)

lemma dprefixes_cS: 
  assumes \<open>Finite x \<in> \<down>\<^sub>d Infinite ` P\<close>
  shows \<open> (\<lambda>i. if i < length x then x ! i else undefined) \<in> cS P\<close>
  using assms unfolding dprefixes_def prefix_closure_def cS_def
  apply clarsimp
  apply (rule infinites_alt_in[THEN iffD2])
  apply (clarsimp simp: extensions_closure_def)
  apply (rule_tac x = \<open>Finite x\<close> in bexI; clarsimp simp: extensions_def)
  by (rule_tac x = \<open>Infinite (\<lambda>_. undefined)\<close> in exI; simp)


lemma safety_cosafety : \<open>safety P \<Longrightarrow> cosafety (- P)\<close>
  unfolding safety_def cosafety_def by blast

lemma cosafety_safety : \<open>cosafety P \<Longrightarrow> safety (- P)\<close>
  unfolding safety_def cosafety_def by simp

lemma coliveness_liveness : \<open>coliveness P \<Longrightarrow> liveness (- P)\<close>
  unfolding liveness_def coliveness_def by simp

lemma liveness_coliveness : \<open>liveness P \<Longrightarrow> coliveness (- P)\<close>
  unfolding liveness_def coliveness_def by simp

lemma cS_cosafety : \<open>cosafety (cS P)\<close>
  unfolding cosafety_def
  using cS_idem cS_def
  by blast

lemma cosafety_Union : 
  assumes \<open>\<forall>S \<in> K. cosafety S\<close>
  shows \<open>cosafety (\<Union> K)\<close>
  unfolding cosafety_alt 
proof
  show \<open>cS (\<Union> K) \<subseteq> \<Union> K\<close>
    by (rule cS_subset)
next
  from assms show \<open>\<Union> K \<subseteq> cS (\<Union> K)\<close>
    unfolding cosafety_alt 
    using cS_Union by fast
qed

lemma finite_cS: \<open>Finite x \<in> \<down>\<^sub>d Infinite ` (cS P) \<longleftrightarrow> Finite x \<in> \<down>\<^sub>d Infinite ` P\<close>
  apply (rule iffI)
   apply (rule subsetD, rule dprefixes_mono, rule image_mono, rule cS_subset, simp)
  apply (simp add: infinites_alt dprefixes_inter_distrib cS_def)
   using extensions_closure_def prefix_closure_subset 
  by (fastforce simp: dprefixes_def)

theorem cS_cosafety_greatest: 
  assumes \<open>A \<subseteq> P\<close> and \<open>cosafety A\<close> shows \<open>A \<subseteq> cS P\<close>
  using assms cS_mono cosafety_alt by blast

lemma comp: "P = cS P \<union> (P - cS P)" 
  using cS_subset by auto

lemma livenessI:
  assumes  \<open>\<And>x. Finite x \<in> \<down>\<^sub>s Infinite ` P\<close>
  shows \<open>liveness P\<close>
  using assms unfolding liveness_def by blast

lemma colivenessI:
  assumes  \<open>\<And>x. Finite x \<in> \<down>\<^sub>s Infinite ` (-P) \<close>
  shows \<open>coliveness P\<close>
  using assms unfolding coliveness_def by auto


lemma colive: \<open>coliveness (P - cS P)\<close>
proof (rule colivenessI)
  fix x show \<open>Finite x \<in> \<down>\<^sub>s Infinite ` (- (P - cS P))\<close>
  proof (cases \<open>Finite x \<in> \<down>\<^sub>d Infinite ` P\<close>)
    case True
    then show ?thesis by (force simp: prefix_closure_def dest: dprefixes_cS)
  next
    case False 
    then show ?thesis by (force simp: prefix_closure_def intro: non_dprefix) 
  qed
qed


lemma co_alpern_schneider: \<open>\<exists> A B. P = A \<union> B \<and> cosafety A \<and> coliveness B\<close> 
  by (intro exI conjI, rule comp, rule cS_cosafety, rule colive)

lemma alpern_schneider: \<open>\<exists>A B. P = A \<inter> B \<and> safety A \<and> liveness B\<close>
proof -
  obtain A and B where \<open>-P = A \<union> B \<and> cosafety A \<and> coliveness B\<close>
    using co_alpern_schneider by metis
  then show ?thesis
    using cosafety_safety and coliveness_liveness
    by (metis boolean_algebra.de_Morgan_disj double_complement)
qed

definition S :: \<open>'a infinite_trace set \<Rightarrow> 'a infinite_trace set\<close> where
\<open>S P = -(cS (-P))\<close>

lemma S_idem: \<open>S (S P) = S P\<close>
  unfolding S_def
  by (simp add: cS_idem)

lemma S_safety: \<open>safety (S P)\<close>
  unfolding S_def safety_alt
  by (simp add: cS_idem)

lemma S_least: \<open>P \<subseteq> Q \<Longrightarrow> safety Q \<Longrightarrow> S P \<subseteq> Q\<close>
  unfolding S_def safety_alt
  using cS_mono by blast

lemma S_subset: \<open>P \<subseteq> S P\<close>
  using S_def cS_subset by blast

lemma S_mono: \<open>P \<subseteq> Q \<Longrightarrow> S P \<subseteq> S Q\<close>
  by (simp add: S_def cS_mono)

lemma safety_alt_S: \<open>safety P \<longleftrightarrow> S P = P\<close>
  using S_def safety_alt by auto

lemma liveness_alt_S: \<open>liveness P \<longleftrightarrow> S P = UNIV\<close>
  unfolding S_def
proof
  assume \<open>liveness P\<close> then show \<open>- cS (- P) = UNIV\<close>
    by (clarsimp simp: liveness_def cS_def infinites_alt_in extensions_closure_def 
                 intro!: set_eqI
       , smt (z3) UN_iff dprefixes_contains_extensions dprefixes_em dprefixes_infinite 
                  image_iff prefix_closure_def prefixes_extensions range_eqI subsetD)
next
  assume  \<open>- cS (- P) = UNIV\<close> then show \<open>liveness P\<close>
    unfolding liveness_def cS_def
    by (metis Diff_Compl boolean_algebra.conj_cancel_left boolean_algebra.disj_cancel_left 
              boolean_algebra_class.boolean_algebra.compl_unique cS_def colive coliveness_def 
              inf_top_right)
qed

lemma coliveness_alt: \<open>coliveness P \<longleftrightarrow> cS P = {}\<close>
  by (force simp: liveness_alt_S S_def 
            dest: coliveness_liveness 
            intro: liveness_coliveness[where P=\<open>-P\<close>, simplified])

(* redundant proof but this is easier to explain *)
lemma colive': \<open>coliveness (P - cS P)\<close>
  apply (simp add: coliveness_alt cS_inter_eq Diff_eq)
  using cS_subset by blast

definition good :: \<open>'a finite_trace \<Rightarrow> 'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>good w P = (Finite w \<in> \<down>\<^sub>d Infinite ` P)\<close>


definition bad :: \<open>'a finite_trace \<Rightarrow> 'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>bad w P = good w (-P)\<close>

lemma good_cos : \<open>good w P \<longleftrightarrow> Finite w \<in> \<down>\<^sub>d Infinite ` cS P\<close>
  unfolding good_def
  by (simp add: finite_cS)

lemma bad_cos : \<open>bad w P \<longleftrightarrow> Finite w \<in> \<down>\<^sub>d Infinite ` cS (-P)\<close>
  unfolding bad_def good_def
  by (simp add: finite_cS)



definition bauer_ugly :: \<open>'a finite_trace \<Rightarrow> 'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>bauer_ugly w P = (\<forall>u. \<not> good (w @ u) P \<and> \<not> bad (w @ u) P)\<close>

definition uglies :: \<open>'a infinite_trace set \<Rightarrow> 'a trace set\<close> where
\<open>uglies P = \<down>\<^sub>d Infinite ` (- (cS P \<union> cS (-P)))\<close>

lemma S_uglies: \<open>uglies P = \<down>\<^sub>d Infinite ` (S P \<inter> S (-P))\<close>
  unfolding uglies_def S_def
  by (simp add: Int_commute)

lemma uglies_alt: \<open>uglies P = \<down>\<^sub>d Infinite ` (S P - cS P)\<close>
  unfolding uglies_def S_def
  by (simp add: Diff_eq Int_commute)

lemma uglies_forwards: 
  assumes ugly: \<open>bauer_ugly w P\<close> 
  shows \<open>Finite w \<in> uglies P\<close>
proof -
  { fix u have \<open>Finite w \<frown> Infinite u \<notin> Infinite ` cS P\<close>
    proof -
      { fix xa 
        assume A1: \<open>Finite xa \<in> \<down>\<^sub>d Infinite ` P\<close> 
           and A2: \<open>Finite w \<frown> Infinite u \<in> \<up> Finite xa\<close>
        then have \<open>False\<close>
        proof -
          { assume \<open>Finite xa \<in> \<down> Finite w\<close>
            with A1 ugly have ?thesis  
              unfolding bauer_ugly_def good_def bad_def
              by (meson dprefixes_contains_extensions prefixes_extensions prefixes_finite subsetD)
          }
          moreover 
          { assume \<open>Finite w \<in> \<down> Finite xa\<close>
            with A1 ugly have ?thesis
              unfolding bauer_ugly_def good_def bad_def
              by (metis prefixes_finite)
          }
          moreover
          have \<open>Finite xa \<in> \<down> Finite w \<frown> Infinite u\<close>
            using A2 prefixes_extensions by blast
          moreover
          have \<open>Finite w \<in> \<down> Finite w \<frown> Infinite u\<close>
            by (simp add: prefixes_def, metis Traces.append.simps(1))
        ultimately show ?thesis
          using prefixes_directed by blast
        qed 
      } 
      then show ?thesis by (clarsimp simp: infinites_alt_in extensions_closure_def cS_def)
    qed
  }
  moreover
  { 
    fix u have \<open>Finite w \<frown> Infinite u \<notin> Infinite ` cS (-P)\<close>
      proof -
      { fix xa 
        assume A1: \<open>Finite xa \<in> \<down>\<^sub>d Infinite ` (-P)\<close> 
           and A2: \<open>Finite w \<frown> Infinite u \<in> \<up> Finite xa\<close>
        then have \<open>False\<close>
        proof -
          { assume \<open>Finite xa \<in> \<down> Finite w\<close>
            with A1 ugly have ?thesis  
              unfolding bauer_ugly_def good_def bad_def
              by (meson dprefixes_contains_extensions prefixes_extensions prefixes_finite subsetD)
          }
          moreover 
          { assume \<open>Finite w \<in> \<down> Finite xa\<close>
            with A1 ugly have ?thesis
              unfolding bauer_ugly_def good_def bad_def
              by (metis prefixes_finite)
          }
          moreover
          have \<open>Finite xa \<in> \<down> Finite w \<frown> Infinite u\<close>
            using A2 prefixes_extensions by blast
          moreover
          have \<open>Finite w \<in> \<down> Finite w \<frown> Infinite u\<close>
            by (simp add: prefixes_def, metis Traces.append.simps(1))
        ultimately show ?thesis
          using prefixes_directed by blast
        qed 
      } 
      then show ?thesis by (clarsimp simp: infinites_alt_in extensions_closure_def cS_def)
    qed
  }
  ultimately
  show ?thesis unfolding uglies_def
    by (auto intro:  definitive_elem_infI simp add: definitive_dprefixes dprefixes_infinite)
qed

lemma uglies_backwards: 
assumes \<open>Finite w \<in> uglies P\<close>
shows \<open>bauer_ugly w P\<close> 
  using assms  unfolding uglies_def bauer_ugly_def good_def bad_def 
  by (clarsimp simp add: dprefixes_inter_distrib
     , meson dprefixes_contains_extensions finite_cS prefixes_extensions prefixes_finite dprefixes_em subsetD)

lemma uglies: \<open>bauer_ugly w P \<longleftrightarrow> Finite w \<in> uglies P\<close>
  using uglies_forwards uglies_backwards by auto

(* STRONG MONITORABILITY *)
(* Intuition: Every infinite trace is predicted by a finite prefix to be either 
   in or out of the property. I.e. there is no infinite behaviour that cannot be
   detected by finite monitoring. *)
definition strong_monitorable :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>strong_monitorable P \<longleftrightarrow> (cS P \<union> cS (-P) = UNIV)\<close>

lemma strong_monitorable_alt: \<open>strong_monitorable P \<longleftrightarrow> uglies P = {}\<close> 
  unfolding strong_monitorable_def uglies_def
  apply (rule iffI)
   apply (simp add: dprefixes_empty)
  by (metis Compl_UNIV_eq boolean_algebra_class.boolean_algebra.compl_eq_compl_iff infinites_dprefixes_Infinite infinites_empty)

(* The strongly monitorable sets are exactly those that are both safety and cosafety properties *)

theorem strong_monitorable_cosafety_safety: 
  shows \<open>strong_monitorable P \<longleftrightarrow> cosafety P \<and> safety P\<close>
proof
  assume \<open>strong_monitorable P\<close>
  then show \<open>cosafety P \<and> safety P\<close>
  unfolding safety_alt cosafety_alt safety_def strong_monitorable_def
  using cS_subset by auto
next
  assume \<open>cosafety P \<and> safety P\<close>
  then show \<open>strong_monitorable P\<close>
  unfolding cosafety_def safety_def strong_monitorable_def cS_def
  by simp
qed

(* Strong monitorability is closed under union, complement, intersection *)

lemma strong_monitorable_union: 
  \<open>strong_monitorable A \<Longrightarrow> strong_monitorable B \<Longrightarrow> strong_monitorable (A \<union> B)\<close>
  unfolding strong_monitorable_def
  apply (clarsimp, rule Orderings.antisym, simp)
  using subset_trans[OF _ Un_mono[OF cS_union cS_inter]]
  by blast

lemma strong_monitorable_neg: 
  \<open>strong_monitorable P \<Longrightarrow> strong_monitorable (-P)\<close>
  unfolding strong_monitorable_def by auto

lemma strong_monitorable_inter: 
  \<open>strong_monitorable A \<Longrightarrow> strong_monitorable B \<Longrightarrow> strong_monitorable (A \<inter> B)\<close>
  using strong_monitorable_neg strong_monitorable_union
  by (metis Compl_Int boolean_algebra_class.boolean_algebra.double_compl)

(* BAUER MONITORABILITY *)
(* Intuition: There is no finite point from which no prediction can ever
   be made. This is Bauer's definition -- no finite ugly prefixes *)
definition monitorable :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where 
\<open>monitorable P \<longleftrightarrow> uglies P \<inter> range Finite = {}\<close>

lemma strong_monitorable_monitorable: \<open>strong_monitorable P \<Longrightarrow> monitorable P\<close>
  unfolding strong_monitorable_alt monitorable_def by simp

(*
to see why monitorable is not as strong as strong_monitorable, think of 
the property P = ((p \<or> q) U r) \<or> G p
--- an infinite trace ppp.. is in P but not cS(P) as no finite prefix of ps is good
--- an infinite trace qqq.. is not in P but is not in cS(-P) as no finite prefix of qs is bad
--- The set of uglies therefore contains these two infinite traces, but none of 
--- their prefixes are definitive.
--- Therefore, while there are no finite ugly prefixes for this property (bauer monitorable), 
--- there are infinite ugly prefixes. Therefore this property is monitorable but not 
--- strongly monitorable.
*) 

lemma cosafety_monitorable: \<open>cosafety P \<Longrightarrow> monitorable P\<close>
  unfolding cosafety_alt monitorable_def uglies_def
  using finite_cS dprefixes_em by (fastforce simp: dprefixes_inter_distrib)

lemma safety_monitorable: \<open>safety P \<Longrightarrow> monitorable P\<close>
  unfolding safety_alt monitorable_def uglies_def
  using finite_cS dprefixes_em by (fastforce simp: dprefixes_inter_distrib)

(* As Bauer points out, the above example also serves as a counterexample to show that 
   monitorable P is not just cosafety P \<or> safety P *)

lemma monitorable_neg: \<open>monitorable P \<Longrightarrow> monitorable (-P)\<close>
  unfolding monitorable_def uglies_def
  by (simp add: Int_commute)

lemma not_ugly_means_good_or_bad : \<open>Finite x \<notin> uglies P \<longleftrightarrow> (\<exists>ys. Finite (x @ ys)  \<in> \<down>\<^sub>d Infinite ` P \<or>  Finite (x @ ys)  \<in> \<down>\<^sub>d Infinite ` (-P))\<close>
   apply (simp add: uglies[THEN sym])
  by (simp add: good_def[THEN sym] bad_def[THEN sym] bauer_ugly_def)

lemma monitorable_inter : 
  assumes \<open>monitorable P\<close> \<open>monitorable Q\<close> 
  shows \<open>monitorable (P \<inter> Q)\<close>
proof -
{
  assume nP: \<open>Finite xs \<notin> uglies P\<close> for xs
  assume nQ: \<open>Finite xs \<notin> uglies Q\<close> for xs
  fix x have \<open>Finite x \<notin> uglies (P \<inter> Q)\<close>
  proof -
    have \<open>Finite x \<notin> uglies P\<close> using nP by auto
    then obtain ys 
      where \<open>Finite (x @ ys) \<in> \<down>\<^sub>d Infinite ` P \<or> Finite (x @ ys) \<in> \<down>\<^sub>d Infinite ` (-P)\<close>
      using not_ugly_means_good_or_bad by auto
    thus ?thesis
    proof (elim disjE)
      assume \<open>Finite (x @ ys) \<in> \<down>\<^sub>d Infinite ` (-P)\<close> thus ?thesis
      unfolding uglies[THEN sym]  bauer_ugly_def bad_def good_def
      by (metis Compl_Int dprefixes_mono image_mono subset_iff sup.cobounded1)
    next      
      assume inP: \<open>Finite (x @ ys) \<in> \<down>\<^sub>d Infinite ` P\<close>
      show ?thesis
      proof -
        have \<open>Finite (x @ ys) \<notin> uglies Q\<close> by (simp add: nQ)
        then obtain zs 
          where \<open>Finite (x @ ys @ zs) \<in> \<down>\<^sub>d Infinite ` Q \<or> Finite (x @ ys @ zs) \<in> \<down>\<^sub>d Infinite ` (-Q)\<close>
          using not_ugly_means_good_or_bad by (metis append.assoc)
        thus ?thesis
        proof (elim disjE) 
          assume \<open>Finite (x @ ys @ zs) \<in> \<down>\<^sub>d Infinite ` (- Q)\<close> thus ?thesis
            unfolding uglies[THEN sym] bauer_ugly_def bad_def good_def
            by (metis Compl_Int Int_commute dprefixes_mono image_mono subset_iff sup.cobounded1)
        next
          from inP have \<open>Finite (x @ ys @ zs) \<in> \<down>\<^sub>d Infinite ` P\<close> 
            using dprefixes_contains_extensions prefixes_extensions prefixes_finite 
            by fastforce
          moreover assume \<open>Finite (x @ ys @ zs) \<in> \<down>\<^sub>d Infinite ` Q\<close>
          ultimately show ?thesis 
            unfolding uglies[THEN sym] bauer_ugly_def bad_def good_def
            using dprefixes_inter_distrib by auto
        qed
      qed
    qed
  qed
} with assms show ?thesis unfolding monitorable_def by blast
qed

lemma monitorable_union : \<open>monitorable P \<Longrightarrow> monitorable Q \<Longrightarrow> monitorable (P \<union> Q)\<close>
  using monitorable_neg monitorable_inter 
  by (metis Compl_Un boolean_algebra_class.boolean_algebra.double_compl)

 
(* While Bauer monitorability is closed under complement (see above), it fails to 
be closed under union (nor intersection) for the same reason that definitive prefixes
are not closed under union. If A and B have no finite ugly prefixes, that does not mean
that A union B will have no finite ugly prefixes. *)

(* WEAK MONITORABILITY *)
(* Intution: There exists at least one finite trace that gives definitive answers. *)

definition good_monitorable :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>good_monitorable P \<longleftrightarrow> P = {} \<or> cS P \<noteq> {}\<close>

definition bad_monitorable :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>bad_monitorable P \<longleftrightarrow> P = UNIV \<or> cS (-P) \<noteq> {}\<close>

lemma good_bad_monitorable_neg: \<open>good_monitorable P \<Longrightarrow> bad_monitorable (-P)\<close>
  unfolding bad_monitorable_def good_monitorable_def by auto

lemma bad_good_monitorable_neg: \<open>bad_monitorable P \<Longrightarrow> good_monitorable (-P)\<close>
  unfolding bad_monitorable_def good_monitorable_def by auto

lemma safety_bad_monitorable: \<open>safety P \<Longrightarrow> bad_monitorable P\<close>
  unfolding safety_alt bad_monitorable_def
  by auto

lemma cosafety_good_monitorable: \<open>cosafety P \<Longrightarrow> good_monitorable P\<close>
  unfolding cosafety_alt good_monitorable_def
  by auto

lemma good_monitorable_union:
   \<open>good_monitorable P \<Longrightarrow> good_monitorable Q \<Longrightarrow> good_monitorable (P \<union> Q)\<close>
  unfolding good_monitorable_def 
  using cS_mono by blast


(* Good monitorability is not necessarily closed under intersection.

   For example, consider the properties P = X a \<or> G b and Q = X (not a). 
   Their intersection is G b, leaving no good prefixes,
   yet they each have good prefixes.  *)

lemma bad_monitorable_inter:
   \<open>bad_monitorable P \<Longrightarrow> bad_monitorable Q \<Longrightarrow> bad_monitorable (P \<inter> Q)\<close>
  unfolding bad_monitorable_def 
  using cS_mono by (simp, blast)

(* Bad monitorability is not closed under union as good monitorability is not closed 
   under intersection *)

definition weak_monitorable :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where 
\<open>weak_monitorable P \<longleftrightarrow> \<epsilon> \<notin> uglies P\<close>

lemma monitorable_weak_monitorable: \<open>monitorable P \<Longrightarrow> weak_monitorable P\<close>
  unfolding monitorable_def weak_monitorable_def good_monitorable_def bad_monitorable_def 
            uglies_alt \<epsilon>_def
  by blast

(* To see why weak_monitorable is not as strong as bauer monitorable, consider the property
   P = G(F b) \<or> X a

   This property is weakly monitorable as CoS(P) includes "a...", but it is not bauer
   monitorable as, for example, "b" is an ugly prefix.
*)

lemma weak_monitorable_alt: \<open>weak_monitorable P \<longleftrightarrow> cS P \<union> cS (-P) \<noteq> {}\<close>
  unfolding weak_monitorable_def uglies_alt good_monitorable_def bad_monitorable_def
  by (rule iffI,clarsimp simp: S_def,
      metis Compl_partition Diff_Diff_Int Diff_UNIV S_def 
            Un_Diff_Int Un_UNIV_right Un_absorb boolean_algebra.compl_one 
            boolean_algebra.disj_conj_distrib definitive_contains_extensions
            definitive_dprefixes double_complement dprefixes_range_infinite 
            extensions_empty infinites_dprefixes_Infinite top.extremum_unique)


lemma weak_monitorable_good_bad: \<open>weak_monitorable P \<longleftrightarrow> good_monitorable P \<or> bad_monitorable P\<close>
proof
  assume \<open>weak_monitorable P\<close> then show \<open>good_monitorable P \<or> bad_monitorable P\<close>
    unfolding uglies_def good_monitorable_def bad_monitorable_def weak_monitorable_alt
    by blast
next
  { assume \<open>good_monitorable P\<close> then have \<open>weak_monitorable P\<close>
    unfolding uglies_def weak_monitorable_alt good_monitorable_def
    by (force simp: cS_UNIV) 
  }
  moreover
  { assume \<open>bad_monitorable P\<close> then have \<open>weak_monitorable P\<close>
    unfolding uglies_def weak_monitorable_alt bad_monitorable_def
    by (force simp: cS_UNIV)
  }
  moreover
  assume \<open>good_monitorable P \<or> bad_monitorable P\<close> 
  ultimately show \<open>weak_monitorable P\<close> by blast
qed

lemma weak_monitorable_neg: \<open>weak_monitorable P \<Longrightarrow> weak_monitorable (-P)\<close>
  unfolding weak_monitorable_alt by auto

(* Weak monitorability is not closed under union nor intersection for the same 
   reason that Good/bad monitorability aren't. *)

(*
   Alpern and Schneider's topology is a metric space. Below is a mechanisation 
   of a proof of that it is at least a Hausdorff space, which is weaker
   than a metric space but doesn't require formalising anything about distances.
   Not anything novel, but it's nice to mechanise the proof, and topology theorems
   might be useful in the future?
   -Liam
 *)

interpretation trace_topology : t2_space \<open>cosafety\<close>
proof
  show \<open>cosafety UNIV\<close> 
    unfolding cosafety_alt
    using cS_UNIV by simp
next
  fix S T :: \<open>'a infinite_trace set\<close> 
  assume \<open>cosafety S\<close> and \<open>cosafety T\<close> then show \<open>cosafety (S \<inter> T)\<close>
    unfolding cosafety_alt
    by (metis cS_subset cS_inter subset_antisym)
next
  fix K :: \<open>'a infinite_trace set set\<close> 
  assume X: \<open>\<forall>S \<in> K. cosafety S\<close> then show \<open>cosafety (\<Union> K)\<close>
    unfolding cosafety_alt[THEN sym] 
    using cosafety_Union X by metis
next 
  fix x y :: \<open>'a infinite_trace\<close> assume \<open>x \<noteq> y\<close>
  then obtain i where H: \<open>x i \<noteq> y i\<close> using infinite_trace_differs by auto
  let ?U = \<open>infinites (\<up> Finite (ttake (Suc i) (Infinite x)))\<close>
  let ?V = \<open>infinites (\<up> Finite (ttake (Suc i) (Infinite y)))\<close>
  have \<open>cosafety ?U\<close> 
    by (force  simp: cosafety_def extensions_closure_def infinites_alt_eq 
                     infinites_alt dprefixes_extensions[OF H] dprefixes_inter_distrib
              intro: set_eqI extensions.dual_order.trans)
  moreover have \<open>cosafety ?V\<close>
    by (force  simp: cosafety_def extensions_closure_def infinites_alt_eq 
                     infinites_alt dprefixes_extensions[OF H] dprefixes_inter_distrib
              intro: set_eqI extensions.dual_order.trans)
  moreover have \<open>x \<in> ?U\<close>
    by (simp del: ttake.simps add: infinites_alt_in,
        metis prefixes_append prefixes_extensions ttake_tdrop)
  moreover have \<open>y \<in> ?V\<close>
    by (simp del: ttake.simps add: infinites_alt_in,
        metis prefixes_append prefixes_extensions ttake_tdrop)
  moreover have \<open>?U \<inter> ?V = {}\<close>
    by (clarsimp intro!: set_eqI simp: infinites_alt_in, 
        metis H last_snoc length_append_singleton length_map prefixes_extensions 
              ttake_finite_prefixes)
  ultimately
  show \<open>\<exists>U V. cosafety U \<and> cosafety V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
    by blast
qed 


(* Show that property is weak monitorable by showing that a 
   particular finite prefix x is good *)
lemma weak_monitorable_goodI: \<open>good x P \<Longrightarrow> weak_monitorable P\<close>
  unfolding weak_monitorable_good_bad good_monitorable_def good_def  
  using dprefixes_cS by blast

(* Show that property is weak monitorable by showing that a 
   particular finite prefix x is bad *)
lemma weak_monitorable_badI: \<open>bad x P \<Longrightarrow> weak_monitorable P\<close>
  unfolding weak_monitorable_good_bad bad_monitorable_def bad_def good_def 
  using dprefixes_cS by blast


lemma monitorable_alt: \<open>monitorable P \<longleftrightarrow> (\<forall>xs. Finite xs \<notin> uglies P)  \<close>
  unfolding monitorable_def
  by blast



(* Show that a property is not Bauer monitorable by showing that 
   some particular finite prefix xs cannot be finitely extended
   to any definitive prefix (for the property or its complement) *)
theorem not_monitorableI:
  assumes \<open>\<And> ys. Finite (xs @ ys) \<notin> \<down>\<^sub>d Infinite ` P\<close>
      and \<open>\<And> ys. Finite (xs @ ys) \<notin> \<down>\<^sub>d Infinite ` (- P)\<close>
  shows \<open>\<not> monitorable P\<close>
  unfolding monitorable_alt uglies[THEN sym] bauer_ugly_def good_def bad_def 
  using assms by blast

(* Show that a property is Bauer monitorable by showing that all
   as-yet-indeterminate finite prefixes xs can be finitely extended 
   to some trace in the (dprefixes of) the property or its negation *)
theorem monitorableI:
  assumes
    "\<And>xs. Finite xs \<notin> \<down>\<^sub>d Infinite ` P 
       \<Longrightarrow> Finite xs \<notin> \<down>\<^sub>d Infinite ` (-P)
       \<Longrightarrow> \<exists>u. Finite (xs @ u) \<in> \<down>\<^sub>d Infinite ` P \<or>
               Finite (xs @ u) \<in> \<down>\<^sub>d Infinite ` (- P)"
  shows "monitorable P"
  using assms 
  apply (subst monitorable_alt [simplified uglies[THEN sym] bauer_ugly_def good_def bad_def, simplified], simp)
  by fastforce

(* Show a particular prefix is definitive for a property P by showing 
   that all extensions satisfy P *)
theorem dprefix_propI:
assumes \<open>\<And>zs. xs \<frown> Infinite zs \<in> Infinite ` P\<close>
shows \<open>xs \<in> \<down>\<^sub>d Infinite ` P\<close>
  using assms
  unfolding dprefixes_alt
  by blast

(* Show a particular prefix is not definitive for a property P by showing 
   that a particular infinite extension violates P
   best used with rule_tac or a [where zs = ..].
*)
theorem not_dprefix_propI :
assumes \<open>xs \<frown> Infinite zs \<in> Infinite ` (-P)\<close>
shows \<open>xs \<notin> \<down>\<^sub>d Infinite ` P\<close>
  using assms
  unfolding dprefixes_alt
  by (metis (no_types, lifting) ComplD Infinite_helper infinite_append_right  mem_Collect_eq)

(* Prove a property is not cosafety by nominating a particular 
   infinite trace x that IS in the property but no finite prefix
   of it is definitively in the property.

Proof template:
lemma PROP_not_cosafety: \<open>\<not> cosafety (PROP)\<close>
proof (rule not_cosafetyI)
  let ?x = \<open>MY_ITRACE\<close>
  show \<open>?x \<in> PROP\<close>
    sorry
  fix ys assume \<open>Finite ys \<in> \<down> Infinite ?x\<close>
  then show \<open>Finite ys \<notin> \<down>\<^sub>d (Infinite ` PROP)\<close>
    sorry (* likely to use not_dprefix_propI *)
qed
*)

theorem not_cosafetyI :
assumes \<open>x \<in> P\<close> 
and \<open>\<And>ys. Finite ys \<in> \<down> Infinite x \<Longrightarrow> Finite ys \<notin> \<down>\<^sub>d Infinite ` P\<close>
shows \<open>\<not> cosafety P\<close>
proof -
  have \<open>x \<in> P\<close> by (simp add: assms)
  also have \<open>x \<notin> cS P\<close>
    unfolding cS_def using assms 
    by (auto simp add: infinites_alt_in extensions_closure_def prefixes_extensions[THEN sym])
  ultimately have \<open>cS P \<noteq> P\<close> by auto
  thus ?thesis unfolding cosafety_alt by simp
qed


(* Prove a property is not safety by nominating a particular 
   infinite trace x that IS NOT in the property but no finite prefix
   of it is definitively not in the property.

Proof template:
lemma PROP_not_safety: \<open>\<not> safety (PROP)\<close>
proof (rule not_safetyI)
  let ?x = \<open>MY_ITRACE\<close>
  show \<open>?x \<in> - PROP\<close>
    sorry
  fix ys assume \<open>Finite ys \<in> \<down> Infinite ?x\<close>
  then show \<open>Finite ys \<notin> \<down>\<^sub>d (Infinite ` (- PROP))\<close>
    sorry (* likely to use not_dprefix_propI *)
qed
*)

theorem not_safetyI :
assumes \<open>x \<in> -P\<close> 
and \<open>\<And>ys. Finite ys \<in> \<down> Infinite x \<Longrightarrow> Finite ys \<notin> \<down>\<^sub>d Infinite ` (-P)\<close>
shows \<open>\<not> safety P\<close>
proof -
  have \<open>x \<in> -P\<close> using assms by simp
  also have \<open>x \<notin> cS (-P)\<close>
    unfolding cS_def using assms 
    by (auto simp add: infinites_alt_in extensions_closure_def prefixes_extensions[THEN sym])
  ultimately have \<open>cS (-P) \<noteq> -P\<close> by auto
  thus ?thesis unfolding safety_alt by simp
qed

datatype example = pP | pQ | pR

(* A family of properties, Rob i is the property containing all traces
   with i separate states that are {} *)
definition Rob :: \<open>nat \<Rightarrow> example state infinite_trace set\<close> where
 \<open>Rob i = { t | t. (\<exists>X. card X = i \<and> (\<forall> j \<in> X. t j = {}))}  \<close>

(* It is monitorable as any prefix can be appended with i {} states
   to produce an affirming in the language *)
lemma Rob_monitorable: \<open>monitorable (Rob i)\<close> 
proof (rule monitorableI)
  fix xs
  let ?y = \<open>replicate i {}\<close>
  have \<open>Finite (xs @ ?y) \<in> \<down>\<^sub>d Infinite ` Rob i\<close>
    unfolding Rob_def
    apply (rule dprefix_propI)
    apply clarsimp
    apply (rule_tac x = \<open>{length xs..<length xs + i}\<close> in exI)
    using le_Suc_ex by fastforce
  thus \<open>\<exists>u. Finite (xs @ u) \<in> \<down>\<^sub>d Infinite ` Rob i \<or>
            Finite (xs @ u) \<in> \<down>\<^sub>d Infinite ` (- Rob i)\<close>
    by blast
qed

lemma Rob_prop: \<open>x \<in> \<Inter>{ Rob i | i. True } \<longleftrightarrow> (\<forall>i. \<exists>X. card X = i \<and> (\<forall> j \<in> X. x j = {})) \<close>
  unfolding Rob_def
  by auto

lemma Rob_limit: \<open>\<Inter>{ Rob i | i. True } = { t | t. (\<exists>X. infinite X \<and> (\<forall> j \<in> X. t j = {}))}\<close>
proof -
  { fix t :: \<open>example state infinite_trace\<close> and X :: \<open>nat set\<close> and i 
    assume \<open>infinite X\<close> and \<open>\<forall>j\<in>X. t j = {}\<close>
    then have \<open>\<exists>X'. card X' = i \<and> (\<forall>j\<in>X'. t j = {})\<close>
      by (meson infinite_arbitrarily_large subset_eq)
  }
  moreover (* have to use axiom of choice *)
  { fix t :: \<open>example state infinite_trace\<close> 
    define F :: \<open>nat \<Rightarrow> nat set\<close> where
      \<open>F = (\<lambda>i. (SOME X. (card X = i \<and> (\<forall>j\<in>X. t j = {}))))\<close>
    assume *: \<open>\<exists>X. card X = i \<and> (\<forall>j\<in>X. t j = {})\<close> for i
    then have \<open>card (F i) = i\<close> for i
      by (simp add: F_def, rule someI2_ex, auto)
    then have \<open>inj F\<close>
      by (force intro: injI dest: arg_cong[where f = card])
    then have \<open>infinite (\<Union>i. F i)\<close> 
      by (force simp: inj_def dest: finite_UnionD finite_imageD)
    moreover from * have \<open>\<forall>j\<in>(\<Union>i. F i). t j = {}\<close>
      apply (simp add: F_def)
      apply (rule allI, rule someI2_ex)
      by auto
    ultimately have \<open>\<exists>X'. infinite X' \<and> (\<forall>j\<in>X'. t j = {})\<close>
      by auto
  }
  ultimately
  show ?thesis
    apply (intro set_eqI, simp only: Rob_prop)
    by auto
qed

lemma Inter_Rob_not_monitorable: \<open>\<not> monitorable (\<Inter>{ Rob i | i. True })\<close>
proof (rule not_monitorableI[where xs = "[]"])
  fix ys 
  show \<open>Finite ys \<notin> \<down>\<^sub>d Infinite ` \<Inter> {Rob i |i. True}\<close>
    unfolding Rob_limit
    apply (rule not_dprefix_propI[where zs = \<open>\<lambda>_. {undefined}\<close>])
    using finite_nat_set_iff_bounded by auto[1]
  show \<open>Finite ys \<notin> \<down>\<^sub>d Infinite ` (- \<Inter> {Rob i |i. True})\<close>
    unfolding Rob_limit
    apply (rule not_dprefix_propI[where zs = \<open>\<lambda>_. {}\<close>])
    using infinite_Ici[where a = \<open>length ys\<close>] by fastforce
qed

definition \<Phi> :: \<open>example state infinite_trace set\<close> where
[simp]: \<open>\<Phi> = \<lbrakk>(G\<^sub>l F\<^sub>l prop\<^sub>l(pP)) or\<^sub>l X\<^sub>l prop\<^sub>l(pQ)\<rbrakk>\<^sub>l T\<close>

definition \<Psi> :: \<open>example state infinite_trace set\<close> where
[simp]: \<open>\<Psi> =  \<lbrakk>(prop\<^sub>l(pP) or\<^sub>l prop\<^sub>l(pQ)) U\<^sub>l prop\<^sub>l(pR) or\<^sub>l G\<^sub>l prop\<^sub>l(pP) \<rbrakk>\<^sub>l T\<close>

lemma phi_weak_monitorable: \<open>weak_monitorable \<Phi>\<close>
proof (rule weak_monitorable_goodI)
  let ?x = \<open>([{pQ},{pQ},{}])\<close>
  show \<open>good ?x \<Phi>\<close>
    by (simp add: good_def dprefixes_alt itdrop_def)
qed

lemma phi_not_bauer_monitorable: \<open>\<not> monitorable \<Phi>\<close>
proof(rule not_monitorableI)
  let ?xs = \<open>([{pP},{pP}])\<close>
  show \<open>\<And>ys. Finite (?xs @ ys) \<notin> \<down>\<^sub>d Infinite ` \<Phi>\<close>
    by (auto simp: dprefixes_alt itdrop_def)
  show \<open>\<And>ys. Finite (?xs @ ys) \<notin> \<down>\<^sub>d Infinite ` (- \<Phi>)\<close>
    by (auto simp: dprefixes_alt itdrop_def)
qed

lemma psi_bauer_monitorable: \<open>monitorable \<Psi>\<close>
proof (rule monitorableI)
  fix xs
  assume A[THEN notE]: \<open>Finite xs \<notin> \<down>\<^sub>d Infinite ` \<Psi>\<close>
     and B[THEN notE]: \<open>Finite xs \<notin> \<down>\<^sub>d Infinite ` (-\<Psi>)\<close>
  {
    fix i assume \<open>i < length xs\<close> then have \<open>xs ! i \<noteq> {} \<and> pR \<notin> xs ! i\<close>
    proof (induct i rule: less_induct)
      case (less x)
      then show ?case 
        apply (intro notI conjI)
         apply (rule B[OF dprefix_propI])
         apply (clarsimp simp add: itdrop_def)
         apply (smt (verit, ccfv_SIG) empty_iff linorder_neqE_nat)
        apply (rule A[OF dprefix_propI])
        apply (simp add: itdrop_def)
        by (metis (full_types) ex_in_conv example.exhaust)
    qed
  }
  then show \<open>\<exists>u. Finite (xs @ u) \<in> \<down>\<^sub>d Infinite ` \<Psi> \<or>
                 Finite (xs @ u) \<in> \<down>\<^sub>d Infinite ` (- \<Psi>)\<close>
    apply (rule_tac x=\<open>[{pR}]\<close> in exI)
    apply (rule disjI1)
    apply (rule dprefix_propI)
    apply (simp add:  itdrop_def)
    apply (rule disjI1)
    apply (rule_tac x=\<open>length xs\<close> in exI)
    by (metis ex_in_conv example.exhaust insertI1 lessI nth_append nth_append_length)
qed

lemma psi_not_cosafety: \<open>\<not> cosafety \<Psi>\<close>
  proof (rule not_cosafetyI)
  let ?x = \<open>\<lambda> _. {pP}\<close>
  show \<open>?x \<in> \<Psi>\<close>
    by (simp add: itdrop_def)
  fix ys assume \<open>Finite ys \<in> \<down> Infinite ?x\<close>
  then have \<open>i < length ys ==> ys ! i = {pP}\<close> for i
    by (clarsimp simp: prefixes_def; metis length_map nth_map ttake.simps(2) ttake_simp)
  then show \<open>Finite ys \<notin> \<down>\<^sub>d (Infinite ` \<Psi>)\<close>
    by (auto intro!: not_dprefix_propI simp: itdrop_def dprefix_propI)
qed

lemma psi_not_safety: \<open>\<not> safety \<Psi>\<close>
proof (rule not_safetyI)
  let ?x = \<open>\<lambda> _. {pQ}\<close>
  show \<open>?x \<in> - \<Psi>\<close>
    by (simp add: itdrop_def)
  fix ys assume \<open>Finite ys \<in> \<down> Infinite ?x\<close>
  then have \<open>i < length ys ==> ys ! i = {pQ}\<close> for i
    by (clarsimp simp add: prefixes_def; metis length_map nth_map ttake.simps(2) ttake_simp)
  then show \<open>Finite ys \<notin> \<down>\<^sub>d (Infinite ` (- \<Psi>))\<close>
    by (force intro!: not_dprefix_propI simp: itdrop_def dprefix_propI)
qed

lemma \<open>\<not> strong_monitorable \<Psi>\<close>
  using psi_not_cosafety strong_monitorable_cosafety_safety by blast


inductive obligation :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
  \<open>safety P \<Longrightarrow> obligation P\<close>
| \<open>cosafety P \<Longrightarrow> obligation P\<close>
| \<open>obligation P \<Longrightarrow> obligation Q \<Longrightarrow> obligation (P \<union> Q)\<close>
| \<open>obligation P \<Longrightarrow> obligation Q \<Longrightarrow> obligation (P \<inter> Q)\<close>

lemma \<open>obligation P \<Longrightarrow> obligation (-P)\<close>
  by (induct rule: obligation.induct, 
      simp_all add: obligation.intros safety_cosafety cosafety_safety)

lemma \<open>obligation P \<Longrightarrow> monitorable P\<close>
  by (induct rule: obligation.induct,
      simp_all add: safety_monitorable cosafety_monitorable monitorable_union monitorable_inter)


end