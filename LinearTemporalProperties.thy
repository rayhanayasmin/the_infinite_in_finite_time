theory LinearTemporalProperties
  imports Main LinearTemporalLogic HOL.Topological_Spaces
begin


definition gk :: \<open>'a infinite_trace set \<Rightarrow> 'a infinite_trace set\<close> where
\<open>gk X \<equiv> infinites (\<up>\<^sub>s ((\<down>\<^sub>d Infinite ` X) \<inter> range Finite))\<close>

definition liveness :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>liveness X = (range Finite \<subseteq> \<down>\<^sub>s Infinite ` X)\<close>

definition morbidity :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>morbidity X = (range Finite \<subseteq> \<down>\<^sub>s Infinite ` (- X))\<close>

definition guarantee :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>guarantee X = (gk X = X)\<close>

definition safety :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>safety X = (gk (-X) = - X)\<close>


lemma gk_subset : \<open>gk P \<subseteq> P\<close>
  unfolding gk_def
proof (rule subsetI)
  fix x assume X: \<open>x \<in> infinites  (\<up>\<^sub>s ((\<down>\<^sub>d Infinite ` P) \<inter> range Finite))\<close>
  show \<open>x \<in> P\<close>
    using infinites_alt_in[THEN iffD1,OF X, simplified extensions_closure_def, simplified]
    by (metis IntE dprefixes_contains_extensions dprefixes_infinite infinites_alt 
              infinites_dprefixes_Infinite infinites_alt_in subset_iff)
qed

lemma gk_idem: \<open>gk (gk P) = gk P\<close> 
proof
  show \<open>gk (gk P) \<subseteq> gk P\<close> by (rule gk_subset)
next
  show \<open>gk (gk P) \<supseteq> gk P\<close>
  unfolding gk_def
  apply (clarsimp simp add: infinites_alt_subset infinites_alt dprefixes_extensions_closure extensions_closure_def)
  apply (rule bexI, simp, clarsimp simp: dprefixes_inter_distrib)
  unfolding dprefixes_def
  using prefix_closure_subset by fastforce
qed

lemma gk_UNIV: \<open>gk UNIV = UNIV\<close> 
  unfolding gk_def
  apply (rule, simp, rule subsetI, simp add: infinites_alt_in)
  by (metis UNIV_I UN_I \<epsilon>_def extensions_closure_def extensions_empty range_eqI)

lemma gk_union: \<open>gk P \<union> gk Q \<subseteq> gk (P \<union> Q)\<close>
  unfolding gk_def
  by (meson Int_mono Un_least Un_upper1 Un_upper2 dprefixes_mono extensions_closure_mono image_mono infinites_alt_subset top.extremum_unique)

lemma infinites_inter: \<open>infinites P \<inter> infinites Q = infinites (P \<inter> Q)\<close>
  by (auto simp add: infinites_alt_in infinites_alt_subset)

lemma gk_mono: \<open>P \<subseteq> Q \<Longrightarrow> gk P \<subseteq> gk Q\<close>
  unfolding gk_def
  by (metis dprefixes_mono dual_order.refl extensions_closure_mono 
            inf_mono infinites_alt infinites_alt_subset infinites_dprefixes_Infinite)

lemma gk_inter: \<open>gk (P \<inter> Q) = gk P \<inter> gk Q\<close>
proof
  show  \<open>gk P \<inter> gk Q \<supseteq> gk (P \<inter> Q)\<close>
    by (simp add: gk_mono)
next
  show \<open>gk P \<inter> gk Q \<subseteq> gk (P \<inter> Q)\<close>
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
      unfolding gk_def
      by (clarsimp simp add: infinites_inter extensions_closure_def infinites_alt_subset 
                             prefixes_extensions[THEN sym])
  qed
qed

lemma gk_Union: \<open>\<Union> (gk ` K) \<subseteq> gk (\<Union> K)\<close>
  unfolding gk_def
  apply (clarsimp simp add: infinites_alt_in extensions_closure_def)
  by (meson IntI Sup_upper dprefixes_mono image_mono range_eqI subsetD)

lemma dprefixes_gk: 
  assumes \<open>Finite x \<in> \<down>\<^sub>d Infinite ` P\<close>
  shows \<open> (\<lambda>i. if i < length x then x ! i else undefined) \<in> gk P\<close>
  using assms unfolding dprefixes_def prefix_closure_def gk_def
  apply clarsimp
  apply (rule infinites_alt_in[THEN iffD2])
  apply (clarsimp simp: extensions_closure_def)
  apply (rule_tac x = \<open>Finite x\<close> in bexI; clarsimp simp: extensions_def)
  by (rule_tac x = \<open>Infinite (\<lambda>_. undefined)\<close> in exI; simp)


lemma safety_guarantee : \<open>safety P \<Longrightarrow> guarantee (- P)\<close>
  unfolding safety_def guarantee_def by blast

lemma guarantee_safety : \<open>guarantee P \<Longrightarrow> safety (- P)\<close>
  unfolding safety_def guarantee_def by simp

lemma morbidity_liveness : \<open>morbidity P \<Longrightarrow> liveness (- P)\<close>
  unfolding liveness_def morbidity_def by simp

lemma liveness_morbidity : \<open>liveness P \<Longrightarrow> morbidity (- P)\<close>
  unfolding liveness_def morbidity_def by simp

lemma gk_guarantee : \<open>guarantee (gk P)\<close>
  unfolding guarantee_def
  using gk_idem gk_def
  by blast

lemma guarantee_Union : 
  assumes \<open>\<forall>S \<in> K. guarantee S\<close>
  shows \<open>guarantee (\<Union> K)\<close>
  unfolding guarantee_def
proof
  show \<open>gk (\<Union> K) \<subseteq> \<Union> K\<close>
    by (rule gk_subset)
next
  from assms show \<open>\<Union> K \<subseteq> gk (\<Union> K)\<close>
    unfolding guarantee_def
    using gk_Union by fast
qed

lemma finite_gk: \<open>Finite x \<in> \<down>\<^sub>d Infinite ` (gk P) \<longleftrightarrow> Finite x \<in> \<down>\<^sub>d Infinite ` P\<close>
  apply (rule iffI)
   apply (rule subsetD, rule dprefixes_mono, rule image_mono, rule gk_subset, simp)
  apply (simp add: infinites_alt dprefixes_inter_distrib gk_def)
   using extensions_closure_def prefix_closure_subset 
  by (fastforce simp: dprefixes_def)

theorem gk_guarantee_greatest: 
  assumes \<open>A \<subseteq> P\<close> and \<open>guarantee A\<close> shows \<open>A \<subseteq> gk P\<close>
  using assms gk_mono guarantee_def by blast

lemma decomposition: "P = gk P \<union> (P - gk P)" 
  using gk_subset by auto

lemma livenessI:
  assumes  \<open>\<And>x. Finite x \<in> \<down>\<^sub>s Infinite ` P\<close>
  shows \<open>liveness P\<close>
  using assms unfolding liveness_def by blast

lemma morbidityI:
  assumes  \<open>\<And>x. Finite x \<in> \<down>\<^sub>s Infinite ` (-P) \<close>
  shows \<open>morbidity P\<close>
  using assms unfolding morbidity_def by auto

lemma morbidity_without_gk: \<open>morbidity (P - gk P)\<close>
proof (rule morbidityI)
  fix x show \<open>Finite x \<in> \<down>\<^sub>s Infinite ` (- (P - gk P))\<close>
  proof (cases \<open>Finite x \<in> \<down>\<^sub>d Infinite ` P\<close>)
    case True
    then show ?thesis by (force simp: prefix_closure_def dest: dprefixes_gk)
  next
    case False 
    then show ?thesis by (force simp: prefix_closure_def intro: non_dprefix) 
  qed
qed


lemma co_alpern_schneider: \<open>\<exists> A B. P = A \<union> B \<and> guarantee A \<and> morbidity B\<close> 
  by (intro exI conjI, rule decomposition, rule gk_guarantee, rule morbidity_without_gk)

lemma alpern_schneider: \<open>\<exists>A B. P = A \<inter> B \<and> safety A \<and> liveness B\<close>
proof -
  obtain A and B where \<open>-P = A \<union> B \<and> guarantee A \<and> morbidity B\<close>
    using co_alpern_schneider by metis
  then show ?thesis
    using guarantee_safety and morbidity_liveness
    by (metis boolean_algebra.de_Morgan_disj double_complement)
qed

definition sc :: \<open>'a infinite_trace set \<Rightarrow> 'a infinite_trace set\<close> where
\<open>sc P = -(gk (-P))\<close>

lemma sc_idem: \<open>sc (sc P) = sc P\<close>
  unfolding sc_def
  by (simp add: gk_idem)

lemma sc_safety: \<open>safety (sc P)\<close>
  unfolding sc_def safety_def
  by (simp add: gk_idem)

lemma sc_least: \<open>P \<subseteq> Q \<Longrightarrow> safety Q \<Longrightarrow> sc P \<subseteq> Q\<close>
  unfolding sc_def safety_def
  using gk_mono by blast

lemma sc_superset: \<open>P \<subseteq> sc P\<close>
  using sc_def gk_subset by blast

lemma sc_mono: \<open>P \<subseteq> Q \<Longrightarrow> sc P \<subseteq> sc Q\<close>
  by (simp add: sc_def gk_mono)

lemma safety_alt: \<open>safety P \<longleftrightarrow> sc P = P\<close>
  using sc_def safety_def by auto

lemma sc_union: \<open>sc (P \<union> Q) = sc P \<union> sc Q\<close>
  by (simp add: sc_def gk_inter)

lemma liveness_dense: \<open>liveness P \<longleftrightarrow> sc P = UNIV\<close>
  unfolding sc_def
proof
  assume \<open>liveness P\<close> then show \<open>- gk (- P) = UNIV\<close>
    by (clarsimp simp: liveness_def gk_def infinites_alt_in extensions_closure_def 
                 intro!: set_eqI
       , smt (z3) UN_iff dprefixes_contains_extensions dprefixes_em dprefixes_infinite 
                  image_iff prefix_closure_def prefixes_extensions range_eqI subsetD)
next
  assume  \<open>- gk (- P) = UNIV\<close> then show \<open>liveness P\<close>
    unfolding liveness_def gk_def
    by (metis Diff_Compl boolean_algebra.conj_cancel_left boolean_algebra.disj_cancel_left 
              boolean_algebra_class.boolean_algebra.compl_unique gk_def morbidity_without_gk morbidity_def 
              inf_top_right)
qed

lemma morbidity_alt: \<open>morbidity P \<longleftrightarrow> gk P = {}\<close>
  by (force simp: liveness_dense sc_def 
            dest: morbidity_liveness 
            intro: liveness_morbidity[where P=\<open>-P\<close>, simplified])

(* redundant proof but this is easier to explain *)
lemma morbidity_without_gk': \<open>morbidity (P - gk P)\<close>
  apply (simp add: morbidity_alt gk_inter Diff_eq)
  using gk_subset by blast

definition good :: \<open>'a finite_trace \<Rightarrow> 'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>good w P = (Finite w \<in> \<down>\<^sub>d Infinite ` P)\<close>

definition bad :: \<open>'a finite_trace \<Rightarrow> 'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>bad w P = good w (-P)\<close>

lemma good_gk_iff : \<open>good w P \<longleftrightarrow> Finite w \<in> \<down>\<^sub>d Infinite ` gk P\<close>
  unfolding good_def
  by (simp add: finite_gk)

lemma bad_gk_iff : \<open>bad w P \<longleftrightarrow> Finite w \<in> \<down>\<^sub>d Infinite ` gk (-P)\<close>
  unfolding bad_def good_def
  by (simp add: finite_gk)


definition ugly :: \<open>'a finite_trace \<Rightarrow> 'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>ugly w P = (\<forall>u. \<not> good (w @ u) P \<and> \<not> bad (w @ u) P)\<close>

definition frontier :: \<open>'a infinite_trace set \<Rightarrow> 'a infinite_trace set\<close> where
\<open>frontier P =  (sc P - gk P)\<close>

lemma frontier_sc: \<open>frontier P = (sc P \<inter> sc (-P))\<close>
  unfolding frontier_def sc_def
  by (simp add: Int_commute Diff_eq)

lemma frontier_neg: \<open>frontier (-P) = frontier P\<close>
  unfolding frontier_sc by auto

theorem ugly_frontier: \<open>ugly w P \<longleftrightarrow> Finite w \<in> \<down>\<^sub>d Infinite ` frontier P\<close>
proof
  assume A0: \<open>ugly w P\<close>
  show \<open>Finite w \<in> \<down>\<^sub>d Infinite ` frontier P\<close>
  proof -
    { fix u have \<open>Finite w \<frown> Infinite u \<notin> Infinite ` gk P\<close>
      proof -
        { fix xa 
          assume A1: \<open>Finite xa \<in> \<down>\<^sub>d Infinite ` P\<close> 
             and A2: \<open>Finite w \<frown> Infinite u \<in> \<up> Finite xa\<close>
          then have \<open>False\<close>
          proof -
            { assume \<open>Finite xa \<in> \<down> Finite w\<close>
              with A0 A1 have ?thesis  
                unfolding ugly_def good_def bad_def
                by (meson dprefixes_contains_extensions prefixes_extensions prefixes_finite subsetD)
            }
            moreover 
            { assume \<open>Finite w \<in> \<down> Finite xa\<close>
              with A0 A1 have ?thesis
                unfolding ugly_def good_def bad_def
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
        then show ?thesis by (clarsimp simp: infinites_alt_in extensions_closure_def gk_def)
      qed
    }
  moreover
    { 
      fix u have \<open>Finite w \<frown> Infinite u \<notin> Infinite ` gk (-P)\<close>
      proof -
        { fix xa 
          assume A1: \<open>Finite xa \<in> \<down>\<^sub>d Infinite ` (-P)\<close> 
             and A2: \<open>Finite w \<frown> Infinite u \<in> \<up> Finite xa\<close>
          then have \<open>False\<close>
          proof -
            { assume \<open>Finite xa \<in> \<down> Finite w\<close>
              with A0 A1 have ?thesis  
                unfolding ugly_def good_def bad_def
                by (meson dprefixes_contains_extensions prefixes_extensions prefixes_finite subsetD)
            }
            moreover 
            { assume \<open>Finite w \<in> \<down> Finite xa\<close>
              with A0 A1 have ?thesis
                unfolding ugly_def good_def bad_def
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
        then show ?thesis by (clarsimp simp: infinites_alt_in extensions_closure_def gk_def)
      qed
    }
    ultimately show ?thesis unfolding frontier_def
      by (auto intro:  definitive_elem_infI simp add: definitive_dprefixes sc_def dprefixes_infinite)
  qed
next
  assume \<open>Finite w \<in> \<down>\<^sub>d Infinite ` frontier P\<close>
  thus \<open>ugly w P\<close> 
  unfolding frontier_def ugly_def good_def bad_def 
  by (clarsimp simp add: dprefixes_inter_distrib sc_def Diff_eq
     , meson dprefixes_contains_extensions finite_gk prefixes_extensions prefixes_finite dprefixes_em subsetD)
qed

(* STRONG MONITORABILITY *)
(* Intuition: Every infinite trace is predicted by a finite prefix to be either 
   in or out of the property. I.e. there is no infinite behaviour that cannot be
   detected by finite monitoring. *)
definition strong_monitorable :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>strong_monitorable P \<longleftrightarrow> frontier P = {}\<close>
(*
lemma strong_monitorable_alt: \<open>strong_monitorable P \<longleftrightarrow> frontier P = {}\<close> 
  unfolding strong_monitorable_def frontier_def
  by blast
*)
(* The strongly monitorable sets are exactly those that are both safety and guarantee properties *)
theorem strong_monitorable_guarantee_safety: 
  shows \<open>strong_monitorable P \<longleftrightarrow> guarantee P \<and> safety P\<close>
proof
  assume \<open>strong_monitorable P\<close>
  then show \<open>guarantee P \<and> safety P\<close>
  unfolding safety_def guarantee_def safety_def strong_monitorable_def frontier_def sc_def
  using gk_subset by auto
next
  assume \<open>guarantee P \<and> safety P\<close>
  then show \<open>strong_monitorable P\<close>
  unfolding guarantee_def safety_def strong_monitorable_def gk_def frontier_def sc_def
  by simp
qed

lemma sc_gk_size_eq[simp]: \<open>sc P \<subseteq> gk P \<longleftrightarrow> sc P = gk P\<close>
  using sc_superset gk_subset by auto


(* Strong monitorability is closed under union, complement, intersection *)
lemma strong_monitorable_union: 
  \<open>strong_monitorable A \<Longrightarrow> strong_monitorable B \<Longrightarrow> strong_monitorable (A \<union> B)\<close>
  unfolding strong_monitorable_def frontier_def
  by (metis diff_shunt_var gk_union sc_gk_size_eq sc_union)

lemma strong_monitorable_neg: 
  \<open>strong_monitorable P \<Longrightarrow> strong_monitorable (-P)\<close>
  unfolding strong_monitorable_def frontier_neg by auto

lemma strong_monitorable_inter: 
  \<open>strong_monitorable A \<Longrightarrow> strong_monitorable B \<Longrightarrow> strong_monitorable (A \<inter> B)\<close>
  using strong_monitorable_neg strong_monitorable_union
  by (metis Compl_Int boolean_algebra_class.boolean_algebra.double_compl)

(* BAUER MONITORABILITY *)
(* Intuition: There is no finite point from which no prediction can ever
   be made. This is Bauer's definition -- no finite ugly prefixes *)
definition bauer_monitorable :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where 
\<open>bauer_monitorable P \<longleftrightarrow> \<down>\<^sub>d Infinite ` frontier P \<inter> range Finite = {}\<close>

lemma bauer_monitorable_alt : \<open>bauer_monitorable P \<longleftrightarrow> gk (frontier P) = {}\<close> 
  unfolding bauer_monitorable_def gk_def
  by (metis dprefixes_empty dprefixes_extensions_closure dprefixes_inter_distrib 
            dprefixes_range_infinite extensions_closure_empty inf_top_right infinites_alt 
            infinites_empty subset_empty)

lemma bauer_monitorable_no_uglies_iff: 
  \<open>bauer_monitorable P \<longleftrightarrow> (\<forall>xs. Finite xs \<notin> \<down>\<^sub>d Infinite ` frontier P)  \<close>
  unfolding bauer_monitorable_def
  by blast

lemma strong_monitorable_bauer_monitorable: 
assumes \<open>strong_monitorable P\<close>
shows \<open>bauer_monitorable P\<close>
  using assms unfolding strong_monitorable_def bauer_monitorable_def 
  by (simp add: dprefixes_empty)

lemma guarantee_bauer_monitorable: \<open>guarantee P \<Longrightarrow> bauer_monitorable P\<close>
  unfolding guarantee_def bauer_monitorable_alt frontier_def
  by (metis Diff_eq Int_commute morbidity_without_gk morbidity_alt sc_def)

lemma safety_bauer_monitorable: \<open>safety P \<Longrightarrow> bauer_monitorable P\<close>
  unfolding safety_def bauer_monitorable_def frontier_def sc_def Diff_eq
  using finite_gk dprefixes_em by (fastforce simp: dprefixes_inter_distrib)

(* As Bauer points out, the above example also serves as a counterexample to show that 
   monitorable P is not just guarantee P \<or> safety P *)

lemma bauer_monitorable_neg: \<open>bauer_monitorable P \<Longrightarrow> bauer_monitorable (-P)\<close>
  unfolding bauer_monitorable_def frontier_sc
  by (simp add: Int_commute)

lemma frontier_trichotomy: 
  \<open>Finite x \<notin> \<down>\<^sub>d Infinite ` frontier P \<longleftrightarrow> 
     (\<exists>ys. Finite (x @ ys)  \<in> \<down>\<^sub>d Infinite ` P 
        \<or>  Finite (x @ ys)  \<in> \<down>\<^sub>d Infinite ` (-P))\<close>
   apply (simp add: ugly_frontier[THEN sym])
  by (simp add: good_def[THEN sym] bad_def[THEN sym] ugly_def)

lemma bauer_monitorable_inter : 
  assumes \<open>bauer_monitorable P\<close> \<open>bauer_monitorable Q\<close> 
  shows \<open>bauer_monitorable (P \<inter> Q)\<close>
proof -
{
  assume nP: \<open>Finite xs \<notin> \<down>\<^sub>d Infinite ` frontier P\<close> for xs
  assume nQ: \<open>Finite xs \<notin> \<down>\<^sub>d Infinite ` frontier Q\<close> for xs
  fix x have \<open>Finite x \<notin> \<down>\<^sub>d Infinite ` frontier (P \<inter> Q)\<close>
  proof -
    have \<open>Finite x \<notin>  \<down>\<^sub>d Infinite ` frontier P\<close> using nP by auto
    then obtain ys 
      where \<open>Finite (x @ ys) \<in> \<down>\<^sub>d Infinite ` P \<or> Finite (x @ ys) \<in> \<down>\<^sub>d Infinite ` (-P)\<close>
      using frontier_trichotomy by auto
    thus ?thesis
    proof (elim disjE)
      assume \<open>Finite (x @ ys) \<in> \<down>\<^sub>d Infinite ` (-P)\<close> thus ?thesis
      unfolding ugly_frontier[THEN sym]  ugly_def bad_def good_def
      by (metis Compl_Int dprefixes_mono image_mono subset_iff sup.cobounded1)
    next      
      assume inP: \<open>Finite (x @ ys) \<in> \<down>\<^sub>d Infinite ` P\<close>
      show ?thesis
      proof -
        have \<open>Finite (x @ ys) \<notin> \<down>\<^sub>d Infinite ` frontier Q\<close> by (simp add: nQ)
        then obtain zs 
          where \<open>Finite (x @ ys @ zs) \<in> \<down>\<^sub>d Infinite ` Q \<or> Finite (x @ ys @ zs) \<in> \<down>\<^sub>d Infinite ` (-Q)\<close>
          using frontier_trichotomy by (metis append.assoc)
        thus ?thesis
        proof (elim disjE) 
          assume \<open>Finite (x @ ys @ zs) \<in> \<down>\<^sub>d Infinite ` (- Q)\<close> thus ?thesis
            unfolding ugly_frontier[THEN sym] ugly_def bad_def good_def
            by (metis Compl_Int Int_commute dprefixes_mono image_mono subset_iff sup.cobounded1)
        next
          from inP have \<open>Finite (x @ ys @ zs) \<in> \<down>\<^sub>d Infinite ` P\<close> 
            using dprefixes_contains_extensions prefixes_extensions prefixes_finite 
            by fastforce
          moreover assume \<open>Finite (x @ ys @ zs) \<in> \<down>\<^sub>d Infinite ` Q\<close>
          ultimately show ?thesis 
            unfolding ugly_frontier[THEN sym] ugly_def bad_def good_def
            using dprefixes_inter_distrib by auto
        qed
      qed
    qed
  qed
} with assms show ?thesis unfolding bauer_monitorable_def by blast
qed

lemma bauer_monitorable_union : \<open>bauer_monitorable P \<Longrightarrow> bauer_monitorable Q \<Longrightarrow> bauer_monitorable (P \<union> Q)\<close>
  using bauer_monitorable_neg bauer_monitorable_inter 
  by (metis Compl_Un boolean_algebra_class.boolean_algebra.double_compl)

definition good_monitorable :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>good_monitorable P \<longleftrightarrow> P = {} \<or> gk P \<noteq> {}\<close>

definition bad_monitorable :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
\<open>bad_monitorable P \<longleftrightarrow> P = UNIV \<or> gk (-P) \<noteq> {}\<close>

lemma good_bad_monitorable_neg: \<open>good_monitorable P \<Longrightarrow> bad_monitorable (-P)\<close>
  unfolding bad_monitorable_def good_monitorable_def by auto

lemma bad_good_monitorable_neg: \<open>bad_monitorable P \<Longrightarrow> good_monitorable (-P)\<close>
  unfolding bad_monitorable_def good_monitorable_def by auto

lemma safety_bad_monitorable: \<open>safety P \<Longrightarrow> bad_monitorable P\<close>
  unfolding safety_def bad_monitorable_def
  by auto

lemma guarantee_good_monitorable: \<open>guarantee P \<Longrightarrow> good_monitorable P\<close>
  unfolding guarantee_def good_monitorable_def
  by auto

lemma good_monitorable_union:
   \<open>good_monitorable P \<Longrightarrow> good_monitorable Q \<Longrightarrow> good_monitorable (P \<union> Q)\<close>
  unfolding good_monitorable_def 
  using gk_mono by blast

lemma bad_monitorable_inter:
   \<open>bad_monitorable P \<Longrightarrow> bad_monitorable Q \<Longrightarrow> bad_monitorable (P \<inter> Q)\<close>
  unfolding bad_monitorable_def 
  using gk_mono by (simp, blast)


definition weak_monitorable :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where 
\<open>weak_monitorable P \<longleftrightarrow> frontier P \<noteq> UNIV\<close>

lemma weak_monitorable_\<epsilon>_ugly_iff: \<open>weak_monitorable P \<longleftrightarrow> \<epsilon> \<notin> \<down>\<^sub>d Infinite ` frontier P\<close>
  unfolding weak_monitorable_def
  by (metis UNIV_I dprefixes_contains_extensions dprefixes_range_infinite 
            extensions_empty infinites_dprefixes_Infinite top.extremum_unique)

lemma monitorable_weak_monitorable: \<open>bauer_monitorable P \<Longrightarrow> weak_monitorable P\<close>
  unfolding bauer_monitorable_def weak_monitorable_\<epsilon>_ugly_iff good_monitorable_def bad_monitorable_def 
            frontier_def \<epsilon>_def
  by blast

lemma weak_monitorable_alt: \<open>weak_monitorable P \<longleftrightarrow> gk P \<union> gk (-P) \<noteq> {}\<close>
  unfolding weak_monitorable_def frontier_def good_monitorable_def bad_monitorable_def
  by (rule iffI,clarsimp simp: sc_def,
      metis Compl_partition Diff_Diff_Int Diff_UNIV sc_def 
            Un_Diff_Int Un_UNIV_right Un_absorb boolean_algebra.compl_one 
            boolean_algebra.disj_conj_distrib double_complement)


lemma weak_monitorable_good_bad: \<open>weak_monitorable P \<longleftrightarrow> good_monitorable P \<or> bad_monitorable P\<close>
proof
  assume \<open>weak_monitorable P\<close> then show \<open>good_monitorable P \<or> bad_monitorable P\<close>
    unfolding frontier_def good_monitorable_def bad_monitorable_def weak_monitorable_alt
    by blast
next
  { assume \<open>good_monitorable P\<close> then have \<open>weak_monitorable P\<close>
    unfolding frontier_def weak_monitorable_alt good_monitorable_def
    by (force simp: gk_UNIV) 
  }
  moreover
  { assume \<open>bad_monitorable P\<close> then have \<open>weak_monitorable P\<close>
    unfolding frontier_def weak_monitorable_alt bad_monitorable_def
    by (force simp: gk_UNIV)
  }
  moreover
  assume \<open>good_monitorable P \<or> bad_monitorable P\<close> 
  ultimately show \<open>weak_monitorable P\<close> by blast
qed

lemma weak_monitorable_neg: \<open>weak_monitorable P \<Longrightarrow> weak_monitorable (-P)\<close>
  unfolding weak_monitorable_alt by auto

(*
   Alpern and Schneider's topology is a metric space. Below is a mechanisation 
   of a proof of that it is at least a Hausdorff space, which is weaker
   than a metric space but doesn't require formalising anything about distances.
   Not anything novel, but it's nice to mechanise the proof, and topology theorems
   might be useful in the future?
   -Liam
 *)

interpretation trace_topology : t2_space \<open>guarantee\<close>
proof
  show \<open>guarantee UNIV\<close> 
    unfolding guarantee_def
    using gk_UNIV by simp
next
  fix S T :: \<open>'a infinite_trace set\<close> 
  assume \<open>guarantee S\<close> and \<open>guarantee T\<close> then show \<open>guarantee (S \<inter> T)\<close>
    unfolding guarantee_def by (metis gk_inter)
next
  fix K :: \<open>'a infinite_trace set set\<close> 
  assume X: \<open>\<forall>S \<in> K. guarantee S\<close> then show \<open>guarantee (\<Union> K)\<close>
    unfolding guarantee_def[THEN sym] 
    using guarantee_Union X by metis
next 
  fix x y :: \<open>'a infinite_trace\<close> assume \<open>x \<noteq> y\<close>
  then obtain i where H: \<open>x i \<noteq> y i\<close> using infinite_trace_differs by auto
  let ?U = \<open>infinites (\<up> Finite (ttake (Suc i) (Infinite x)))\<close>
  let ?V = \<open>infinites (\<up> Finite (ttake (Suc i) (Infinite y)))\<close>
  have \<open>guarantee ?U\<close> 
    by (force  simp: guarantee_def gk_def extensions_closure_def infinites_alt_eq 
                     infinites_alt dprefixes_extensions[OF H] dprefixes_inter_distrib
              intro: set_eqI extensions.dual_order.trans)
  moreover have \<open>guarantee ?V\<close>
    by (force  simp: guarantee_def gk_def extensions_closure_def infinites_alt_eq 
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
  show \<open>\<exists>U V. guarantee U \<and> guarantee V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
    by blast

qed 


(* Show that property is weak monitorable by showing that a 
   particular finite prefix x is good *)
lemma weak_monitorable_goodI: \<open>good x P \<Longrightarrow> weak_monitorable P\<close>
  unfolding weak_monitorable_good_bad good_monitorable_def good_def  
  using dprefixes_gk by blast

(* Show that property is weak monitorable by showing that a 
   particular finite prefix x is bad *)
lemma weak_monitorable_badI: \<open>bad x P \<Longrightarrow> weak_monitorable P\<close>
  unfolding weak_monitorable_good_bad bad_monitorable_def bad_def good_def 
  using dprefixes_gk by blast




(* Show that a property is not Bauer monitorable by showing that 
   some particular finite prefix xs cannot be finitely extended
   to any definitive prefix (for the property or its complement) *)
theorem not_bauer_monitorableI:
  assumes \<open>\<And> ys. Finite (xs @ ys) \<notin> \<down>\<^sub>d Infinite ` P\<close>
      and \<open>\<And> ys. Finite (xs @ ys) \<notin> \<down>\<^sub>d Infinite ` (- P)\<close>
  shows \<open>\<not> bauer_monitorable P\<close>
  unfolding bauer_monitorable_alt frontier_def ugly_frontier[THEN sym] ugly_def good_def bad_def 
  using assms
  by (metis all_not_in_conv dprefixes_empty finite_gk frontier_def frontier_trichotomy image_empty)

(* Show that a property is Bauer monitorable by showing that all
   as-yet-indeterminate finite prefixes xs can be finitely extended 
   to some trace in the (dprefixes of) the property or its negation *)
theorem bauer_monitorableI:
  assumes
    "\<And>xs. Finite xs \<notin> \<down>\<^sub>d Infinite ` P 
       \<Longrightarrow> Finite xs \<notin> \<down>\<^sub>d Infinite ` (-P)
       \<Longrightarrow> \<exists>u. Finite (xs @ u) \<in> \<down>\<^sub>d Infinite ` P \<or>
               Finite (xs @ u) \<in> \<down>\<^sub>d Infinite ` (- P)"
  shows "bauer_monitorable P"
  using assms 
  apply (subst bauer_monitorable_alt [simplified ugly_frontier[THEN sym] ugly_def good_def bad_def, simplified], simp)
  by (metis append_assoc bauer_monitorable_alt bauer_monitorable_no_uglies_iff frontier_trichotomy)

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

(* Prove a property is not guarantee by nominating a particular 
   infinite trace x that IS in the property but no finite prefix
   of it is definitively in the property.

Proof template:
lemma PROP_not_guarantee: \<open>\<not> guarantee (PROP)\<close>
proof (rule not_guaranteeI)
  let ?x = \<open>MY_ITRACE\<close>
  show \<open>?x \<in> PROP\<close>
    sorry
  fix ys assume \<open>Finite ys \<in> \<down> Infinite ?x\<close>
  then show \<open>Finite ys \<notin> \<down>\<^sub>d (Infinite ` PROP)\<close>
    sorry (* likely to use not_dprefix_propI *)
qed
*)

theorem not_guaranteeI :
assumes \<open>x \<in> P\<close> 
and \<open>\<And>ys. Finite ys \<in> \<down> Infinite x \<Longrightarrow> Finite ys \<notin> \<down>\<^sub>d Infinite ` P\<close>
shows \<open>\<not> guarantee P\<close>
proof -
  have \<open>x \<in> P\<close> by (simp add: assms)
  also have \<open>x \<notin> gk P\<close>
    unfolding gk_def using assms 
    by (auto simp add: infinites_alt_in extensions_closure_def prefixes_extensions[THEN sym])
  ultimately have \<open>gk P \<noteq> P\<close> by auto
  thus ?thesis unfolding guarantee_def by simp
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
  also have \<open>x \<notin> gk (-P)\<close>
    unfolding gk_def using assms 
    by (auto simp add: infinites_alt_in extensions_closure_def prefixes_extensions[THEN sym])
  ultimately have \<open>gk (-P) \<noteq> -P\<close> by auto
  thus ?thesis unfolding safety_def by simp
qed

datatype example = pP | pQ | pR

(* A family of properties, Rob i is the property containing all traces
   with i separate states that are {} *)
definition Rob :: \<open>nat \<Rightarrow> example state infinite_trace set\<close> where
 \<open>Rob i = { t | t. (\<exists>X. card X = i \<and> (\<forall> j \<in> X. t j = {}))}  \<close>

(* It is Bauer monitorable as any prefix can be appended with i {} states
   to produce an affirming in the language *)
lemma Rob_bauer_monitorable: \<open>bauer_monitorable (Rob i)\<close> 
proof (rule bauer_monitorableI)
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

lemma Inter_Rob_not_bauer_monitorable: \<open>\<not> bauer_monitorable (\<Inter>{ Rob i | i. True })\<close>
proof (rule not_bauer_monitorableI[where xs = "[]"])
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

lemma phi_not_bauer_monitorable: \<open>\<not> bauer_monitorable \<Phi>\<close>
proof(rule not_bauer_monitorableI)
  let ?xs = \<open>([{pP},{pP}])\<close>
  show \<open>\<And>ys. Finite (?xs @ ys) \<notin> \<down>\<^sub>d Infinite ` \<Phi>\<close>
    by (auto simp: dprefixes_alt itdrop_def)
  show \<open>\<And>ys. Finite (?xs @ ys) \<notin> \<down>\<^sub>d Infinite ` (- \<Phi>)\<close>
    by (auto simp: dprefixes_alt itdrop_def)
qed

lemma psi_bauer_monitorable: \<open>bauer_monitorable \<Psi>\<close>
proof (rule bauer_monitorableI)
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

lemma psi_not_guarantee: \<open>\<not> guarantee \<Psi>\<close>
  proof (rule not_guaranteeI)
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
  using psi_not_guarantee strong_monitorable_guarantee_safety by blast


inductive obligation :: \<open>'a infinite_trace set \<Rightarrow> bool\<close> where
  \<open>safety P \<Longrightarrow> obligation P\<close>
| \<open>guarantee P \<Longrightarrow> obligation P\<close>
| \<open>obligation P \<Longrightarrow> obligation Q \<Longrightarrow> obligation (P \<union> Q)\<close>
| \<open>obligation P \<Longrightarrow> obligation Q \<Longrightarrow> obligation (P \<inter> Q)\<close>

lemma \<open>obligation P \<Longrightarrow> obligation (-P)\<close>
  by (induct rule: obligation.induct, 
      simp_all add: obligation.intros safety_guarantee guarantee_safety)

lemma \<open>obligation P \<Longrightarrow> bauer_monitorable P\<close>
  by (induct rule: obligation.induct,
      simp_all add: safety_bauer_monitorable guarantee_bauer_monitorable 
                    bauer_monitorable_union bauer_monitorable_inter)

lemma obligation_minus_guarantee:\<open>obligation P \<Longrightarrow> guarantee Q \<Longrightarrow> obligation (P - Q) \<close>
  using obligation.intros(1,4)
  by (metis Diff_eq guarantee_safety)

definition make_bm :: \<open>'a infinite_trace set \<Rightarrow> 'a option infinite_trace set\<close> where
  \<open>make_bm P = ((\<circ>) Some ` P)  \<union> {t. \<exists>i. t i = None}\<close>

lemma union_minus_helper: \<open> A \<inter> B = {} \<Longrightarrow> A \<union> B - B = A\<close>
  by auto

lemma make_bm_minus: \<open>make_bm P - {t. \<exists>i. t i = None} = ((\<circ>) Some ` P)\<close>
  unfolding make_bm_def
  apply (rule union_minus_helper)
  by auto

lemma guarantee_part_make_bm: \<open>guarantee {t. \<exists>i. (t :: 'a option infinite_trace) i = None} \<close>
  unfolding guarantee_def
proof 
  show \<open>gk {t. \<exists>i. t i = None} \<subseteq> {t. \<exists>i. t i = None}\<close>
    apply (clarsimp simp: gk_def infinites_alt_in 
                    extensions_closure_def prefixes_extensions[THEN sym] 
                    dprefixes_alt)
   apply (rule ccontr)
   apply (drule_tac x = \<open>\<lambda>_. Some undefined\<close> in spec)
    by (metis diff_zero nth_map_upt option.simps(3) ttake.simps(2) ttake_finite_prefixes)
next
  show \<open>({t. \<exists>i. t i = None} :: 'a option infinite_trace set) \<subseteq> gk {t. \<exists>i. t i = None}\<close>
  proof -
    {
    fix x :: \<open>'a option infinite_trace\<close>
    fix i :: nat 
    assume \<open>x i = None\<close>
    then have \<open>x \<in> gk {t. \<exists>i. t i = None}\<close>
      apply (clarsimp simp: gk_def infinites_alt_in 
                      extensions_closure_def prefixes_extensions[THEN sym]
                      dprefixes_alt)
      apply (rule_tac x = \<open>Finite (ttake (Suc i) (Infinite x))\<close> in bexI)
       apply (metis prefixes_append ttake_tdrop)
      apply clarsimp
      apply (rule_tac x = i in exI)
      apply clarsimp
      by (metis diff_zero length_map length_upt nth_append_length)
    }
    thus ?thesis by blast
  qed
qed

lemma make_bm_bauer_monitorable: \<open>bauer_monitorable (make_bm P)\<close>
  apply (rule bauer_monitorableI)
  apply (rule_tac x = \<open>[None]\<close> in exI)
  apply (rule disjI1)
  apply (simp add: make_bm_def)
  apply (rule dprefix_propI)
  apply simp
  apply (rule disjI2)
  by (meson lessI nth_append_length)

lemma obligation_smaller_than_bm:
  assumes \<open>\<not> obligation ((\<circ>) Some ` P)\<close>
  shows \<open>bauer_monitorable (make_bm P) \<and> \<not> obligation (make_bm P)\<close>
proof -
  have \<open>bauer_monitorable (make_bm P)\<close> by (rule make_bm_bauer_monitorable)
  moreover
  have \<open>\<not> obligation (make_bm P)\<close>
    apply (rule notI)
    apply (drule obligation_minus_guarantee[where Q = \<open>{t. \<exists>i. t i = None}\<close>])
    apply (rule guarantee_part_make_bm)
    by (simp add: make_bm_minus assms)
  ultimately show ?thesis by auto
qed

end