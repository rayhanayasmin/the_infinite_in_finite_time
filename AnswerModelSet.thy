theory AnswerModelSet
  imports Main Traces
begin

section \<open>Answer Model Set\<close>

typedecl 'a state
consts L :: "'a state => 'a set"
datatype answer = T | F
type_synonym 'a AsF = "answer \<Rightarrow> 'a set"

fun and_AsF :: "'a AsF \<Rightarrow> 'a AsF \<Rightarrow> 'a AsF" (infixl "\<and>\<sqdot>" 60) where
"(a \<and>\<sqdot> b) T = a T \<inter> b T"|
"(a \<and>\<sqdot> b) F = a F \<union> b F"

fun or_AsF :: "'a AsF \<Rightarrow> 'a AsF \<Rightarrow> 'a AsF" (infixl "\<or>\<sqdot>" 59) where
"(a \<or>\<sqdot> b) T = a T \<union> b T"|
"(a \<or>\<sqdot> b) F = a F \<inter> b F"

fun not_AsF :: "'a AsF \<Rightarrow> 'a AsF" ("\<not>\<sqdot> _") where
"(\<not>\<sqdot> a) T = a F"|
"(\<not>\<sqdot> a) F = a T"

fun univ_AsF :: "'a AsF" ("T\<bullet>") where
"T\<bullet> T = UNIV"|
"T\<bullet> F = {}"

fun satisfying_AsF :: "'a \<Rightarrow> 'a state AsF" ("sat\<bullet>") where
"sat\<bullet> x T = {state. x \<in> L state}" |
"sat\<bullet> x F = {state. x \<notin> L state}"

section \<open>Propositional logic\<close>

datatype (atoms_plogic: 'a) plogic =
    True_plogic                               ("true\<^sub>p")
  | Prop_plogic 'a                            ("prop\<^sub>p'(_')")
  | Not_plogic "'a plogic"                    ("not\<^sub>p _" [85] 85)
  | Or_plogic  "'a plogic" "'a plogic"        ("_ or\<^sub>p _" [82,82] 81)
  | And_plogic "'a plogic" "'a plogic"        ("_ and\<^sub>p _" [82,82] 81)

fun plogic_semantics :: "'a plogic \<Rightarrow> 'a state AsF" ("\<lbrakk>_\<rbrakk>\<^sub>p") where
"\<lbrakk> true\<^sub>p    \<rbrakk>\<^sub>p = T\<bullet>"|
"\<lbrakk> not\<^sub>p \<phi>   \<rbrakk>\<^sub>p = \<not>\<sqdot> \<lbrakk>\<phi>\<rbrakk>\<^sub>p"|
"\<lbrakk> prop\<^sub>p(a) \<rbrakk>\<^sub>p = sat\<bullet> a"|
"\<lbrakk> \<phi> or\<^sub>p \<psi>  \<rbrakk>\<^sub>p = \<lbrakk>\<phi>\<rbrakk>\<^sub>p \<or>\<sqdot> \<lbrakk>\<psi>\<rbrakk>\<^sub>p"|
"\<lbrakk> \<phi> and\<^sub>p \<psi> \<rbrakk>\<^sub>p = \<lbrakk>\<phi>\<rbrakk>\<^sub>p \<and>\<sqdot> \<lbrakk>\<psi>\<rbrakk>\<^sub>p"

definition false_p ("false\<^sub>p") where
false_p_def [simp]: "false\<^sub>p = not\<^sub>p true\<^sub>p"

definition implies_p :: "'a plogic \<Rightarrow> 'a plogic \<Rightarrow> 'a plogic" ("_ implies\<^sub>p _" [81,81] 80)  where
implies_p_def[simp]: "\<phi> implies\<^sub>p \<psi> = (not\<^sub>p \<phi> or\<^sub>p \<psi>)"

section \<open>Propositional logic lemmas\<close>

lemma AsF_cases:  
  assumes "A T = B T" and "A F = B F"
  shows "A = B"
proof (rule ext)
  fix x show "A x = B x" by (cases x; simp add: assms) 
qed

lemma or_and_negation[simp]: "\<lbrakk> \<phi> or\<^sub>p \<psi> \<rbrakk>\<^sub>p = \<lbrakk> not\<^sub>p ((not\<^sub>p \<phi>) and\<^sub>p (not\<^sub>p \<psi>)) \<rbrakk>\<^sub>p"
  by (rule AsF_cases; simp)

lemma and_or_negation[simp]: "\<lbrakk> \<phi> and\<^sub>p \<psi>\<rbrakk>\<^sub>p = \<lbrakk> not\<^sub>p ((not\<^sub>p \<phi>) or\<^sub>p (not\<^sub>p \<psi>)) \<rbrakk>\<^sub>p"
  by (rule AsF_cases; simp)

lemma de_morgan_1[simp]: "\<lbrakk> not\<^sub>p (\<phi> and\<^sub>p \<psi>) \<rbrakk>\<^sub>p = \<lbrakk> (not\<^sub>p \<phi>) or\<^sub>p (not\<^sub>p \<psi>) \<rbrakk>\<^sub>p"
  by (rule AsF_cases; simp)

lemma de_morgan_2[simp]: "\<lbrakk> not\<^sub>p (\<phi> or\<^sub>p \<psi>)  \<rbrakk>\<^sub>p = \<lbrakk> (not\<^sub>p \<phi>) and\<^sub>p (not\<^sub>p \<psi>) \<rbrakk>\<^sub>p"
  by (rule AsF_cases; simp)

section \<open>Propositional logic equivalence\<close>

fun plogic_semantics' :: "'a state \<Rightarrow> 'a plogic \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>p" 60) where
"\<Gamma> \<Turnstile>\<^sub>p true\<^sub>p = True" |
"\<Gamma> \<Turnstile>\<^sub>p not\<^sub>p \<phi> = (\<not> \<Gamma> \<Turnstile>\<^sub>p \<phi>)"|
"\<Gamma> \<Turnstile>\<^sub>p prop\<^sub>p(a) = (a \<in> L \<Gamma>)"|
"\<Gamma> \<Turnstile>\<^sub>p \<phi> or\<^sub>p \<psi> = (\<Gamma> \<Turnstile>\<^sub>p \<phi> \<or> \<Gamma> \<Turnstile>\<^sub>p \<psi>)"|
"\<Gamma> \<Turnstile>\<^sub>p \<phi> and\<^sub>p \<psi> = (\<Gamma> \<Turnstile>\<^sub>p \<phi> \<and> \<Gamma> \<Turnstile>\<^sub>p \<psi>)"

lemma plogic_equivalence:
  shows "(  \<Gamma>  \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> \<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>p T)" 
  and   "(\<not> \<Gamma>  \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> \<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>p F)"
proof (induct \<phi>)
qed (auto)

section \<open>Linear temporal logic\<close>

datatype (atoms_ltl: 'a) ltl =
      True_ltl                             ("true\<^sub>l")
    | Not_ltl "'a ltl"                     ("not\<^sub>l _" [85] 85)
    | Prop_ltl 'a                          ("prop\<^sub>l'(_')")
    | Or_ltl "'a ltl" "'a ltl"             ("_ or\<^sub>l _" [82,82] 81)
    | And_ltl "'a ltl" "'a ltl"            ("_ and\<^sub>l _" [82,82] 81)
    | Next_ltl "'a ltl"                    ("X\<^sub>l _" [88] 87)
    | Until_ltl "'a ltl" "'a ltl"          ("_ U\<^sub>l  _" [84,84] 83)

fun lsatisfying_AsF :: "'a \<Rightarrow> 'a state infinite_trace AsF" ("lsat\<bullet>") where
"lsat\<bullet> x T = {t. x \<in> L (t 0)}" |
"lsat\<bullet> x F = {t. x \<notin> L (t 0)}"

fun x_operator :: "'a infinite_trace AsF \<Rightarrow> 'a infinite_trace AsF" ("X\<sqdot>") where
"X\<sqdot> t T = {x | x. itdrop 1 x \<in> (t T)}"|
"X\<sqdot> t F = {x | x. itdrop 1 x \<in> (t F)}"

fun u_operator :: "'a infinite_trace AsF \<Rightarrow> 'a infinite_trace AsF \<Rightarrow> 'a infinite_trace AsF" (infix "U\<sqdot>" 61) where
"(a U\<sqdot> b) T = {x | x. \<exists>k. (\<forall>i<k. itdrop i x \<in> (a T)) \<and> itdrop k x \<in> (b T)}"|
"(a U\<sqdot> b) F = {x | x. \<forall>k. (\<exists>i<k. itdrop i x \<in> (a F)) \<or> itdrop k x \<in> (b F)}"

fun ltl_semantics :: "'a ltl \<Rightarrow> 'a state infinite_trace AsF" ("\<lbrakk>_\<rbrakk>\<^sub>l") where
"\<lbrakk> true\<^sub>l    \<rbrakk>\<^sub>l = T\<bullet>"|
"\<lbrakk> not\<^sub>l \<phi>   \<rbrakk>\<^sub>l = \<not>\<sqdot> \<lbrakk> \<phi> \<rbrakk>\<^sub>l"|
"\<lbrakk> prop\<^sub>l(a) \<rbrakk>\<^sub>l = lsat\<bullet> a"|
"\<lbrakk> \<phi> or\<^sub>l \<psi>  \<rbrakk>\<^sub>l = \<lbrakk> \<phi> \<rbrakk>\<^sub>l \<or>\<sqdot> \<lbrakk> \<psi> \<rbrakk>\<^sub>l"|
"\<lbrakk> \<phi> and\<^sub>l \<psi> \<rbrakk>\<^sub>l = \<lbrakk> \<phi> \<rbrakk>\<^sub>l \<and>\<sqdot> \<lbrakk> \<psi> \<rbrakk>\<^sub>l"|
"\<lbrakk> X\<^sub>l \<phi>     \<rbrakk>\<^sub>l = X\<sqdot> \<lbrakk> \<phi> \<rbrakk>\<^sub>l"|
"\<lbrakk> \<phi> U\<^sub>l \<psi>   \<rbrakk>\<^sub>l = \<lbrakk> \<phi> \<rbrakk>\<^sub>l U\<sqdot> \<lbrakk> \<psi> \<rbrakk>\<^sub>l"

lemma excluded_middle_ltl' : 
  shows "(\<Gamma> \<notin> \<lbrakk>\<phi>\<rbrakk>\<^sub>l T) \<longleftrightarrow> (\<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>l F)"
  and   "(\<Gamma> \<notin> \<lbrakk>\<phi>\<rbrakk>\<^sub>l F) \<longleftrightarrow> (\<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>l T)"
proof (induct \<phi> arbitrary: \<Gamma>)
qed auto

lemma excluded_middle_ltl: "\<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>l T \<or> \<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>l F"
  using excluded_middle_ltl' by blast

definition false_ltl ("false\<^sub>l") where
  [simp]: "false\<^sub>l = not\<^sub>l true\<^sub>l"

definition implies_ltl :: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" (infix "implies\<^sub>l" 80)  where
  [simp]: "\<phi> implies\<^sub>l \<psi> = (not\<^sub>l \<phi> or\<^sub>l \<psi>)"

definition final_ltl :: "'a ltl \<Rightarrow> 'a ltl" ("F\<^sub>l _") where
  [simp]: "(F\<^sub>l \<phi>) = (true\<^sub>l U\<^sub>l \<phi>)"

definition global_ltl :: "'a ltl \<Rightarrow> 'a ltl" ("G\<^sub>l _") where
  [simp]: "(G\<^sub>l \<phi>) = (not\<^sub>l F\<^sub>l (not\<^sub>l \<phi>))"

section \<open>Linear temporal logic equivalence\<close>

fun ltl_semantics' :: "'a state infinite_trace \<Rightarrow> 'a ltl \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>l" 60) where
"\<Gamma> \<Turnstile>\<^sub>l true\<^sub>l    = True"|
"\<Gamma> \<Turnstile>\<^sub>l not\<^sub>l \<phi>   = (\<not> \<Gamma> \<Turnstile>\<^sub>l \<phi>)"|
"\<Gamma> \<Turnstile>\<^sub>l prop\<^sub>l(a) = (a \<in> L (\<Gamma> 0))"|
"\<Gamma> \<Turnstile>\<^sub>l \<phi> or\<^sub>l \<psi>  = (\<Gamma> \<Turnstile>\<^sub>l \<phi> \<or> \<Gamma> \<Turnstile>\<^sub>l \<psi>)"|
"\<Gamma> \<Turnstile>\<^sub>l \<phi> and\<^sub>l \<psi> = (\<Gamma> \<Turnstile>\<^sub>l \<phi> \<and> \<Gamma> \<Turnstile>\<^sub>l \<psi>)"|
"\<Gamma> \<Turnstile>\<^sub>l (X\<^sub>l \<phi>)   = itdrop 1 \<Gamma> \<Turnstile>\<^sub>l \<phi>"|
"\<Gamma> \<Turnstile>\<^sub>l (\<phi> U\<^sub>l \<psi>) = (\<exists>k. (\<forall>i<k. itdrop i \<Gamma> \<Turnstile>\<^sub>l \<phi>) \<and> itdrop k \<Gamma> \<Turnstile>\<^sub>l \<psi>)"


section \<open>Linear temporal logic lemmas\<close>
lemma \<open>\<lbrakk> F\<^sub>l (F\<^sub>l \<phi>) \<rbrakk>\<^sub>l = \<lbrakk> F\<^sub>l \<phi> \<rbrakk>\<^sub>l\<close>
proof (rule AsF_cases)
  show \<open>\<lbrakk>F\<^sub>l F\<^sub>l \<phi>\<rbrakk>\<^sub>l T = \<lbrakk>F\<^sub>l \<phi>\<rbrakk>\<^sub>l T\<close>
    apply (clarsimp intro!: set_eqI, rule)
     apply auto[1]
    by (clarsimp, metis add_0)
next
  show \<open> \<lbrakk>F\<^sub>l F\<^sub>l \<phi>\<rbrakk>\<^sub>l F = \<lbrakk>F\<^sub>l \<phi>\<rbrakk>\<^sub>l F\<close>
    apply (clarsimp intro!: set_eqI, rule)
     apply (clarsimp, metis add_0)
    by simp
qed

lemma ltl_equivalence: 
  shows "   \<Gamma> \<Turnstile>\<^sub>l \<phi>  = (\<Gamma> \<in> \<lbrakk> \<phi> \<rbrakk>\<^sub>l T)"
  and   "(\<not> \<Gamma> \<Turnstile>\<^sub>l \<phi>) = (\<Gamma> \<in> \<lbrakk> \<phi> \<rbrakk>\<^sub>l F)"
proof(induct \<phi> arbitrary: \<Gamma>)
qed auto

section \<open>Ltl 3\<close>

type_synonym 'a AsF\<^sub>3 = "answer \<Rightarrow> 'a state dset"

primrec and_AsF\<^sub>3 :: "'a AsF\<^sub>3 \<Rightarrow> 'a AsF\<^sub>3 \<Rightarrow> 'a AsF\<^sub>3" (infixl "\<and>\<^sub>3\<sqdot>" 60) where
"(a \<and>\<^sub>3\<sqdot> b) T = a T \<sqinter> b T"|
"(a \<and>\<^sub>3\<sqdot> b) F = a F \<squnion> b F"

primrec or_AsF\<^sub>3 :: "'a AsF\<^sub>3 \<Rightarrow> 'a AsF\<^sub>3 \<Rightarrow> 'a AsF\<^sub>3" (infixl "\<or>\<^sub>3\<sqdot>" 59) where
"(a \<or>\<^sub>3\<sqdot> b) T = a T \<squnion> b T"|
"(a \<or>\<^sub>3\<sqdot> b) F = a F \<sqinter> b F"

fun not_AsF\<^sub>3 :: "'a AsF\<^sub>3 \<Rightarrow> 'a AsF\<^sub>3" ("\<not>\<^sub>3\<sqdot> _") where
"(\<not>\<^sub>3\<sqdot> a) T = a F"|
"(\<not>\<^sub>3\<sqdot> a) F = a T"

fun univ_AsF\<^sub>3 :: "'a AsF\<^sub>3" ("T\<^sub>3\<bullet>") where
"T\<^sub>3\<bullet> T = \<D>"|
"T\<^sub>3\<bullet> F = \<emptyset>"

fun lsatisfying_AsF\<^sub>3 :: "'a \<Rightarrow> 'a AsF\<^sub>3" ("lsat\<^sub>3\<bullet>") where
"lsat\<^sub>3\<bullet> x T = compr (\<lambda>t. t \<noteq> \<epsilon> \<and> x \<in> L (thead t))" |
"lsat\<^sub>3\<bullet> x F = compr (\<lambda>t. t \<noteq> \<epsilon> \<and> x \<notin> L (thead t))"

fun x\<^sub>3_operator :: "'a AsF\<^sub>3 \<Rightarrow> 'a AsF\<^sub>3" ("X\<^sub>3\<sqdot>") where
"X\<^sub>3\<sqdot> t T = prepend (t T)"|
"X\<^sub>3\<sqdot> t F = prepend (t F)"

fun iterate :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)" where
"iterate f 0 x = x"|
"iterate f (Suc n) x = f (iterate f n x)"

primrec u\<^sub>3_operator :: "'a AsF\<^sub>3 \<Rightarrow> 'a AsF\<^sub>3 \<Rightarrow> 'a AsF\<^sub>3" (infix "U\<^sub>3\<sqdot>" 61) where
"(a U\<^sub>3\<sqdot> b) T = \<Squnion>{ iterate (\<lambda>x. prepend x \<sqinter> a T) i (b T) | i. True}"|
"(a U\<^sub>3\<sqdot> b) F = \<Sqinter>{ iterate (\<lambda>x. prepend x \<squnion> a F) i (b F) | i. True}"

fun triv_true :: "'a \<Rightarrow> bool" where
"triv_true x = (\<forall>s. x\<in> L s)"

fun triv_false :: "'a \<Rightarrow> bool" where
"triv_false x = (\<forall>s. x\<notin> L s)"

fun nontrivial :: "'a \<Rightarrow> bool" where
"nontrivial x = ((\<exists>s. x\<in> L s) \<and> (\<exists>t. x\<notin> L t))"

fun zero_length :: "'a trace \<Rightarrow> bool" where
"zero_length (Finite t) = (length t = 0)"|
"zero_length (Infinite t) = False"

fun ltl_semantics\<^sub>3 :: "'a ltl \<Rightarrow> 'a AsF\<^sub>3" ("\<lbrakk>_\<rbrakk>\<^sub>3") where
"\<lbrakk> true\<^sub>l    \<rbrakk>\<^sub>3 = T\<^sub>3\<bullet>"|
"\<lbrakk> not\<^sub>l \<phi>   \<rbrakk>\<^sub>3 = \<not>\<^sub>3\<sqdot> \<lbrakk>\<phi>\<rbrakk>\<^sub>3"|
"\<lbrakk> prop\<^sub>l(a) \<rbrakk>\<^sub>3 = lsat\<^sub>3\<bullet> a"|
"\<lbrakk> \<phi> or\<^sub>l \<psi>  \<rbrakk>\<^sub>3 = \<lbrakk>\<phi>\<rbrakk>\<^sub>3 \<or>\<^sub>3\<sqdot> \<lbrakk>\<psi>\<rbrakk>\<^sub>3"|
"\<lbrakk> \<phi> and\<^sub>l \<psi> \<rbrakk>\<^sub>3 = \<lbrakk>\<phi>\<rbrakk>\<^sub>3 \<and>\<^sub>3\<sqdot> \<lbrakk>\<psi>\<rbrakk>\<^sub>3"|
"\<lbrakk> X\<^sub>l \<phi>     \<rbrakk>\<^sub>3 = X\<^sub>3\<sqdot> \<lbrakk>\<phi>\<rbrakk>\<^sub>3"|
"\<lbrakk> \<phi> U\<^sub>l \<psi>   \<rbrakk>\<^sub>3 = \<lbrakk>\<phi>\<rbrakk>\<^sub>3 U\<^sub>3\<sqdot> \<lbrakk>\<psi>\<rbrakk>\<^sub>3"

section \<open>LTL/LTL3 equivalence\<close>

declare dset.Inf_insert[simp del]
declare dset.Sup_insert[simp del]


lemma itdrop_all_split: 
assumes \<open>x \<in> A\<close>
and \<open>\<forall>i<k. itdrop (Suc i) x \<in> A\<close>
shows \<open>i < Suc k \<Longrightarrow> itdrop i x \<in> A\<close>
using assms proof (cases i)
qed (auto simp: itdrop_def)

lemma itdrop_exists_split[simp]:
  shows \<open>(\<exists>i<Suc k. itdrop i x \<in> A) \<longleftrightarrow> (\<exists>i < k. itdrop (Suc i) x \<in> A) \<or> x \<in> A\<close>
proof (rule;clarsimp?)
  fix i
  assume \<open>i < Suc k\<close> \<open>itdrop i x \<in> A\<close> \<open>x \<notin> A\<close>
  then show \<open>\<exists>i<k. itdrop (Suc i) x \<in> A\<close>
  proof (cases i)
  qed auto
next
  assume \<open>(\<exists>i<k. itdrop (Suc i) x \<in> A) \<or> x \<in> A\<close>
  then show \<open>\<exists>i<Suc k. itdrop i x \<in> A\<close>
    by auto
qed

lemma until_iterate : 
     \<open>{x. \<exists>k. (\<forall>i<k. itdrop i x \<in> A) \<and> itdrop k x \<in> B} 
 = \<Union> { iterate (\<lambda>x. iprepend x \<inter> A) k B | k. True }\<close>
proof (rule; rule; clarsimp)
  fix x k
  assume  \<open>\<forall>i<k. itdrop i x \<in> A \<close> and \<open>itdrop k x \<in> B\<close>
  then have \<open>x \<in> iterate (\<lambda>x. iprepend x \<inter> A) k B\<close>
  proof (induct k arbitrary: x)
    case 0
    then show ?case by simp
  next
    case (Suc k)
    from this(2,3) show ?case 
      by (auto intro!: Suc.hyps[where x = \<open>itdrop 1 x\<close>, simplified])
  qed
  then show \<open>\<exists>xa. (\<exists>k. xa = iterate (\<lambda>x. iprepend x \<inter> A) k B) \<and> x \<in> xa\<close>
    by blast
next
  fix x k
  assume \<open>x \<in> iterate (\<lambda>x. iprepend x \<inter> A) k B\<close>
  then have \<open>(\<forall>i<k. itdrop i x \<in> A) \<and> itdrop k x \<in> B \<close>
  proof (induct k arbitrary: x)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    from this(2) show ?case
      by (auto dest: Suc.hyps[where x = "itdrop 1 x", simplified] 
               intro: itdrop_all_split)
  qed
  then show \<open>\<exists>k. (\<forall>i<k. itdrop i x \<in> A) \<and> itdrop k x \<in> B \<close>
    by blast
qed

lemma release_iterate:
  \<open> {u. \<forall>k. (\<exists>i<k. itdrop i u \<in> A) \<or> itdrop k u \<in> B} 
  = \<Inter> { iterate (\<lambda>x. iprepend x \<union> A) i B | i. True}\<close>
proof (rule; rule; clarsimp)
  fix x i assume \<open> \<forall>k. (\<exists>i<k. itdrop i x \<in> A) \<or> itdrop k x \<in> B\<close>
  then show \<open>x \<in> iterate (\<lambda>x. iprepend x \<union> A) i B\<close>
  proof (induct i arbitrary: x)
    case 0
    then show ?case by auto
  next
    case (Suc i)
    show ?case
      apply (clarsimp)
      apply (rule Suc.hyps[where x = "itdrop 1 x", simplified])
      using Suc(2)[THEN spec, where x = "Suc _",simplified]
      by auto
  qed
next
  fix x k
  assume \<open> \<forall>xa. (\<exists>i. xa = iterate (\<lambda>x. iprepend x \<union> A) i B) \<longrightarrow> x \<in> xa\<close>
  then have P: \<open>\<forall>i. x \<in> iterate (\<lambda>x. iprepend x \<union> A) i B\<close> 
    by blast
  assume \<open>itdrop k x \<notin> B\<close> with P show \<open>\<exists>i<k. itdrop i x \<in> A\<close>
  proof (induct k arbitrary: x)
    case 0
    then show ?case by (simp, metis AnswerModelSet.iterate.simps(1))
  next
    case (Suc k)
    from this(3) show ?case
      apply clarsimp
      apply (rule Suc.hyps[where x = "itdrop 1 x", simplified])
      using Suc(2)[THEN spec, where x = "Suc _"]
      by auto
  qed
qed

lemma property_until_iterate: 
  \<open>property (iterate (\<lambda>x. prepend x \<sqinter> A) k B) 
 = iterate (\<lambda>x. iprepend x \<inter> property A) k (property B)\<close>
  by (induct k, auto simp: property_Inter property_prepend)

lemma property_release_iterate: 
  \<open>property (iterate (\<lambda>x. prepend x \<squnion> A) k B) 
 = iterate (\<lambda>x. iprepend x \<union> property A) k (property B)\<close>
  by (induct k, auto simp: property_Union property_prepend)


lemma [simp]: "{f uu |uu. \<exists>i. uu = g i} = {f (g i) | i. True}"
  by blast

lemma ltl3_equiv_ltl: 
  shows "property (\<lbrakk> \<phi> \<rbrakk>\<^sub>3 T) = \<lbrakk> \<phi> \<rbrakk>\<^sub>l T"
  and   "property (\<lbrakk> \<phi> \<rbrakk>\<^sub>3 F) = \<lbrakk> \<phi> \<rbrakk>\<^sub>l F"
proof (induct \<phi>)
  case True_ltl
  {
    case 1
    then show ?case by (simp, transfer, simp)
  next
    case 2
    then show ?case by (simp, transfer, simp)
  }
next
  case (Not_ltl \<phi>)
  {
    case 1
    then show ?case using Not_ltl by simp
  next
    case 2
    then show ?case using Not_ltl by simp
  }
next
  case (Prop_ltl x)
  {
    case 1
    then show ?case
      apply simp
      apply transfer
      apply (simp add: infinites_dprefixes)
      apply (clarsimp simp add: infinites_def  split: trace.split_asm trace.split)
      apply (rule,rule)
       apply (clarsimp  split: trace.split_asm trace.split)
       apply (metis zero_length.cases)
       apply (clarsimp split: trace.split_asm trace.split)
      by (metis Traces.append.simps(3) append_is_empty(2) trace.distinct(1) trace.inject(2))
  next
    case 2
    then show ?case
      apply simp
      apply transfer
      apply (simp add: infinites_dprefixes)
      apply (clarsimp simp add: infinites_def  split: trace.split_asm trace.split)
      apply (rule,rule)
       apply (clarsimp  split: trace.split_asm trace.split)
       apply (metis zero_length.cases)
       apply (clarsimp split: trace.split_asm trace.split)
      by (metis Traces.append.simps(3) append_is_empty(2) trace.distinct(1) trace.inject(2))
  }
next
  case (Or_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show ?case by (simp add: property_Union Or_ltl)
  next
    case 2
    then show ?case by (simp add: property_Inter Or_ltl)
  }
next
  case (And_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show ?case by (simp add: property_Inter And_ltl)
  next
    case 2
    then show ?case by (simp add: property_Union And_ltl)
  }
next
  case (Next_ltl \<phi>)
  {
    case 1
    then show ?case by (simp add: property_prepend Next_ltl iprepend_def)
    next
    case 2
    then show ?case by (simp add: property_prepend Next_ltl iprepend_def)
  }
next
  case (Until_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show ?case
      apply (simp add: Until_ltl[THEN sym] property_Union image_Collect property_until_iterate)
      using until_iterate[simplified] by blast 
  next
    case 2
    then show ?case 
      apply (simp add: Until_ltl[THEN sym] property_Inter image_Collect property_release_iterate)
      using release_iterate[simplified] by metis
  }
qed

lemma extension_lemma: \<open>in_dset t A = (\<forall>\<omega>. t \<frown> Infinite \<omega> \<in> Infinite ` property A)\<close>
proof transfer
  fix t and A :: \<open>'a trace set\<close>
  assume D: \<open>definitive A\<close> 
  show \<open>t \<in> A = (\<forall>\<omega>. t \<frown> Infinite \<omega> \<in> Infinite ` infinites A) \<close>
  proof (rule iffI)
    assume \<open>t \<in> A\<close>
    with D have D': \<open>\<up> t \<subseteq> A \<close> by (rule definitive_contains_extensions)
    { fix \<omega> have \<open>t \<frown> Infinite \<omega> \<in> A\<close>
        by (rule subsetD[OF D'], force simp add: extensions_def)
    } then have \<open> \<forall>\<omega>. t \<frown> Infinite \<omega> \<in>  A\<close> by auto
    thus  \<open> \<forall>\<omega>. t \<frown> Infinite \<omega> \<in> Infinite ` infinites A\<close>
      by (simp add: infinites_append_right infinites_alt)
  next
    assume \<open> \<forall>\<omega>. t \<frown> Infinite \<omega> \<in> Infinite ` infinites A\<close> then
    have inA: \<open> \<forall>\<omega>. t \<frown> Infinite \<omega> \<in> A\<close>
      by (simp add: infinites_alt infinites_append_right)
    have \<open>\<up> t \<subseteq> \<down>\<^sub>s A\<close> 
    proof -
      { fix u 
        obtain \<omega> :: \<open>'a infinite_trace\<close> where \<open>Infinite \<omega> = u \<frown> Infinite undefined\<close>
          by (cases u; simp)
        then have \<open>\<exists>v. (t \<frown> u) \<frown> v \<in> A\<close> 
          using inA[THEN spec, where x = \<omega>] by (metis trace.assoc)
      } thus ?thesis unfolding extensions_def prefix_closure_def prefixes_def by auto
    qed
    with D show \<open>t \<in> A\<close> by (rule definitive_elemI)
  qed
qed

lemma extension: 
  shows \<open>in_dset t (ltl_semantics\<^sub>3 \<phi> T) = (\<forall>\<omega>. (t \<frown> Infinite \<omega>) \<in> Infinite ` (ltl_semantics \<phi> T))\<close>
  and   \<open>in_dset t (ltl_semantics\<^sub>3 \<phi> F) = (\<forall>\<omega>. (t \<frown> Infinite \<omega>) \<in> Infinite ` (ltl_semantics \<phi> F))\<close>
  by (simp_all add: ltl3_equiv_ltl[THEN sym] extension_lemma)


fun progress :: "'a ltl \<Rightarrow> 'a state \<Rightarrow> 'a ltl" where
"progress true\<^sub>l \<sigma> = true\<^sub>l"|
"progress (not\<^sub>l \<phi>) \<sigma> = not\<^sub>l (progress \<phi>) \<sigma>"|
"progress (prop\<^sub>l(a)) \<sigma> = (if a \<in> L \<sigma> then true\<^sub>l else not\<^sub>l true\<^sub>l)"|
"progress (\<phi> or\<^sub>l \<psi>) \<sigma> = (progress \<phi> \<sigma>) or\<^sub>l (progress \<psi> \<sigma>)"|
"progress (\<phi> and\<^sub>l \<psi>) \<sigma> = (progress \<phi> \<sigma>) and\<^sub>l (progress \<psi> \<sigma>)"|
"progress (X\<^sub>l \<phi>) \<sigma> = \<phi>"|
"progress (\<phi> U\<^sub>l \<psi>) \<sigma> = (progress \<psi> \<sigma>) or\<^sub>l ((progress \<phi> \<sigma>) and\<^sub>l (\<phi> U\<^sub>l \<psi>))"




lemma iterate_unroll_union: \<open>\<Squnion> {P i |i. True} = P 0 \<squnion> (\<Squnion> {P (Suc i) | i. True})\<close>
 (* TODO tidy: maybe the isomorphism can be encoded with the transfer package? *)
  apply (subst definitives_inverse[THEN sym])
  apply (rule sym)
  apply (subst definitives_inverse[THEN sym])
  apply (simp add: property_Union)
  apply (rule dset.order_antisym)
   apply (rule definitives_mono)
   apply blast
   apply (rule definitives_mono)
  apply clarsimp
  by (metis not0_implies_Suc)


lemma iterate_unroll_inter: \<open>\<Sqinter> {P i |i. True} = P 0 \<sqinter> (\<Sqinter> {P (Suc i) | i. True})\<close>
  apply (subst definitives_inverse[THEN sym])
  apply (rule sym)
  apply (subst definitives_inverse[THEN sym])
  apply (simp add: property_Inter)
   apply (rule dset.order_antisym)
   apply (rule definitives_mono)
   apply clarsimp
   apply (case_tac i; blast) (* TODO fix *)
  apply (rule definitives_mono)
  by blast


lemma inf_inf: \<open>x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<sqinter> (x \<sqinter> z)\<close>
  by (simp add: dset.inf_assoc dset.inf_left_commute)

theorem progression_tf :
"prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 T) \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> \<lbrakk> \<phi> \<rbrakk>\<^sub>3 T "
"prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 F) \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> \<lbrakk> \<phi> \<rbrakk>\<^sub>3 F "
proof (induct \<phi>)
  case True_ltl
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case apply simp
      apply transfer
      apply (simp add: prepend'_def)
      done
  }
next
  case (Not_ltl \<phi>)
  {
    case 1
    then show ?case using Not_ltl by simp
  next
    case 2
    then show ?case using Not_ltl by simp
  }
next
  case (Prop_ltl x)
  {
    case 1
    then show ?case
      apply simp
      apply transfer
      apply (clarsimp simp add: prepend'_def)
      apply (rule dprefixes_mono[THEN subsetD, rotated], simp)
      by (auto simp: prepend'_def intro: dprefixes_mono[THEN subsetD, rotated])
  next
    case 2
    then show ?case 
      apply simp
      apply transfer
      by (auto simp: prepend'_def intro: dprefixes_mono[THEN subsetD, rotated])
  }
next
  case (Or_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show ?case
      apply (simp add: prepend_Union[THEN sym])
      using Or_ltl(1, 3)
      by (metis (no_types, lifting) dset.inf_sup_distrib2 dset.sup_mono)
  next
    case 2
    then show ?case
      apply (simp add: prepend_Inter[THEN sym])
      using Or_ltl(2,4)
      by (meson dset.dual_order.refl dset.dual_order.trans dset.inf.coboundedI2 dset.inf_le1 dset.inf_mono)
  }
next
  case (And_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show ?case
      apply (simp add: prepend_Inter[THEN sym])
      using And_ltl(1,3)
      by (smt (verit, del_insts) dset.dual_order.eq_iff dset.inf.boundedI dset.le_infE dset.order_trans)
  next
    case 2
    then show ?case
      apply (simp add: prepend_Union[THEN sym])
      using And_ltl(2, 4)
      by (metis (no_types, lifting) dset.inf_sup_distrib2 dset.sup_mono)
  }
next
  case (Next_ltl \<phi>)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  }
next
  case (Until_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show ?case (*ridiculous TODO tidy*)
      apply (simp only: progress.simps)
      apply (simp add: prepend_Union[THEN sym] prepend_Inter[THEN sym])
       apply (subst dset.inf_commute)
      apply (subst dset.distrib(3))
      apply (rule dset.order_trans)
       apply (rule dset.sup_mono[OF _ dset.order_refl])
      apply (subst dset.inf_commute)
       apply (rule Until_ltl(3))
      apply (subst dset.inf_assoc[THEN sym])
      apply (rule dset.order_trans)
       apply (rule dset.sup_mono[OF dset.order_refl])
       apply (rule dset.inf_mono[OF _ dset.order_refl])
       apply (subst dset.inf_commute)
       apply (rule Until_ltl(1))
      apply (simp add: image_Collect)
      apply (rule)
       apply (metis (mono_tags, lifting) AnswerModelSet.iterate.simps(1) dset.Sup_upper mem_Collect_eq)
      apply (subgoal_tac \<open>\<Squnion> {uu. \<exists>i. uu = iterate (\<lambda>x. prepend x \<sqinter> \<lbrakk>\<phi>1\<rbrakk>\<^sub>3 T) i (\<lbrakk>\<phi>2\<rbrakk>\<^sub>3 T)} = (\<lbrakk>\<phi>2\<rbrakk>\<^sub>3 T) \<squnion> \<Squnion> {uu. \<exists>i. uu = iterate (\<lambda>x. prepend x \<sqinter> \<lbrakk>\<phi>1\<rbrakk>\<^sub>3 T) (Suc i) (\<lbrakk>\<phi>2\<rbrakk>\<^sub>3 T)}\<close>)
       apply simp
       apply (rule dset.le_supI2)
       apply (subgoal_tac "\<And>x. prepend x \<sqinter> \<lbrakk>\<phi>1\<rbrakk>\<^sub>3 T =  \<lbrakk>\<phi>1\<rbrakk>\<^sub>3 T \<sqinter> prepend x")
      apply simp
        apply (simp add: full_SetCompr_eq)
        apply (subst dset.inf_SUP[where B = UNIV, THEN sym])
        apply blast
       apply (subst dset.inf_commute, simp)
      apply (simp add: full_SetCompr_eq)
      apply (subgoal_tac "\<And>x. prepend x \<sqinter> \<lbrakk>\<phi>1\<rbrakk>\<^sub>3 T =  \<lbrakk>\<phi>1\<rbrakk>\<^sub>3 T \<sqinter> prepend x")
       apply simp
       apply (subst dset.inf_SUP[where B = UNIV, THEN sym])
        apply (subst prepend_Union[where S = "range (\<lambda> b. iterate (\<lambda>x. \<lbrakk>\<phi>1\<rbrakk>\<^sub>3 T \<sqinter> prepend x) b (\<lbrakk>\<phi>2\<rbrakk>\<^sub>3 T))", simplified image_image])
        apply (subst iterate_unroll_union[simplified,simplified full_SetCompr_eq])
        apply simp
        apply (subst dset.inf_SUP[where B = UNIV, THEN sym])
        apply (subst prepend_Union[where S = "range (\<lambda> b. iterate (\<lambda>x. \<lbrakk>\<phi>1\<rbrakk>\<^sub>3 T \<sqinter> prepend x) b (\<lbrakk>\<phi>2\<rbrakk>\<^sub>3 T))", simplified image_image])
        apply simp
       apply (rule dset.inf_commute)
      done
  next
    case 2
    then show ?case (* TODO tidy *)
      apply simp
      apply (subst prepend_Inter[THEN sym] prepend_Union[THEN sym], simp)
      apply (subst dset.inf_commute)
      apply (subst inf_inf)
      apply (rule dset.order_trans)
       apply (rule dset.inf_mono)
      apply (subst dset.inf_commute)
        apply (rule Until_ltl(4))
      apply (simp add: prepend_Union[THEN sym])
      apply (subst dset.distrib(3))
       apply (rule dset.sup_mono)
      apply (subst dset.inf_commute)
        apply (rule Until_ltl(2))       
       apply (rule dset.le_infI2, rule dset.order_refl)
      apply (subgoal_tac \<open>\<Sqinter> {uu. \<exists>i. uu = iterate (\<lambda>x. prepend x \<squnion> \<lbrakk>\<phi>1\<rbrakk>\<^sub>3 F) i (\<lbrakk>\<phi>2\<rbrakk>\<^sub>3 F)} = \<lbrakk>\<phi>2\<rbrakk>\<^sub>3 F \<sqinter>
    (\<lbrakk>\<phi>1\<rbrakk>\<^sub>3 F \<squnion> prepend (\<Sqinter> {uu. \<exists>i. uu = iterate (\<lambda>x. prepend x \<squnion> \<lbrakk>\<phi>1\<rbrakk>\<^sub>3 F) i (\<lbrakk>\<phi>2\<rbrakk>\<^sub>3 F)}))\<close>)
       apply simp
      apply (simp add: full_SetCompr_eq)
        apply (subst iterate_unroll_inter[simplified,simplified full_SetCompr_eq])
      apply simp
      apply (subst dset.sup_commute)
      apply (simp add: prepend_Inter[THEN sym], simp add: image_image)
      by (simp add: dset.sup_INF)
  }
qed

theorem progression_tf' :
"\<lbrakk> \<phi> \<rbrakk>\<^sub>3 T \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 T) "
"\<lbrakk> \<phi> \<rbrakk>\<^sub>3 F \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 F) "
proof (induct \<phi>)
  case True_ltl
  {
    case 1
    then show ?case apply simp
      apply transfer
      apply (simp add: prepend'_def)
      done
  next
    case 2
    then show ?case 
      by simp
  }
next
  case (Not_ltl \<phi>)
  {
    case 1
    then show ?case using Not_ltl by simp
  next
    case 2
    then show ?case using Not_ltl by simp
  }
next
  case (Prop_ltl x)
  {
    case 1
    then show ?case apply simp
      apply transfer
      apply clarsimp
      apply (clarsimp simp: prepend'_def)
      apply (subst compr'_inter_thead)
      by (metis (mono_tags, lifting) Collect_empty_eq dprefixes_empty)
  next
    case 2
    then show ?case 
      apply simp
      apply transfer
      apply (clarsimp simp: prepend'_def)
      apply (subst compr'_inter_thead)
      by (metis (mono_tags, lifting) Collect_empty_eq dprefixes_empty)
  }
next
  case (Or_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show ?case
      apply (simp add: prepend_Union[THEN sym])
      using Or_ltl(1,3)
      by (metis (no_types, lifting) dset.inf_sup_distrib2 dset.sup_mono)
  next
    case 2
    then show ?case
      apply (simp add: prepend_Inter[THEN sym])
      using Or_ltl(2,4)
      by (meson dset.dual_order.refl dset.dual_order.trans dset.inf.coboundedI2 dset.inf_le1 dset.inf_mono)
  }
next
  case (And_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show ?case 
      apply (simp add: prepend_Inter[THEN sym])
      using And_ltl(1,3)
      by (meson dset.dual_order.refl dset.dual_order.trans dset.le_inf_iff)
  next
    case 2
    then show ?case 
      apply (simp add: prepend_Union[THEN sym])
      using And_ltl(2,4)
      by (metis (no_types,lifting) dset.inf_sup_distrib2 dset.sup_mono)
  }
next
  case (Next_ltl \<phi>)
  {
    case 1
    then show ?case using Next_ltl
      by simp
  next
    case 2
    then show ?case using Next_ltl
      by simp
  }
next
  case (Until_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show ?case (* AFP compliant but maybe TODO tidy *)
    unfolding ltl_semantics\<^sub>3.simps u\<^sub>3_operator.simps
              ltl_semantics.simps progress.simps u_operator.simps or_AsF\<^sub>3.simps and_AsF\<^sub>3.simps
      apply (simp add: full_SetCompr_eq prepend_Union[THEN sym])
      apply (rule dset.order_trans[rotated])
       apply (rule dset.sup_mono [OF _ dset.order_refl], rule Until_ltl(3))
      apply (simp add: prepend_Inter[THEN sym])
      apply (rule dset.order_trans[rotated])
       apply (rule dset.sup_mono [OF dset.order_refl])
       apply (rule dset.inf_mono [OF _ dset.order_refl])
       apply (rule Until_ltl(1))
      apply (subst iterate_unroll_union[simplified, simplified full_SetCompr_eq])
      apply simp
      apply (simp add: prepend_Union[THEN sym] image_image)
      apply (subst dset.inf_commute)
      apply (subst dset.distrib(3))
      apply simp
      apply rule
       apply (simp add: insert_commute)
      by (metis dset.Inf_insert dset.inf_assoc dset.sup_ge2 insert_commute dset.SUP_inf)
  next
    case 2
    then show ?case  (* AFP compliant but maybe TODO tidy *)
    unfolding ltl_semantics\<^sub>3.simps u\<^sub>3_operator.simps
              ltl_semantics.simps progress.simps u_operator.simps or_AsF\<^sub>3.simps and_AsF\<^sub>3.simps
      apply (simp add: full_SetCompr_eq prepend_Inter[THEN sym])
      apply (rule,rule dset.order_trans[rotated])
        apply (rule Until_ltl(4))
       apply (rule dset.inf_mono; simp?)
       apply (metis AnswerModelSet.iterate.simps(1) dset.Inf_lower rangeI)
      apply (simp add: prepend_Union[THEN sym])
      apply (rule dset.order_trans[rotated])
       apply (rule dset.sup_mono)
        apply (rule Until_ltl(2))
       apply (rule dset.order_refl)
      apply (subst iterate_unroll_inter[simplified, simplified full_SetCompr_eq])
      apply clarsimp
      apply (subst dset.inf_assoc)
      apply (rule dset.le_infI2)
      apply (simp add: prepend_Inter[THEN sym] image_image)
      apply (simp add: dset.INF_sup [where B = UNIV, THEN sym] )
      by (smt (verit, best) doubleton_eq_iff dset.distrib_inf_le dset.le_supE dset.sup_inf_distrib2)
  }
qed

theorem progression_tf'_u :
"\<lbrakk> \<phi> \<rbrakk>\<^sub>3 A \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 A)"
  by (cases A; simp add: progression_tf')

theorem progression_tf_u:
"prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 A) \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> \<lbrakk> \<phi> \<rbrakk>\<^sub>3 A"
  by (cases A; simp add: progression_tf)

lemma in_dset_\<epsilon>: \<open>in_dset \<epsilon> A \<Longrightarrow> A = \<D>\<close>
  apply (transfer)
  apply (rule)
   apply simp
  apply (rule subset_iff[THEN iffD2], clarsimp)
  using definitive_contains_extensions extensions_empty by blast

lemma in_dset_UNIV: \<open>in_dset x \<D>\<close>
  apply (transfer)
  apply simp
  done

lemma in_dset_subset: \<open>A \<sqsubseteq> B \<Longrightarrow> in_dset x A \<Longrightarrow> in_dset x B\<close>
  apply transfer
  by auto

lemma in_dset_inter: \<open>in_dset x A \<Longrightarrow> in_dset x B \<Longrightarrow> in_dset x (A \<sqinter> B)\<close>
  apply transfer
  by simp


lemma in_dset_prepend: \<open>in_dset (Finite [a] \<frown> x) (prepend A) \<Longrightarrow> in_dset x A\<close>
  apply transfer
  apply (simp add: prepend'_def)
  by (metis Traces.singleton_def tdrop_singleton_append tdrop_zero)

lemma in_dset_prepend': \<open>in_dset x A \<Longrightarrow> in_dset (Finite [a] \<frown> x) (prepend A)\<close>
  apply transfer
  apply (simp add: prepend'_def)
  by (metis Traces.singleton_def tdrop_singleton_append tdrop_zero)


lemma fp:
\<open>in_dset (Finite t) (\<lbrakk> \<phi> \<rbrakk>\<^sub>3 A) \<longleftrightarrow> \<lbrakk> foldl progress \<phi> t \<rbrakk>\<^sub>3 A = \<D> \<close>
proof (induct t arbitrary: \<phi>)
  case Nil
  then show ?case 
    apply (rule)
     apply (simp add: in_dset_\<epsilon>[simplified \<epsilon>_def])
    apply (simp add: in_dset_UNIV)
    done
next
  case (Cons a t)
  show ?case
    apply (simp add: Cons[where \<phi>=\<open>progress \<phi> a\<close>, THEN sym])
    apply rule
     apply (rule_tac a = a in in_dset_prepend)
    apply simp
     apply (rule in_dset_subset)
      apply (rule progression_tf'_u)
     apply (rule in_dset_inter)
      apply simp
     apply transfer
     apply (simp add: dprefixes_def)
     apply (simp add: subset_iff extensions_def prefix_closure_def prefixes_def)
     apply (metis \<epsilon>_def list.distinct(1) nth_Cons_0 thead.simps(1) thead_append trace.inject(1) trace.left_neutral trace.right_neutral)

    apply (rule in_dset_subset)
     apply (rule progression_tf_u)
    apply (rule in_dset_inter)
     apply (rule in_dset_prepend'[where x = \<open>Finite u\<close> for u, simplified], simp)
    apply transfer
     apply (simp add: dprefixes_def)
     apply (simp add: subset_iff extensions_def prefix_closure_def prefixes_def)
    by (metis \<epsilon>_def list.distinct(1) nth_Cons_0 thead.simps(1) thead_append trace.inject(1) trace.left_neutral trace.right_neutral)
qed

lemma [simp]: \<open>property (complement X) = UNIV - property X\<close>
  apply transfer
  apply (simp add: infinites_dprefixes)
  apply (simp add: infinites_def)
  by (force split: trace.split_asm trace.split)

lemma em_ltl: \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>l T = UNIV - (\<lbrakk> \<phi> \<rbrakk>\<^sub>l F)\<close>
  by (rule; clarsimp simp add: subset_iff ltl_equivalence[THEN sym])

lemma em: \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>3 T = complement (\<lbrakk> \<phi> \<rbrakk>\<^sub>3 F)\<close>
  apply (subst definitives_inverse[THEN sym])
  apply (simp add: ltl3_equiv_ltl)
  apply (rule sym)
  apply (subst definitives_inverse[THEN sym])
  apply (simp add: ltl3_equiv_ltl)
  by (simp add: em_ltl)
end
