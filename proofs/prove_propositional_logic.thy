theory prove_propositional_logic
  imports Main
begin

datatype 'a formula
  = Atom "'a set"
  | T | F
  | Not   "'a formula"
  | Imp   "'a formula" "'a formula"
  | And   "'a formula" "'a formula"
  | Or    "'a formula" "'a formula"

fun holds  :: "'a formula \<Rightarrow> 'a \<Rightarrow> bool" where
  "holds T v = True" | "holds F v = False" |
  "holds (Atom a)    v = (v \<in> a)" |
  "holds (Not \<phi>)     v = (\<not> holds \<phi> v)" |
  "holds (Imp \<phi> \<psi>)   v = (holds \<phi> v \<longrightarrow> holds \<psi> v)" |
  "holds (And \<phi> \<psi>)   v = (holds \<phi> v \<and> holds \<psi> v)" |
  "holds (Or  \<phi> \<psi>)   v = (holds \<phi> v \<or> holds \<psi> v)"

fun entails where
  "entails \<Gamma> q = (\<forall> v. (\<forall> p \<in> set \<Gamma>. holds p v) \<longrightarrow> holds q v)"

fun tt :: "'a formula list \<Rightarrow> bool \<Rightarrow> 'a formula" where
  "tt \<Gamma> True  = T" |
  "tt \<Gamma> False = (if (entails \<Gamma> (Not T)) then F else T)"

fun ff :: "'a formula list \<Rightarrow> bool \<Rightarrow> 'a formula" where
  "ff \<Gamma> True  = (if (entails \<Gamma> F) then T else F)" |
  "ff \<Gamma> False = F"

fun atom :: "'a formula list \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a formula" where
  "atom \<Gamma> a True  = (if (entails \<Gamma> (Atom a)) then T else Atom a)" |
  "atom \<Gamma> a False = (if (entails \<Gamma> (Not (Atom a))) then F else Atom a)"

fun not :: "'a formula \<Rightarrow> 'a formula" where
  "not T = F" | "not F = T" | "not p = Not p"

fun imp :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" where
  "imp  F q = T" | "imp  T q = q" | "imp  p T = T" | "imp  p F = (Not p)" | "imp  p q = Imp p q"

fun and' :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" where
  "and' F q = F" | "and' T q = q" | "and' p T = p" | "and' p F = F" | "and' p q = And p q"

fun or :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" where
  "or   F p = p" | "or   T p = T" | "or   p T = T" | "or   p F = p" | "or   p q = Or p q"

lemma holds_tt[simp]:
  assumes "\<forall> p \<in> set \<Gamma>. holds p v"
  shows   "holds (tt \<Gamma> b) v = holds T v"
  using assms by (cases b) auto

lemma holds_ff[simp]:
  assumes "\<forall> p \<in> set \<Gamma>. holds p v"
  shows   "holds (ff \<Gamma> b) v = holds F v"
  using assms by (cases b) auto

lemma holds_atom[simp]:
  assumes "\<forall> p \<in> set \<Gamma>. holds p v"
  shows   "holds (atom \<Gamma> a b) v = holds (Atom a) v"
  using assms by (cases b) auto

lemma holds_not[simp]:
  "holds (not p) v = holds (Not p) v"
  by (cases p) auto

lemma holds_imp[simp]:
  "holds (imp p q) v = holds (Imp p q) v"
  apply (cases p)
  by (cases q, auto)+

lemma imp_T[simp]:
  "imp p T = T"
  by (cases p) auto

lemma imp_F[simp]:
  "imp p F = (not p)"
  by (cases p) auto

lemma holds_and[simp]:
  "holds (and' p q) v = holds (And p q) v"
  apply (cases p)
  by (cases q, auto)+

lemma and_F[simp]:
  "and' p F = F"
  by (cases p) auto

lemma and_T[simp]:
  "and' p T = p"
  by (cases p) auto

lemma holds_or[simp]:
  "holds (or p q) v = holds (Or p q) v"
  apply (cases p)
  by (cases q, auto)+

lemma or_T[simp]:
  "or p T = T"
  by (cases p) auto

lemma or_F[simp]:
  "or p F = p"
  by (cases p) auto

fun prove and disprove where
  "prove \<Gamma> F = (if (entails \<Gamma> F) then T else F)" |
  "prove \<Gamma> T = T" |
  "prove \<Gamma> (Atom a)  = (if (entails \<Gamma> (Atom a)) then T else (Atom a))" |
  "prove \<Gamma> (Not \<phi>)   = not  (disprove \<Gamma> \<phi>)" |
  "prove \<Gamma> (And \<phi> \<psi>) = and' (prove \<Gamma> \<phi>)    (prove (\<phi>#\<Gamma>) \<psi>)" |
  "prove \<Gamma> (Imp \<phi> \<psi>) = imp  (prove \<Gamma> \<phi>)    (prove (\<phi>#\<Gamma>) \<psi>)" |
  "prove \<Gamma> (Or  \<phi> \<psi>) = or (or (disprove \<Gamma> \<phi>) (disprove (Not \<phi>#\<Gamma>) \<psi>))
                           (if entails \<Gamma> (Or \<phi> \<psi>) then T else F)" |
  
  "disprove \<Gamma> F = F" |
  "disprove \<Gamma> T = (if (entails \<Gamma> F) then F else T)" |
  "disprove \<Gamma> (Atom a) = (if (entails \<Gamma> (Not (Atom a))) then F else (Atom a))" |
  "disprove \<Gamma> (Not \<phi>)   = not  (prove \<Gamma> \<phi>)" |
  "disprove \<Gamma> (And \<phi> \<psi>) = and' (and' (prove \<Gamma> \<phi>) (prove (\<phi>#\<Gamma>) \<psi>))
                                (if entails \<Gamma> (Not (And \<phi> \<psi>)) then F else T)" |
  "disprove \<Gamma> (Imp \<phi> \<psi>) = imp  (prove \<Gamma> \<phi>)    (disprove (\<phi>#\<Gamma>) \<psi>)" |
  "disprove \<Gamma> (Or  \<phi> \<psi>) = or   (disprove \<Gamma> \<phi>) (disprove (Not \<phi>#\<Gamma>) \<psi>)" (* to work with prove and associativity *)

lemma prove_sound[simp]:
  assumes "\<forall> p \<in> set \<Gamma>. holds p v"
  shows "holds (prove \<Gamma> q) v = holds q v" and
        "holds (disprove \<Gamma> q) v = holds q v"
  using assms
  by (induction rule: prove_disprove.induct)
     auto

lemma prove_complete:
  shows "entails \<Gamma> q       \<Longrightarrow> prove \<Gamma> q = T"
    and "entails \<Gamma> (Not q) \<Longrightarrow> disprove \<Gamma> q = F"
  by (induction q arbitrary: \<Gamma>)
     auto

corollary prove_known_T[simp]:
  shows "A \<in> set \<Gamma> \<Longrightarrow> prove \<Gamma> A = T"
  by (rule prove_complete) auto

corollary prove_known_F[simp]:
  shows "(Not A) \<in> set \<Gamma> \<Longrightarrow> disprove \<Gamma> A = F"
  by (rule prove_complete) auto

fun size :: "'a formula \<Rightarrow> nat"  where
  "size T         = 0" |
  "size F         = 0" |
  "size (Atom a)  = 1" |
  "size (Not \<phi>)   = 1 + (size \<phi>)" |
  "size (And \<phi> \<psi>) = 1 + (size \<phi>) + (size \<psi>)" |
  "size (Imp \<phi> \<psi>) = 1 + (size \<phi>) + (size \<psi>)" |
  "size (Or  \<phi> \<psi>) = 1 + (size \<phi>) + (size \<psi>)"

lemma size_not[intro]:
  "size (Not p) \<le> n \<Longrightarrow> size (not p) \<le> n"
  by (cases p, auto)

lemma size_imp[intro]:
  "size (Imp p q) \<le> n \<Longrightarrow> size (imp p q) \<le> n"
  apply (cases p)
  by (cases q, auto)+

lemma size_or[intro]:
  "size (Or p q) \<le> n \<Longrightarrow> size (or p q) \<le> n"
  apply (cases p)
  by (cases q, auto)+

lemma size_and[intro]:
  "size (And p q) \<le> n \<Longrightarrow> size (and' p q) \<le> n"
  apply (cases p)
  by (cases q, auto)+

lemma size_decreases:
  shows "size (prove \<Gamma> f)    \<le> size f"
    and "size (disprove \<Gamma> f) \<le> size f"
  by (induction \<Gamma> f rule: prove_disprove.induct)
    auto

fun tf_free :: "'a formula \<Rightarrow> bool" where
  "tf_free T = False" | "tf_free F = False" |
  "tf_free (Atom a) = True" |
  "tf_free (Not p) = tf_free p" | "tf_free (And p q) = (tf_free p & tf_free q)" |
  "tf_free (Or p q) = (tf_free p & tf_free q)" | "tf_free (Imp p q) = (tf_free p & tf_free q)"

lemma size_decreases_strictly:
  assumes "tf_free f"
  shows "prove    \<Gamma> f \<noteq> f \<Longrightarrow> size (prove    \<Gamma> f) < size f"
    and "disprove \<Gamma> f \<noteq> f \<Longrightarrow> size (disprove \<Gamma> f) < size f"
  using assms
proof (induction \<Gamma> f rule: prove_disprove.induct)
  case (3 \<Gamma> a)
  then show ?case
    by (simp, metis)
next
  case (4 \<Gamma> \<phi>)
  then show ?case
    apply simp
    try
    sorry
next
  case (5 \<Gamma> \<phi> \<psi>)
  then show ?case
    sorry
next
  case (6 \<Gamma> \<phi> \<psi>)
  then show ?case sorry
next
  case (7 \<Gamma> \<phi> \<psi>)
  then show ?case sorry
next
  case (10 \<Gamma> a)
  then show ?case
    by (simp, metis)
next
  case (11 \<Gamma> \<phi>)
  then show ?case sorry
next
  case (12 \<Gamma> \<phi> \<psi>)
  then show ?case sorry
next
  case (13 \<Gamma> \<phi> \<psi>)
  then show ?case sorry
next
  case (14 \<Gamma> \<phi> \<psi>)
  then show ?case sorry
qed auto