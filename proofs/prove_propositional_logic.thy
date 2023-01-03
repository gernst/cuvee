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

fun size' :: "bool \<Rightarrow> 'a formula \<Rightarrow> nat"  where
  "size' True  T         = 0" |
  "size' False F         = 0" |
  "size' False T         = 1" |
  "size' True  F         = 1" |
  "size' b     (Atom a)  = 1" |
  "size' b     (Not p)   = 1 + (size' (\<not> b) p)" |
  "size' b     (And p q) = 1 + (size' True  p) + (size' True  q)" |
  "size' b     (Or  p q) = 1 + (size' False p) + (size' False q)" |
  "size' b     (Imp p q) = 1 + (size' True  p) + (size' b     q)"

lemma size'_ex_atom:
  "size' b (atom \<Gamma> a c) = 0 \<or> size' b (atom \<Gamma> a c) = 1"
(* Wie kann ich hier cases (c, auto) auf alle subgoals anwenden? Ich hab es schon mit apply probiert,
   das Taktiken, soweit ich das verstehe, auf alle Goals anwenden soll. Das hat Isabelle aber nicht
   genommen, als ich das am Ende mit `done` abgeschlossen habe. *)
proof (cases b)
  case True
  then show ?thesis by (cases c, auto)
next
  case False
  then show ?thesis by (cases c, auto)
qed
(* I hoped it would work similarly to the induction proofs, however, this doesn't seem to be the case.
   More concretely, what I hoped would work is:   by (cases b) (cases c, auto)   
   As far as I understand, this would be short for
     proof (cases b) qed (cases c, auto)
   which I thought applies the proof commands after `qed` to all cases which are not given.
   So in this situation, I expected this to close the proof.

   What I don't understand now is why the proof above works / is correct and mine doesn't work :/
*)

lemma size'_atom[intro]:
  "size' b (Atom a) \<le> n \<Longrightarrow> size' b (atom \<Gamma> a c) \<le> n"
  (* by auto  \<leftarrow> Doesn't work at all, though I hoped it could use the previous lemma. *)
  (* Also, I thought this would be easy, since size' b (Atom a) = 1, so I expected that the goal should end up being "size' b (atom \<Gamma> a c) \<le> 1" or something similar. *)
  (* proof (simp add: size'_def) (* Here, I get an error: Undefined fact: "size'_def"\<^here>  *) *)

(* Cases below generated by the IDE. isabelle doesn't like them. *)
(*
proof (cases rule: atom.cases)
  case (1 \<Gamma> a)
  then show ?thesis sorry
next
  case (2 \<Gamma> a)
  then show ?thesis sorry
qed
*)


(* Another attempt, here the problem was basically showing that we have covered all cases here \<down> (i.e. totality)
   Syntax was taken from https://isabelle.in.tum.de/community/Isabelle_Cheat_Sheet
*)
(*lemma size'_atom[intro]:
  "size' b (Atom a) \<le> n \<Longrightarrow> size' b (atom \<Gamma> a c) \<le> n"
proof -
  consider (foo) "atom \<Gamma> a c = T" | (bar) "atom \<Gamma> a c = F" | (baz) "atom \<Gamma> a c = Atom a" by sorry
  then show ?thesis
  proof cases
    case foo
    then show ?thesis
      by (cases b, auto)
  next
    case bar
    then show ?thesis
      by (cases b, auto)
  next
    case baz
    then show ?thesis
      by (cases b, auto)
  qed
qed *)

(* trying to follow p. 24 of the Isar/Isabelle reference manual *)
proof -
  consider (zero) "size' b (atom \<Gamma> a c) = 0" | (one) "size' b (atom \<Gamma> a c) = 1"
    by auto
  then have "size' b (atom \<Gamma> a c) \<le> 1"
  proof cases
    case zero
    then show ?thesis by auto
  next
    case one
    then show ?thesis by auto
  qed
  have "size' b (Atom a) = 1" by simp
  hence "1 \<le> n" sorry
  then have "size' b (atom \<Gamma> a c) \<le> n" sorry
  (* And here, this is the RHS of the implicaiton, which I'd wanna use here. *sigh* *)

(* bailing out here :/ *)

lemma size'_not[intro]:
  "size' b (Not p) \<le> n \<Longrightarrow> size' b (not p) \<le> n"
proof (cases b)
  case True
  then show ?thesis
  (* then show "size' True (Not p) \<le> n \<Longrightarrow> size' True (not p) \<le> n"  \<leftarrow> This seemed reasonable at first, but doesn't work *)
    (* Here, I seem to have lost the antecedent from the implication :/ *)
    (* using assm(s)  doesn't work, as the LHS doesn't seem to be in the context anymore? Where'd it go?
       I am under the impression that it was removed by the `then show ?thesis` part, however, I don't know why.
       According to the manual, ?thesis should be the *unchanged* goal statement?
    *)
    apply (simp)
    
    sorry
next
  case False
  then show ?thesis sorry
qed

lemma size'_and[intro]:
  "size' b (And p q) \<le> n \<Longrightarrow> size' b (and' p q) \<le> n"
  sorry

lemma size'_or[intro]:
  "size' b (Or p q) \<le> n \<Longrightarrow> size' b (or p q) \<le> n"
  sorry

lemma size'_imp[intro]:
  "size' b (Imp p q) \<le> n \<Longrightarrow> size' b (imp p q) \<le> n"
  sorry

lemma size'_decreases:
  shows   "size' True  (prove    \<Gamma> f) \<le> size' True  f"
    and   "size' False (disprove \<Gamma> f) \<le> size' False f"
  by (induction \<Gamma> f rule: prove_disprove.induct)
    auto
