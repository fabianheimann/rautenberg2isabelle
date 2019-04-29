theory PropLogic
  imports Main
begin

datatype 'av formula =
  p "'av"
  | andf "'av formula" "'av formula" (infixr "And" 68)
  | negf "'av formula" ("Neg")
 (* | Falsum *)

lemma and_assoc_example: "(p 1) And (p 2) And (p 3) = (p 1) And ((p 2) And (p 3))"
  by simp

lemma and_assoc_example2: "(p 1) And (p 2) And (p 3) \<noteq> ((p 1) And (p 2)) And (p 3)"
  by auto

abbreviation orf (infixr "Or" 67) where
"(orf f1 f2) \<equiv> Neg ( (Neg f1) And (Neg f2) )"

lemma binding_prior_example: "Neg (p 1) Or (p 2) And (p 1) =  (Neg (p 1) Or ((p 2) And (p 1) ) )"
  by simp

abbreviation implf (infixr "Impl" 68) where
"(implf f1 f2) \<equiv> Neg (f1 And (Neg f2))"

abbreviation biimplf (infixr "IImpl" 69) where
"biimplf f1 f2 \<equiv> (f1 Impl f2) And (f2 Impl f1)"

fun rg::"'a formula \<Rightarrow> nat" where
"rg (p _) = 0" |
"rg (f1 And f2) = max(rg f1)(rg f2) +1" |
"rg (Neg f1) = rg f1 +1" 
(* | "rg Falsum = 1" *)

lemma "(rg (andf (p (1::nat)) (orf (p 2) (negf (p 1)) ))) = 5"
  by(simp)

type_synonym 'a model = "('a \<Rightarrow> bool)"

fun ext_mod :: " ('a model) \<Rightarrow> 'a formula \<Rightarrow> bool" where
"ext_mod w (p y) = w y" |
"ext_mod w (f1 And f2) = ( (ext_mod w f1) \<and> (ext_mod w f2) )" |
"ext_mod w (Neg f) = (\<not> (ext_mod w f))"
(* | "ext_mod w Falsum = False" *)

fun w_example ::"nat \<Rightarrow> bool" where
"w_example n = (n=2)"

lemma ext_mod_example: " ext_mod w_example (andf (p (1::nat)) (orf (p 2) (negf (p 1)) )) = False"
  by(simp)

abbreviation sem_equiv (infix "\<equiv>f" 70) where
"sem_equiv (f1::'a formula) (f2:: 'a formula) \<equiv> \<forall> (w :: 'a model). ext_mod w f1 = ext_mod w f2"

lemma sem_equiv_neg_neg: "alpha \<equiv>f ( negf (negf alpha))"
  by(simp)

lemma sem_equiv_assoc_and: "((alpha And beta) And gamma) \<equiv>f (alpha And (beta And gamma))"
  by(simp)

lemma sem_equiv_assoc_or: "((alpha Or beta) Or gamma) \<equiv>f (alpha Or beta Or gamma)"
  by(simp)

lemma sem_equiv_comm_and: "(alpha And beta) \<equiv>f (beta And alpha)"
  by(simp, auto)

lemma sem_equiv_comm_or: "(alpha Or beta) \<equiv>f (beta Or alpha)"
  by(simp, auto)

lemma sem_equiv_diag_and: "(alpha And alpha) \<equiv>f alpha"
  by(simp)

lemma sem_equiv_diag_or: "(alpha Or alpha) \<equiv>f alpha"
  by(simp)

lemma sem_equiv_absorb_and: "(alpha And (alpha Or beta)) \<equiv>f alpha"
  by(simp, auto)

lemma sem_equiv_absorb_or : "(alpha Or (alpha And beta)) \<equiv>f alpha"
  by(simp, auto)

lemma sem_equiv_distr1: "(alpha And (beta Or gamma)) \<equiv>f ((alpha And beta) Or (alpha And gamma))"
  by(simp, auto)

lemma sem_equiv_distr2: "(alpha Or (beta And gamma)) \<equiv>f ((alpha Or beta) And (alpha Or gamma))"
  by(simp, auto)

lemma sem_equiv_demorgan1: "(Neg (alpha And beta)) \<equiv>f (Neg alpha Or Neg beta)"
  by(simp)

lemma sem_equiv_demorgan2: "(Neg (alpha Or beta)) \<equiv>f (Neg alpha And Neg beta)"
  by(simp)

lemma sem_equiv_refl: "alpha \<equiv>f alpha"
  by(simp)

lemma sem_equiv_symm: "sem_equiv alpha beta \<longrightarrow> sem_equiv beta alpha"
  by(simp)

lemma sem_equiv_trans: "sem_equiv alpha beta \<longrightarrow> sem_equiv beta gamma \<longrightarrow> sem_equiv alpha gamma"
  by(simp)

lemma sem_equiv_kongr: "alpha \<equiv>f alpha' \<and> beta \<equiv>f beta'
 \<longrightarrow> (andf alpha beta) \<equiv>f (andf alpha' beta') \<and>
     (orf alpha beta) \<equiv>f (orf alpha' beta') \<and>
     (negf alpha) \<equiv>f (negf alpha')"
  by(simp)

abbreviation fulfills where
"fulfills (w :: 'a model) (alpha :: 'a formula) \<equiv> (ext_mod w alpha = True)"

abbreviation fulfillsS where
"fulfillsS (w :: 'a model) (X :: 'a formula set) \<equiv> (\<forall> alpha \<in> X. fulfills w alpha)"

lemma fulfills_prop_prime: "\<forall> (v:: 'a) (w::'a model). fulfills w (p v) \<longleftrightarrow> w v = True"
  by(simp)

lemma fulfills_prop_and: "fulfills w (alpha And beta) \<longleftrightarrow> fulfills w alpha \<and> fulfills w beta"
  by(simp)

lemma fulfills_prop_or: "fulfills w (alpha Or beta) \<longleftrightarrow> fulfills w alpha \<or> fulfills w beta"
  by(simp)

lemma fulfills_prop_neg: "fulfills w (Neg alpha ) \<longleftrightarrow> \<not> fulfills w alpha"
  by(simp)

lemma fulfills_prop_impl: "fulfills w (alpha Impl beta) \<longleftrightarrow> ( (fulfills w alpha) \<longrightarrow> (fulfills w beta))"
  by(simp)

abbreviation taut where
" taut (alpha :: 'a formula) \<equiv> \<forall> (w :: 'a model). fulfills w alpha"

abbreviation contradiction where
"contradiction (alpha :: 'a formula) \<equiv> \<nexists> (w :: 'a model). fulfills w alpha"

lemma taut_example: "taut (alpha Or Neg alpha)"
  by(simp)

lemma contradiction_example1: "contradiction (alpha And Neg alpha)"
  by(simp)

lemma contradiction_example2: "contradiction (alpha IImpl ( Neg alpha))"
  by(simp)

lemma impl_taut_self: "taut (p1 Impl p1)"
  by(simp)

lemma impl_taut_add_praem: "taut ( p1 Impl (q Impl p1))"
  by(simp)

lemma impl_taut_swap_praem: "taut ( (p1 Impl q Impl r) Impl (q Impl p1 Impl r) )"
  by(simp)

lemma impl_taut_circ: "taut ( (p1 Impl q) Impl (q Impl r) Impl (p1 Impl r) )"
  by(simp)

lemma impl_taut_fregecirc: "taut ( (p1 Impl q Impl r) Impl ( (p1 Impl q) Impl (p1 Impl r)) )"
  by(simp)

lemma impl_taut_pierce: "taut ( ( (p1 Impl q) Impl p1) Impl p1)"
  by(simp, blast)

definition ImplSem (infix "\<Turnstile>" 74) where
" ImplSem (X :: ('a formula) set) (alpha :: 'a formula) \<equiv>
  \<forall> (w:: 'a model). (\<forall> x \<in> X. fulfills w x) \<longrightarrow> fulfills w alpha"

lemma empty_ImplSem_iff_taut: "taut alpha \<longleftrightarrow> {} \<Turnstile> alpha"
  by(simp add: ImplSem_def)

lemma ImplSem_refl: "alpha \<in> X \<longrightarrow> X \<Turnstile> alpha"
  by(simp add:ImplSem_def)

lemma Impl_Sem_mon: " X \<subseteq> X' \<longrightarrow> X \<Turnstile> alpha \<longrightarrow> X' \<Turnstile> alpha"
  by(simp add:ImplSem_def, auto)

lemma Impl_Sem_trans: "(\<forall> y \<in> Y. X \<Turnstile> y) \<and> Y \<Turnstile> alpha \<longrightarrow> X \<Turnstile> alpha"
  by(simp add:ImplSem_def)

lemma Impl_Sem_and_example1: "{alpha, beta} \<Turnstile> (alpha And beta)"
  by(simp add:ImplSem_def)

lemma Impl_Sem_and_example2: "{alpha And beta} \<Turnstile> alpha"
  by(simp add:ImplSem_def)

lemma Impl_Sem_and_example3: "{alpha And beta} \<Turnstile> beta"
  by(simp add:ImplSem_def)

lemma Impl_Sem_and_example4: "(X \<Turnstile> (alpha And beta) ) \<longleftrightarrow> ( X \<Turnstile> alpha \<and> X \<Turnstile> beta )"
  by(simp add:ImplSem_def, auto)

lemma Impl_Sem_impl_example: "{alpha, alpha Impl beta} \<Turnstile> beta"
  by(simp add: ImplSem_def)

lemma Impl_Sem_elim_example:
"(X \<union> {alpha}) \<Turnstile> beta \<and> (X \<union> {Neg alpha}) \<Turnstile> beta \<longrightarrow> X \<Turnstile> beta"
  by(simp add: ImplSem_def, auto)

type_synonym 'a subst = "('a \<Rightarrow> 'a formula)"

fun ext_subst ::"'a subst \<Rightarrow> 'a formula \<Rightarrow> 'a formula" where
"ext_subst sigma (p v) = sigma v" |
"ext_subst sigma (f1 And f2) = (ext_subst sigma f1) And (ext_subst sigma f2)" |
"ext_subst sigma (Neg f) = Neg (ext_subst sigma f)"
(* | "ext_subst sigma Falsum = Falsum" *)

fun app_subst ::"'a subst \<Rightarrow> 'a formula set \<Rightarrow> 'a formula set" where
"app_subst sigma X = ext_subst sigma ` X"

lemma app_subst_demo:
"app_subst (\<lambda> n. (p (n+2) ) And (p (n+1) )) { p (1:: nat), (p (2::nat)) And (p (3::nat))}
= {p 3 And p 2, (p 4 And p 3) And p 5 And p 4} " by(auto)

(*
lemma subst_helper_lemma:
" fulfills (w :: 'a model) (ext_subst sigma alpha)
= fulfills (\<lambda> (a :: 'a). ext_mod w (sigma a)) alpha"
  apply(induction alpha) apply(auto) done
*)

lemma subst_helper_lemma2:
" ext_mod (w :: 'a model) (ext_subst sigma alpha)
= ext_mod (\<lambda> (a :: 'a). ext_mod w (sigma a)) alpha"
  by(induction alpha, auto)

theorem substituion_invariance: "X \<Turnstile> alpha \<longrightarrow> app_subst sigma X \<Turnstile> ext_subst sigma alpha"
  apply(simp add:ImplSem_def) apply(auto)
  apply(simp add:subst_helper_lemma2) done

theorem deduction_theorem: " (X \<union> {alpha}) \<Turnstile> beta \<longleftrightarrow> X \<Turnstile> (alpha Impl beta)"
  apply(simp add:ImplSem_def) apply(auto) done

inductive ImplGen :: "'a formula set \<Rightarrow> 'a formula \<Rightarrow> bool" (infix "\<turnstile>" 56) where
AR: "ImplGen {alpha} alpha" |
MR: "\<lbrakk> (X::'a formula set) \<subseteq> (X' ::'a formula set) ; ImplGen X alpha \<rbrakk> \<Longrightarrow> ImplGen X' alpha" |
ANDI: "\<lbrakk> ImplGen X alpha ; ImplGen X beta \<rbrakk> \<Longrightarrow> ImplGen X (alpha And beta)" |
ANDl: "ImplGen X (alpha And beta) \<Longrightarrow> ImplGen X alpha" |
ANDr: "ImplGen X (alpha And beta) \<Longrightarrow> ImplGen X beta" |
NEG1: " \<lbrakk> ImplGen X alpha ; ImplGen X (Neg alpha) \<rbrakk> \<Longrightarrow> ImplGen X beta" |
NEG2: " \<lbrakk> ImplGen (X \<union> {alpha}) beta ; ImplGen (X \<union> { Neg alpha}) beta \<rbrakk>
       \<Longrightarrow> ImplGen X beta"

lemma ImplGen_and_example: "{alpha, beta} \<turnstile> (alpha And beta)"
proof -
  from ImplGen.AR have "{alpha} \<turnstile> alpha" by(auto)
  hence A: "{alpha,beta} \<turnstile> alpha" by(simp add: ImplGen.MR[of "{alpha}" "{alpha,beta}"])
  from ImplGen.AR have "{beta} \<turnstile> beta" by(auto)
  hence B: "{alpha,beta} \<turnstile> beta" by(simp add: ImplGen.MR[of "{beta}" "{alpha,beta}"])
  from A B show "{alpha, beta} \<turnstile> (alpha And beta)" by(rule ImplGen.ANDI)
qed

lemma ImplGen_neg_elim_example: "X \<union> {Neg alpha} \<turnstile> alpha \<longrightarrow> X \<turnstile> alpha"
proof
  assume A: "X \<union> {Neg alpha} \<turnstile> alpha"
  have 0: "{alpha} \<turnstile> alpha" by(rule AR)
  have 1: "{alpha} \<subseteq> X \<union> {alpha}" by(auto)
  from 0 1 MR have 2: "X \<union> {alpha} \<turnstile> alpha" by(blast)
  from A 2 NEG2 show "X \<turnstile> alpha" by(auto)
qed

lemma ImplGen_reductio_example: " (X \<union> {Neg alpha} \<turnstile> beta \<and>
X \<union> {Neg alpha} \<turnstile> Neg beta ) \<longrightarrow> X \<turnstile> alpha"
proof
  assume A: " X \<union> {Neg alpha} \<turnstile> beta \<and> X \<union> {Neg alpha} \<turnstile> Neg beta"
  from A have A1: "X \<union> {Neg alpha} \<turnstile> beta" by(simp)
  from A have A2: "X \<union> {Neg alpha} \<turnstile> Neg beta" by (simp)
  from A1 A2 have 2: "X \<union> {Neg alpha} \<turnstile> alpha" by (rule NEG1)
  from 2 ImplGen_neg_elim_example show "X \<turnstile> alpha" by (auto)
qed

lemma ImplGen_rightarrow_elim_example: " (X \<turnstile> alpha Impl beta) \<longrightarrow> X \<union> {alpha} \<turnstile> beta"
proof
  assume H: "(X \<turnstile> alpha Impl beta)"
  from ImplGen.AR[of "alpha"] ImplGen.MR[of "{alpha}" "X \<union> {alpha, Neg beta}"]
  have A: "X \<union> {alpha, Neg beta} \<turnstile> alpha" by(auto)
  from ImplGen.AR[of "Neg beta"] ImplGen.MR[of "{Neg beta}" "X \<union> {alpha, Neg beta}"]
  have B: "X \<union> {alpha, Neg beta} \<turnstile> Neg beta" by(auto)
  from A B have 2: "X \<union> {alpha, Neg beta} \<turnstile> alpha And (Neg beta)" by(rule ImplGen.ANDI)
  from H have 3: "X \<turnstile> Neg(alpha And Neg beta)" by(simp)
  from ImplGen.MR 3 have 4: "X \<union> {alpha, Neg beta} \<turnstile> Neg(alpha And Neg beta)" by(blast)
  from 2 4 have 5: "X \<union> {alpha, Neg beta} \<turnstile> beta" by(rule ImplGen.NEG1)
  from this ImplGen_neg_elim_example [of "X \<union> {alpha}" "beta"]
  show "X \<union> {alpha} \<turnstile> beta" by (simp add: insert_commute)
qed

(* TODO: Further examples *)

theorem ImplGen_correct:"X \<turnstile> alpha \<longrightarrow> X \<Turnstile> alpha"
proof
  fix alpha
  show "X \<turnstile> alpha \<Longrightarrow> X \<Turnstile> alpha"
  proof(induction alpha rule: ImplGen.induct)
case (AR alpha)
  thus "{alpha} \<Turnstile> alpha" by(simp add:ImplSem_refl)
next
case (MR X X' alpha)
  thus ?case by(simp add:Impl_Sem_mon)
next
case (ANDI X alpha beta)
  thus ?case by(simp add:Impl_Sem_and_example4)
next
  case (ANDl X alpha beta)
  thus ?case by(simp add: Impl_Sem_and_example4)
next
case (ANDr X alpha beta)
  thus ?case by(simp add: Impl_Sem_and_example4)
next
  case (NEG1 X alpha beta)
  thus ?case by(simp add: ImplSem_def, auto)
next
case (NEG2 X alpha beta)
  thus ?case by(simp add: Impl_Sem_elim_example[of "X" "alpha" "beta"])
qed
qed
  
theorem finiteness_theorem: "((X :: 'a formula set) \<turnstile> (alpha :: 'a formula) ) \<Longrightarrow>
      (\<exists> (X0 :: 'a formula set). X0 \<subseteq> X \<and> finite X0 \<and> X0 \<turnstile> alpha )"
proof(induction rule: ImplGen.induct)
  case (AR alpha)
  show ?case proof
    have 1: "{alpha} \<turnstile> alpha" by(rule AR)
    have 2: "finite {alpha}" by(auto)
    from 1 2 show "{alpha} \<subseteq> {alpha} \<and> finite {alpha} \<and> {alpha} \<turnstile> alpha" by(simp)
  qed
next
  case(MR X X' alpha)
  from MR.IH obtain X0 where pX0: "X0\<subseteq>X \<and> finite X0 \<and> X0 \<turnstile> alpha" by(auto)
  show ?case proof
      from pX0 MR(1) have SP: "X0 \<subseteq> X'" by (auto)
      from SP pX0 show "X0\<subseteq>X' \<and> finite X0 \<and> X0 \<turnstile> alpha" by(simp)
    qed
next
  case (ANDI X alpha beta)
  from ANDI.IH(1) obtain X0a where pX0a: "X0a\<subseteq>X \<and> finite X0a \<and> X0a \<turnstile> alpha" by(auto)
  from ANDI.IH(2) obtain X0b where pX0b: "X0b\<subseteq>X \<and> finite X0b \<and> X0b \<turnstile> beta" by(auto)
  show ?case proof
    from pX0a pX0b have p1: "(X0a \<union> X0b) \<subseteq> X" by(auto)
    from pX0a pX0b have p2: "finite (X0a \<union> X0b)" by(auto)
    from pX0a MR have p3: "(X0a \<union> X0b) \<turnstile> alpha" by(blast)
    from pX0b MR have p4: "(X0a \<union> X0b) \<turnstile> beta" by(blast)
    from p3 p4 have p5: "(X0a \<union> X0b) \<turnstile> (alpha And beta)" by (rule ImplGen.ANDI)
    from p1 p2 p5 show "( X0a \<union> X0b) \<subseteq> X \<and> finite ( X0a \<union> X0b) \<and> ( X0a \<union> X0b) \<turnstile> alpha And beta" by(auto)
  qed
next
  case (ANDl X alpha beta)
  from ANDl.IH obtain X0 where pX0: "X0\<subseteq>X \<and> finite X0 \<and> X0 \<turnstile> (alpha And beta)" by(auto)
  show ?case proof
    from ImplGen.ANDl pX0 show "X0 \<subseteq> X \<and> finite X0 \<and> X0 \<turnstile> alpha" by(auto)
  qed
next
  case (ANDr X alpha beta)
  from ANDr.IH obtain X0 where pX0: "X0\<subseteq>X \<and> finite X0 \<and> X0 \<turnstile> (alpha And beta)" by(auto)
  show ?case proof
    from ImplGen.ANDr pX0 show "X0 \<subseteq> X \<and> finite X0 \<and> X0 \<turnstile> beta" by(auto)
  qed
next
  case (NEG1 X alpha beta)
  from NEG1.IH(1) obtain X0p where pX0p: "X0p\<subseteq>X \<and> finite X0p \<and> X0p \<turnstile> alpha" by(auto)
  from NEG1.IH(2) obtain X0n where pX0n: "X0n\<subseteq>X \<and> finite X0n \<and> X0n \<turnstile> Neg alpha" by(auto)
  show ?case proof
    from pX0p pX0n have p1: "(X0p \<union> X0n) \<subseteq> X" by(auto)
    from pX0p pX0n have p2: "finite (X0p \<union> X0n)" by(auto)
    from pX0p MR have p3: "(X0p \<union> X0n) \<turnstile> alpha" by(blast)
    from pX0n MR have p4: "(X0p \<union> X0n) \<turnstile> Neg alpha" by(blast)
    from p3 p4 have p5: "(X0p \<union> X0n) \<turnstile> beta" by (rule ImplGen.NEG1)
    from p1 p2 p5 show "( X0p \<union> X0n) \<subseteq> X \<and> finite ( X0p \<union> X0n) \<and> ( X0p \<union> X0n) \<turnstile> beta" by(auto)
  qed
next
  case (NEG2 X alpha beta)
  from NEG2.IH(1) obtain X0p where pX0p: "X0p\<subseteq>X\<union> {alpha} \<and> finite X0p \<and> X0p \<turnstile> beta" by(auto)
  from NEG2.IH(2) obtain X0n where pX0n: "X0n\<subseteq>X\<union> {Neg alpha} \<and> finite X0n \<and> X0n \<turnstile> beta" by(auto)
  show ?case proof
    from pX0p pX0n have p1: "((X0p - {alpha}) \<union> (X0n - {Neg alpha})) \<subseteq> X" by(auto)
    from pX0p pX0n have p2: "finite ((X0p \<union> X0n)- {alpha, Neg alpha})" by(auto)
    have "X0p \<subseteq> ((X0p - {alpha}) \<union> {alpha})" by (blast)
    from this pX0p have p3: "((X0p - {alpha}) \<union> {alpha}) \<turnstile> beta" by(simp add: ImplGen.MR)
    have "X0n \<subseteq> ((X0n - {Neg alpha}) \<union> {Neg alpha})" by (blast)
    from this pX0n have p4: "((X0n - {Neg alpha}) \<union> {Neg alpha}) \<turnstile> beta" by(simp add: ImplGen.MR)
    have "((X0p - {alpha}) \<union> {alpha}) \<subseteq> ((X0p - {alpha}) \<union> (X0n - {Neg alpha})) \<union> {alpha}" by(blast)
    from this p3 have p5: "((X0p - {alpha}) \<union> (X0n - {Neg alpha})) \<union> {alpha} \<turnstile> beta" by(rule ImplGen.MR)
    have "((X0n - {Neg alpha}) \<union> {Neg alpha}) \<subseteq> ((X0p - {alpha}) \<union> (X0n - {Neg alpha})) \<union> {Neg alpha}" by(blast)
    from this p4 have p6: "((X0p - {alpha}) \<union> (X0n - {Neg alpha})) \<union> {Neg alpha} \<turnstile> beta" by(rule ImplGen.MR)
    from p5 p6 have p7: "((X0p - {alpha}) \<union> (X0n - {Neg alpha})) \<turnstile> beta" by(rule ImplGen.NEG2)
    from p7 p1 p2 show "((X0p - {alpha}) \<union> (X0n - {Neg alpha}))\<subseteq>X
               \<and> finite ((X0p - {alpha}) \<union> (X0n - {Neg alpha}))
               \<and> ((X0p - {alpha}) \<union> (X0n - {Neg alpha})) \<turnstile> beta" by (auto)
  qed
qed

definition incons_FS ::"'a formula set \<Rightarrow> bool" where
"incons_FS (X:: 'a formula set) \<equiv> \<forall> (alpha::'a formula). X \<turnstile> alpha"

abbreviation cons_FS ::"'a formula set \<Rightarrow> bool" where
"cons_FS X \<equiv> \<not> incons_FS X"

definition max_cons_FS::"'a formula set \<Rightarrow> bool" where
"max_cons_FS (X :: 'a formula set) \<equiv>
   (cons_FS X) \<and> ( \<forall> (Y :: 'a formula set). Y \<supset> X \<longrightarrow> incons_FS Y)"

abbreviation Falsum where
"Falsum (f :: 'a formula) \<equiv> (f) And (Neg f)"

lemma incons_prop: "\<forall> (f :: 'a formula). X \<turnstile> Falsum f \<longleftrightarrow> incons_FS X"
proof
  fix f show "X \<turnstile> Falsum f \<longleftrightarrow> incons_FS X" proof
    assume H: "X \<turnstile> Falsum f"
    have "\<forall> alpha. X \<turnstile> alpha" proof
      fix alpha
      from H ImplGen.ANDl ImplGen.ANDr ImplGen.NEG1 show "X \<turnstile> alpha" by(blast)
    qed
    from this incons_FS_def show "incons_FS X" by(auto)
  next
    assume "incons_FS X"
    hence H:"\<forall> alpha. X \<turnstile> Falsum f" by(simp add: incons_FS_def)
    thus "X \<turnstile> Falsum f" by (auto)
  qed
qed

lemma cons_prop: " \<forall> (f :: 'a formula). \<not> ( X \<turnstile> Falsum f) \<longleftrightarrow> cons_FS X"
  by(simp add: incons_prop)

lemma Cplus_ImplSem_prop: " X \<turnstile> alpha \<longleftrightarrow> incons_FS ( X \<union> { Neg alpha} )"
proof
  assume H: "X \<turnstile> alpha"
  from this ImplGen.MR have 1: "X \<union> {Neg alpha} \<turnstile> alpha" by(blast)
  have 2: "{Neg alpha} \<turnstile> Neg alpha" by(rule ImplGen.AR)
  from this ImplGen.MR have 3: "X \<union> {Neg alpha} \<turnstile> Neg alpha" by(blast)
  from 1 3 ImplGen.NEG1 have "\<forall> beta. X \<union> {Neg alpha} \<turnstile> beta" by(auto)
  thus "incons_FS (X \<union> {Neg alpha}) " by(simp add: incons_FS_def)
next
  assume "incons_FS (X \<union> {Neg alpha})"
  hence 1:"X \<union> {Neg alpha} \<turnstile> alpha" by(simp add:incons_FS_def)
  from ImplGen.MR ImplGen.AR have 2: "X \<union> {alpha} \<turnstile> alpha" by (blast)
  from 1 2 ImplGen.NEG2 show "X \<turnstile> alpha" by(auto)
qed

lemma Cplus_ImplSem_prop2: "\<forall> (f :: 'a formula).
                     X \<turnstile> alpha \<longleftrightarrow> (X \<union> {Neg alpha}) \<turnstile> Falsum f"
proof
  fix f show " X \<turnstile> alpha \<longleftrightarrow> (X \<union> {Neg alpha}) \<turnstile> Falsum f" proof
    assume H: "X \<turnstile> alpha"
    from this Cplus_ImplSem_prop have "incons_FS (X \<union> {Neg alpha})" by(auto)
    from this incons_prop show "(X \<union> {Neg alpha}) \<turnstile> Falsum f" by(auto)
  next
    assume H: "(X \<union> {Neg alpha}) \<turnstile> Falsum f"
    from this incons_prop have "incons_FS (X \<union> {Neg alpha})" by(auto)
    from this Cplus_ImplSem_prop show "X \<turnstile> alpha" by(auto)
  qed
qed

lemma Cminus_ImplSem_prop: " X \<turnstile> Neg alpha \<longleftrightarrow> incons_FS ( X \<union> {alpha} )"
proof
  assume H: "X \<turnstile> Neg alpha"
  from this ImplGen.MR have 1: "X \<union> {alpha} \<turnstile> Neg alpha" by(blast)
  have 2: "{alpha} \<turnstile> alpha" by(rule ImplGen.AR)
  from this ImplGen.MR have 3: "X \<union> {alpha} \<turnstile> alpha" by(blast)
  from 1 3 ImplGen.NEG1 have "\<forall> beta. X \<union> {alpha} \<turnstile> beta" by(auto)
  thus "incons_FS (X \<union> { alpha}) " by(simp add: incons_FS_def)
next
  assume "incons_FS (X \<union> {alpha})"
  hence 1:"X \<union> {alpha} \<turnstile> Neg alpha" by(simp add:incons_FS_def)
  from ImplGen.MR ImplGen.AR have 2: "X \<union> {Neg alpha} \<turnstile> Neg alpha" by (blast)
  from 1 2 ImplGen.NEG2 show "X \<turnstile> Neg alpha" by(auto)
qed

lemma Cminus_ImplSem_prop2: "\<forall> (f :: 'a formula).
                    X \<turnstile> Neg alpha \<longleftrightarrow> (X \<union> {alpha}) \<turnstile> Falsum f"
proof
  fix f show "X \<turnstile> Neg alpha \<longleftrightarrow> (X \<union> {alpha}) \<turnstile> Falsum f" proof
    assume H: "X \<turnstile> Neg alpha"
    from this Cminus_ImplSem_prop have "incons_FS (X \<union> {alpha})" by(auto)
    from this incons_prop show "(X \<union> {alpha}) \<turnstile> Falsum f" by(auto)
  next
    assume H: "(X \<union> {alpha}) \<turnstile> Falsum f"
    from this incons_prop have "incons_FS (X \<union> {alpha})" by(auto)
    from this Cminus_ImplSem_prop show "X \<turnstile> Neg alpha" by(auto)
  qed
qed

definition H::"'a formula set \<Rightarrow> 'a formula set set" where
"H X = { Y. X \<subseteq> Y \<and> cons_FS Y}"

lemma finite_chain_contains_Union:
"finite (F :: 'a set set) \<Longrightarrow> F \<noteq> {} \<Longrightarrow> 
 (\<forall> x \<in>F. \<forall> y \<in> F. (x \<subseteq> y) \<or> (y \<subseteq> x) )
 \<Longrightarrow> \<Union> F \<in> F"
proof(induct F rule: finite_induct)
  case empty
  then show ?case by(simp)
next
  case (insert x F)
  then show ?case
    by (metis Sup_insert Un_absorb1 Un_absorb2 ccpo_Sup_singleton insertCI)
qed

lemma empty_set_consistent: "\<not> ( {} \<turnstile> Falsum alpha)"
proof
  assume H: "{} \<turnstile> (alpha :: 'a formula) And (Neg alpha)"
  from H have "{} \<turnstile> alpha" by (simp add: ImplGen.ANDl)
  hence A: "{} \<Turnstile> alpha" by (simp add: ImplGen_correct)
  hence "\<forall> w. fulfills w alpha" by(simp add: ImplSem_def)
  hence "ext_mod (\<lambda> v. True) alpha = True" by(auto)
  hence CON1: "ext_mod (\<lambda> v. True) (Neg alpha) = False" by(auto)
  from H have "{} \<turnstile> Neg alpha" by (simp add: ImplGen.ANDr)
  hence B: "{} \<Turnstile> Neg alpha" by (simp add: ImplGen_correct)
  hence "\<forall> w. fulfills w (Neg alpha)" by(simp add: ImplSem_def[of "{}" "Neg alpha"])
  hence CON2: "ext_mod (\<lambda> v. True) (Neg alpha) = True" by(auto)
  from CON1 CON2 show "False" by(auto)
qed

lemma lindenbaum: "cons_FS (X:: 'a formula set) \<longrightarrow> ( \<exists> X'. X \<subseteq> X' \<and> max_cons_FS X' )"
proof
  assume "cons_FS X"
  from this H_def have 0: "X \<in> H X" by(blast)

  have " \<forall> K . subset.chain (H X) K \<longrightarrow> (\<exists> U \<in> (H X). \<forall> X' \<in>K . X' \<subseteq> U)" proof
    fix K :: "'a formula set set"
    have "K = {} \<or> K \<noteq> {}" by(auto)
    then show "subset.chain (H X) K \<longrightarrow> (\<exists> U \<in> (H X). \<forall> X' \<in>K . X' \<subseteq> U)" proof
    assume A: "K = {}"
    show "subset.chain (H X) K \<longrightarrow> (\<exists> U \<in> (H X). \<forall> X' \<in>K . X' \<subseteq> U)" proof
      assume 1: "subset.chain (H X) K"
      show "(\<exists> U \<in> (H X). \<forall> X' \<in>K . X' \<subseteq> U)" proof
        from A show "\<forall> X' \<in> K. X' \<subseteq> X" by(auto)
        from 0 show "X \<in> H X" by(simp)
      qed
    qed
  next
    assume B: "K \<noteq> {}"
    show "subset.chain (H X) K \<longrightarrow> (\<exists> U \<in> (H X). \<forall> X' \<in>K . X' \<subseteq> U)" proof
      assume 1: "subset.chain (H X) K"
        show "(\<exists> U \<in> (H X). \<forall> X' \<in>K . X' \<subseteq> U)" proof
          show "\<forall> X' \<in> K. X' \<subseteq> \<Union> K" by (auto)
          from 1 subset.chain_def have 2: "K \<subseteq> (H X)" by(auto)
          from this H_def have 3: "\<forall> Y \<in> K. X \<subseteq> Y" by(auto)
          from B 3 have 4: "X \<subseteq> \<Union> K" by(auto)
          have 5: "cons_FS (\<Union> K)" proof(rule ccontr)
            assume "\<not> cons_FS (\<Union> K)"
            hence "incons_FS (\<Union> K)" by(simp)
            hence "\<Union> K \<turnstile> Falsum alpha" by(simp add: incons_prop)
            hence "\<exists> U0 \<subseteq> \<Union> K. finite U0 \<and> U0 \<turnstile> Falsum alpha" by(simp add:finiteness_theorem)
            then obtain U0 where 6: "U0 \<subseteq> \<Union> K \<and> finite U0 \<and> U0 \<turnstile> Falsum alpha" by(auto)
            then have fin: "finite U0" by(auto)
            from 6 have 7: "\<forall> alpha_i \<in> U0. \<exists> Y. Y \<in> K \<and> alpha_i \<in> Y" by(auto)
            from finite_set_choice[OF fin 7] obtain f where fprop: "\<forall> alpha_i \<in> U0. f alpha_i \<in> K \<and> alpha_i \<in> f alpha_i" by(auto)
            from fprop have "U0 \<subseteq> \<Union> (f ` U0)" by(auto) (* Y = \<Union> (f ` U0) *)
            from this 6 ImplGen.MR have CON1: "\<Union> (f ` U0) \<turnstile> Falsum alpha" by(auto)
            from fin have fin': "finite ( (f ` U0) )" by(auto)
            from fprop 1 have "subset.chain (H X) (f ` U0)" by (simp add: subset.chain_def subset_eq)
            from this subset.chain_def[of "H X" "(f ` U0)"] have 8: "\<forall> x \<in> (f` U0). \<forall> y \<in> (f` U0). x \<subseteq> y \<or> y \<subseteq> x" by(auto)
            have U0_nonempty: "U0 \<noteq> {}" proof
              assume "U0 = {}"
              from this 6 have "{} \<turnstile> Falsum alpha" by(auto)
              from this empty_set_consistent show "False" by(auto)
            qed
            from this have "(f ` U0) \<noteq> {}" by(auto)
            from this 8 fin' finite_chain_contains_Union[of "(f ` U0)"] have "\<Union> (f` U0) \<in> (f ` U0)" by(auto)
            from this fprop 2 have "\<Union> (f ` U0) \<in> (H X)" by(auto)
            from this have "cons_FS ( \<Union> (f `U0) )" by(simp add: H_def)
            from this have CON2: "\<not> ( \<Union> (f `U0) \<turnstile> Falsum alpha )" by(simp add: cons_prop)
            from CON1 CON2  show "False"  by(auto)
          qed
          from 4 5 H_def show "\<Union> K \<in> (H X)" by(auto)
        qed
      qed
    qed
  qed
  from this subset_Zorn have "\<exists> M \<in> (H X). \<forall> X' \<in> (H X). M \<subseteq> X' \<longrightarrow> X' = M" by(blast)
  then obtain M where Mprop: "M \<in> (H X) \<and> (\<forall> X' \<in> (H X). M \<subseteq> X' \<longrightarrow> X' = M)" by(auto)
  show " \<exists>X'. X \<subseteq> X' \<and> max_cons_FS X'" proof
    from Mprop have Prop1: "X \<subseteq> M" by(simp add: H_def)
    from Mprop have 2: "cons_FS M" by(simp add:H_def)
    have 3: "\<forall> Y. M \<subset> Y \<longrightarrow> incons_FS Y" proof
      fix Y show "M \<subset> Y \<longrightarrow> incons_FS Y" proof
        assume H1: "M \<subset> Y" show "incons_FS Y" proof(rule ccontr)
          assume H2: "cons_FS Y"
          from H_def[of "X"] H2 Prop1 H1 have "Y \<in> (H X)" by (simp add:H_def)
          from this Mprop H1 have "M = Y" by(blast)
          from this H1 show "False" by(auto)
        qed
      qed
    qed
    from 2 3 max_cons_FS_def have Prop2: "max_cons_FS M" by(auto)
    from Prop1 Prop2 show "X \<subseteq> M \<and> max_cons_FS M " by(auto)
  qed
qed

lemma max_cons_set_prop: "max_cons_FS X \<longrightarrow> (\<forall> alpha. X \<turnstile> Neg alpha \<longleftrightarrow> \<not> (X \<turnstile> alpha))"
proof
  assume H1: "max_cons_FS X" show "(\<forall> alpha. X \<turnstile> Neg alpha \<longleftrightarrow> \<not> (X \<turnstile> alpha))" proof
    fix alpha show "X \<turnstile> Neg alpha \<longleftrightarrow> \<not> (X \<turnstile> alpha)" proof
      assume H2: "X \<turnstile> Neg alpha"
      show "\<not> (X \<turnstile> alpha)" proof(rule ccontr)
        assume "\<not> \<not> X \<turnstile> alpha"
        hence "X \<turnstile> alpha" by(auto)
        from this H2 have "X \<turnstile> (alpha And (Neg alpha) )" by(simp add: ImplGen.ANDI)
        hence "incons_FS X" by (simp add: incons_prop)
        from this H1 show "False" by(simp add: max_cons_FS_def)
      qed
    next
      assume H3: "\<not> (X \<turnstile> alpha)"
      hence "cons_FS (X \<union> {Neg alpha})" by(simp add:Cplus_ImplSem_prop)
      from this H1 max_cons_FS_def[of "X"] have "Neg alpha \<in> X" by(auto)
      from this ImplGen.AR[of"Neg alpha"] ImplGen.MR show "X \<turnstile> Neg alpha" by(blast)
    qed
  qed
qed

lemma max_cons_fullfillable:
" max_cons_FS (X:: 'a formula set) \<longrightarrow> ( \<exists> (w :: 'a model). fulfillsS w X )"
proof
  assume H: "max_cons_FS ( X :: 'a formula set)"
  show " \<exists> (w :: 'a model). fulfillsS w X" proof
    have star: "\<forall> alpha :: 'a formula. fulfills (\<lambda> (a :: 'a). X \<turnstile> p a) alpha \<longleftrightarrow> X \<turnstile> alpha"
    proof fix alpha show "fulfills (\<lambda> (a :: 'a). X \<turnstile> p a) alpha \<longleftrightarrow> X \<turnstile> alpha" proof(induction alpha)
      case (p x)
      then show ?case by(auto)
    next
      case (andf alpha1 alpha2)
      then show ?case using ANDI ANDl ANDr ext_mod.simps(2) by blast
    next
     case (negf alpha)
     then show ?case by (simp add: negf.IH H max_cons_set_prop)
   qed
 qed
  have "\<forall> alpha \<in> X. X \<turnstile> alpha" using ImplGen.AR ImplGen.MR by blast
  from this star show "\<forall> alpha \<in> X. fulfills (\<lambda> (a :: 'a). X \<turnstile> p a) alpha" by(simp)
  qed
qed

theorem completeness_theorem: "\<forall> (X:: 'a formula set) (alpha :: 'a formula).
 X \<turnstile> alpha \<longleftrightarrow> X \<Turnstile> alpha"
proof
  fix X :: "'a formula set"
  show "\<forall> alpha :: 'a formula. X \<turnstile> alpha \<longleftrightarrow> X \<Turnstile> alpha" proof
    fix alpha :: "'a formula"
    show " X \<turnstile> alpha \<longleftrightarrow> X \<Turnstile> alpha" proof
      assume H1: "X \<turnstile> alpha"
      from this ImplGen_correct show "X \<Turnstile> alpha" by(auto)
    next
      assume H2: "X \<Turnstile> alpha"
      show "X \<turnstile> alpha" proof(rule ccontr)
        assume H3: "\<not> X \<turnstile> alpha"
        from this Cplus_ImplSem_prop have "cons_FS ( X \<union> {Neg alpha})" by(auto)
        from this lindenbaum[of "X \<union> {Neg alpha}"] have "\<exists>X'.  (X \<union> {Neg alpha}) \<subseteq> X' \<and> max_cons_FS X'" by(auto)
        then obtain Y where H'prop: "(X \<union> {Neg alpha}) \<subseteq> Y \<and> max_cons_FS Y" by(auto)
        from H'prop max_cons_fullfillable have "\<exists> w. fulfillsS w Y" by(auto)
        from H'prop this have "\<exists> w. fulfillsS w (X \<union> {Neg alpha})" by(blast)
        then obtain w where wprop: "fulfillsS w (X \<union> {Neg alpha})" by(auto)
        from this H2 ImplSem_def have CON1: "fulfills w alpha" by(auto)
        from wprop have "fulfills w (Neg alpha)" by(auto)
        hence CON2: "\<not> fulfills w alpha" by(auto)
        from CON1 CON2 show "False" by(auto)
      qed
    qed
  qed
qed

inductive ImplHil :: "'a formula set \<Rightarrow> 'a formula \<Rightarrow> bool" (infix "|~" 56) where
AR: "(alpha :: 'a formula) \<in> (X:: 'a formula set) \<Longrightarrow> ImplHil X alpha" |
MP: "\<lbrakk> ImplHil (X::'a formula set) alpha; ImplHil X (alpha Impl beta) \<rbrakk> \<Longrightarrow> ImplHil X beta" |
L1: " ImplHil (X :: 'a formula set) ( ((alpha :: 'a formula) Impl beta Impl gamma) Impl (alpha Impl beta) Impl (alpha Impl gamma) )" |
L2: " ImplHil (X :: 'a formula set) ( (alpha :: 'a formula) Impl beta Impl (alpha And beta))" |
L3a: " ImplHil (X :: 'a formula set) ( ( (alpha :: 'a formula) And beta) Impl alpha )" |
L3b: " ImplHil (X :: 'a formula set) ( ( (alpha :: 'a formula) And beta) Impl beta )" |
L4: " ImplHil (X :: 'a formula set) ( ( (alpha :: 'a formula) Impl Neg beta) Impl (beta Impl Neg alpha) )"

lemma ImplHil_example1: "{(alpha :: 'a formula), beta} |~ (alpha And beta)"
proof -
  from ImplHil.AR have 1: "{alpha, beta} |~ alpha" by (blast)
  from ImplHil.AR have 2: "{alpha, beta} |~ beta" by (blast)
  from ImplHil.L2 have 3: "{alpha, beta} |~ (alpha Impl beta Impl (alpha And beta) )" by(blast)
  from 1 3 ImplHil.MP have 4: "{alpha, beta} |~ (beta Impl (alpha And beta))" by(blast)
  from 4 2 ImplHil.MP show 5: "{alpha, beta} |~ (alpha And beta)" by(blast)
qed

lemma ImplHil_correct: " X |~ alpha \<longrightarrow> X \<Turnstile> alpha"
proof
  fix alpha
  show "X |~ alpha \<Longrightarrow> X \<Turnstile> alpha" proof(induction alpha rule: ImplHil.induct)
    case (AR alpha X)
    then show ?case  by(simp add: ImplSem_def)
next
  case (MP X alpha beta)
  then show ?case by (simp add: ImplSem_def)
next
  case (L1 X alpha beta gamma)
  then show ?case by (simp add: ImplSem_def)
next
  case (L2 X alpha beta)
  then show ?case by (simp add: ImplSem_def)
next
  case (L3a X alpha beta)
  then show ?case by (simp add: ImplSem_def)
next
  case (L3b X alpha beta)
  then show ?case by (simp add: ImplSem_def)
next
  case (L4 X alpha beta)
  then show ?case by (simp add: ImplSem_def)
qed
qed

lemma ImplHil_monot_prop: " X |~ alpha \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> X' |~ alpha"
proof(induct rule: ImplHil.induct)
    case (AR alpha X)
    then show ?case using ImplHil.AR by(auto)
  next
    case (MP X alpha beta)
    then show ?case using ImplHil.MP by(auto)
  next
    case (L1 X alpha beta gamma)
    then show ?case by(simp add: ImplHil.L1)
  next
    case (L2 X alpha beta)
    then show ?case by(simp add: ImplHil.L2)
  next
    case (L3a X alpha beta)
    then show ?case by(simp add: ImplHil.L3a)
  next
    case (L3b X alpha beta)
    then show ?case by(simp add: ImplHil.L3b)
  next
    case (L4 X alpha beta)
    then show ?case by(simp add: ImplHil.L4)
qed

lemma ImplHil_propa: "X |~ alpha Impl Neg beta \<longrightarrow> X |~ beta Impl Neg alpha"
proof
  assume H: "X |~ alpha Impl Neg beta"
  from ImplHil.L4 have "X |~ (alpha Impl Neg beta) Impl (beta Impl Neg alpha)" by(auto)
  from this H ImplHil.MP show "X |~ beta Impl Neg alpha" by(auto)
qed

lemma ImplHil_propb: "{} |~ alpha Impl beta Impl alpha"
proof -
  from ImplHil.L3b have "{} |~ (beta And Neg alpha) Impl (Neg alpha)" by(auto)
  from this ImplHil_propa show "{} |~ alpha Impl Neg(beta And Neg alpha)" by(auto)
qed

lemma ImplHil_propc: "{} |~ alpha Impl alpha"
proof -
  from ImplHil.L1 have "{} |~ (alpha Impl (alpha Impl alpha) Impl alpha) Impl (alpha Impl (alpha Impl alpha)) Impl (alpha Impl alpha)" by(auto)
  from this ImplHil.MP ImplHil_propb have "{} |~ (alpha Impl (alpha Impl alpha)) Impl (alpha Impl alpha)" by(blast)
  from this ImplHil.MP ImplHil_propb show "{} |~ alpha Impl alpha" by(blast)
qed

lemma ImplHil_propd: "{} |~ (alpha Impl (Neg (Neg alpha)) )"
proof -
  from ImplHil_propc have "{} |~ (Neg alpha) Impl (Neg alpha)" by(auto)
  from this ImplHil_propa show "{} |~ alpha Impl (Neg (Neg alpha))" by(auto)
qed

lemma ImplHil_prope: "{} |~ beta Impl (Neg beta Impl alpha)"
proof -
  from ImplHil.L3a have "{} |~ ( (Neg beta) And (Neg alpha)) Impl Neg beta" by(auto)
  from this ImplHil_propa show "{} |~ beta Impl Neg( (Neg beta) And (Neg alpha))" by(auto)
qed

lemma ImplHil_deduction_theorem: " X' |~ gamma \<Longrightarrow> X' = X \<union> {alpha} \<Longrightarrow> X |~ alpha Impl gamma"
proof(induct rule: ImplHil.induct)
  case (AR gamma X')
  then have or_prop: "gamma \<in> X \<or> gamma = alpha" by(auto)
  from this show ?case proof
    assume "gamma \<in> X"
    from this ImplHil.AR have 1: "X |~ gamma" by(auto)
    from ImplHil_propb ImplHil_monot_prop have "X |~ gamma Impl alpha Impl gamma" by(blast)
    from this 1 ImplHil.MP show "X |~ alpha Impl gamma" by(auto)
  next
    assume "gamma = alpha"
    from this ImplHil_propc ImplHil_monot_prop show "X |~ alpha Impl gamma" by(blast)
  qed
next
  case (MP X' beta gamma)
  then have H:"X |~ alpha Impl beta \<and> X |~ alpha Impl beta Impl gamma" by(auto)
  from ImplHil.L1 have "X |~ (alpha Impl beta Impl gamma) Impl (alpha Impl beta) Impl (alpha Impl gamma)" by(auto)
  from this H ImplHil.MP show ?case by(blast)
next
  case (L1 X' beta gamma delta)
  then show ?case using ImplHil.L1
    by (metis ImplHil_monot_prop ImplHil_propb MP sup.orderI sup_bot.right_neutral)
next
  case (L2 X' beta gamma)
  then show ?case
    by (metis ImplHil.L2 ImplHil_monot_prop ImplHil_propb MP sup.orderI sup_bot.right_neutral)
next
  case (L3a X' beta gamma)
  then show ?case
    by (metis ImplHil.L3a ImplHil_monot_prop ImplHil_propb MP sup.orderI sup_bot.right_neutral)
next
  case (L3b X' beta gamma)
  then show ?case 
    by (metis ImplHil.L3b ImplHil_monot_prop ImplHil_propb MP sup.orderI sup_bot.right_neutral)
next
  case (L4 X' beta gamma)
  then show ?case
    by (metis ImplHil.L4 ImplHil_monot_prop ImplHil_propb MP sup.orderI sup_bot.right_neutral)
qed

lemma ImplHil_negneg_elim: " {} |~ (Neg (Neg alpha )) Impl alpha"
proof -
  from ImplHil.L3a ImplHil.AR ImplHil.MP have I1: "{ (Neg (Neg alpha)) And Neg alpha } |~ Neg (Neg alpha)" by(blast)
  from ImplHil.L3b ImplHil.AR ImplHil.MP have I2: "{ (Neg (Neg alpha)) And Neg alpha } |~ Neg alpha" by(blast)
  from I1 I2 ImplHil.MP ImplHil_prope[of "Neg alpha" "Neg (alpha Impl alpha)"]
   ImplHil_monot_prop[of "{}" "Neg alpha Impl Neg (Neg alpha) Impl Neg (alpha Impl alpha) " "{Neg (Neg alpha) And Neg alpha}"]
  have 3: "{ (Neg (Neg alpha)) And Neg alpha } |~ Neg (alpha Impl alpha)" by(blast)
  from this ImplHil_deduction_theorem have " {} |~ ((Neg (Neg alpha)) And Neg alpha) Impl Neg( alpha Impl alpha)" by(auto)
  from this ImplHil_propa have " {} |~ (alpha Impl alpha) Impl Neg(((Neg (Neg alpha)) And Neg alpha))" by(auto)
  from this ImplHil_propc ImplHil.MP show "{} |~ Neg(((Neg (Neg alpha)) And Neg alpha))" by(auto)
qed

lemma ImplHil_fulfills_ImplGenNEG1: " X |~ alpha \<Longrightarrow> X |~ (Neg alpha) \<Longrightarrow> X |~ beta"
proof -
  assume H1: "X |~ alpha"
  assume H2: "X |~ Neg alpha"
  from ImplHil_prope ImplHil_monot_prop have "X |~ alpha Impl Neg alpha Impl beta" by(blast)
  from this H1 H2 ImplHil.MP show "X |~ beta" by(blast)
qed

lemma ImplHil_fulfills_ImplGenNEG2:
"\<lbrakk> X \<union> {beta} |~ alpha; X \<union> {Neg beta} |~ alpha \<rbrakk> \<Longrightarrow> X |~ alpha"
proof -
  fix alpha beta
  assume H1: "X \<union> {beta} |~ alpha"
  assume H2: "X \<union> {Neg beta} |~ alpha"
  from ImplHil_propd have T:"{} |~ alpha Impl Neg (Neg alpha)" by(auto)
  from this ImplHil_monot_prop have "X \<union> {beta} |~ alpha Impl Neg (Neg alpha)" by(auto)
  from this H1 ImplHil.MP have "X \<union> {beta} |~ Neg (Neg alpha)" by(auto)
  from this ImplHil_deduction_theorem have "X |~ beta Impl Neg (Neg alpha)" by(auto)
  from this ImplHil_propa have 1: "X |~ Neg alpha Impl Neg beta" by(auto)
  from ImplHil.AR ImplHil_monot_prop have 2: "X \<union> {Neg alpha} |~ Neg alpha" by(blast)
  from this 1 ImplHil.MP ImplHil_monot_prop have 3: "X \<union> {Neg alpha} |~ Neg beta " by(blast)
  from T ImplHil_monot_prop have "X \<union> {Neg beta} |~ alpha Impl Neg (Neg alpha)" by(auto)
  from this H2 ImplHil.MP have "X \<union> {Neg beta} |~ Neg (Neg alpha)" by(auto)
  from this ImplHil_deduction_theorem have "X |~ (Neg beta) Impl Neg (Neg alpha)" by(auto)
  from this ImplHil_propa have "X |~ Neg alpha Impl (Neg (Neg beta))" by(auto)
  from this 2 ImplHil.MP ImplHil_monot_prop have 4: "X \<union> {Neg alpha} |~ Neg (Neg beta) " by(blast)
  from 3 4 ImplHil_fulfills_ImplGenNEG1 have "X \<union> {Neg alpha} |~ Neg (alpha Impl alpha)" by(auto)
  from this ImplHil_deduction_theorem[of "X \<union> {Neg alpha}" _ "X" "Neg alpha"] have "X |~ (Neg alpha) Impl Neg(alpha Impl alpha)" by(auto)
  from this ImplHil_propa have " X |~ (alpha Impl alpha) Impl (Neg (Neg alpha))" by(auto)
  from this ImplHil.MP ImplHil_propc ImplHil_monot_prop have 5: "X |~ Neg (Neg alpha)" by(blast)
  from ImplHil_negneg_elim ImplHil_monot_prop have "X |~ Neg (Neg alpha) Impl alpha" by(auto)
  from this 5 ImplHil.MP show "X |~ alpha" by(auto)
qed

lemma ImplGen_implies_ImpHil: "X \<turnstile> alpha \<Longrightarrow> X |~ alpha"
proof(induct rule: ImplGen.induct)
case (AR alpha)
  then show ?case using ImplHil.AR by(auto)
next
  case (MR X X' alpha)
  then show ?case using ImplHil_monot_prop by(auto)
next
  case (ANDI X alpha beta)
  then show ?case using ImplHil.L2 ImplHil.MP by(blast)
next
  case (ANDl X alpha beta)
  then show ?case using ImplHil.L3a ImplHil.MP by(blast)
next
  case (ANDr X alpha beta)
  then show ?case using ImplHil.L3b ImplHil.MP by(blast)
next
  case (NEG1 X alpha beta)
  then show ?case using ImplHil_fulfills_ImplGenNEG1 by(auto)
next
  case (NEG2 X alpha beta)
  then show ?case using ImplHil_fulfills_ImplGenNEG2 by(auto)
qed

theorem ImplHil_complete: "X |~ alpha \<longleftrightarrow> X \<Turnstile> alpha"
proof
  assume H1: "X |~ alpha"
  from this ImplHil_correct show "X \<Turnstile> alpha" by(auto)
next
  assume H2: "X \<Turnstile> alpha"
  from this have "X \<turnstile> alpha" by (simp add: completeness_theorem)
  from this show "X |~ alpha" by (simp add: ImplGen_implies_ImpHil)
qed

end