theory Ex9_4 
imports "~~/src/HOL/IMP/Star"
begin

text{*
\begin{exercise}
Modify the typed version of IMP as follows. Values are now either integers or booleans.
Thus variables can have boolean values too. Merge the two expressions types
@{typ aexp} and @{typ bexp} into one new type @{text exp} of expressions
that has the constructors of both types (of course without real constants).
Combine @{const taval} and @{const tbval} into one evaluation predicate
@{text "eval :: exp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool"}. Similarly combine the two typing predicates
into one: @{text "\<Gamma> \<turnstile> e : \<tau>"} where @{text "e :: exp"} and the IMP-type @{text \<tau>} can
be one of @{text Ity} or @{text Bty}. 
Adjust the small-step semantics and the type soundness proof.
\end{exercise}
*}

datatype val = Iv int | Bv bool

type_synonym vname = string
type_synonym state = "vname \<Rightarrow> val"

text_raw{*\snip{exptDef}{0}{2}{% *}
datatype exp =
Ic int |
Bc bool |
V vname |
Plus exp exp |
Not exp |
And exp exp |
Less exp exp
text_raw{*}%endsnip*}

inductive tval :: "exp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
"tval (Ic i) s (Iv i)" |
"tval (Bc b) s (Bv b)" |
"tval (V x) s (s x)" |
"tval a1 s (Iv i1) \<Longrightarrow> tval a2 s (Iv i2)
 \<Longrightarrow> tval (Plus a1 a2) s (Iv(i1+i2))" |
"tval b s (Bv bv) \<Longrightarrow> tval (Not b) s (Bv (\<not> bv))" |
"tval b1 s (Bv bv1) \<Longrightarrow> tval b2 s (Bv bv2) \<Longrightarrow> tval (And b1 b2) s (Bv (bv1 & bv2))" |
"tval a1 s (Iv i1) \<Longrightarrow> tval a2 s (Iv i2) \<Longrightarrow> tval (Less a1 a2) s (Bv (i1 < i2))"

declare tval.intros [intro!]
inductive_cases [elim!]:
  "tval (Ic i) s v"  "tval (Bc i) s v"
  "tval (V x) s v"
  "tval (Plus a1 a2) s v"
  "tval (Not b) s v"
  "tval (And b1 b2) s v"
  "tval (Less a1 a2) s v"

datatype
  com = SKIP 
      | Assign vname exp        ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;; _"  [60, 61] 60)
      | If     exp com com      ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  exp com          ("WHILE _ DO _"  [0, 61] 61)

inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "tval a s v \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := v))" |

Seq1:   "(SKIP;;c,s) \<rightarrow> (c,s)" |
Seq2:   "(c1,s) \<rightarrow> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow> (c1';;c2,s')" |

IfTrue:  "tval b s (Bv True) \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)" |
IfFalse: "tval b s (Bv False) \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

datatype ty = Ity | Bty

type_synonym tyenv = "vname \<Rightarrow> ty"

inductive etyping :: "tyenv \<Rightarrow> exp \<Rightarrow> ty \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50)
where
Ic_ty: "\<Gamma> \<turnstile> Ic i : Ity" |
B_ty: "\<Gamma> \<turnstile> Bc v : Bty" |
V_ty: "\<Gamma> \<turnstile> V x : \<Gamma> x" |
Plus_ty: "\<Gamma> \<turnstile> a1 : Ity \<Longrightarrow> \<Gamma> \<turnstile> a2 : Ity \<Longrightarrow> \<Gamma> \<turnstile> Plus a1 a2 : Ity" |
Not_ty: "\<Gamma> \<turnstile> b : Bty \<Longrightarrow> \<Gamma> \<turnstile> Not b : Bty" |
And_ty: "\<Gamma> \<turnstile> b1 : Bty \<Longrightarrow> \<Gamma> \<turnstile> b2 : Bty \<Longrightarrow> \<Gamma> \<turnstile> And b1 b2 : Bty" |
Less_ty: "\<Gamma> \<turnstile> a1 : Ity \<Longrightarrow> \<Gamma> \<turnstile> a2 : Ity \<Longrightarrow> \<Gamma> \<turnstile> Less a1 a2 : Bty"

declare etyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> V x : \<tau>"
  "\<Gamma> \<turnstile> Ic i : \<tau>"
  "\<Gamma> \<turnstile> Bc r : \<tau>"
  "\<Gamma> \<turnstile> Plus a1 a2 : \<tau>"
  "\<Gamma> \<turnstile> Not b : \<tau>"
  "\<Gamma> \<turnstile> And b1 b2 : \<tau>"
  "\<Gamma> \<turnstile> Less a1 a2 : \<tau>"

inductive ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool" (infix "\<turnstile>" 50) where
Skip_ty: "\<Gamma> \<turnstile> SKIP" |
Assign_ty: "\<Gamma> \<turnstile> a : \<Gamma>(x) \<Longrightarrow> \<Gamma> \<turnstile> x ::= a" |
Seq_ty: "\<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> c1;;c2" |
If_ty: "\<Gamma> \<turnstile> b : Bty \<Longrightarrow> \<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN c1 ELSE c2" |
While_ty: "\<Gamma> \<turnstile> b : Bty \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> WHILE b DO c"

declare ctyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> x ::= a"
  "\<Gamma> \<turnstile> c1;;c2"
  "\<Gamma> \<turnstile> IF b THEN c1 ELSE c2"
  "\<Gamma> \<turnstile> WHILE b DO c"

fun type :: "val \<Rightarrow> ty" where
"type (Iv i) = Ity" |
"type (Bv r) = Bty"

lemma type_eq_Ity[simp]: "type v = Ity \<longleftrightarrow> (\<exists>i. v = Iv i)"
by (cases v) simp_all

lemma type_eq_Bty[simp]: "type v = Bty \<longleftrightarrow> (\<exists>r. v = Bv r)"
by (cases v) simp_all

definition styping :: "tyenv \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 50)
where "\<Gamma> \<turnstile> s  \<longleftrightarrow>  (\<forall>x. type (s x) = \<Gamma> x)"

lemma epreservation:
  "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> tval a s v \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> type v = \<tau>"
apply(induction arbitrary: v rule: etyping.induct)
apply (fastforce simp: styping_def)+
done

lemma eprogress: "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. tval a s v"
apply(induction rule: etyping.induct)
apply (metis epreservation tval.intros type_eq_Bty type_eq_Ity)+
done

theorem progress:
  "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c,s) \<rightarrow> cs'"
proof(induction rule: ctyping.induct)
  case Skip_ty thus ?case by simp
next
  case Assign_ty 
  thus ?case by (metis Assign eprogress)
next
  case Seq_ty thus ?case by simp (metis Seq1 Seq2)
next
  case (If_ty \<Gamma> b c1 c2)
  then obtain bv where "tval b s (Bv bv)" by (metis epreservation eprogress type_eq_Bty)
  show ?case
  proof(cases bv)
    assume "bv"
    with `tval b s (Bv bv)` show ?case by simp (metis IfTrue)
  next
    assume "\<not>bv"
    with `tval b s (Bv bv)` show ?case by simp (metis IfFalse)
  qed
next
  case While_ty show ?case by (metis While)
qed

theorem styping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<Gamma> \<turnstile> s'"
proof(induction rule: small_step_induct)
  case Assign thus ?case 
    by (auto simp: styping_def) (metis Assign(1,3) epreservation)
qed auto

theorem ctyping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c'"
by (induct rule: small_step_induct) (auto simp: ctyping.intros)

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

theorem type_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c' \<noteq> SKIP
   \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
apply(induction rule:star_induct)
apply (metis progress)
by (metis styping_preservation ctyping_preservation)

end

