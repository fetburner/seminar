theory Ex7_9 (* 2015/10/2 *)
imports "~~/src/HOL/IMP/BExp" "~~/src/HOL/IMP/Star"
begin

text{*
\begin{exercise}\label{exe:IMP:OR}
Extend IMP with a new command @{text "c\<^sub>1 OR c\<^sub>2"} that is a
nondeterministic choice: it may execute either @{text
"c\<^sub>1"} or @{text "c\<^sub>2"}. Add the constructor
\begin{alltt}
  Or com com   ("_ OR/ _" [60, 61] 60)
\end{alltt}
to datatype @{typ com}. Adjust the definitions of big-step
and small-step semantics, prove @{text"(c\<^sub>1 OR c\<^sub>2) \<sim> (c\<^sub>2 OR c\<^sub>1)"}
and update the equivalence proof between the two semantics.
\end{exercise}
*}

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
      | Or     com com          ("_ OR/ _" [60, 61] 60)

text_raw{*\snip{BigStepdef}{0}{1}{% *}
inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
"\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
(********************************************************)
OrL: "(c\<^sub>1,s) \<Rightarrow> t \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2, s) \<Rightarrow> t" |
OrR: "(c\<^sub>2,s) \<Rightarrow> t \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2, s) \<Rightarrow> t"
text_raw{*}%endsnip*}

declare big_step.intros [intro]
inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
(********************************************************)
inductive_cases OrE[elim]: "(c1 OR c2,s) \<Rightarrow> t"

text_raw{*\snip{BigStepEquiv}{0}{1}{% *}
abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"
text_raw{*}%endsnip*}

(********************************************************)
theorem or_comm: "(c\<^sub>1 OR c\<^sub>2) \<sim> (c\<^sub>2 OR c\<^sub>1)" by blast

inductive
  small_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
  where
  Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

  Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |
  Seq2:    "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

  IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
  IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

  While:   "(WHILE b DO c,s) \<rightarrow>
              (IF b THEN c;; WHILE b DO c ELSE SKIP,s)" |
(*******************************************************)
  OrL:     "(c\<^sub>1 OR c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
  OrR:     "(c\<^sub>1 OR c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)"

abbreviation
  small_steps :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

declare small_step.intros[simp,intro]
inductive_cases SkipES[elim!]: "(SKIP,s) \<rightarrow> ct"
inductive_cases AssignES[elim!]: "(x::=a,s) \<rightarrow> ct"
inductive_cases SeqES[elim]: "(c1;;c2,s) \<rightarrow> ct"
inductive_cases IfES[elim!]: "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases WhileES[elim]: "(WHILE b DO c, s) \<rightarrow> ct"
(*******************************************************)
inductive_cases OrES[elim]: "(c1 OR c2,s) \<rightarrow> ct"

lemma star_seq2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* (c1';;c2,s')"
proof(induction rule: star_induct)
  case refl thus ?case by simp
next
  case step
  thus ?case by (metis Seq2 star.step)
qed

lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (SKIP,s3)"
by(blast intro: star.step star_seq2 star_trans)

lemma big_to_small:
  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induction rule: big_step.induct)
  fix s show "(SKIP,s) \<rightarrow>* (SKIP,s)" by simp
next
  fix x a s show "(x ::= a,s) \<rightarrow>* (SKIP, s(x := aval a s))" by auto
next
  fix c1 c2 s1 s2 s3
  assume "(c1,s1) \<rightarrow>* (SKIP,s2)" and "(c2,s2) \<rightarrow>* (SKIP,s3)"
  thus "(c1;;c2, s1) \<rightarrow>* (SKIP,s3)" by (rule seq_comp)
next
  fix s::state and b c0 c1 t
  assume "bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c0,s)" by simp
  moreover assume "(c0,s) \<rightarrow>* (SKIP,t)"
  ultimately 
  show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
next
  fix s::state and b c0 c1 t
  assume "\<not>bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c1,s)" by simp
  moreover assume "(c1,s) \<rightarrow>* (SKIP,t)"
  ultimately 
  show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
next
  fix b c and s::state
  assume b: "\<not>bval b s"
  let ?if = "IF b THEN c;; WHILE b DO c ELSE SKIP"
  have "(WHILE b DO c,s) \<rightarrow> (?if, s)" by blast
  moreover have "(?if,s) \<rightarrow> (SKIP, s)" by (simp add: b)
  ultimately show "(WHILE b DO c,s) \<rightarrow>* (SKIP,s)" by(metis star.refl star.step)
next
  fix b c s s' t
  let ?w  = "WHILE b DO c"
  let ?if = "IF b THEN c;; ?w ELSE SKIP"
  assume w: "(?w,s') \<rightarrow>* (SKIP,t)"
  assume c: "(c,s) \<rightarrow>* (SKIP,s')"
  assume b: "bval b s"
  have "(?w,s) \<rightarrow> (?if, s)" by blast
  moreover have "(?if, s) \<rightarrow> (c;; ?w, s)" by (simp add: b)
  moreover have "(c;; ?w,s) \<rightarrow>* (SKIP,t)" by(rule seq_comp[OF c w])
  ultimately show "(WHILE b DO c,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
(*******************************************************)
next
  fix c\<^sub>1 s t c\<^sub>2
  show "(c\<^sub>1 OR c\<^sub>2, s) \<rightarrow>* (SKIP, t)" by (metis star.simps)
next
  fix c\<^sub>1 s t c\<^sub>2
  show "(c\<^sub>1 OR c\<^sub>2, s) \<rightarrow>* (SKIP, t)" by (metis star.simps)
qed

text{* Each case of the induction can be proved automatically: *}
lemma  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induction rule: big_step.induct)
  case Skip show ?case by blast
next
  case Assign show ?case by blast
next
  case Seq thus ?case by (blast intro: seq_comp)
next
  case IfTrue thus ?case by (blast intro: star.step)
next
  case IfFalse thus ?case by (blast intro: star.step)
next
  case WhileFalse thus ?case
    by (metis star.step star_step1 small_step.IfFalse small_step.While)
next
  case WhileTrue
  thus ?case
    by(metis While seq_comp small_step.IfTrue star.step[of small_step])
(*******************************************************)
next
  case OrL thus ?case by (blast intro: star.step)
next
  case OrR thus ?case by (blast intro: star.step)
qed

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induction arbitrary: t rule: small_step.induct)
apply auto
done

lemma small_to_big:
  "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
apply (induction cs "(SKIP,t)" rule: star.induct)
apply (auto intro: small1_big_continue)
done

theorem big_iff_small:
  "cs \<Rightarrow> t = cs \<rightarrow>* (SKIP,t)"
by(metis big_to_small small_to_big)

end

