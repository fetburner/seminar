header "Arithmetic and Boolean Expressions"
(* https://github.com/fetburner/seminar の concrete_semantics/Ex3_4.thy を参照 *)

theory Ex3_4 imports Main begin

subsection "Arithmetic Expressions"

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

text_raw{*\snip{AExpaexpdef}{2}{1}{% *}
datatype aexp = N int | V vname | Plus aexp aexp | Times aexp aexp
text_raw{*}%endsnip*}

text_raw{*\snip{AExpavaldef}{1}{2}{% *}
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s" |
"aval (Times a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s * aval a\<^sub>2 s"
text_raw{*}%endsnip*}


value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"

text {* The same state more concisely: *}
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"

text {* A little syntax magic to write larger states compactly: *}

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"

text {* \noindent
  We can now write a series of updates to the function @{text "\<lambda>x. 0"} compactly:
*}
lemma "<a := Suc 0, b := 2> = (<> (a := Suc 0)) (b := 2)"
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"


text {* In  the @{term[source] "<a := b>"} syntax, variables that are not mentioned are 0 by default:
*}
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>"

text{* Note that this @{text"<\<dots>>"} syntax works for any function space
@{text"\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2"} where @{text "\<tau>\<^sub>2"} has a @{text 0}. *}

text{* Now we also eliminate all occurrences 0 in additions. The standard
method: optimized versions of the constructors: *}

text_raw{*\snip{AExpplusdef}{0}{2}{% *}
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"
text_raw{*}%endsnip*}

lemma aval_plus[simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
apply(induction a1 a2 rule: plus.induct)
apply simp_all (* just for a change from auto *)
done

text_raw{*\snip{AExptimesdef}{0}{2}{% *}
fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"times (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1*i\<^sub>2)" |
"times (N i) a = (if i=0 then N 0 else if i=1 then a else Times (N i) a)" |
"times a (N i) = (if i=0 then N 0 else if i=1 then a else Times a (N i))" |
"times a\<^sub>1 a\<^sub>2 = Times a\<^sub>1 a\<^sub>2"
text_raw{*}%endsnip*}

lemma aval_times[simp]:
  "aval (times a1 a2) s = aval a1 s * aval a2 s"
apply(induction a1 a2 rule: times.induct)
apply simp_all (* just for a change from auto *)
done

text_raw{*\snip{AExpasimpdef}{2}{0}{% *}
fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)" |
"asimp (Times a\<^sub>1 a\<^sub>2) = times (asimp a\<^sub>1) (asimp a\<^sub>2)"
text_raw{*}%endsnip*}

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

value "asimp (Plus (Times (V ''x'') (N 0)) (Times (V ''y'') (N 1)))"

theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
apply(induction a)
apply simp_all
done

end
