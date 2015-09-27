(* Excercise 5.5 2015/7/17 MIZUNO MASAYUKI *)
theory Ex5_5 
imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter_0: "iter r 0 x x" |
iter_Suc: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

text{*
\exercise
Recall predicate @{const star} from Section 4.5 and @{const iter}
from Exercise~\ref{exe:iter}.
*}

lemma "iter r n x y \<Longrightarrow> star r x y"
(* proof (prove): depth 0

goal (1 subgoal):
 1. iter r n x y \<Longrightarrow> star r x y *)
proof (induction rule: iter.induct)
(* proof (state): depth 0

goal (2 subgoals):
 1. \<And>x. star r x x
 2. \<And>x y n z. r x y \<Longrightarrow> iter r n y z \<Longrightarrow> star r y z \<Longrightarrow> star r x z *)
  case iter_0
(* proof (state): depth 0

this:
  

goal (2 subgoals):
 1. \<And>x. star r x x
 2. \<And>x y n z. r x y \<Longrightarrow> iter r n y z \<Longrightarrow> star r y z \<Longrightarrow> star r x z *)
  show "\<And>x. star r x x"
(* proof (prove): depth 1

goal (1 subgoal):
 1. \<And>x. star r x x *)
  by (simp add: refl)
(* show star r ?x ?x 
Successful attempt to solve goal by exported rule:
  star r ?x ?x 
proof (state): depth 0

this:
  star r ?x ?x

goal (1 subgoal):
 1. \<And>x y n z. r x y \<Longrightarrow> iter r n y z \<Longrightarrow> star r y z \<Longrightarrow> star r x z *)
next
(* proof (state): depth 0

goal (1 subgoal):
 1. \<And>x y n z. r x y \<Longrightarrow> iter r n y z \<Longrightarrow> star r y z \<Longrightarrow> star r x z *)
  case iter_Suc
(* proof (state): depth 0

this:
    r x_ y_
    iter r n_ y_ z_
    star r y_ z_

goal (1 subgoal):
 1. \<And>x y n z. r x y \<Longrightarrow> iter r n y z \<Longrightarrow> star r y z \<Longrightarrow> star r x z *)
  show "\<And>x y n z. r x y \<Longrightarrow> iter r n y z \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
(* proof (prove): depth 1

 goal (1 subgoal):
 1. \<And>x y n z. r x y \<Longrightarrow> iter r n y z \<Longrightarrow> star r y z \<Longrightarrow> star r x z *)
  by (simp add: step)
(* show r ?x ?y \<Longrightarrow> iter r ?n ?y ?z \<Longrightarrow> star r ?y ?z \<Longrightarrow> star r ?x ?z 
Successful attempt to solve goal by exported rule:
  (r ?xa4 ?ya4) \<Longrightarrow>
  (iter r ?na4 ?ya4 ?z4) \<Longrightarrow>
  (star r ?ya4 ?z4) \<Longrightarrow>
  r ?x ?y \<Longrightarrow> iter r ?n ?y ?z \<Longrightarrow> star r ?y ?z \<Longrightarrow> star r ?x ?z 
proof (state): depth 0

this:
  r ?x ?y \<Longrightarrow> iter r ?n ?y ?z \<Longrightarrow> star r ?y ?z \<Longrightarrow> star r ?x ?z

goal (3 subgoals):
 1. \<And>x y n z.
       r x y \<Longrightarrow> iter r n y z \<Longrightarrow> star r y z \<Longrightarrow> r x (?y5 x y n z)
 2. \<And>x y n z.
       r x y \<Longrightarrow>
       iter r n y z \<Longrightarrow>
       star r y z \<Longrightarrow> iter r (?n5 x y n z) (?y5 x y n z) z
 3. \<And>x y n z.
       r x y \<Longrightarrow>
       iter r n y z \<Longrightarrow> star r y z \<Longrightarrow> star r (?y5 x y n z) z *)
  qed
end

