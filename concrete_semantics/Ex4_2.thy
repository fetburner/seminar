theory Ex4_2
  imports Main
begin
  inductive palindrome :: "'a list \<Rightarrow> bool" where
    palindrome_nil : "palindrome []" |
    palindrome_singleton : "palindrome [a]" |
    palindrome_cons_snoc : "palindrome l \<Longrightarrow> palindrome (a # l @ [a])"

  theorem palindrome_rev : "palindrome l \<Longrightarrow> rev l = l"
    apply (induction l rule: palindrome.induct)
    (*
      goal (3 subgoals):
       1. rev [] = []
       2. \<And>a. rev [a] = [a]
       3. \<And>l a.
             palindrome l \<Longrightarrow>
             rev l = l \<Longrightarrow> rev (a # l @ [a]) = a # l @ [a]
     *)
    apply auto
  done
end
