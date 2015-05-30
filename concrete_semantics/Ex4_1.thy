theory Ex4_1
  imports Main
begin
  datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

  fun set :: "'a tree \<Rightarrow> 'a set" where
    "set Tip = {}" |
    "set (Node l i r) = set l \<union> {i} \<union> set r"

  value "set (Node (Node Tip 1 Tip) 2 Tip)"
  (*
  "fold insert (List.insert 1 [1 + 1]) {}"
    :: "'a set"
  *)

  text {*
  An @{typ "int tree"} is ordered if for every @{term "Node l i r"} in the tree,
  @{text l} and @{text r} are ordered
  and all values in @{text l} are @{text "< i"}
  and all values in @{text r} are @{text "> i"}.
  Define a function that returns the elements in a tree and one
  the tests if a tree is ordered:
  *}

  fun ord :: "int tree \<Rightarrow> bool" where
    "ord Tip = True" |
    "ord (Node l i r) =
    (ord l \<and> ord r \<and> (\<forall>x\<in>set l. x < i) \<and> (\<forall>x\<in>set r. i < x))"

  value "ord (Node (Node Tip 1 Tip) 2 (Node Tip 3 Tip))"
  (*
  "True"
    :: "bool"
  *)
  value "ord (Node Tip 3 (Node Tip 2 (Node Tip 3 Tip)))"
  (*
  "False"
    :: "bool"
  *)

  text{* Hint: use quantifiers.

  Define a function @{text ins} that inserts an element into an ordered @{typ "int tree"}
  while maintaining the order of the tree. If the element is already in the tree, the
  same tree should be returned.
  *}

  fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
    "ins x Tip = Node Tip x Tip" |
    "ins x (Node l i r) =
      (if x < i then Node (ins x l) i r
       else if x = i then Node l i r
       else Node l i (ins x r))"

  (* [simp] is required *)
  lemma set_ins [simp] : "set (ins x t) = {x} \<union> set t"
    apply (induct t)
    apply auto
  done

  lemma ord_ins : "ord t \<Longrightarrow> ord (ins x t)"
    apply (induct t)
    (*
    goal (2 subgoals):
     1. ord Tip \<Longrightarrow> ord (ins x Tip)
     2. \<And>t1 a t2.
	   (ord t1 \<Longrightarrow> ord (ins x t1)) \<Longrightarrow>
	   (ord t2 \<Longrightarrow> ord (ins x t2)) \<Longrightarrow>
	   ord (Node t1 a t2) \<Longrightarrow> ord (ins x (Node t1 a t2))
    *)
    apply (auto)
  done

end
