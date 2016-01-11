Require Import Arith ZArith Reals List Omega Program.
(** * Motivation *)

(** As I presented previously, I would like to prove correctness of MinCaml.
    Thus I'm planning to prove correctness of an earlier compile phase, K-normalization at the beggining. *)

(* ###################################################################### *)

(** * What is K-normalization? *)

(** As you can see, the compiler phase that translate host languages into one of the intermediate languages, K-normal form.
    CPS is also well known for intermediate language.
    To compare them:

    - CPS does not allow any function calls appear in tail positions.
      K-normal form allows that.

    - CPS does not allow any branches appear in let bindings.
      K-normal form allows that.

    - In both intermediate languages, all subexpressions must be named by let bindings.

    K-normal form can be considered a mild intermediate language. *)

(* ###################################################################### *)

(** * Semantics *)

(** We need to define semantics before the proof.
    Generally, big-step operational semantics cannot distinguish diverges and stuck states,
    so that I tried to prove correctness using small-step operational semantics. *)

(** ** Small-step operational semantics *)

Definition shift_var x c d :=
  (if lt_dec x c then x
  else d + x).

Section UntypedSmallStep.
  Require Import Relations.
  (** I used de Bruijn indices to express bindings *)
  Inductive exp :=
    | Var : nat -> exp
    | Abs : exp -> exp
    | Let : exp -> exp -> exp
    | App : exp -> exp -> exp.

  Fixpoint shift e c d :=
    match e with
    | Var x => Var (shift_var x c d)
    | Abs e => Abs (shift e (S c) d)
    | Let e1 e2 => Let (shift e1 c d) (shift e2 (S c) d)
    | App e1 e2 => App (shift e1 c d) (shift e2 c d)
    end.

  Definition subst_var y x es :=
    if le_dec x y then shift (nth (y - x) es (Var (y - x - length es))) 0 x
    else Var y.

  Fixpoint subst e x es :=
    match e with
    | Var y => subst_var y x es
    | Abs e => Abs (subst e (S x) es)
    | Let e1 e2 => Let (subst e1 x es) (subst e2 (S x) es)
    | App e1 e2 => App (subst e1 x es) (subst e2 x es)
    end.

  Inductive value : exp -> Prop :=
    | V_Abs : forall e, value (Abs e).

  Inductive simplto : exp -> exp -> Prop :=
    | S_Let1 : forall e1 e1' e2,
        simplto e1 e1' ->
        simplto (Let e1 e2) (Let e1' e2)
    | S_Let : forall v1 e2,
        value v1 ->
        simplto (Let v1 e2) (subst e2 0 [v1])
    | S_App1 : forall e1 e1' e2,
        simplto e1 e1' ->
        simplto (App e1 e2) (App e1' e2)
    | S_App2 : forall v1 e2 e2',
        value v1 ->
        simplto e2 e2' ->
        simplto (App v1 e2) (App v1 e2')
    | S_App : forall e0 v2,
        value v2 ->
        simplto (App (Abs e0) v2) (subst e0 0 [v2]).

  Fixpoint knormal e :=
    match e with
    | Var x => Var x
    | Abs e => Abs (knormal e)
    | Let e1 e2 => Let (knormal e1) (knormal e2)
    | App e1 e2 =>
        Let (knormal e1)
          (Let (shift (knormal e2) 0 1)
            (App (Var 1) (Var 0)))
    end.
  
  (** Boring lemmas *)
  Axiom knormal_preserves_value : forall v,
    value v -> value (knormal v).
  Hint Resolve knormal_preserves_value.
  Axiom knormal_subst : forall e x es,
    knormal (subst e x es) = subst (knormal e) x (map knormal es).
  Axiom S_Let1_multi : forall e1 e1' e2,
    clos_refl_trans _ simplto e1 e1' ->
    clos_refl_trans _ simplto (Let e1 e2) (Let e1' e2).
  Axiom S_App1_multi : forall e1 e1' e2,
    clos_refl_trans _ simplto e1 e1' ->
    clos_refl_trans _ simplto (App e1 e2) (App e1' e2).

  (** I'm glad if consist this statement, but real is brutal. *)
  Theorem knormal_correctness : forall e e',
    simplto e e' ->
    clos_refl_trans _ simplto (knormal e) (knormal e').
  Proof.
    intros e e' Hsimplto.
    induction Hsimplto; simpl in * |- *.
      apply S_Let1_multi.
      auto.

      apply rt_step.
      rewrite knormal_subst.
      apply S_Let.
      apply knormal_preserves_value.
      auto.
      
      apply S_Let1_multi.
      auto.

      (** This subgoal looks correct at first sight. But it is inconsistent. *)
  Abort.
  (** To prove such correspondence, We need to transform the statement into complex one.
      I finded other way because of these difficulty. *)
End UntypedSmallStep.

(* ###################################################################### *)

(** ** Coinductive big-step operational semantics *)

Section UntypedBigStep.
(** "Generally", big-step operational semantics cannot distinguish diverges and stuck states.
    Having said that, there are some ways to extend big-step operational semantics to distinguish diverges and stuck states.
    One of them is "Coinductive big-step operational semantics".
    
    Coinductive big-step operational semantics works following reasons.

    - Inductive definition cannot express infinite datatypes. *)

  Inductive evalto : exp -> exp -> Prop :=
    | E_Abs : forall e0, evalto (Abs e0) (Abs e0)
    | E_Let : forall e1 e2 v1 v2,
        evalto e1 v1 ->
        evalto (subst e2 0 [v1]) v2 ->
        evalto (Let e1 e2) v2
    | E_App : forall e1 e2 e0 v2 v,
        evalto e1 (Abs e0) ->
        evalto e2 v2 ->
        evalto (subst e0 0 [v2]) v ->
        evalto (App e1 e2) v.
  Hint Constructors value evalto.

  (** There are no value v that ensures "(fun x0 -> x0 x0) (fun x0 -> x0 x0) => v". *)
  Definition omega := Abs (App (Var 0) (Var 0)).
  Goal forall v, ~evalto (App omega omega) v.
  Proof.
    intros v Hevalto.
    remember (App omega omega).
    induction Hevalto; unfold omega in * |-; subst; inversion Heqe; subst.
      inversion Hevalto1; subst.
      inversion Hevalto2; subst.
      apply IHHevalto3.
      reflexivity.
  Qed.

  (** - But coinductive definition can.
        So we can define complementary proposition to distinguish diverges and others.  *)

  CoInductive diverge : exp -> Prop :=
    | D_LetL : forall e1 e2,
        diverge e1 ->
        diverge (Let e1 e2)
    | D_LetR : forall e1 e2 v1,
        evalto e1 v1 ->
        diverge (subst e2 0 [v1]) ->
        diverge (Let e1 e2)
    | D_AppL : forall e1 e2,
        diverge e1 ->
        diverge (App e1 e2)
    | D_AppR : forall e1 v1 e2,
        evalto e1 v1 ->
        diverge e2 ->
        diverge (App e1 e2)
    | D_App : forall e1 e2 e0 v2,
        evalto e1 (Abs e0) ->
        evalto e2 v2 ->
        diverge (subst e0 0 [v2]) ->
        diverge (App e1 e2).
    Hint Constructors diverge.

    Goal diverge (App omega omega).
    Proof.
      unfold omega.
      cofix.
      eapply D_App.
        econstructor.
        econstructor.
        eauto.
    Qed.

    Goal (forall v, ~evalto (Var 0) v) /\ ~diverge (Var 0).
    Proof.
      split; [ intros v Hevalto | intros Hevalto ]; inversion Hevalto.
    Qed.

(* ###################################################################### *)

(** * Lemmas for shift and substitution *)

(** K-normalization is accompanied by binding replacement because of let insertion.
    It makes shift operation be inevitable. *)
 
  Lemma shift_var_0 : forall x c,
    shift_var x c 0 = x.
  Proof.
    intros x c.
    unfold shift_var.
    destruct (lt_dec x c); auto.
  Qed.

  Lemma shift_0 : forall e c,
    shift e c 0 = e.
  Proof.
    intros e.
    induction e; intros c; simpl; f_equal;
      try apply shift_var_0; eauto.
  Qed.

  Lemma shift_var_meld : forall x c c' d d',
    c <= c' <= c + d ->
    shift_var (shift_var x c d) c' d' = shift_var x c (d + d').
  Proof.
    intros x c c' d d' Hle.
    unfold shift_var.
    repeat match goal with
    | [ |- context [ lt_dec ?x ?c ] ] =>
        destruct (lt_dec x c)
    end; omega.
  Qed.

  Lemma shift_meld : forall e c c' d d',
    c <= c' <= c + d ->
    shift (shift e c d) c' d' = shift e c (d + d').
  Proof.
    intros e.
    induction e; intros c c' d d' Hle; simpl; f_equal; auto;
    try (apply shift_var_meld; omega);
      match goal with
      | [ IH : forall _ _ _ _, _ -> shift (shift _ _ _) _ _ = shift _ _ _ |- _ ] =>
          apply IH
      end; omega.
  Qed.

  Lemma shift_var_swap : forall x c c' d d',
    c' <= c ->
    shift_var (shift_var x c d) c' d' = shift_var (shift_var x c' d') (d' + c) d.
  Proof.
    intros x c c' d d' Hle.
    unfold shift_var.
    repeat match goal with
    | [ |- context [ lt_dec ?x ?c ] ] =>
        destruct (lt_dec x c)
    end; omega.
  Qed.

  Lemma shift_swap : forall e c c' d d',
    c' <= c ->
    shift (shift e c d) c' d' = shift (shift e c' d') (d' + c) d.
  Proof.
    intros e.
    induction e; intros c c' d d' Hle; simpl; f_equal; auto;
      try apply shift_var_swap;
      repeat match goal with
      | [ |- context [ S (?d + ?c) ] ] =>
          replace (S (d + c)) with (d + (S c)) by omega
      | [ IH : forall _ _ _ _, _ -> shift (shift _ _ _) _ _ = shift (shift _ _ _) _ _ |- _ ] =>
          apply IH
      end; omega.
  Qed.

  Lemma subst_var_shift : forall x y es c d,
    c <= x ->
    shift (subst_var y x es) c d = subst_var (shift_var y c d) (d + x) es.
  Proof.
    intros.
    unfold subst_var.
    repeat (simpl in * |- *; unfold shift_var; match goal with
    | [ |- context [ le_dec ?x ?n ] ] => destruct (le_dec x n)
    | [ |- context [ lt_dec ?x ?n ] ] => destruct (lt_dec x n)
    end); 
    try rewrite shift_meld by omega;
    (* DANGER! *)
    repeat (f_equal; try omega).
  Qed.

  Lemma subst_shift : forall e c d x es,
    c <= x ->
    shift (subst e x es) c d = subst (shift e c d) (d + x) es.
  Proof.
    intros e.
    induction e; intros; simpl; f_equal; auto;
      try (apply subst_var_shift; omega);
      repeat match goal with
      | [ subst_shift : forall _ _ _ _, _ -> shift (subst ?e _ _) _ _ = subst (shift ?e _ _) _ _ |- shift (subst ?e ?x ?es) ?c ?d = subst (shift ?e ?c ?d) ?dx ?es ] =>
          replace dx with (d + x) by omega; apply subst_shift; omega
      end.
  Qed.

  Lemma subst_var_ignore : forall y c d x es,
    c <= x ->
    length es + x <= d + c ->
    subst_var (shift_var y c d) x es = Var (shift_var y c (d - length es)).
  Proof.
    intros.
    unfold subst_var.
    repeat (try (rewrite nth_overflow by omega; simpl);
    unfold shift_var; match goal with
    | [ |- context [ le_dec ?x ?n ] ] => destruct (le_dec x n)
    | [ |- context [ lt_dec ?x ?n ] ] => destruct (lt_dec x n)
    end); f_equal; try omega.
  Qed.

  Lemma subst_ignore : forall e c d x es,
    c <= x ->
    length es + x <= d + c ->
    subst (shift e c d) x es = shift e c (d - length es).
  Proof.
    fix 1.
    intros [] c d x es Hle Hlength; simpl; f_equal; auto;
      try (apply subst_var_ignore; omega);
      match goal with
      | [ |- subst (shift ?e ?c ?d) ?x ?es = shift ?e ?c ?dlength ] =>
          apply subst_ignore; omega
      end.
  Qed.

(* ###################################################################### *)

(** * Main theorem *)

(** Now, We are ready to prove correctness of K-normalization. *)

  Lemma evalto_ident : forall v,
    value v -> evalto v v.
  Proof.
    intros v Hvalue.
    inversion Hvalue; auto.
  Qed.
  Hint Resolve evalto_ident.

  Lemma evalto_value : forall e v,
    evalto e v -> value v.
  Proof.
    intros e v Hevalto.
    induction Hevalto; auto.
  Qed.
  Hint Resolve evalto_value.

  Theorem knormal_evalto : forall e v,
    evalto e v -> evalto (knormal e) (knormal v).
  Proof.
    intros e v Hevalto.
    induction Hevalto;
    repeat (simpl in * |- *;
      unfold subst_var;
      try (rewrite subst_ignore by (simpl; omega));
      match goal with
      | [ |- evalto (Let _ _) _ ] => econstructor
      | [ |- evalto (App _ _) _ ] => eapply E_App
      | [ |- context [ shift _ _ 0 ] ] => rewrite shift_0
      | [ H : context [ knormal (subst _ _ _) ] |- _ ] => rewrite knormal_subst in H; simpl in * |- *
      end); simpl; eauto.
  Qed.

  Theorem knormal_diverge : forall e,
    diverge e -> diverge (knormal e).
  Proof.
    cofix.
    intros e Hdiverge.
    inversion Hdiverge; subst; clear Hdiverge; simpl;
      repeat (simpl in * |- *;
      unfold subst_var;
      try (rewrite subst_ignore by (simpl; omega); simpl in * |- *);
      match goal with
      | [ H : diverge ?t |- diverge (Let (knormal ?t) _) ] =>
          apply D_LetL; auto
      | [ H : evalto ?t _ |- diverge (Let (knormal ?t) _) ] =>
          eapply D_LetR
      | [ |- evalto (knormal _) _ ] =>
          eapply knormal_evalto; try eassumption
      | [ |- context [ shift _ _ 0 ] ] => rewrite shift_0
      end).

    generalize (knormal_subst e2 0 [v1]); simpl; intros H_.
    rewrite <- H_.
    apply knormal_diverge.
    auto.

    eapply D_App.
      eauto.
      apply evalto_ident.
      apply knormal_preserves_value.
      eapply evalto_value.
      eauto.

      eapply knormal_diverge in H1.
      rewrite knormal_subst in * |- *.
      simpl in * |- *.
      auto.
  Qed.
End UntypedBigStep.

(** * Future work *)

(** Extend target languages until it reaches MinCaml's target language
    
    - variable-arity syntax support

    - arrays

    - external function call *)
