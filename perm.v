(* La librairie strandard est décrite ici

   https://coq.inria.fr/distrib/current/stdlib/

*)

Require Import List. (* Voir https://coq.inria.fr/distrib/current/stdlib/Coq.Lists.List.html *)

Reserved Notation "x '~p' y" (at level 70, no associativity).

Section list_perm.

  Variable X : Type.

  Inductive perm : list X -> list X -> Prop :=

    | perm_nil   :                    nil ~p nil

    | perm_cons  : forall x l1 l2,     l1 ~p l2 
                               ->   x::l1 ~p x::l2

    | perm_swap  : forall x y l,  x::y::l ~p y::x::l

    | perm_trans : forall l1 l2 l3,    l1 ~p l2 
                               ->      l2 ~p l3 
                               ->      l1 ~p l3

  where "x '~p' y " := (perm x y).

  Fact perm_refl l : l ~p l.
  Proof.
    induction l as [
                   | l x IH
                   ].

    (* subgoal 1 *)
    apply perm_nil.

    (* subgoal 2 *)
    apply perm_cons.
    apply IH.
  Qed.


  Fact perm_length l1 l2 : l1 ~p l2 -> length l1 = length l2.
  Proof.
    intros H.
    induction H as [ 
                   | x l1 l2 H1 IH1
                   | x y l
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ].

    (* subgoal 1 *)
    reflexivity.

    (* subgoal 2 *)
    simpl.
    f_equal.
    apply IH1.

    (* subgoal 3 *)
    simpl.
    reflexivity.

    (* subgoal 4 *)
    transitivity (length l2).
    apply IH1.
    apply IH2.
  Qed.


  Fact perm_sym l1 l2 : l1 ~p l2 -> l2 ~p l1.
  Proof.
    intros H.
    induction H.

    (* subgoal 1 *)
    apply perm_nil.

    (* subgoal 2 *)
    apply perm_cons.
    apply IHperm.

    (* subgoal 3 *)
    apply perm_swap.

    (* subgoal 4 *)
    apply perm_trans with l2. 
    apply IHperm2.
    apply IHperm1.
  Qed.


  Fact perm_middle x l r : x::l++r ~p l++x::r.
  Proof.
    induction l as [
                   | y list IHl
                   ].

    (* subgoal 1 *)
    simpl.

    (* subgoal 2 *)
    apply perm_refl.
    simpl.
    apply perm_trans with (1 := perm_swap _ _ _).
    apply perm_cons.
    apply IHl.
  Qed.


  Let perm_app_left l r1 r2 : r1 ~p r2 -> l++r1 ~p l++r2.
  Proof.
    intros H.
    induction l.

    (* subgoal 1 *)
    simpl.
    apply H.

    (* subgoal 2 *)
    simpl.
    apply perm_cons.
    apply IHl.
  Qed.


  Fact perm_app l1 l2 r1 r2 : l1 ~p l2 -> r1 ~p r2 -> l1++r1 ~p l2++r2.
  Proof.
   intros H.
   revert H r1 r2.
   intros H.
   induction H as [ 
                  | x l1 l2 H1 IH1 
                  | x y l 
                  | l1 l2 l3 H1 IH1 H2 IH2 
                  ].

    (*subgoal 1 *)
    simpl.
    intros ? ? H5.
    apply H5.
    
    (*subgoal 2 *)
    intros ? ? ?.
    simpl.
    apply perm_cons.
    apply IH1.
    apply H.

    (*subgoal 3 *)
    intros ? ? ?.
    simpl.
    apply perm_trans with (1 := perm_swap _ _ _).
    apply perm_cons.  
    apply perm_cons.
    apply perm_app_left.
    apply H.

    (*subgoal 4 *)
    intros ? ? ?.
    apply perm_trans with (l2 ++ r2).
    apply IH1.
    apply H.
    apply perm_trans with (l3++r1).
    apply IH2.
    apply perm_sym.
    apply H.
    apply perm_app_left.
    apply H.
  Qed.


  (* incl est défini dans la librairie standard, fichier List.v *)

  Print incl.

  Fact perm_incl l m : l ~p m -> incl l m.
  Proof.
    intros H.
    induction H as [ 
                   | x l1 l2 H1 IH1 
                   | x y l 
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ]. 
    (* subgoal 1 *)    
    intros ? ?.
    apply H.
    
    (* subgoal 2 *)
    intros ? ?.
    destruct H.
    left.
    apply H.
    right.
    apply IH1.
    apply H.
    
    (* subgoal 3 *)
    intros ? ?.
    destruct H.
    right.
    left.
    apply H.

    destruct H.
    left.
    apply H.
    right.
    right.
    apply H.

    (* subgoal 4 *)
    revert IH2.
    revert IH1.
    apply incl_tran.
  Qed.

End list_perm.

Infix "~p" := (perm _) (at level 70, no associativity).