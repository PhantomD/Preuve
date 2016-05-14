(* La librairie strandard est décrite ici

   https://coq.inria.fr/distrib/current/stdlib/

*)

Require Import List.  (* https://coq.inria.fr/distrib/current/stdlib/Coq.Lists.List.html *)
Require Import Arith. (* https://coq.inria.fr/distrib/current/stdlib/Coq.Arith.Arith_base.html *)

Require Import perm.

Section list_incl.

  Variable (X : Type).
  
  Implicit Types (l m : list X).

  Print In.
  Print incl.
  
  Fact incl_left_cons l m x : incl (x::m) l -> In x l /\ incl m l.
  Proof.
    intros H; split.
    apply H; left; reflexivity.
    intros ? ?; apply H; right; assumption.
  Qed.
 
  Fact incl_left_app l m k : incl (l++m) k <-> incl l k /\ incl m k.
  Proof.
    split.  
    intros H; split; intros ? ?; apply H; apply in_or_app; [ left | right ]; auto.
    intros ?.
    
    destruct H.
    SearchPattern (incl _  _ ).
    apply incl_app; assumption.
  Qed.


  Fact incl_right_nil l : incl l nil -> l = nil.
  Proof.
    intros H.
    destruct l as [ | x l ].
    reflexivity.
    apply incl_left_cons in H. 
    destruct H as (H1 & H2).
    destruct H1.
  Qed.

  Let incl_nil_x l : incl nil l.
  Proof.
    intros ? [].
  Qed.

  Fact incl_right_app l m p : incl m (l++p) -> exists m1 m2, m ~p m1++m2 /\ incl m1 l /\ incl m2 p.
  Proof.
    induction m as [ | x m IHm ].

    exists nil, nil; simpl; repeat split.
    apply perm_nil.
    apply incl_nil_x.
    apply incl_nil_x.

    intros H.
    apply incl_left_cons in H. 
    destruct H as (H1 & H2).    
    apply IHm in H2.
    destruct H2 as (m1 & m2 & H3 & H4 & H5).

    exists (x :: m1),m2.
    split.
    
    simpl.
    apply perm_cons.
    apply H3.

    split.

    apply incl_cons.

    apply in_app_or in H1.
    destruct H1 as [H1 | H2].
    
    apply H1.
    
    apply H4.

    apply perm_incl in H3.

    admit.

    apply H4.
    apply H5.
  Admitted.




  Fact incl_right_cons_split x l m : incl m (x::l) -> exists m1 m2, m ~p m1 ++ m2 /\ (forall a, In a m1 -> a = x) /\ incl m2 l.
  Proof.
    intros H.
    apply (incl_right_app (x::nil) _ l) in H.
    destruct H. destruct H. destruct H.
    destruct H0.
    
    exists x0, x1.
    split.
    apply H.
    split.

    intros ? ?.

    apply perm_incl in H.
    apply incl_cons with(l:=nil) in H2.
    apply incl_tran with(l:=a::nil) in H0.

    apply incl_left_cons in H0.
    destruct H0.
    induction H0.
    subst.
    trivial.
    exfalso.
    apply H0.

    apply H2.

    apply incl_nil_x.

    apply H1.
  Qed.




  Fact incl_right_cons_split x l m : incl m (x::l) -> exists m1 m2, m ~p m1 ++ m2 /\ (forall a, In a m1 -> a = x) /\ incl m2 l.
  Proof.
    intros H.
    apply (incl_right_app (x::nil) _ l) in H.




    exists nil,m.
    simpl.
    split.
    apply perm_refl.
    split.
    intros ? ?.
    apply sym_equal.
    destruct H0.

    apply perm_incl in H3.

admit.
  Admitted.
  
  Fact incl_right_cons_choose x l m : incl m (x::l) -> In x m \/ incl m l.
  Proof.
    intros H.
    apply incl_right_cons_split in H.
    destruct H as ( m1 & m2 & H1 & H2 & H3 ); simpl in H1.
    destruct m1 as [ | y m1 ].


    right.
   (* apply incl_tran with (m2).*)
    induction H1.
    apply incl_nil_x.
    
    intros ? ?.

  Admitted.

  Fact list_remove (x : X) l : In x l -> exists m, incl l (x::m) /\ length m < length l.
  Proof.
    induction l as [ | y l IHl ].
    intros [].
    intros [ ? | H ].

    subst.
    exists l.
    split.
    apply incl_refl.
    simpl; apply lt_n_Sn.
    
    specialize (IHl H).
    destruct IHl as (m & H1 & H2).
    exists (y::m); split.
    intros u [ Hu | Hu ].
    subst; right; left; auto.
    apply H1 in Hu.
    destruct Hu; [ left | right; right ]; auto.
    simpl; apply lt_n_S; auto.
  Qed.

End list_incl.
