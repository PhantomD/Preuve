Require Import Arith.
Require Import List.

Section generalized_list_induction.

  (* to prove a property inductively over lists, 
     we can assume that it already holds for shorter lists *)
  
  Variables (X : Type) (P : list X -> Prop).
    
  Hypothesis HP : forall l, (forall m, length m < length l -> P m) -> P l.
  
  Let list_gen_ind_rec n : forall l, length l < n -> P l.
  Proof.
    induction n as [ | n IHn ]; intros l Hl.
    exfalso; revert Hl; apply lt_n_0.
    apply HP.
    intros m Hm.
    apply IHn.
    apply lt_le_trans with (1 := Hm).
    apply le_S_n, Hl.
  Qed.

  Theorem list_gen_ind : forall l, P l.
  Proof.
    intros l. 
    apply list_gen_ind_rec with (n := S (length l)).
    apply le_refl.
  Qed.

End generalized_list_induction.

Check list_gen_ind.