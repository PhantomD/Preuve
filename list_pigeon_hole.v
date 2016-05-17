Require Import Arith.
Require Import List.

Load perm.
Load list_ind.
Load list_incl.
Section pigeon.

  Variable (X : Type).

  Inductive list_has_dup : list X -> Prop :=
    | in_lhd_1 : forall x l, In x l -> list_has_dup (x::l)
    | in_lhd_2 : forall x l, list_has_dup l -> list_has_dup (x::l).

  Notation lhd := list_has_dup.

  Fact lhd_app_left l m : lhd l -> lhd (l++m).
  Proof.
    intros H.
    induction H as [ x l H | x l H IH ]; simpl.
    left.
    apply in_or_app. (*Afin d'intégrer un ou pour faire left ensuite*)
    left.
    apply H.
    right.
    apply IH.
  Qed.

  Fact lhd_app_right l m : lhd m -> lhd (l++m).
  Proof.
    induction l.
    intros H1.
    apply H1. (* Supprimer le premier sous but *)
    intro H1.
    apply IHl in H1.
    simpl.
    right.
    apply H1.
  Qed.

  Fact lhd_app x l m : In x l -> In x m -> lhd (l++m).
  Proof.
    induction l as [ | y l IHl ].
    intro H1.
    intro H2.
    contradict H1. (*Utilisable lorsque l'hypothèse est fausse*)
    
    intros ? ?.
    
    apply in_inv in H. (*Trouvé dans la doc list*)
    destruct H.
    simpl.
    left.

    subst. (*Substituer y à x !*)
    apply in_or_app.
    right.
    apply H0.
    simpl.

    right.
    apply IHl.
    apply H.
    apply H0.
   Qed.
 
  Fact lhd_cons_inv x l : lhd (x::l) -> In x l \/ lhd l.
  Proof.
    inversion_clear 1;auto.
  Qed.

  (* these are the equivalent characterizations *)

  Section alternate.

    Definition lhd_alt1 (m : list X) := exists x a b c, m = a++x::b++x::c.
    
    Fixpoint lhd_alt2 (m : list X) :=
      match m with 
        | nil  => False
        | x::m => In x m \/ lhd_alt2 m
      end.
  
    Fact lhd_lhd_alt_1 m : lhd m -> lhd_alt1 m.
    Proof.     
      induction 1 as [ x m Hm | x m Hm IHm ].
      apply in_split in Hm.
      destruct Hm as (l & r & Hm).
      subst m.
      exists x, nil, l, r.
      reflexivity.
      
      destruct IHm as (y & a & b & c & H).
      subst m.
      exists y, (x::a), b, c.
      reflexivity.
    Qed.
    
    Fact lhd_alt2_app_right l m : lhd_alt2 m -> lhd_alt2 (l++m).
    Proof.
      induction l; simpl; auto.
    Qed.
    
    Fact lhd_alt1_lhd_alt2 m : lhd_alt1 m -> lhd_alt2 m.
    Proof.    
      intros (x & a & b & c & H).
      subst m.
      apply lhd_alt2_app_right.    
      constructor 1.
      apply in_or_app; right; left; auto.
    Qed.
    
    Fact lhd_alt2_lhd m : lhd_alt2 m -> lhd m.
    Proof.
      induction m as [ | x m ].
      intros [].
      intros [ H | H ].
      constructor 1; auto.
      constructor 2; auto.
    Qed.

    Fact lhd_equiv m : lhd m <-> exists x a b c, m = a++x::b++x::c.
    Proof.
      split.
      apply lhd_lhd_alt_1.
      intros H; apply lhd_alt2_lhd, lhd_alt1_lhd_alt2, H.
    Qed. 
  
  End alternate.     

  Fact perm_lhd l m : l ~p m -> list_has_dup l -> list_has_dup m.
  Proof.
    intros H.
    induction H as [ | x l m H1 IH1 | x y l | ]; auto.
    intros H.
    apply lhd_cons_inv in H; destruct H as [ H | H ].
    
    left.
    apply perm_incl in H1. (*Transformer la permutation afin quelle soit utilisable par la suite*)
    apply H1.
    apply H.
    
    right.
    apply IH1.
    apply H.

    intros H.
    apply lhd_cons_inv in H.
    destruct H as [[ H | H] | H];subst.
   
    induction l.
    left.
    left.
    reflexivity.

    left.
    left.
    reflexivity.

    right.
    left.
    apply H.
    
    apply lhd_cons_inv in H.
    destruct H as [ H | H ].

    left.
    right.
    apply H.

    right.
    right.
    apply H.
    
  Qed.
  
  Fact In_perm_head (x : X) l : In x l -> exists m, l ~p x::m.
  Proof.
    intros H.
    apply in_split in H.
    destruct H as (u & v & ?).
    subst l.
    exists (u++v).
    apply perm_sym, perm_middle.
  Qed.
  
  Fact repeat_choice_two (x : X) m : (forall a, In a m -> a = x) -> (exists m', m = x::x::m') \/ m = nil \/ m = x::nil.
  Proof.
    intros H.
    destruct m as [ | a [ | b m ] ].
    right; left; auto.
    right; right; rewrite (H a); auto; left; auto.
    left; rewrite (H a), (H b).
    exists m; auto.
    right; left; auto.
    left; auto.
  Qed.

  Fact incl_right_cons_incl_or_lhd_or_perm m x l : incl m (x::l) -> incl m l \/ lhd m \/ exists m', m ~p x::m' /\ incl m' l.
  Proof.
    intros H.
    apply incl_right_cons_split in H.
    destruct H as (m1 & m2 & H1 & H2 & H3).
    destruct (repeat_choice_two _ _ H2) as [ (m3 & H4) | [ H4 | H4 ] ]; 
      subst m1; simpl in H1; clear H2.
    
    apply perm_sym in H1.
    right; left.
    apply perm_lhd with (1 := H1).
    constructor 1; left; auto.
    
    left.
    intros u Hu.
    apply H3.
    apply perm_incl with (1 := H1); auto.
    
    right; right.
    exists m2; auto.
  Qed.
    
  Fact length_le_and_incl_implies_dup_or_perm l :  
               forall m, length l <= length m 
                      -> incl m l 
                      -> lhd m \/ m ~p l.
  Proof.   
    
    (* the proof is by generalized induction over length l *) 

    induction l as [ [ | x l ] IHl ] using list_gen_ind.

    (* case l -> nil *)
    intros ? ? ?.
    right.
    apply incl_right_nil in H0.
    subst. (*Remplace m par nil dans le sous but*)
    apply perm_nil.
       
    intros [ | y m ] H1 H2.
    
    (* case l -> x::l and m -> nil *)
    
    apply le_Sn_0 in H1; destruct H1.
    
    (* case l -> x::l and m -> y :: m *)
    
    simpl in H1; apply le_S_n in H1.
    apply incl_left_cons in H2. 
    destruct H2 as [ H3 H4 ].

    simpl in H3.
    destruct H3 as [ H3 | H3 ].
    
    (* case x = y *)
    
    subst y.
    apply incl_right_cons_choose in H4.
    destruct H4 as [ H4 | H4 ].
    
    (* case x = y & In x m *)
    
    left.
    left.
    apply H4.

        
    
    (* case x = y & incl m l *)
 
    destruct IHl with (3 := H4).
    simpl; apply lt_n_Sn.
    assumption.
    left.
    right.
    apply H.
    right.
    apply perm_cons.
    apply H.
    
    
    (* case In y l *)
    
    apply incl_right_cons_incl_or_lhd_or_perm in H4.
    destruct H4 as [ H4 | [ H4 | (m' & H4 & H5) ] ].
    
    (* case In y l and incl m l *)
    
    destruct IHl with (3 := H4) as [ H5 | H5 ]; auto.
    left;right;apply H5.
    left.
    left.
    apply perm_sym in H5.
    apply perm_incl in H5.
    apply H5.
    apply H3.
       
    (* case In y l and lhd m *)
    
    left.
    right.
    apply H4.

    (* case In y l and m ~p x::m' and incl m' l *)
    
    apply perm_sym in H4.
    apply In_perm_head in H3.
    destruct H3 as (l' & Hl').
    
    
    (* l ~p y::l' for some l' *)

    assert (incl m' (y::l')) as H6.
      intros ? ?; apply perm_incl with (1 := Hl'), H5; auto.
    clear H5.
    
    (* and incl m' (y::l') *)

    apply incl_right_cons_choose in H6.
    destruct H6 as [ H6 | H6 ].
    
    (* subcase In y m' *)
    
    left.
    left.
    apply perm_incl in H4. (*Transformation en inclusion de H4*)
    apply H4.
    right.
    apply H6.
    
    (* subcase incl m' l' *)

    (* apply the induction hypothesis *)
    
    apply IHl in H6.
    destruct H6 as [ H6 | H6 ].
    
    (* and either lhd m' *)
    
    left.
    apply perm_lhd in H4. (*A permis de me débloquer*)
    right.
    apply H4.
    right.
    apply H6.
     
    
    
    (* or m' ~p l', which leads to y::m ~p x::l *)
    (*partie gauche improuvable *)
    right.
    move Hl' after m'.

    apply perm_sym in H4.
    apply perm_cons with(x:=y) in H4.
    apply perm_cons with(x:=x) in H6.
    apply perm_cons with(x:=y) in H6.
    apply perm_cons with(x:=x) in Hl'.
    apply perm_sym in Hl'.
    apply perm_trans with(l2:=x::y::l')(l1:=y::x::l') in Hl' . 
  (*on passe par la transitivité pour pouvoir faire le swap x y qu'on prouvera après *)
    apply perm_trans with(l1:=y::m) in H6.
    apply perm_trans with(l1:=y::m) in Hl'.
    (*on résoud bitches *)

    apply Hl'.
    apply H6.
    apply H4.
    apply perm_swap.
    
    (* two checks that the induction hypothesis can be used *)
    
    apply perm_length in Hl'.
    simpl in Hl' |- *.
    rewrite Hl'.
    apply le_n_Sn.
    
    apply perm_length in Hl'.
    apply perm_length in H4.
    simpl in H4, Hl'.
    apply le_S_n.
    rewrite <- Hl', H4; auto.
  Qed.

  (* if l is strictly shorter that m but m has all its elements in l 
     then some element of m must be repeated *)
 
  Theorem finite_pigeon_hole l m : incl m l -> length l < length m -> lhd m.
  Proof.
    intros H2 H1.
    destruct length_le_and_incl_implies_dup_or_perm with (2 := H2) as [ H3 | H3 ]; auto.
    apply lt_le_weak; auto.
    apply perm_length in H3.
    exfalso; revert H1; rewrite H3; apply lt_irrefl.
  Qed.

End pigeon.

