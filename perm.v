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

  Fact perm_refl l : l ~p l. (* Cours *)
  Proof.
   induction l as [
                  |list head IH]. (*Division en deux subgoals*)
   apply perm_nil. (*Afin d'enlever le premier subgoal*)
   apply perm_cons. (* Afin d'enlever le second subgoal*)
   apply IH. (*Appliquer IH pour enlever le dernier subgoal*)
  Qed.

  Fact perm_length l1 l2 : l1 ~p l2 -> length l1 = length l2.
  Proof.
    intros H. (*Introduire hypothèse qui dit que l1 permute avec l2*)
    induction H as [ 
                   | x l1 l2 H1 IH1 (*Si on ajoute x à l1 et à l2 et que length l1 = length l2 
                   alors elles font toujours la même taille*)
                   | x y l (*Ajouter deux éléments pas dans le même ordre 
                   pour montrer que l'ordre n'influe pas*)
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ].
    apply refl_equal. (* Reflexivity :S'applique sur le but length nil = length nil*)
    simpl. (* Permet d'enlever les x:: et de travailler directement
    sur les listes *)
    f_equal. (* Permet d'éliminer la fonction S des deux côtés*)
    apply IH1. (* Appliquer IH1 *)
    simpl. (* Enleve les x et y des sous buts *) 
    apply refl_equal. (* Reflexivity *)
    transitivity (length l2). (* Transitivité sur l2 *)
    apply IH1.
    apply IH2.
   Qed.

  Fact perm_sym l1 l2 : l1 ~p l2 -> l2 ~p l1.
  Proof.
   intros H.
   induction H. (* Création des 4 cas possibles *)
   apply perm_nil.
   apply perm_cons.
   assumption. (* Applique IHperm *)
   apply perm_swap.
   apply perm_trans with l2. (* Pour pouvoir utiliser IHperm1 et IHperm2 *) 
   apply IHperm2.
   apply IHperm1.
  Qed.

  Fact perm_middle x l r : x::l++r ~p l++x::r.
  Proof.
    induction l as [ | y list IHl ]. (* 1 sous but avec le cas de la liste vide et
    un sous but avec le swap *)
    simpl. (* Enlever les nil *)
    apply perm_refl. (* Permet d'enlever un sous but *)
    simpl. (*Permet d'enlever les parenthèses inutiles *)
    apply perm_trans with (1 := perm_swap _ _ _).
    apply perm_cons.
    apply IHl.
  Qed.

  Let perm_app_left l r1 r2 : r1 ~p r2 -> l++r1 ~p l++r2.
  Proof.
    intros H.
    induction l. (*Sous but avec le cas de la liste vide 
    et un sous but avec le swap*)
    simpl. (* Enlever les nil *)
    apply H.
    simpl. (* Enlever parenthèses*)
    apply perm_cons.
    apply IHl.
  Qed.

  Fact perm_app l1 l2 r1 r2 : l1 ~p l2 -> r1 ~p r2 -> l1++r1 ~p l2++r2.
  Proof.
   intros H.
   revert H r1 r2. (* Rentre les hypothèses dans le goal *)
   intros H.
   induction H as [ 
                   | x l1 l2 H1 IH1 
                   | x y l 
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ].
    (*subgoal 1 *)    
    simpl . (* Enlever les nil *)
    intro H3.
    intro H4.
    intro H5.
    apply H5. (* tout ça pour dire que r1 ~p r2 -> r1 ~p r2 *)
    
    (*subgoal 2 *)
    intro .
    intro .
    intro.
    simpl.
    apply perm_cons.
    apply IH1.
    apply H.

    (*subgoal 3 *)
    intro .
    intro .
    intro .
    simpl.
    apply perm_trans with (1 := perm_swap _ _ _).
    apply perm_cons.  
    apply perm_cons.
    apply perm_app_left.
    apply H.

    (*subgoal 4 *)
    intro .
    intro .
    intro .
    apply perm_trans with (l2 ++ r2).
    apply IH1.
    apply H.
    apply perm_trans with (l3++r1).
    apply IH2.
    apply perm_sym.
    apply H.
    apply perm_app_left.
    apply H. (* c'est qui les patrons maintenant ? *)
    
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
    intro .
    intro .
    apply H.    

    (* subgoal 2 *)
        


(* subgoal 3 *)

(* subgoal 4 *)

  
  Qed.

End list_perm.

Infix "~p" := (perm _) (at level 70, no associativity).
