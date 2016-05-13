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
   revert H r1 r2. (* Rentre les hypothèses dans le subgoal *)
   intros H.
   induction H as [ 
                   | x l1 l2 H1 IH1 
                   | x y l 
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ].
    simpl . (* Enlever les nil *)
    intros H3 H4 H5.
    apply H5.  (*Enlever le premier subgoal*)
    intros H3 H4 H5.
    simpl.
    apply perm_cons. (*Permet d'enlever les x*)
    apply IH1.
    apply H5. (* Enlever le second subgoal *)
    intros H3 H4 H5.
    simpl.
    apply perm_trans with (1 := perm_swap _ _ _). (*Permet de rendre le memvre de gauche 
    identique à celui de droite*)
    apply perm_cons. (*enlève y*)  
    apply perm_cons. (*Enlève x*)
    apply perm_app_left.
    apply H5. (* Enlève le troisième sous but *)
    (*subgoal 4 *)
    intros H3 H4 H5.
    apply perm_trans with (l2 ++ H4). (* Faire le lien entre l1 et l3 *)
    apply IH1.
    apply H5.
    apply perm_trans with (l3++H3).
    apply IH2.
    apply perm_sym. (* Pour appliquer H5 *)
    apply H5.
    apply perm_app_left.
    apply H5. (* Résolution du dernier sous but *)
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
    intros Hyp1 Hyp2 .
    apply Hyp2.
    intros Hyp1 Hyp2 .
    destruct Hyp2. (* *)
    left. (* Afin de récupérer x = Hyp1 *)
    apply H.
    right. (* Afin de récupérer l2 = Hyp1 *)
    apply IH1. (* Pour pouvoir utiliser H ensuite *)
    apply H.
    intros ? ?.
    revert H.
    simpl. (* Pour faire fonctionner le tauto *)
    tauto. (* Pas arrivé à trouver autrement *)
    revert IH2.
    revert IH1.
    apply incl_tran. (* Transitivité sur les listes *)
  Qed.


End list_perm.

Infix "~p" := (perm _) (at level 70, no associativity).
