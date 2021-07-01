(** Tools.v Version 1.0 January 2012 *)
(** runs under V8.4beta, tested with version trunk 15623 *)

(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(**  provides the implementation of some basic tools
     relating to arithmetic, lists, and so on *)

Require Export Arith.
Require Import Utf8.
Require Import Setoid.
Require Import Morphisms.
Require Import List.
Require Import Basics.
Require Import Max. 

Set Implicit Arguments.

Section Tools_lists.

  Lemma eq_nth (T: Set)(l1 l2 : list T)(d: T) : 
    length l1 = length l2 -> 
    (forall n, nth n l1 d = nth n l2 d) -> l1 = l2.
  Proof.
    revert l2.
    induction l1 as [|t1 l1 IH] ; intros l2 H1 H2 ;destruct l2 as [|t2 l2].
    reflexivity.
    inversion H1.
    inversion H1.
    f_equal.
    apply (H2 0).
    apply IH.
    apply eq_add_S, H1.
    intros n.
    apply (H2 (S n)).
  Qed.
  
  
  Lemma eq_nth_cor (T: Set)(l1 l2 : list T): 
    length l1 = length l2 -> 
    (forall n d, nth n l1 d = nth n l2 d) -> l1 = l2.
  Proof.
    intros H1 H2.
    destruct l1 as [|t1 l1] ;destruct l2 as [|t2 l2].
    reflexivity.
    inversion H1.
    inversion H1.
    apply (eq_nth _ _ t1).
    assumption.
    intros n.
    apply (H2 n t1).
  Qed.
  
  Lemma nth_default (T: Set)(l: list T)(n: nat)(d: T) : length l <= n -> nth n l d = d.
  Proof.
    revert l ; induction n as [|n IH] ; destruct l as [|t l] ; intros H.
    reflexivity.
    inversion H.
    reflexivity.
    simpl.
    apply IH.
    apply le_S_n.
    assumption.
  Qed.
  
  Lemma eq_nth_cor' (T: Set)(l1 l2 : list T): 
    length l1 = length l2 -> 
    (forall n d,  n < length l1 -> nth n l1 d = nth n l2 d) -> l1 = l2.
  Proof.
    intros h1 h2.
    apply eq_nth_cor ; try assumption.
    intros n d.
    elim (le_lt_dec (length l1) n); intros a.
    rewrite nth_default, nth_default ; try assumption.
    reflexivity.
    rewrite <- h1 ; assumption.
    apply h2.
    assumption.
  Qed.
  
  Section MaxListNat.
  
    Fixpoint max_list_nat_aux (m: nat)(l: list nat){struct l}: nat :=
      match l with 
      | nil => m 
      | t :: h => (max_list_nat_aux (max m t) h)
      end.
      
      (* definition of the maximum of a list of natural numbers *)
      Definition max_list_nat (l: list nat) : nat := max_list_nat_aux 0 l.
      
      Fixpoint max_list_nat' (l: list nat): nat := 
        fold_left max l 0.
        
      Lemma max_list_nat_max_list_nat': forall (l: list nat), max_list_nat l = max_list_nat' l.
      Proof.
        destruct l as [|t q].
        reflexivity.
        revert t ; induction q as [|t' q' IH]; intros t.
        reflexivity.
        apply IH.
      Qed.
      
      (* properties on max_list_nat *)
      Lemma max_list_nat_aux_max: forall (n m: nat)(l: list nat), 
        max_list_nat_aux (max n m) l = max n (max_list_nat_aux m l).
      Proof.
        intros n m l.
        revert n m ; 
        induction l as [|t l IHl] ; intros n m.
        reflexivity.
        simpl.
        do 2 rewrite IHl.
        rewrite max_assoc.
        reflexivity.
      Qed.

      Lemma max_list_cons: forall (t: nat)(l: list nat),
        max_list_nat (t:: l) = max t (max_list_nat l).
      Proof.
        intros t l.
        destruct l as [| h l].
        destruct t as [|t] ;
        reflexivity.
        destruct t as [|t].
        reflexivity.
        apply max_list_nat_aux_max.
      Qed.
      

      Lemma max_list_nat_nil: max_list_nat nil = 0.
      Proof.
        reflexivity.
      Qed.
      
      Lemma max_list_max (l: list nat) : 
        forall (x: nat), In x l -> x <= max_list_nat l.
      Proof.
        induction l as [|h t] ;
        intros x H.
        inversion H.
        rewrite max_list_cons.
        destruct H as [e | H].
        rewrite <- e.
        apply le_max_l.
        assert (H1: max_list_nat t <= max h (max_list_nat t)).
        apply le_max_r.
        apply (le_trans _ _ _ (IHt x H) H1).
      Qed.
      
      Lemma exists_max_list_nat: forall l: list nat, 
        exists m, forall n, In n l -> n <= m.
      Proof.
        intros l.
        exists (max_list_nat l).
        apply max_list_max.
      Qed.
  
  End MaxListNat.
  
   
End Tools_lists.

Section Tools_arith.

  Lemma lt_m_n_Sm_n: forall m n: nat, m < n -> (n - (S m)) < n.
  Proof.
    intros m n h.
    apply lt_minus.
    apply (lt_le_S m n h).
    apply lt_O_Sn.
  Qed.

  Lemma Sn_Sm_eq_n_m: forall (n m: nat), (S n) - (S m) = n - m.
  Proof.
    reflexivity.
  Qed.

  Lemma minus_to_minus: forall (n m p: nat), n - m = p -> n - m - p = 0. 
  Proof.
    intros n m p h.
    rewrite h.
    apply minus_diag.
  Qed.

  Lemma minus_reg_l: forall (n m: nat)(h: m <= n), n - m = n -> m = 0.
  Proof.
    intros n m h H.
    elim (lt_eq_lt_dec m 0); intros a.
    inversion_clear a as [H0|e].
    inversion H0.
    assumption.
    apply False_rec.
    assert (n-m < n).
    apply (lt_minus _ _ h a).
    rewrite H in H0.
    apply (lt_irrefl _ H0).
  Qed.

  Lemma lt_plus_S : forall n m, n < n + (S m).
  Proof.
    intros n m.
    rewrite <- plus_n_Sm , <- plus_Sn_m.
    apply lt_plus_trans, lt_n_Sn.
  Qed.

  Lemma minus_n_m_0 (n m: nat) : m <= n -> n - m = 0 -> n = m.
  Proof.
    revert m ; induction n as [|n IH] ; intros m h1 h2.
    symmetry.
    apply (minus_reg_l h1 h2).
    destruct m as [|m].
    inversion h2.
    apply eq_S.
    apply IH.
    apply le_S_n, h1.
    rewrite <- Sn_Sm_eq_n_m; assumption.
  Qed.

  Lemma lt_minus_S: forall m n: nat, m < n -> (n - (S m)) < n.
  Proof.
    intros m n h.
    apply lt_minus.
    apply (lt_le_S m n h).
    apply lt_O_Sn.
  Qed.

  Lemma lt_n_m_0: forall m n: nat, m < n -> 0 < n.
  Proof.
    intros m n h.
    rewrite (S_pred n m h).
    apply (gt_Sn_O (pred n)).
  Qed. 

  Lemma pred_inf_n: forall m n: nat, m < n -> pred n < n. 
  Proof. 
    intros m n h.
    apply (lt_pred_n_n n (lt_n_m_0 h)).
  Qed.



End Tools_arith.

Section Tools_option.

  Definition RelOp (T: Set)(RelT: relation T): relation (option T).
  Proof.
    intros [t1|] [t2|].
    exact (RelT t1 t2).
    exact False.
    exact False.
    exact True.
  Defined.

  Lemma RelOp_refl (T: Set)(RelT: relation T)(Req: Reflexive RelT)(ot: option T): 
    RelOp RelT ot ot.
  Proof.
    destruct ot as [t|] ; simpl ; reflexivity.
  Qed.
  
  Lemma RelOp_sym (T: Set)(RelT: relation T)(Req: Symmetric RelT)(ot1 ot2: option T): 
    RelOp RelT ot1 ot2 -> RelOp RelT ot2 ot1.
  Proof.
    intros H ; destruct ot1 as [t1|] ; destruct ot2 as [t2|] ; simpl ; try inversion H.
    simpl in H ; symmetry ; assumption.
    reflexivity.
  Qed.
  
  Lemma RelOp_trans (T: Set)(RelT: relation T)(Req: Transitive RelT)(ot1 ot2 ot3: option T): 
    RelOp RelT ot1 ot2 -> RelOp RelT ot2 ot3 -> RelOp RelT ot1 ot3.
  Proof.
    intros H1 H2 ; destruct ot1 as [t1|] ; destruct ot2 as [t2|] ; destruct ot3 as [t3|] ; 
    simpl ; try inversion H1 ; try inversion H2.
    simpl in H1, H2 ; transitivity t2 ; assumption.
    reflexivity.
  Qed.
  
  Add Parametric Relation (T: Set)(RelT: relation T)(Req: Equivalence RelT): 
    (option T) (RelOp RelT)
    reflexivity proved by (RelOp_refl _)
    symmetry proved by (RelOp_sym _)
    transitivity proved by (RelOp_trans _)
  as RelOpRel.
End Tools_option.

Section Bijective.

   Definition Bijective (T U:Type) (f:T->U)(g: U -> T):Prop:=
     (forall t, g (f t) = t) /\ (forall u, f (g u) = u).

   Lemma Bij_sym (T U:Type)(f:T->U)(g: U -> T): 
     Bijective f g -> Bijective g f.
   Proof.
     intros [h1 h2].
     split ; assumption.
   Qed.

   Lemma Bij_trans (T U V: Set)(f1: T -> U)(g1 : U -> T)(f2 : U -> V)(g2 : V -> U) :
     Bijective f1 g1 -> Bijective f2 g2 -> Bijective (fun x => f2 (f1 x)) (fun x => g1 (g2 x)).
   Proof.
     intros [h1 h2] [h3 h4].
     split.
     intros t.
     rewrite h3.
     apply h1.
     intros u.
     rewrite h2.
     apply h4.
   Qed.

  Lemma bij_inj (A B: Set)(f : A -> B)(g : B -> A): 
    Bijective f g -> forall a1 a2, f a1 = f a2 -> a1 = a2.
  Proof.
    intros [H1 _] a1 a2 H3.
    rewrite <- (H1 a1), <- (H1 a2).
    rewrite H3.
    reflexivity.
  Qed.

End Bijective.