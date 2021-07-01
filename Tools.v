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
Require Import PeanoNat.
Require Import Lia.

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
      
      Definition max_list_nat' (l: list nat): nat := 
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
        rewrite Nat.max_assoc.
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
        apply Nat.le_max_l.
        assert (H1: max_list_nat t <= max h (max_list_nat t)).
        apply Nat.le_max_r.
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
  
  Fixpoint remove' (X: Set)(eq_dec : forall x y : X, {x = y}+{x <> y})(x: X)(l: list X) : 
    list X:= 
  match l with 
    nil => nil
  | t::q => if (eq_dec x t) then q else t::(remove' eq_dec x q)
  end.
  
  Lemma remove'_In_length (X: Set)(eq_dec : forall x y : X, {x = y}+{x <> y})
    (x: X)(l: list X): In x l -> S (length (remove' eq_dec x l)) = length l.
  Proof.
    induction l as [|t l IH] ; intro H.
    inversion H.
    destruct H as [H|H].
    rewrite H.
    simpl.
    elim (eq_dec x x) ; intros a.
    reflexivity.
    contradiction (eq_refl x).
    simpl.
    elim (eq_dec x t) ; intros a.
    reflexivity.
    simpl.
    rewrite (IH H).
    reflexivity.
  Qed.

  Lemma remove'_In (X: Set)(eq_dec : forall x y : X, {x = y}+{x <> y})
    (x1 x2: X)(l: list X): In x1 l -> x1 <> x2 -> In x1 (remove' eq_dec x2 l).
  Proof.
    induction l as [|t l IH].
    intros H ; inversion H.
    intros [H1|H1] H2.
    simpl.
    elim (eq_dec x2 t) ; intros a.
    contradiction (sym_eq (trans_eq a H1)).
    left.
    assumption.
    simpl.
    elim (eq_dec x2 t) ; intros a.
    assumption.
    right.
    apply IH ; assumption.
  Qed.
  
  Lemma NoDup_cons'(X: Set)(x: X)(l: list X) : NoDup (x::l) -> NoDup l.
  Proof.
    intros H.
    inversion_clear H.
    assumption.
  Qed.

  Lemma incl_length (X: Set)(eq_dec : forall x y : X, {x = y}+{x <> y})(l1 l2 : list X): 
    incl l1 l2 -> NoDup l1 -> length l1 = length l2 -> incl l2 l1.
  Proof.
    revert l2 ; induction l1 as [|t1 l1 IH] ; intros [|t2 l2] H1 H2 H3 x H4.
    assumption.
    inversion H3.
    inversion H3.
    destruct H4 as [H4 | H4].
    rewrite <- H4 ; clear x H4.
    destruct (H1 t1 (in_eq _ _)).
    rewrite H ; apply in_eq.
    inversion_clear H2 as [| t1' l1' H4 H5].
    right.
    apply (IH (remove' eq_dec t1 (t2 :: l2))).
    intros x H6.
    apply remove'_In.
    apply (H1 x (in_cons _ _ _ H6)).
    intro H7 ; rewrite H7 in H6 ; contradiction H6.
    assumption.
    apply eq_add_S.
    rewrite remove'_In_length.
    assumption.
    apply (in_cons _ _ _ H).
    
    simpl.
    elim (eq_dec t1 t2) ; intros a.
    rewrite <- a ; assumption.
    apply in_eq.
    
    elim (eq_dec t1 x) ; intros a.
    left ; assumption.
    right.
    apply (IH (remove' eq_dec t1 (t2::l2))).
    inversion_clear H2 as [| t1' l1' H5 H6].
    intros x1 H7.

    apply remove'_In.
    apply H1, in_cons, H7.
    intros H8 ; rewrite H8 in H7 ; contradiction H7.
    apply (NoDup_cons' H2).
    apply eq_add_S.
    rewrite remove'_In_length.
    assumption.
    apply (H1 t1 (in_eq _ _)).
    apply remove'_In.
    apply (in_cons _ _ _ H4).
    intro H ; contradiction (sym_eq H).
  Qed.

  Lemma incl_length2 (X: Set)(eq_dec : forall x y : X, {x = y}+{x <> y})(l1 l2 : list X): 
    incl l1 l2 -> NoDup l1 -> length l1 <= length l2.
  Proof.
    revert l2 ; induction l1 as [|t1 l1 IH] ; intros l2 H1 H2.
    apply le_0_n.
    simpl.
    rewrite <- (remove'_In_length eq_dec t1 l2).
    apply le_n_S.
    apply IH.
    intros x H3.
    apply remove'_In.
    apply H1, (in_cons _ _ _ H3).
    inversion_clear H2 as [| t1' l1' H4 H5].
    intros H6.
    rewrite H6 in H3 ; contradiction H3.
    apply (NoDup_cons' H2).
    apply (H1 _ (in_eq _ _)).
  Qed.
  
  Lemma cons_not_eq(X: Set): forall (x: X) l, x :: l <> l.
  Proof.
    intros x l ; revert x ; induction l ; intros x H.
    inversion H.
    inversion H.
    apply (IHl a H2).
  Qed.

  Lemma eq_list_nat_dec : forall (l l': list nat), {l = l'} + {not (l = l')}.
  Proof.
    induction l.
    intros [| n l].
    left.
    reflexivity.
    right.
    intros H.
    inversion H.
    intros l'.
    elim (IHl l') ; intros H.
    rewrite H.
    right.
    apply cons_not_eq.
    destruct l'.
    right.
    intros H1 ; inversion H1.
    elim (eq_nat_dec a n) ; intros H1.
    rewrite H1.
    elim (IHl l') ; intros H2.
    left.
    f_equal; assumption.
    right.
    intros H3.
    inversion H3.
    contradiction H2.
    right.
    intros H3.
    inversion H3.
    contradiction H2.
  Qed.
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
  
  Lemma minus_le (n m: nat) : n <= m -> 0 = m - n -> m = n.
  Proof.
    lia.
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

Section subrel.

  Lemma subrelation_eq (X: Set)(RelX: relation X): Reflexive RelX -> subrelation eq RelX.
  Proof.
    intros H1 x1 x2 H2.
    rewrite H2.
    apply H1.
  Qed.
  
End subrel.


