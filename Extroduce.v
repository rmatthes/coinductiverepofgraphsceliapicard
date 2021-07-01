(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(** provides the definition of extroduce and all associated tools 
    and lemmas *)

Require Import Fin.
Require Import Ilist. 
Require Import Setoid.
Require Import Tools.
Require Import List.
Require Import Utf8.

Set Implicit Arguments. 

   (* Called remEl in the paper *) 
   Definition extroduce : forall (T: Set)(i: ilist T)(f: Fin (lgti i)), ilist T.
   Proof.
     intros T [n i] f.
     induction n as [|n IH].
     inversion f.
     elim (zerop (decode_Fin f)) ; intros a.
     exact (mkilist (fun x => i (succ x))).
     exact (icons (i (first n)) (IH (fun x => (i (succ x))) (get_cons _ a))).
   Defined.
   
   Lemma extroduce_lgti: forall (T: Set)(i: ilist T)(f: Fin (lgti i)),
     lgti i = S (lgti (extroduce i f)).
   Proof.
     intros T [n i] f.
     simpl in *|-*.
     unfold nat_rec, nat_rect, sumbool_rec, sumbool_rect, icons, mkilist.
     induction n as [|n IH].
     inversion f.
     apply eq_S.
     elim (zerop (decode_Fin f)) ; intros a.
     reflexivity.
     apply IH.
   Defined.

   Hint Rewrite <- extroduce_lgti: evalLgti.

   Ltac extroduce_lgti_S := apply eq_add_S; 
                         rewrite <- extroduce_lgti.
   Ltac evalLgtiExtro := repeat (autorewrite with evalLgti || extroduce_lgti_S).
   Ltac extroduce_lgti_S_Ass h := apply eq_S in h;
                               rewrite <- extroduce_lgti in h.
   Ltac evalLgtiExtro_Ass h := repeat (autorewrite with evalLgti in h || extroduce_lgti_S_Ass h).
     
   Lemma extroduce_ok1 : forall (T: Set)(RelT: relation T)(EqT: Equivalence RelT) 
     (i: ilist T)(f: Fin (lgti i))(h: 0 < decode_Fin f),
     RelT (ihead (extroduce i f) (fcti i f)) (ihead i (fcti i f)).
   Proof.
     intros T RelT [Rrefl _ _] [n i] f h.
     simpl in *|-*.
     unfold nat_rec, nat_rect, sumbool_rec, sumbool_rect, iconsn.
     destruct n as [|n].
     inversion f.
     elim (zerop (decode_Fin f)) ; intros a.
     apply False_rec ; rewrite <- a in h ; apply (lt_irrefl _ h).
     apply Rrefl.
   Qed.

   Lemma extroduce_ok2: forall (T: Set)
     (i: ilist T)(f: Fin (lgti i))(f': Fin (lgti (extroduce i f)))
     (h: decode_Fin f' < decode_Fin f),
       (fcti (extroduce i f) f') =
        (fcti i (rewriteFins (sym_eq (extroduce_lgti i f)) (code_Fin1 (lt_S _ _(decode_Fin_inf_n f'))))).
   Proof.
     intros T [n i] f f' h.
     fold (mkilist i) in *|-*.
     simpl in f.

     assert (e:= lt_S _ _ (decode_Fin_inf_n f')).
     rewrite (code_Fin1_proofirr _ e).
     assert (e1 := sym_eq (extroduce_lgti (mkilist i) f)).
     change (lgti (mkilist i)) with n in e1.
     assert (e3: rewriteFins (sym_eq (extroduce_lgti (mkilist i) f)) (code_Fin1 e) = 
       rewriteFins e1 (code_Fin1 e)) by treatFinPure.
     rewrite e3 ; clear e3.
     change (fcti (mkilist i)) with (i).
     assert (e3 : decode_Fin f' < n).
     rewrite <- e1.
     assumption.
     assert (e4: rewriteFins e1 (code_Fin1 e) = code_Fin1 e3) by treatFinPure.
     rewrite e4 ; clear e4 e1 e.
     induction n as [|n IH].
     inversion f.

     revert f' h e3.
     simpl.
     unfold sumbool_rec, sumbool_rect.
     elim (zerop (decode_Fin f)) ; simpl ; intros a f' e1 e2.
     rewrite a in e1.
     inversion e1.
     
     elim (zerop (decode_Fin f')) ; intros b.
     revert e2 ; rewrite b ; intro e2.
     rewrite code_Fin1_Sn_0, (decode_Fin_0_first _ b).
     reflexivity.

     assert (h1 : f' = succ (get_cons f' b)) by treatFinPure.
     revert e1 e2 ; rewrite h1 ; intros e1 e2 ; clear h1.
     simpl.
     change ((fcti (extroduce (mkilist (fun x : Fin n => i (succ x))) (get_cons f a)) (get_cons f' b)) =
                  (i (code_Fin1_Sn (lt_n_Sm_le _ _ e2)))).
     assert (e3: decode_Fin (get_cons f' b) < decode_Fin (get_cons f a)).
     apply lt_S_n.
     rewrite <- (decode_Fin_get_cons f a).
     assumption.
     assert (e4 : decode_Fin (get_cons f' b) < n).
     apply (lt_S_n _ _ e2).
     rewrite (IH _ _ _ e3 e4).
     f_equal.
     change (succ (code_Fin1 e4) = code_Fin1 e2).
     apply decode_Fin_unique.
     treatFinPure.
   Qed.

   Lemma extroduce_ok3 : forall (T: Set)(i: ilist T)(f: Fin (lgti i))(f': Fin (lgti (extroduce i f)))
     (h: decode_Fin f <= decode_Fin f'),
      (fcti (extroduce i f) f') =
        (fcti i (rewriteFins (sym_eq (extroduce_lgti i f))(code_Fin1 (decode_Fin_inf_n (succ f'))))).
   Proof.
     intros T i f f' h.
     rewrite code1_decode_Id.
     assert (e1:= decode_Fin_inf_n (succ f')).
     rewrite <- extroduce_lgti in e1.
     assert (e2: rewriteFins (sym_eq (extroduce_lgti i f))(succ f') = code_Fin1 e1).
     treatFinPure.
     rewrite e2 ; clear e2.
     destruct i as [n i].
     fold (mkilist i) in *|-*.
     simpl fcti at 2.
     simpl in f, e1.
     
     induction n as [|n IH].
     inversion e1.
     
     revert f' h e1.
     simpl.
     unfold sumbool_rec, sumbool_rect.
     elim (zerop (decode_Fin f)) ; simpl ; intros a f' h e1.
     fold (code_Fin1 e1).
     f_equal.
     treatFinPure.
     
     elim (zerop (decode_Fin f')) ; intros b;
     change (Fin (S (lgti (extroduce (mkilist (fun x : Fin n => i (succ x))) (get_cons f a))))) in f'.
     rewrite b in h.
     apply False_rec.
     apply (lt_irrefl _ (lt_le_trans _ _ _ a h)).

     assert (h1 : f' = succ (get_cons f' b)) by treatFinPure.
     revert e1 ; rewrite h1 ; intros e1 ; clear h1.
     
     (* by looking closely: *)
     change ((fcti (extroduce (mkilist (fun x : Fin n => i (succ x))) (get_cons f a)) (get_cons f' b)) =
                  (i (code_Fin1_Sn (lt_n_Sm_le _ _ e1)))).
     assert (e3: decode_Fin (get_cons f a) <= decode_Fin (get_cons f' b)).
     treatFinAss.
     assert (e4 : S (decode_Fin (get_cons f' b)) < n).
     apply (lt_S_n _ _ e1).
     change ((fcti (extroduce (mkilist (fun x : Fin n => i (succ x))) (get_cons f a)) (get_cons f' b)) =
       (i (code_Fin1 e1))).
     rewrite (IH (fun x : Fin n => i (succ x)) _ _ e3 e4).
     f_equal.
     treatFinPure.
   Qed.

(* we want to understand better aux_extroduce_ok2 by help of the following definition *)

    (* this is weakening in the sense of logic *)
   Fixpoint weakFin (n: nat)(f: Fin n): Fin (S n) :=
     match f in Fin k return Fin (S k) with first k => first (S k) | succ f => succ (weakFin f) end.

    (* the minimum requirement for weakening *)
   Lemma weakFin_ok : forall (n:nat)(f: Fin n), decode_Fin (weakFin f) = decode_Fin f.
   Proof.
     intros n f.
     induction f as [k|k f IH].
     reflexivity.
     simpl.
     rewrite IH.
     reflexivity.
   Qed.
  
   Hint Rewrite weakFin_ok: evalDecode_FinDb.

   (* an auxiliary lemma that characterizes weakFin *)
   Lemma aux_extroduce_ok2': forall (n: nat)(f: Fin n), code_Fin1 (lt_S _ _(decode_Fin_inf_n f)) = weakFin f.
   Proof.
     intros n [k |k f]; treatFinPure.
   Qed.
   
   (* a better formulation of extroduce_ok2 which is just a corollary (could a direct proof
   of extroduce_ok2' be better than the direct proof of extroduce_ok2?) *)
   Lemma extroduce_ok2' : forall (T: Set)(i: ilist T)(f: Fin (lgti i))(f': Fin (lgti (extroduce i f)))
     (h: decode_Fin f' < decode_Fin f),
     (fcti (extroduce i f) f') = (fcti i (rewriteFins (sym_eq (extroduce_lgti i f)) (weakFin f'))).
   Proof.
     intros T [n i] f f' h.
     rewrite <- aux_extroduce_ok2'.
     rewrite (extroduce_ok2 _ _ _ h).
     reflexivity.
   Qed.

   Instance eqEq : forall (T: Set), Equivalence (fun t t0:T => t = t0).
   Proof.
     intro T.
     assert (H := @eq_equivalence T).
     destruct H as [H1 H2 H3].
     apply Build_Equivalence ; assumption.
   Defined.

   Lemma fRel: forall (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(n: nat)
     (i: ilistn T n)(f1 f2: Fin n), f1 = f2 -> RelT (i f1) (i f2).
   Proof.
     intros T RelT EqT n i f1 f2 e.
     rewrite e ; reflexivity.
   Qed.

   Lemma extroduce_ok3' (T: Set)(i: ilist T)(f: Fin (lgti i))(f': Fin (lgti (extroduce i f)))
    (h: decode_Fin f <= decode_Fin f'):
     fcti (extroduce i f) f' = fcti i (rewriteFins (sym_eq (extroduce_lgti i f))(succ f')).
   Proof.
     intros.
     rewrite (extroduce_ok3 _ _ _ h).
     f_equal.
     treatFinPure.
   Qed.

   Lemma extroduce_ok_cor (T: Set)(i1: ilist T)(f1: Fin(lgti i1))(f0:Fin (lgti (extroduce i1 f1))):
     exists f1': Fin (lgti i1), fcti (extroduce i1 f1) f0 = fcti i1 f1'.
   Proof.
    elim (le_lt_dec (decode_Fin f1) (decode_Fin f0)) ; intros a.
    exists (rewriteFins (eq_sym (extroduce_lgti i1 f1)) (succ f0)).
    apply extroduce_ok3', a.
    exists (rewriteFins (eq_sym (extroduce_lgti i1 f1)) (weakFin f0)).
    apply extroduce_ok2', a.
   Qed.
 
   Lemma extroduce_ilist_rel (T: Set)(RelT: relation T)(n: nat)(l1 l2 : ilistn T n)
     (i: Fin n): ilist_rel RelT (mkilist l1) (mkilist l2) -> 
     ilist_rel RelT (extroduce (mkilist l1) i) (extroduce (mkilist l2) i).
   Proof.
     intros [h1 H1].
     assert (h2 : lgti (extroduce (mkilist l1) i) = lgti (extroduce (mkilist l2) i)).
     apply eq_add_S.
     do 2 rewrite <- extroduce_lgti.
     reflexivity.
     assert (H1' : forall i, RelT (l1 i) (l2 i)).
     intros i'.
     rewrite (decode_Fin_unique _ _ (decode_Fin_match' i' h1)) at 2.
     apply H1.
     clear H1.
     
     apply (is_ilist_rel _ _ _ h2).
     intro i'.
     elim (le_lt_dec (decode_Fin i) (decode_Fin i')) ; intros a.
     rewrite extroduce_ok3' ; try assumption.
     rewrite (decode_Fin_match' i' h2) in a.
     rewrite extroduce_ok3' ; try assumption.
     assert (H4 : rewriteFins (Logic.eq_sym (extroduce_lgti (mkilist l2) i)) (succ (rewriteFins h2 i')) = 
       rewriteFins (eq_sym (extroduce_lgti (mkilist l1) i)) (succ i')).
     apply decode_Fin_unique.
     do 2 rewrite <- decode_Fin_match'.
     simpl.
     rewrite <- decode_Fin_match'.
     reflexivity.
     rewrite H4.
     apply H1'.
     
     rewrite extroduce_ok2' ; try assumption.
     rewrite (decode_Fin_match' i' h2) in a.
     rewrite extroduce_ok2' ; try assumption.
     assert (H4 : rewriteFins (Logic.eq_sym (extroduce_lgti (mkilist l2) i)) (weakFin (rewriteFins h2 i')) = 
       rewriteFins (eq_sym (extroduce_lgti (mkilist l1) i)) (weakFin i')).
     apply decode_Fin_unique.
     do 2 rewrite <- decode_Fin_match'.
     do 2 rewrite weakFin_ok.
     rewrite <- decode_Fin_match'.
     reflexivity.
     rewrite H4.
     apply H1'.
   Qed.

   Lemma extroduce_ilist_rel_bis (T: Set)(RelT: relation T)(l1 l2 : ilist T)
     (i: Fin (lgti l1))(h: lgti l1 = lgti l2) : ilist_rel RelT l1 l2 ->
     ilist_rel RelT (extroduce l1 i) (extroduce l2 (rewriteFins h i)).
   Proof.
     destruct l1 as [n l1] ; destruct l2 as [n2 l2].
     simpl in i, h.
     revert l2 ; rewrite <- h ; clear n2 h ; intros l2 h.
     apply extroduce_ilist_rel, h.
   Qed.
   
   Lemma extroduce_ilist_rel_refined (A: Set)(R: relation A)(l1 l2 : ilist A)
     (i: Fin (lgti l1))(Hyp: ilist_rel R l1 l2): 
     ilist_rel R (extroduce l1 i) (extroduce l2 (rewriteFins (ilist_rel_lgti Hyp) i)).
   Proof.
     destruct l1 as [n l1].
     destruct l2 as [n' l2].
     assert (ii := ilist_rel_lgti Hyp).
     simpl in ii.
     revert l2 Hyp.
     rewrite <- ii.
     clear ii.
     intros.
     assert (rewriteFins (ilist_rel_lgti Hyp) i = i).
     treatFinPure.
     
     rewrite H.
     apply extroduce_ilist_rel.
     assumption.
   Qed.

   Lemma extroduce_imap (T U: Set)(f: T -> U)(l: ilist T)(i: Fin (lgti l)): 
     ilist_rel eq (extroduce (imap f l) i) (imap f (extroduce l i)).
   Proof.
     assert (h: lgti (extroduce (imap f l) i) =  lgti (imap f (extroduce l i))).
     apply eq_add_S.
     do 2 rewrite imap_lgti, <- extroduce_lgti.
     reflexivity.
     apply (is_ilist_rel _ _ _  h).
     intro i'.
     rewrite imap_apply. 
     elim (le_lt_dec (decode_Fin i) (decode_Fin i')); intros a.
     rewrite extroduce_ok3'; try assumption.
     rewrite imap_apply.
     rewrite extroduce_ok3'.
     repeat f_equal.
     treatFinPure.
     rewrite <- decode_Fin_match' ; assumption.

     rewrite extroduce_ok2' ; try assumption.
     rewrite imap_apply.
     rewrite extroduce_ok2'.
     repeat f_equal.
     treatFinPure.
     rewrite <- decode_Fin_match' ; assumption.
   Qed.

   Definition extroduce_Fin : forall (n: nat)(fex: Fin (S n))(f: Fin n), Fin (S n).
   Proof.
     intros n fex f.
     elim (le_lt_dec (decode_Fin fex) (decode_Fin f)) ; intros a.
     exact (succ f).
     exact (weakFin f).
   Defined.

   Lemma extroduce_Fin_not_fex (n: nat)(fex: Fin (S n))(f: Fin n):
      extroduce_Fin fex f <> fex.
   Proof.
     intros.
     unfold extroduce_Fin; unfold sumbool_rec; unfold sumbool_rect.
     elim (le_lt_dec (decode_Fin fex) (decode_Fin f)) ; intros a; intro Hyp.
     rewrite <- Hyp in a.
     simpl in a.
     apply le_Sn_n in a.
     assumption.
     assert (H: decode_Fin (weakFin f) = decode_Fin fex).
     rewrite Hyp.
     reflexivity.
     evalDecode_Fin_Ass H.
     rewrite H in a.
     exact (lt_irrefl _ a).
   Qed.

   Lemma extroduce_lgti_S: forall (T: Set) (n: nat) (i: ilistn T (S n)) (f: Fin(S n)), 
     n = lgti (extroduce (mkilist i) f).
   Proof.
     intros T n i f.
     apply eq_add_S.
     rewrite (refl_equal _ : S n = lgti (mkilist i)) at 1.
     apply extroduce_lgti.
   Qed.

   Lemma extroduce_Fin_ok: forall (T: Set)(RelT: relation T)(EqT: Equivalence RelT)(n: nat)
     (i: ilistn T (S n))(fex: Fin (S n))(f: Fin n),
       RelT (i (extroduce_Fin fex f)) 
       (fcti (extroduce (mkilist i) fex) (rewriteFins (extroduce_lgti_S i fex) f)).
   Proof.
     intros T RelT EqT n i fex f.
     unfold extroduce_Fin.
     unfold sumbool_rec ; unfold sumbool_rect.
     elim (le_lt_dec (decode_Fin fex) (decode_Fin f)) ; intros a.
     assert (h: decode_Fin fex <= 
       decode_Fin (rewriteFins (@extroduce_lgti_S T n i fex) f)).
     treatFin a.
     rewrite extroduce_ok3'; try assumption.
     apply (fRel EqT).
     treatFinPure.
     rewrite extroduce_ok2'; try assumption.
     apply (fRel EqT).
     treatFinPure.
     treatFinAss.
   Qed.
  
   Corollary extroduce_Fin_ok_cor (T: Set)(n: nat)(i: ilistn T (S n))(fex: Fin (S n))(f: Fin n): 
     i (extroduce_Fin fex f) = 
     fcti (extroduce (mkilist i) fex) (rewriteFins (extroduce_lgti_S i fex) f).
   Proof.
     intros.
     apply extroduce_Fin_ok.
     apply eqEq.
   Qed.

   Lemma extroduce_Fin_ok1  (n: nat)(iex: Fin (S n))(i: Fin n) (h: decode_Fin iex <= decode_Fin i): 
     extroduce_Fin iex i = succ i.
   Proof.
     unfold extroduce_Fin, sumbool_rec, sumbool_rect.
     elim (le_lt_dec (decode_Fin iex) (decode_Fin i)) ; intros a.
     reflexivity.
     apply False_rec, (lt_irrefl _ (lt_le_trans _ _ _ a h)).
   Qed.

   Lemma extroduce_Fin_ok2  (n: nat)(iex: Fin (S n))(i: Fin n) (h: decode_Fin i < decode_Fin iex): 
     extroduce_Fin iex i = weakFin i.
   Proof.
     unfold extroduce_Fin, sumbool_rec, sumbool_rect.
     elim (le_lt_dec (decode_Fin iex) (decode_Fin i)) ; intros a.
     apply False_rec, (lt_irrefl _ (lt_le_trans _ _ _ h a)).
     reflexivity.
   Qed.

   Definition index_in_extroduce (n: nat)(fex: Fin (S n))(f: Fin (S n)): 
     decode_Fin fex <> decode_Fin f -> Fin n.
   Proof.
     intros.
     elim (lt_eq_lt_dec  (decode_Fin fex) (decode_Fin f)) ; intros a.
     destruct a as [a|a].
     exact (get_cons f (lt_n_m_0 a)).
     (* idea: f is a successor, hence one can take its predecessor in Fin n *)
     apply False_rec.
     exact (H a).
     exact (code_Fin1 (lt_le_trans _ _ _ a (lt_n_Sm_le _ _ (decode_Fin_inf_n fex)))).
     (* idea: f < fex, hence f(!) can be strenghtened to be in Fin n *)
   Defined.

   Lemma index_in_extroduce_decode1 (n: nat)(fex: Fin (S n))(f: Fin (S n))(Hyp1:
     decode_Fin fex <> decode_Fin f)(Hyp2:
     decode_Fin fex < decode_Fin f): S(decode_Fin(index_in_extroduce fex f Hyp1)) = decode_Fin f.
   Proof.
     intros.
     unfold index_in_extroduce.
     unfold sumor_rec ; unfold sumor_rect.
     elim (lt_eq_lt_dec  (decode_Fin fex) (decode_Fin f)) ; intros a.
     destruct a as [a|a].
     treatFinPure.
     apply False_rec.
     apply (Hyp1 a).
     apply False_rec.
     apply (lt_asym _ _ a Hyp2).
   Qed.

   Lemma index_in_extroduce_decode2 (n: nat)(fex: Fin (S n))(f: Fin (S n))(Hyp1:
     decode_Fin fex <> decode_Fin f)(Hyp2:
     decode_Fin f < decode_Fin fex): decode_Fin(index_in_extroduce fex f Hyp1) = decode_Fin f.
   Proof.
     intros.
     unfold index_in_extroduce.
     unfold sumor_rec ; unfold sumor_rect.
     elim (lt_eq_lt_dec  (decode_Fin fex) (decode_Fin f)) ; intros a.
     destruct a as [a|a].
     apply False_rec.
     apply (lt_asym _ _ a Hyp2).
     apply False_rec.
     apply (Hyp1 a).
     treatFinPure.
   Qed.
    
   Lemma index_in_extroduce_decode3 (n: nat)(fex: Fin (S n))(f: Fin (S n))(Hyp1:
     decode_Fin fex <> decode_Fin f): decode_Fin(index_in_extroduce fex f Hyp1) <= decode_Fin f.
   Proof.
     intros.
     elim (lt_eq_lt_dec  (decode_Fin fex) (decode_Fin f)) ; intros a.
     destruct a as [a|a].
     rewrite <- (index_in_extroduce_decode1 fex f Hyp1 a).
     auto.
     apply False_rec.
     apply (Hyp1 a).
     rewrite index_in_extroduce_decode2.
     auto.
     assumption.
   Qed.
    
   Lemma index_in_extroduce_decode4 (n: nat)(fex: Fin (S n))(f: Fin (S n))(Hyp1:
     decode_Fin fex <> decode_Fin f): S(decode_Fin(index_in_extroduce fex f Hyp1)) >= decode_Fin f.
   Proof.
     intros.
     elim (lt_eq_lt_dec  (decode_Fin fex) (decode_Fin f)) ; intros a.
     destruct a as [a|a].
     rewrite <- (index_in_extroduce_decode1 fex f Hyp1 a).
     auto.
     apply False_rec.
     apply (Hyp1 a).
     rewrite index_in_extroduce_decode2.
     auto.
     assumption.
   Qed.

   Lemma index_in_extroduce_ok (T: Set)(RelT: relation T)(EqT: Equivalence RelT)
     (n: nat)(i: ilistn T (S n))(fex: Fin (S n))(f: Fin (S n))(H: decode_Fin fex <> decode_Fin f): 
     RelT (i f) (fcti (extroduce (mkilist i) fex) 
       (rewriteFins (extroduce_lgti_S i fex) (index_in_extroduce fex f H))).
   Proof.
     intros.
     unfold index_in_extroduce.
     unfold sumor_rec ; unfold sumor_rect.
     elim (lt_eq_lt_dec  (decode_Fin fex) (decode_Fin f)) ; try intros [a|a] ; try intros a.
     rewrite (extroduce_ok3' (mkilist i)).
     apply (fRel EqT).
     treatFinPure.
     treatFinAss.
     apply False_rec.
     exact (H a).
     rewrite (extroduce_ok2' (mkilist i)).
     apply (fRel EqT).
     treatFinAss.
     treatFinAss.
   Qed.
    
   Corollary index_in_extroduce_ok_cor (T: Set)(n: nat)(i: ilistn T (S n))(fex: Fin (S n))(f: Fin (S n))
     (H: decode_Fin fex <> decode_Fin f): 
     i f = fcti (extroduce (mkilist i) fex) (rewriteFins (extroduce_lgti_S i fex) (index_in_extroduce fex f H)).
   Proof.
     intros.
     apply index_in_extroduce_ok.
     apply eqEq.
   Qed.

   (* wish: index_in_extroduce_ok that does not only speak about mkilist i *)
  
   Lemma index_in_extroduce_ok'_aux (T: Set)(n: nat)(i: ilist T)(Hyp: S n = lgti i)(fex: Fin (lgti i)):
     n = lgti (extroduce i fex).
   Proof.
     intros.
     apply eq_add_S.
     rewrite <- extroduce_lgti.
     assumption.
   Qed.
  (* this little lemma guarantees that Hyp' in the following lemma is always available *)  

   Lemma index_in_extroduce_ok' (T: Set)(RelT: relation T)(EqT: Equivalence RelT)
     (n: nat)(i: ilist T)(Hyp: S n = lgti i)(fex: Fin (lgti i))
     (Hyp': n = lgti (extroduce i fex))(f: Fin (S n))
     (H: decode_Fin (rewriteFins (sym_eq Hyp) fex) <> decode_Fin f): 
     RelT (fcti i (rewriteFins Hyp f)) 
          (fcti (extroduce i fex) (rewriteFins Hyp' (index_in_extroduce (rewriteFins (sym_eq Hyp) fex) f H))).
   Proof.
     intros.
     destruct i as [n' i].
     fold (mkilist i) in *|-*.
     unfold index_in_extroduce.
     unfold sumor_rec ; unfold sumor_rect.
     elim (lt_eq_lt_dec  (decode_Fin(rewriteFins (sym_eq Hyp) fex)) (decode_Fin f)) ; intros a.
     destruct a as [a|a].
     set (fnew := get_cons f (lt_n_m_0 a)).
     assert (fnew_ok: decode_Fin f = S (decode_Fin fnew)).
     unfold fnew.
     treatFinPure.
     rewrite (extroduce_ok3' (mkilist i)).
     apply (fRel EqT).
     treatFinAss.
     evalDecode_Fin.
     apply lt_n_Sm_le.
     rewrite <- fnew_ok.
     treatFin a.
     apply False_rec.
     exact (H a).
     set (fnew := code_Fin1 (lt_le_trans _ _ _ a (lt_n_Sm_le _ _ 
       (decode_Fin_inf_n (rewriteFins (sym_eq Hyp) fex))))).
     assert (fnew_ok: decode_Fin f = decode_Fin fnew).
     unfold fnew.
     treatFinPure.
     rewrite (extroduce_ok2' (mkilist i)).
     apply (fRel EqT).
     treatFinAss.
     evalDecode_Fin.
     rewrite <- fnew_ok.
     treatFin a.
   Qed.

   Corollary index_in_extroduce_ok'_cor (T: Set)(n: nat)(i: ilist T)(Hyp: S n = lgti i)(fex: Fin (lgti i))
     (Hyp': n = lgti (extroduce i fex))(f: Fin (S n))
     (H: decode_Fin (rewriteFins (sym_eq Hyp) fex) <> decode_Fin f): 
       fcti i (rewriteFins Hyp f) = 
       fcti (extroduce i fex) (rewriteFins Hyp' (index_in_extroduce (rewriteFins (sym_eq Hyp) fex) f H)).
   Proof.
     intros.
     apply index_in_extroduce_ok'.
     apply eqEq.
   Qed.

   Lemma index_in_extroduce_proofirr (n: nat) (i1 i2 : Fin (S n))(h1 h2 : decode_Fin i1 <> decode_Fin i2) : 
     index_in_extroduce _ _ h1 = index_in_extroduce _ _ h2.
   Proof. 
     apply decode_Fin_unique. 
     elim (lt_eq_lt_dec (decode_Fin i1) (decode_Fin i2)) ; try intros [d|d] ; try intros d.
     apply eq_add_S.
     rewrite index_in_extroduce_decode1, index_in_extroduce_decode1 ; try assumption.
     reflexivity.
     contradiction h1.
     rewrite index_in_extroduce_decode2, index_in_extroduce_decode2 ; try assumption.
     reflexivity.
   Qed.

   Lemma index_in_extroduce_weakFin (n: nat) (i1: Fin (S n)) (i2: Fin n)(h: decode_Fin i1 <> decode_Fin (weakFin i2)): 
     decode_Fin (weakFin i2) < decode_Fin i1 -> index_in_extroduce i1 (weakFin i2) h = i2.
   Proof.
     intros h2.
     assert (h3 := index_in_extroduce_decode2 _ _ h h2).
     rewrite weakFin_ok in h3.
     rewrite (decode_Fin_unique _ _ h3).
     reflexivity.
   Qed.
   
   Lemma index_in_extroduce_succ (n: nat)(i1 i2: Fin (S n))(a : decode_Fin i1 <> decode_Fin i2) : 
     decode_Fin i1 <= decode_Fin (index_in_extroduce i1 i2 a) -> succ (index_in_extroduce i1 i2 a) = i2.
   Proof.
     intros h2.
     apply decode_Fin_unique.
     simpl.
     apply index_in_extroduce_decode1.
     destruct (le_lt_or_eq _ _ (le_trans _ _ _ h2 (index_in_extroduce_decode3 i1 i2 a)))  as [e|e].
     assumption.
     contradiction e.
   Qed. 

   Lemma index_in_extroduce_weakFin2 (n: nat)(i1 i2: Fin (S n))(a : decode_Fin i1 <> decode_Fin i2) : 
     decode_Fin (index_in_extroduce i1 i2 a)< decode_Fin i1 -> weakFin (index_in_extroduce i1 i2 a) = i2.
   Proof.
     intros h2.
     apply decode_Fin_unique.
     rewrite weakFin_ok.
     apply index_in_extroduce_decode2.
     destruct (le_lt_or_eq _ _ (le_trans _ _ _ (index_in_extroduce_decode4 i1 i2 a) (lt_le_S _ _ h2)))  as [e|e].
     assumption.
     contradiction a.
     symmetry ; assumption.
   Qed. 
   
   Lemma index_in_extroduce_succ2 (n: nat) (i1: Fin (S n)) (i2: Fin n)(h: decode_Fin i1 <> decode_Fin (succ i2)): 
     decode_Fin i1 < decode_Fin (succ i2) -> index_in_extroduce i1 (succ i2) h = i2.
   Proof.
     intros h2.
     apply decode_Fin_unique.
     apply eq_add_S.
     rewrite index_in_extroduce_decode1 ; try assumption.
     reflexivity.
   Qed.

   Lemma index_from_in_extroduce (n: nat)(iex i: Fin (S n))(h: decode_Fin iex <> decode_Fin i) : 
     extroduce_Fin iex (index_in_extroduce _ _ h) = i.
   Proof.
     apply decode_Fin_unique.
     elim (not_eq _ _ h) ; intros a.
     rewrite extroduce_Fin_ok1.
     apply index_in_extroduce_decode1 ; try assumption.
     apply gt_S_le.
     rewrite index_in_extroduce_decode1; assumption.
     
     rewrite extroduce_Fin_ok2, weakFin_ok.
     apply index_in_extroduce_decode2 ; try assumption.
     rewrite index_in_extroduce_decode2; assumption.
   Qed.
  
   Lemma decode_Fin_extroduce_Fin_neq (n: nat)(iex: Fin (S n))(i: Fin n): 
     decode_Fin iex <> decode_Fin (extroduce_Fin iex i).
   Proof.
     unfold extroduce_Fin, sumbool_rec, sumbool_rect.
     elim (le_lt_dec (decode_Fin iex) (decode_Fin i)) ; intros a h ; rewrite h in a.
     apply (le_Sn_n _ a).
     rewrite weakFin_ok in a.
     apply (lt_irrefl _ a).
   Defined.

   Lemma index_in_from_extroduce (n: nat)(iex: Fin (S n))(i: Fin n)
     (h: decode_Fin iex <> decode_Fin (extroduce_Fin iex i)) : index_in_extroduce _ _ h = i.
   Proof.
     revert h ; elim (le_lt_dec (decode_Fin iex) (decode_Fin i)) ; intros a.
     rewrite extroduce_Fin_ok1 ; try assumption.
     intros h.
     apply decode_Fin_unique, eq_add_S.
     apply index_in_extroduce_decode1.
     apply le_lt_n_Sm, a.
     
     rewrite extroduce_Fin_ok2 ; try assumption.
     intros h.
     apply decode_Fin_unique.
     rewrite index_in_extroduce_decode2.
     apply weakFin_ok.
     rewrite weakFin_ok.
     assumption.
   Qed.

   Lemma extroduce_interchange_aux (T : Set)(n : nat)(i : ilistn T (S n))
     (f f': Fin (S n))(a : decode_Fin f <> decode_Fin f')(a' : decode_Fin f' <> decode_Fin f):
       lgti (extroduce (extroduce (mkilist i) f)
          (rewriteFins (extroduce_lgti_S i f) (index_in_extroduce f f' a))) =
       lgti (extroduce (extroduce (mkilist i) f')
          (rewriteFins (extroduce_lgti_S i f') (index_in_extroduce f' f a'))).
   Proof.
     intros.
     evalLgtiExtro.
     reflexivity.
   Qed.

   Require Import Lia.
   Definition extroduce_interchange_statement_eq: Prop :=
     forall (T : Set)(n : nat)(i : ilistn T (S n))
       (f f': Fin (S n))(a : decode_Fin f <> decode_Fin f')(a' : decode_Fin f' <> decode_Fin f),
       ilist_rel (@eq T)
         (extroduce (extroduce (mkilist i) f)
           (rewriteFins (extroduce_lgti_S i f) (index_in_extroduce f f' a)))
         (extroduce (extroduce (mkilist i) f')
           (rewriteFins (extroduce_lgti_S i f') (index_in_extroduce f' f a'))).
 
   (*Check extroduce_interchange: extroduce_interchange_statement.*)
   Ltac excludeCase f fnew f' f'new a' := 
     let d := fresh in 
     let Hyp1 := fresh "Hyp" in 
     let Hyp2:= fresh "Hyp" in 
     apply False_rec; 
     elim (lt_eq_lt_dec (decode_Fin f') (decode_Fin f)) ; [intros [d|d]|intros d];
     [
     assert (Hyp1: decode_Fin f'new = decode_Fin f') 
     by (apply index_in_extroduce_decode2; exact d);
     assert (Hyp2: S (decode_Fin fnew) = decode_Fin f)
     by (apply index_in_extroduce_decode1; exact d);
     unfold fnew in *|-;
     unfold f'new in *|-;
     lia | 
     exact (a' d) |
     assert (Hyp1: decode_Fin fnew = decode_Fin f) 
     by (apply index_in_extroduce_decode2; exact d);
     assert (Hyp2: S (decode_Fin f'new) = decode_Fin f') 
     by (apply index_in_extroduce_decode1; exact d);
     unfold fnew in *|-;
     unfold f'new in *|-;
     lia
     ];
     fail.
     
   Ltac treatLeaf_eq f fnew f' f'new a' :=
     ((f_equal; treatFinPure) || excludeCase f fnew f' f'new a'); fail.
    
   Ltac treatAllCases_eq f fnew f' f'new a' :=
     match goal with
       | [ |- context [(fcti (extroduce _ ?Xf) ?Xf')]] => let c := fresh in 
       elim (le_lt_dec (decode_Fin Xf) (decode_Fin Xf')); 
       [ intro c; evalDecode_Fin_Ass c; rewrite extroduce_ok3' by (treatFin c); 
       treatAllCases_eq f fnew f' f'new a'
       | intro c; evalDecode_Fin_Ass c; rewrite extroduce_ok2' by (treatFin c); 
       treatAllCases_eq f fnew f' f'new a']; 
       fail
       | [ |- _ ] => treatLeaf_eq f fnew f' f'new a'
     end; 
     fail.

   Lemma extroduce_interchange_eq: extroduce_interchange_statement_eq.
   Proof.
     red.
     intros.
     set (f'new := index_in_extroduce f f' a).
     set (fnew := index_in_extroduce f' f a').
     set (l1 := extroduce (extroduce (mkilist i) f)
     (rewriteFins (extroduce_lgti_S i f) f'new)).
     set (l2 := extroduce (extroduce (mkilist i) f')
     (rewriteFins (extroduce_lgti_S i f') fnew)).
     apply (is_ilist_rel _ _ _ (extroduce_interchange_aux i f f' a a')) ; intro g.
     clear l1 l2.
     treatAllCases_eq f fnew f' f'new a'.
   Qed.

   (* It is quite obvious that the tactics are way too eager for the normalization of 
   decode_Fin expressions, and that they are also too cautious concerning the hypotheses 
   being in normal form. Most of the steps of the execution are completely unproductive. 
   Still, the question is if optimization is useful here. How could one know if lia takes 
   most of the time in the whole proof? Are there profiling tools for Coq? At least, 
   we can see better how much is really needed in order to program the proof. *) 

  Section left_right_sib_extro.
    
    Lemma left_right_sib_extroduce (T: Set)(l : ilist T)(i: Fin (lgti l)): 
      ilist_rel eq (iappend (left_sib l i) (right_sib l i)) (extroduce l i).
    Proof.
      assert (h : lgti (iappend (left_sib l i) (right_sib l i)) = lgti (extroduce l i)).
      rewrite iappend_lgti.
      apply eq_add_S.
      rewrite left_sib_right_sib_lgti.
      apply extroduce_lgti.
      apply (is_ilist_rel _ _ _ h).
      intros i'.
      elim (le_lt_dec (decode_Fin i) (decode_Fin (rewriteFins h i'))) ; intros a.
      rewrite extroduce_ok3' ; try assumption.
      rewrite <- (left_sib_lgti l i) in a.
      rewrite <- decode_Fin_match', (decode_Fin_match' i' (iappend_lgti (left_sib l i) (right_sib l i))) in a.
      rewrite (iappend_right _ _ _ a).
      simpl .
      f_equal.
      apply decode_Fin_unique.
      unfold rightFin.
      do 2 rewrite decode_code1_Id.
      rewrite le_plus_minus_r ; try assumption.
      do 2 rewrite <- decode_Fin_match'.
      simpl.
      rewrite <- decode_Fin_match'.
      reflexivity.
      
      rewrite extroduce_ok2'; try assumption.
      rewrite <- (left_sib_lgti l i), <- decode_Fin_match' in a.
      rewrite (iappend_left _ _ _ a).
      simpl fcti at 1.
      f_equal.
      apply decode_Fin_unique.
      do 2 rewrite decode_code1_Id.
      rewrite <- decode_Fin_match'.
      rewrite weakFin_ok.
      apply decode_Fin_match'.
    Qed.
    
    Lemma left_right_sib_extroduce_bis (T: Set)(l : ilist T)(i: Fin (lgti l)): 
      ilist2list (left_sib l i) ++ ilist2list (right_sib l i) = ilist2list (extroduce l i).
    Proof.
      rewrite <- append_iappend.
      destruct (left_right_sib_extroduce l i) as [H1 H2].
      unfold ilist2list.
      assert (H3 : makeListFin (lgti (extroduce l i)) = map (rewriteFins H1) 
      (makeListFin (lgti (iappend (left_sib l i) (right_sib l i))))).
      rewrite <- H1.
      apply sym_eq, map_id.
      rewrite H3.
      rewrite map_map.
      apply map_ext.
      assumption.
    Qed.
    
  End left_right_sib_extro.
