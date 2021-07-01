(** Introduce.v Version 1.2 February 2011 *)
(** runs under V8.4beta, tested with version 8.5pl1 *)

(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(** provides the definition of introduce and all associated tools 
    and lemmas  -- just to compare with extroduce *)

Require Import Arith.
Require Import Utf8.
Require Import Setoid.
Require Import Fin.
Require Import Ilist.
Require Import Tools.
Require Import Extroduce.

Set Implicit Arguments.

(* introduces element t at place f in i *)
Definition introduce: forall (T: Set)(t: T)(i: ilist T)(f: Fin (S (lgti i))), ilist T.
Proof.
  intros T t [n i] f.
  simpl in f.
  apply (mkilist (n:=S n)).
  intro f'.
  elim (lt_eq_lt_dec  (decode_Fin f') (decode_Fin f)) ; intros a.
  destruct a as [a|a].
  exact (i (code_Fin1 (lt_le_trans _ _ _ a (lt_n_Sm_le _ _ (decode_Fin_inf_n f))))).
  exact t.
  exact (i (get_cons f' (lt_n_m_0 a))).
Defined.

Lemma introduce_lgti : forall (T: Set)(i: ilist T)(f: Fin (S (lgti i)))(t:T), 
  lgti (introduce t i f) = S (lgti i).
Proof.
  intros T [n i] f t.
  reflexivity.
Defined.

Lemma introduce_ok1': forall (T: Set)(i: ilist T)(f: Fin (S (lgti i)))(t:T)
  (f': Fin (lgti (introduce t i f))), 
  decode_Fin f = decode_Fin f' -> fcti (introduce t i f) f' = t.
Proof.
  intros T [n i] f t f' h.
  simpl in *|-*.
  elim (lt_eq_lt_dec (decode_Fin f') (decode_Fin f)) ; intros a; try destruct a as [a|a]; 
  unfold sumor_rec,  sumor_rect;
  try (apply False_rec ; rewrite h in a ; apply (lt_irrefl _ a)).
  reflexivity.
Qed.

Lemma introduce_ok2': forall (T: Set)(i: ilist T)(f: Fin (S (lgti i)))(t:T)
  (f': Fin (lgti (introduce t i f)))(h: decode_Fin f' < decode_Fin f),    
  fcti (introduce t i f) f' = 
  fcti i (code_Fin1 (lt_le_trans _ _ _ h (lt_n_Sm_le _ _ (decode_Fin_inf_n f)))).
Proof.
  intros T [n i] f t f' h.
  simpl in *|-*.
  unfold sumor_rec, sumor_rect.
  elim (lt_eq_lt_dec (decode_Fin f') (decode_Fin f)) ; [intros [a|a]|intros a].
  f_equal.
  destruct n as [|n].
  revert h a ; rewrite (Fin_first_1 f'), (Fin_first_1 f) ; simpl ; intros h a.
  inversion h.
  apply code_Fin1_proofirr.
  apply False_rec, (lt_irrefl (decode_Fin f)).
  rewrite <- a at 1.
  assumption.
  apply False_rec, (lt_irrefl (decode_Fin f) (lt_trans _ _ _ a h)).
Qed.

Lemma inf_rewriteFins (n m r: nat)(i: Fin n)(h: n = m) : 
  r < decode_Fin i -> r < decode_Fin (rewriteFins h i).
Proof.
  intros h1.
  rewrite <- decode_Fin_match'.
  assumption.
Qed.
 
Lemma introduce_ok3': forall (T: Set)(i: ilist T)(f: Fin (S (lgti i)))(t:T)
  (f': Fin (lgti (introduce t i f)))(h: decode_Fin f < decode_Fin f'),   
  fcti (introduce t i f) f' = fcti i (get_cons (rewriteFins (introduce_lgti _ _ _) f') 
  (inf_rewriteFins f' (introduce_lgti _ _ _) (lt_n_m_0 h))).
Proof.
  intros T [n i] f t f' h.
  simpl in *|-*.
  unfold sumor_rec, sumor_rect.
  elim (lt_eq_lt_dec (decode_Fin f') (decode_Fin f)) ; [intros a|intros a] ;
  [apply False_rec, (lt_irrefl (decode_Fin f)); destruct a as [a|a] | f_equal].
  apply (lt_trans _ _ _ h a).
  rewrite <- a at 2.
  assumption.
  apply get_cons_proofirr.
Qed.

Lemma introduce_extroduce_id: forall (T: Set) (RelT : relation T) (EqT: Equivalence RelT)
  (i: ilist T) (f: Fin (lgti i)), ilist_rel RelT i (introduce (fcti i f) (extroduce i f) 
  (rewriteFins (extroduce_lgti i f) f)).
Proof.
  intros T RelT EqT i f.
  assert (h: lgti i = lgti (introduce (fcti i f) (extroduce i f)
    (rewriteFins (extroduce_lgti i f) f))).
  rewrite introduce_lgti.
  apply extroduce_lgti.
  apply (is_ilist_rel _ _ _ h).
  intro f'.
  destruct i as [n i].
  simpl in f, f'.
  fold (mkilist i) in *|-*.
  change (fcti (mkilist i)) with i in *|-*.
  
  elim (lt_eq_lt_dec (decode_Fin (rewriteFins h f')) 
    (decode_Fin (rewriteFins (extroduce_lgti (mkilist i) f) f)));
  try intros [b|b]; try intro b.
  rewrite (introduce_ok2' _ _ _ _ b ).
  rewrite extroduce_ok2'.
  apply (fRel EqT).
  treatFinPure.
  rewrite decode_code1_Id.
  rewrite <- (decode_Fin_match' _ (extroduce_lgti (mkilist i) f)) in b.
  assumption.
  
  rewrite introduce_ok1'.
  apply (fRel EqT), decode_Fin_unique.
  do 2 rewrite <- decode_Fin_match' in b.
  assumption.
  symmetry ; assumption.
  
  rewrite (introduce_ok3' _ _ _ _ b ).
  rewrite extroduce_ok3'.
  apply (fRel EqT).
  treatFinPure.
  apply le_S_n.
  rewrite <- decode_Fin_get_cons, <- decode_Fin_match'.
  rewrite <- (decode_Fin_match' _ (extroduce_lgti (mkilist i) f)) in b.
  apply gt_le_S, b.
Qed.

Lemma extroduce_introduce_id (T: Set) (RelT : relation T) (EqT: Equivalence RelT)
  (i: ilist T) (f: Fin (S (lgti i)))(t: T) : ilist_rel RelT i (extroduce (introduce t i f) 
  (rewriteFins (sym_eq (introduce_lgti i f t)) f)).
Proof.
  assert (h : lgti i = lgti (extroduce (introduce t i f)
     (rewriteFins (Logic.eq_sym (introduce_lgti i f t)) f))).
  apply eq_add_S.
  rewrite <- extroduce_lgti, introduce_lgti.
  reflexivity.
  apply (is_ilist_rel _ _ _ h).
  intros f'.
  elim (le_lt_dec (decode_Fin f) (decode_Fin f')) ; intros a.
  rewrite extroduce_ok3'.
  assert (h' : decode_Fin f < decode_Fin (rewriteFins (Logic.eq_sym
    (extroduce_lgti (introduce t i f) 
    (rewriteFins (Logic.eq_sym (introduce_lgti i f t)) f))) (succ (rewriteFins h f')))).
  rewrite <- decode_Fin_match'.
  simpl.
  rewrite <- decode_Fin_match'.
  apply le_lt_n_Sm, a.
  rewrite (introduce_ok3' _ _ _ _ h').
  apply (fRel EqT).
  treatFinPure.
  do 2 rewrite <- decode_Fin_match'.
  assumption.

  rewrite extroduce_ok2'.
  assert (h' : decode_Fin  (rewriteFins (Logic.eq_sym (extroduce_lgti (introduce t i f)
    (rewriteFins (Logic.eq_sym (introduce_lgti i f t)) f))) (weakFin (rewriteFins h f'))) 
    < decode_Fin f).
  rewrite <- decode_Fin_match', weakFin_ok, <- decode_Fin_match'.
  assumption.
  rewrite (introduce_ok2' _ _ _ _ h').
  apply (fRel EqT).
  treatFinPure.
  do 2 rewrite <- decode_Fin_match'.
  assumption.
Qed.
















