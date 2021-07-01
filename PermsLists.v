(** PermsLists.v Version 1.2.1 April 2016 *)
(** runs under V8.5pl1 *)

(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(** provides the definition of various relation of permutations 
    on lists and equivalence between them *)

Require Export Arith.
Require Import Utf8.
Require Import Setoid.
Require Import Morphisms.
Require Import List.
Require Import Basics.

Set Implicit Arguments.

Section Tools.

  Lemma length_nil (T: Set)(l: list T) : length l = 0 -> l = nil.
  Proof.
    destruct l as [|t l].
    reflexivity.
    intros h ; inversion h.
  Qed.

  Lemma nth_nil (T: Set)(d: T)(n: nat) : nth n nil d = d.
  Proof.
    destruct n ; reflexivity.
  Qed.
  
  Lemma length_skipn  (T: Set)(l: list T)(n: nat) : length (skipn n l) = length l - n.
  Proof.
    revert l ; induction n as [|n IH] ; intros l.
    apply minus_n_O.
    destruct l as [|t l].
    reflexivity.
    apply IH.
  Qed.

  Lemma firstn_ext(T: Set)(l: list T)(n: nat) : length l <= n -> firstn n l = l.
  Proof.
    revert l ; induction n as [|n IH] ; intros l h.
    simpl.
    apply le_n_0_eq, sym_eq in h.
    apply sym_eq, length_nil, h.
    destruct l as [|t l].
    reflexivity.
    simpl; f_equal ; apply IH.
    apply le_S_n, h.
  Qed.
  
  Lemma skipn_ext(T: Set)(l: list T)(n: nat) : length l <= n -> skipn n l = nil.
  Proof.
    revert l ; induction n as [|n IH] ; intros l h.
    simpl.
    apply le_n_0_eq, sym_eq in h.
    apply length_nil, h.
    destruct l as [|t l].
    reflexivity.
    apply IH.
    apply le_S_n, h.
  Qed.

(* alternative by R.M. without extra induction *)
  Lemma skipn_ext_ALT(T: Set)(l: list T)(n: nat) : length l <= n -> skipn n l = nil.
  Proof.
    intro h.
    apply firstn_ext in h.
    apply (app_inv_head (firstn n l)).
    rewrite firstn_skipn.
    symmetry.
    rewrite app_nil_r.
    assumption.
  Qed.
    
  Lemma firstn_app (T: Set)(l1 l2 : list T) : 
    firstn (length l1) (l1 ++ l2) = l1.
  Proof.
    induction l1 as [|t1 l1].
    reflexivity.
    simpl.
    f_equal ; assumption.
  Qed.
  
  Lemma skipn_app (T: Set)(l1 l2 : list T) : 
    skipn (length l1) (l1 ++ l2) = l2.
  Proof.
    induction l1 as [|t1 l1].
    reflexivity.
    assumption.
  Qed.

(* alternative by R.M. without extra induction, same idea as for skipn_ext_ALT *)
  Lemma skipn_app_ALT (T: Set)(l1 l2 : list T) : 
    skipn (length l1) (l1 ++ l2) = l2.
  Proof.
    apply (app_inv_head l1).
    rewrite <- (firstn_app l1 l2) at 1.
    apply firstn_skipn.
  Qed.
  
  Lemma skipn_app_cor (T: Set)(l1 l2 : list T)(n : nat) : n = length l1 ->  
    skipn n (l1 ++ l2) = l2.
  Proof.
    intros h.
    rewrite h.
    apply skipn_app.
  Qed.

  Lemma firstn_nth_skipn (T: Set)(d: T)(n: nat)(l: list T) : 
    n < length l -> l = firstn n l ++ nth n l d :: skipn (S n) l.
  Proof.
    revert l ; induction n as [|n IH] ; intros [|t l] h.
    inversion h.
    reflexivity.
    inversion h.
    simpl.
    f_equal.
    apply IH.
    apply lt_S_n, h.
  Qed.

(* another exercise by R.M. to use firstn_skipn - not so successful *)
  Lemma firstn_nth_skipn_ALT_aux (T: Set)(d: T)(n: nat)(l: list T) : 
    n < length l -> firstn (S n) l = firstn n l ++ nth n l d :: nil.
  Proof.
    revert l ; induction n as [|n IH] ; intros [|t l] h.
    inversion h.
    reflexivity.
    inversion h.
    simpl.
    f_equal.
    apply IH.
    apply lt_S_n, h.
  Qed.

Lemma firstn_nth_skipn_ALT (T: Set)(d: T)(n: nat)(l: list T) : 
    n < length l -> l = firstn n l ++ nth n l d :: skipn (S n) l.
  Proof.
    intro h.
    rewrite <- (firstn_skipn (S n)) at 1.
    rewrite (firstn_nth_skipn_ALT_aux d) by assumption.
    rewrite app_ass.
    f_equal.
  Qed.
    
End Tools. 

Section remel.
  Definition remel (T: Set)(n: nat)(l: list T) : list T := firstn n l ++ skipn (S n) l.

  Lemma remel_O_cons (T: Set)(t: T)(l: list T) : 
    remel 0 (t :: l) = l.
  Proof.
    reflexivity.
  Qed.
  
  Lemma length_remel (T: Set)(l: list T)(n: nat) : n < length l ->  
    S (length (remel n l)) = length l.
  Proof.
    intros h.
    unfold remel.
    rewrite app_length, firstn_length, length_skipn, Nat.min_l, <- plus_Sn_m.
    apply le_plus_minus_r, lt_le_S, h.
    apply lt_le_weak, h.
  Qed.
  
  Lemma remel_nil (T: Set)(n: nat) : remel n nil = @nil T.
  Proof.
    destruct n as [|n] ; reflexivity.
  Qed.
  
  Lemma remel_S_cons (T: Set)(t: T)(l: list T)(n: nat) : 
    remel (S n) (t::l) = t :: remel n l.
  Proof.
    reflexivity.
  Qed.
  
  Lemma remel_ext(T: Set)(l: list T)(n: nat) : length l <= n -> remel n l = l.
  Proof.
    intros h.
    unfold remel.
    rewrite firstn_ext, skipn_ext ; try assumption.
    apply app_nil_r.
    apply le_S, h.
  Qed.
  
  Lemma remel_app (T: Set)(t : T)(l1 l2 : list T) : 
    remel (length l1) (l1 ++ t :: l2) = l1 ++ l2.
  Proof.
    unfold remel.
    rewrite firstn_app.
    f_equal.
    rewrite (app_assoc l1 (t :: nil) l2 : l1 ++ t :: l2 = (l1 ++ (t :: nil)) ++ l2).
    apply skipn_app_cor.
    rewrite app_length.
    simpl.
    rewrite <- plus_n_Sm, <- plus_n_O.
    reflexivity.
  Qed.
  
  Lemma remel_nth1 (T: Set)(d: T)(n n': nat)(l: list T) : 
    n' < n -> nth n' (remel n l) d = nth n' l d.
  Proof.
    revert n n' ; induction l as [|t l IH] ; intros n n' H.
    rewrite remel_nil.
    reflexivity.
    destruct n as [|n].
    inversion H.
    rewrite remel_S_cons.
    destruct n' as [|n'].
    reflexivity.
    apply IH.
    apply lt_S_n, H.
  Qed.
  
  Lemma remel_nth2 (T: Set)(d: T)(n n': nat)(l: list T) : 
    n <= n' -> nth n' (remel n l) d = nth (S n') l d.
  Proof.
    revert n n' ; induction l as [|t l IH] ; intros n n' H.
    rewrite remel_nil, nth_nil, nth_nil.
    reflexivity.
    destruct n as [|n].
    rewrite remel_O_cons.
    reflexivity.
    destruct n' as [|n'].
    inversion H.
    rewrite remel_S_cons.
    apply IH.
    apply le_S_n, H.
  Qed.
  
  Section index_from_in_remel.

(* a motivating lemma by R.M. for index_in_remel - in fact, the latter is the constructive contents *)
    Lemma index_in_remel_prep (T: Set)(d: T)(n n' : nat)(l: list T)(h : n <> n') : exists n'',
      nth n' l d = nth n'' (remel n l) d.
    Proof.
      destruct n' as [|n'].
      exists 0.
      rewrite remel_nth1.
      reflexivity.
      elim (not_eq _ _ h) ; intros a.
      inversion a.
      assumption.
      elim (lt_eq_lt_dec n (S n')) ; try intros [a|a] ; try intros a ; try contradiction a.
      exists n'.
      apply sym_eq, remel_nth2.
      apply lt_n_Sm_le, a.
      exists (S n').
      apply sym_eq, remel_nth1 ; assumption.
    Qed. 

(* R.M.: notice that the lemma can be put much more uniformly: *)
    Lemma index_in_remel_prep_gen (n n' : nat)(h : n <> n') : exists n'',
      forall (T: Set)(d: T)(l: list T), nth n' l d = nth n'' (remel n l) d.
    Proof.
      destruct n' as [|n'].
      exists 0; intros.
      rewrite remel_nth1.
      reflexivity.
      elim (not_eq _ _ h) ; intros a.
      inversion a.
      assumption.
      elim (lt_eq_lt_dec n (S n')) ; try intros [a|a] ; try intros a ; try contradiction a.
      exists n'; intros.
      apply sym_eq, remel_nth2.
      apply lt_n_Sm_le, a.
      exists (S n'); intros.
      apply sym_eq, remel_nth1 ; assumption.
    Qed.

(* R.M.: the intention is that index_in_remel h is obtained as the index in remel n l
   that corresponds to the n'-th element of the original list l *)
    Definition index_in_remel (n n' : nat)(h : n <> n') : nat.
    Proof.
      destruct n' as [|n'].
      exact 0.
      elim (lt_eq_lt_dec n (S n')) ; try intros [a|a] ; try intros a ; try contradiction a.
      exact n'.
      exact (S n').
    Defined.
    
    Lemma index_in_remel_ok1 (n n' : nat)(h : n <> S n') : 
      n < S n' ->  index_in_remel h = n'.
    Proof.
      intros h1.
      simpl.
      unfold sumor_rec, sumor_rect.
      elim (lt_eq_lt_dec n (S n')) ; try intros [a|a] ; try intros a ; try contradiction a.
      reflexivity.
      apply False_rec, (lt_irrefl _ (lt_trans _ _ _ h1 a)).
    Qed.
    
    Lemma index_in_remel_ok2 (n n' : nat)(h : n <> n') : 
      n' < n ->  index_in_remel h = n'.
    Proof.
      intros h1.
      destruct n' as [|n'].
      reflexivity.
      simpl.
      unfold sumor_rec, sumor_rect.
      elim (lt_eq_lt_dec n (S n')) ; try intros [a|a] ; try intros a ; try contradiction a.
      apply False_rec, (lt_irrefl _ (lt_trans _ _ _ h1 a)).
      reflexivity.
    Qed.
    
    Lemma index_in_remel_ok3 (T: Set)(d: T)(n n' : nat)(l: list T)(h : n <> n') : 
      nth n' l d = nth (index_in_remel h) (remel n l) d.
    Proof.
      elim (not_eq _ _ h) ; intros a.
      destruct n' as [|n'].
      inversion a.
      rewrite index_in_remel_ok1 ; try assumption.
      apply sym_eq, remel_nth2.
      apply lt_n_Sm_le, a.

      rewrite index_in_remel_ok2 ; try assumption.
      apply sym_eq, remel_nth1 ; assumption.
    Qed. 
    
    Lemma index_in_remel_le (n n' : nat)(h: n <> n') : index_in_remel h <= n'.
    Proof.
      elim (not_eq _ _ h) ; intros a.
      destruct n' as [|n'].
      inversion a.
      rewrite index_in_remel_ok1 ; try assumption.
      apply le_n_Sn.
      rewrite index_in_remel_ok2 ; try assumption.
      apply le_refl.
    Qed.

(* same kind of motivation by R.M. for index_from_remel *)
    Lemma index_from_remel_prep (T: Set)(d: T)(n n' : nat)(l: list T): exists n'',
      nth n'' l d = nth n' (remel n l) d.
    Proof.
      elim (le_lt_dec n n') ; intros a.
      exists (S n').
      apply sym_eq, remel_nth2 ; assumption.
      exists n'.
      apply sym_eq, remel_nth1 ; assumption.
    Qed.

(* R.M.: notice that the lemma can again be put much more uniformly: *)
    Lemma index_from_remel_prep_gen (n n' : nat): exists n'', 
      forall(T: Set)(d: T)(l: list T), nth n'' l d = nth n' (remel n l) d.
    Proof.
      elim (le_lt_dec n n') ; intros a.
      exists (S n').
      intros; apply sym_eq, remel_nth2 ; assumption.
      exists n'.
      intros; apply sym_eq, remel_nth1 ; assumption.
    Qed.

(* R.M.: the intuition is that index_from_remel n n' is the index in the original list l
   of the n'-th element taken from remel n l *)
    Definition index_from_remel (n n' : nat) : nat.
    Proof.
      elim (le_lt_dec n n') ; intros a.
      exact (S n').
      exact n'.
    Defined.
    
    Lemma ifr_not_eq (n n': nat): index_from_remel n n' <> n.
    Proof.
      unfold index_from_remel, sumbool_rec, sumbool_rect.
      elim (le_lt_dec n n') ; intros a h ; rewrite <- h in a.
      apply (le_Sn_n _ a).
      apply (lt_irrefl _ a).
    Qed.
    
    Lemma index_from_remel_ok1 (n n' : nat) : n <= n' -> index_from_remel n n' = S n'.
    Proof.
      intros h.
      unfold index_from_remel, sumbool_rec, sumbool_rect.
      elim (le_lt_dec n n') ; intros a.
      reflexivity.
      apply False_rec, (lt_irrefl _ (le_lt_trans _ _ _ h a)).
    Qed.
    
    Lemma index_from_remel_ok2 (n n' : nat) : n' < n -> index_from_remel n n' = n'.
    Proof.
      intros h.
      unfold index_from_remel, sumbool_rec, sumbool_rect.
      elim (le_lt_dec n n') ; intros a.
      apply False_rec, (lt_irrefl _ (le_lt_trans _ _ _ a h)).
      reflexivity.
    Qed.
    
    Lemma index_from_remel_ok3 (T: Set)(d: T)(n n' : nat)(l: list T): 
      nth (index_from_remel n n') l d = nth n' (remel n l) d.
    Proof.
      elim (le_lt_dec n n') ; intros a.
      rewrite index_from_remel_ok1 ; try assumption.
      apply sym_eq, remel_nth2 ; assumption.
      rewrite index_from_remel_ok2 ; try assumption.
      apply sym_eq, remel_nth1 ; assumption.
    Qed. 
    
    Lemma index_from_remel_le (n n' : nat): n' <= index_from_remel n n'.
    Proof.
      elim (le_lt_dec n n') ; intros a.
      rewrite index_from_remel_ok1 ; try assumption.
      apply le_n_Sn.
      rewrite index_from_remel_ok2 ; try assumption.
      apply le_refl.
    Qed.
    
    Lemma index_from_remel_le2 (n n' : nat): index_from_remel n n' <= S n'.
    Proof.
      elim (le_lt_dec n n') ; intros a.
      rewrite index_from_remel_ok1 ; try assumption.
      apply le_refl.
      rewrite index_from_remel_ok2 ; try assumption.
      apply le_n_Sn.
    Qed.
    
    Lemma index_in_from_remel (n n' : nat)(h: n <> index_from_remel n n') : 
      index_in_remel h = n'.
    Proof.
      revert h ; elim (le_lt_dec n n') ; intros a.
      rewrite index_from_remel_ok1 ; try assumption.
      intros h.
      apply index_in_remel_ok1, le_lt_n_Sm, a.
      
      rewrite index_from_remel_ok2 ; try assumption.
      intros h.
      apply index_in_remel_ok2, a.
    Qed.
    
    Lemma index_from_in_remel (n n' : nat)(h: n <> n') : 
      index_from_remel n (index_in_remel h) = n'.
    Proof.
      elim (not_eq _ _ h) ; intros a.
      destruct n' as [|n'].
      inversion a.
      rewrite index_in_remel_ok1, index_from_remel_ok1 ; try assumption.
      reflexivity.
      apply lt_n_Sm_le, a.
      
      rewrite index_in_remel_ok2, index_from_remel_ok2 ; try assumption.
      reflexivity.
    Qed.
    
    Lemma iir_length_remel (T: Set)(n n': nat)(h : n <> n')(l: list T) : 
      n' < length l -> index_in_remel h < length (remel n l).
    Proof.
      intros h1.
      elim (not_eq _ _ h) ; intros a.
      apply lt_S_n.
      destruct n' as [|n'].
      inversion a.
      rewrite length_remel, index_in_remel_ok1 ; try assumption.
      apply (lt_trans _ _ _ a h1).
      
      elim (le_lt_dec (length l) n) ; intros b.
      rewrite remel_ext ; try assumption.
      apply (le_lt_trans _ _ _ (index_in_remel_le h) h1).
      apply lt_S_n.
      rewrite length_remel, index_in_remel_ok2 ; try assumption.
      apply lt_le_S in a.
      apply (le_lt_trans _ _ _ a b).
    Qed.
    
    Lemma index_in_remel_proof_irrel (n n': nat) (a a' : n <> n') : 
      index_in_remel a = index_in_remel a'.
    Proof.
      elim (not_eq _ _ a) ; intros b.
      destruct n' as [|n'].
      inversion b.
      rewrite index_in_remel_ok1, index_in_remel_ok1 ; try assumption.
      reflexivity.
      rewrite index_in_remel_ok2, index_in_remel_ok2 ; try assumption.
      reflexivity.
    Qed.

  End index_from_in_remel.
  
  Lemma remel_interchange_aux1  (T: Set)(n n': nat)(h : n < S n')(l: list T) : 
    remel n' (remel n l) = remel n (remel (S n') l).
  Proof.
    revert n n' h ; induction l as [|t l IH] ; intros n n' h.
    repeat rewrite remel_nil.
    reflexivity.
    destruct n as [|n].
    rewrite remel_O_cons, remel_S_cons, remel_O_cons.
    reflexivity.
    destruct n' as [|n'].
    apply lt_S_n in h ; inversion h.
    repeat rewrite remel_S_cons.
    f_equal.
    apply IH.
    apply lt_S_n, h.
  Qed.

  Lemma remel_interchange_aux1_elemwise_aux  (n n' n'': nat)(h : n < S n') :
    index_from_remel n (index_from_remel n' n'') = index_from_remel (S n') (index_from_remel n n'').
  Proof.
    elim (le_lt_dec n' n'') ; intros a.
    assert (b := le_trans _ _ _ (lt_n_Sm_le _ _ h) a).
    repeat  rewrite index_from_remel_ok1 ; try assumption.
    reflexivity.
    apply le_n_S, a.
    apply (le_trans _ _ _ b (le_n_Sn n'')).
    rewrite (index_from_remel_ok2 a), (@index_from_remel_ok2 (S n') _).
    reflexivity.
    elim (le_lt_dec n n'') ; intros b.
    rewrite (index_from_remel_ok1 b).
    apply lt_n_S, a.
    rewrite (index_from_remel_ok2 b).
    apply (lt_trans _ _ _ b h).
  Qed.

  Lemma remel_interchange_aux1_elemwise  (T: Set)(n n' n'': nat)(h : n < S n')(l: list T)(d: T) : 
    nth n'' (remel n' (remel n l)) d = nth n'' (remel n (remel (S n') l)) d.
  Proof.
    do 4 rewrite <- index_from_remel_ok3.
    rewrite remel_interchange_aux1_elemwise_aux.
    reflexivity.
    assumption.
  Qed.
    

(* R.M.: element-wise, it would be as follows:
  Lemma remel_interchange_aux1_elemwise_aux  (n n' n'': nat)(h : n < S n') :
    index_from_remel n (index_from_remel n' n'') = index_from_remel (S n') (index_from_remel n n'').
  Proof.

How? Like in Ilist.v?

  Lemma remel_interchange_aux1_elemwise  (T: Set)(n n' n'': nat)(h : n < S n')(l: list T)(d: T) : 
    nth n'' (remel n' (remel n l)) d = nth n'' (remel n (remel (S n') l)) d.
  Proof.
    do 4 rewrite <- index_from_remel_ok3.
    rewrite remel_interchange_aux1_elemwise_aux.
    reflexivity.
    assumption.
  Qed.

Extra problem: element-wise equality does not imply equality if T is degenerate (has only one element)

At least, the above lemma is a consequence of remel_interchange_aux1: *)

  Fixpoint ntrue (n: nat) : list bool := 
    match n with | 0 => nil | S n' => true :: ntrue n' end.
  
  Lemma ntruelength (n: nat): length(ntrue n) = n.
  Proof.
    induction n.
    reflexivity.
    simpl.
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma ntruentheq (n: nat): nth n (ntrue n) false = false.
  Proof.
    apply nth_overflow.
    rewrite ntruelength.
    auto.
  Qed.

  Lemma ntruenthlt (n m: nat): m < n -> nth m (ntrue n) false = true.
  Proof.
    intro H.
    revert m H; induction n; intros.
    inversion H.
    destruct m.
    reflexivity.
    simpl.
    apply IHn.
    apply lt_S_n.
    assumption.
  Qed.

  Lemma from_all_lists_to_indices (m n: nat): 
    (forall (d: bool)(l: list bool), nth m l d = nth n l d) -> m = n.
  Proof.
    intro H.
    destruct (lt_eq_lt_dec m n) as [[h1|h2] | h3].
    assert (Hyp := H false (ntrue n)).
    clear H.
    rewrite ntruentheq in Hyp.
    rewrite (ntruenthlt h1) in Hyp.
    inversion Hyp.
    assumption.
    assert (Hyp := H false (ntrue m)).
    clear H.
    rewrite ntruentheq in Hyp.
    rewrite (ntruenthlt h3) in Hyp.
    inversion Hyp.
  Qed.

  Lemma remel_interchange_aux1_elemwise_aux_ALT  (n n' n'': nat)(h : n < S n') :
    index_from_remel n (index_from_remel n' n'') = 
    index_from_remel (S n') (index_from_remel n n'').
  Proof.
    apply from_all_lists_to_indices.
    intros.
    do 4 rewrite index_from_remel_ok3.
    rewrite remel_interchange_aux1.
    reflexivity.
    assumption.
  Qed.

(* end of detour by R.M. *)
    
  Lemma remel_interchange_aux2  (T: Set)(n n': nat)(h : n' < S n)(l: list T) : 
    remel n' (remel (S n) l) = remel n (remel n' l).
  Proof.
    apply sym_eq, remel_interchange_aux1, h.
  Qed.
  
  Lemma remel_interchange (T: Set)(n n': nat)(h : n <> n')(l: list T) : 
    remel (index_in_remel h) (remel n l)  = 
    remel (index_in_remel (not_eq_sym h)) (remel n' l).
  Proof.
    elim (not_eq _ _ h) ; intros a.
    destruct n' as [|n'].
    inversion a.
    rewrite (index_in_remel_ok1 h), (index_in_remel_ok2 (not_eq_sym h)); try assumption.
    apply remel_interchange_aux1 ; assumption.
    destruct n as [|n].
    inversion a.
    rewrite (index_in_remel_ok2 h), (index_in_remel_ok1 (not_eq_sym h)); try assumption.
    apply remel_interchange_aux2; assumption.
  Qed.

(* R.M.: again see what this means element-wise: *)
  Lemma remel_interchange_elemwise_aux (n n' n'': nat)(h : n <> n') : 
    index_from_remel n (index_from_remel (index_in_remel h) n'') =
    index_from_remel n' (index_from_remel (index_in_remel (not_eq_sym h)) n'').
  Proof.
    apply from_all_lists_to_indices.
    intros.
    do 4 rewrite index_from_remel_ok3.
    rewrite remel_interchange.
    reflexivity.
  Qed.

(* an alternative proof analogous to that of remel_interchange *)
Lemma remel_interchange_elemwise_aux_ALT (n n' n'': nat)(h : n <> n') : 
    index_from_remel n (index_from_remel (index_in_remel h) n'') =
    index_from_remel n' (index_from_remel (index_in_remel (not_eq_sym h)) n'').
  Proof.
    elim (not_eq _ _ h) ; intros a.
    destruct n' as [|n'].
    inversion a.
    rewrite (index_in_remel_ok1 h), (index_in_remel_ok2 (not_eq_sym h)); try assumption.
    apply remel_interchange_aux1_elemwise_aux; assumption.
    destruct n as [|n].
    inversion a.
    rewrite (index_in_remel_ok2 h), (index_in_remel_ok1 (not_eq_sym h)); try assumption.
    rewrite <- remel_interchange_aux1_elemwise_aux.
    reflexivity.
    assumption.
  Qed.
(* end of detour by R.M. *)

End remel.

Section Permutations_definitions.
  (* Contejean's definition *)
  Inductive permut (A B : Set) (R : A -> B -> Prop) : (list A -> list B -> Prop) :=
    | Pnil : permut R nil nil
    | Pcons : forall a b l l1 l2, R a b -> permut R l (l1 ++ l2) ->
                     permut R (a :: l) (l1 ++ b :: l2).

  (* Definition corresponding to IlistPerm3 *)                     
  Inductive permut1 (T: Set) (R : relation T) : (list T -> list T -> Prop) :=
    | P1nil : permut1 R nil nil
    | P1cons : forall n1 n2 t l1 l2, n1 < length l1 -> n2 < length l2 -> 
        R (nth n1 l1 t) (nth n2 l2 t) -> 
        permut1 R (remel n1 l1) (remel n2 l2) -> 
        permut1 R l1 l2.
    
  Lemma permut1_length (T: Set)(R: relation T)(l1 l2 : list T) : 
    permut1 R l1 l2 -> length l1 = length l2.
  Proof.
    intro H ; induction H as [|n1 n2 t l1 l2 H1 H2 H3 H4 IH].
    reflexivity.
    rewrite <- (length_remel l1 H1), <- (length_remel l2 H2), IH.
    reflexivity.
  Qed.
  
  Lemma permut1_refl (T: Set)(R: relation T)(Rrefl: Reflexive R)(l : list T) : 
    permut1 R l l.
  Proof.
    induction l as [|t l IH].
    apply P1nil.
    apply (@P1cons _ _ 0 0 t) ; try apply lt_0_Sn.
    reflexivity.
    assumption.
  Qed. 
  
  Lemma permut1_sym (T: Set)(R: relation T)(Rsym: Symmetric R)(l1 l2 : list T) : 
    permut1 R l1 l2 -> permut1 R l2 l1.
  Proof.
    intros H.
    induction H as [| n1 n2 t l1 l2 H1 H2 H3 H4 IH].
    apply P1nil.
    apply (P1cons t _ _ H2 H1).
    symmetry ; assumption.
    apply IH.
  Qed.
  
  (* Definition corresponding to IlistPerm4 *)                     
  Inductive permut2 (T: Set) (R : relation T) : (list T -> list T -> Prop) :=
    | P2intro : forall l1 l2, length l1 = length l2 -> (forall n1 t, 
        n1 < length l1 -> exists n2,
        R (nth n1 l1 t) (nth n2 l2 t) /\ permut2 R (remel n1 l1) (remel n2 l2)) -> 
        permut2 R l1 l2.
(* R.M.: exists n2 now under the condition n1 < length l1 *)

  Lemma permut2_nil (T: Set)(R: relation T): permut2 R nil nil.
  Proof.
    apply P2intro.
    reflexivity.
    intros n t H.
    inversion H.
  Qed.
  
  Lemma permut2_length (T: Set)(R: relation T)(l1 l2 : list T): 
    permut2 R l1 l2 -> length l1 = length l2.
  Proof.
    intros h.
    inversion_clear h as [l1' l2' H1 _].
    assumption.
  Qed.

(* R.M.: this implies the following "hygienic property" 
   (extracted from proof of permut2_trans): *)
  Lemma permut2_wellformed (T: Set)(R: relation T)(l1 l2: list T)(n1 n2: nat): 
        length l1 = length l2 ->  
        n1 < length l1 -> 
        permut2 R (remel n1 l1) (remel n2 l2) -> 
        n2 < length l2.
  Proof.
    intros H1 H2 H3.
    elim (le_lt_dec (length l2) n2) ; intros a.
    assert (H4 := eq_S _ _ (permut2_length H3)).
    rewrite (remel_ext l2 a), length_remel, H1 in H4 ; try assumption.
    contradict H4.
    apply n_Sn.
    assumption.
  Qed.
    
  Lemma permut2_ind_better: forall (T : Set)(RelT : relation T)(P: list T -> list T -> Prop),
    (forall l1 l2 : list T, length l1 = length l2 -> 
    (forall n1 t, n1 < length l1 -> exists n2,
    RelT (nth n1 l1 t) (nth n2 l2 t) /\ permut2 RelT (remel n1 l1) (remel n2 l2) /\
    P (remel n1 l1) (remel n2 l2)) -> P l1 l2) ->
    (forall l l0 : list T, permut2 RelT l l0 -> P l l0).
  Proof.
    fix Hr 7.
    intros T RelT P H1 _ _ [l1 l2 H2 H3].
    apply H1 ; try assumption.
    intros n1 t H.
    destruct (H3 n1 t H) as [n2 H4].
    exists n2 ; destruct H4 as [H5 H6].
    split ; try split; try assumption.
    apply (Hr _ RelT) ; assumption.
  Qed.
  
(* not necessary: *)
  Lemma permut2_cons_FYI (T: Set)(R: relation T)(Rrefl: Reflexive R)(t : T) (l1 l2 : list T): 
    permut2 R l1 l2 -> permut2 R (t::l1) (t::l2).
  Proof.
    intros h.
    assert (h1 := h).
    induction h as [l1 l2 H1 H2] using permut2_ind_better.
    apply P2intro.
    simpl ; f_equal ; assumption.
    intros [|n1] d HL.
    exists 0.
    split.
    reflexivity.
    do 2 rewrite remel_O_cons.
    assumption.
    simpl in HL.
    apply lt_S_n in HL.
    destruct (H2 n1 d HL) as [n2 H] ; clear H2.
    exists (S n2).
    destruct H as [H3 [H4 H5]].
    split.
    assumption.
    do 2 rewrite remel_S_cons.
    apply H5, H4.
  Qed.
  
(* the proof without the equivalence between all the notions *)
  Lemma permut2_refl_ALT (T: Set)(R: relation T)(Rrefl: Reflexive R)(l : list T) : 
    permut2 R l l.
  Proof.
    induction l as [|t l IH].
    apply permut2_nil.
    apply permut2_cons_FYI ; assumption.
  Qed. 
  
  Lemma permut2_trans (T: Set)(R: relation T)(Rtrans: Transitive R)(l1 l2 l3: list T) : 
    permut2 R l1 l2 -> permut2 R l2 l3 -> permut2 R l1 l3.
  Proof.
    intros H1 H3.
    revert l1 H1; induction H3 as [l2 l3 H3 H4] using permut2_ind_better ; intros l1 H1.
    induction H1 as [l1 l2 H1 H2] using permut2_ind_better.
    apply P2intro.
    transitivity (length l2) ; assumption.
    intros n1 t HL.
    destruct (H2 n1 t HL) as [n2 H5].
    destruct H5 as [H7 [H8 H9]]. 
    assert (HL' := permut2_wellformed l1 l2 n2 H1 HL H8).
    destruct (H4 n2 t HL') as [n3 H6].
    exists n3.
    destruct H6 as [H10 [H11 H12]].
    split.
    transitivity (nth n2 l2 t) ; assumption.
    apply H12.
    assumption.
  Qed.

End Permutations_definitions.

Section Proofs_of_equivalence.

  Lemma permut_permut1 (T: Set)(R: relation T)(l1 l2 : list T) : 
    permut R l1 l2 -> permut1 R l1 l2.
  Proof.
    intros H ; induction H as [|a b l l1 l2 H1 H2 IH].
    apply P1nil.
    apply (@P1cons _ _ 0 (length l1) a) ; try apply lt_O_Sn.
    rewrite app_length.
    rewrite <- (plus_0_r (length l1)) at 1.
    apply plus_lt_compat_l, lt_O_Sn.
    rewrite app_nth2, minus_diag ; try apply le_refl.
    assumption.
    rewrite remel_app, remel_O_cons.
    exact IH.
  Qed.

(* not necessary since it follows from the lemmas immediately before and after it *)
  Lemma permut2_permut1_ALT (T: Set)(R: relation T)(l1 l2 : list T) : 
    permut2 R l1 l2 -> permut1 R l1 l2.
  Proof.
    intros H ; induction H as [l1 l2 H1 IH] using permut2_ind_better.
    destruct l1 as [|t1 l1] ; destruct l2 as [|t2 l2].
    apply P1nil.
    inversion H1.
    inversion H1.
    destruct (IH 0 t1 (lt_O_Sn _ : 0 < length (t1 :: l1))) as [n2 H].
    destruct H as [H2 [H3 H4]] ; clear IH.
    apply (@P1cons _ _ 0 n2 t1) ; try assumption.
    apply lt_O_Sn.
    apply (permut2_wellformed _ _ n2 H1 (lt_O_Sn _ : 0 < length (t1 :: l1)) H3).
  Qed.

  Lemma permut2_permut (T: Set)(R: relation T)(l1 l2 : list T) : 
    permut2 R l1 l2 -> permut R l1 l2.
  Proof.
    intros H ; induction H as [l1 l2 H1 IH] using permut2_ind_better.
    destruct l1 as [|t1 l1] ; destruct l2 as [|t2 l2].
    apply Pnil.
    inversion H1.
    inversion H1.
    destruct (IH 0 t1 (lt_O_Sn _ : 0 < length (t1 :: l1))) as [n2 H]; clear IH.
    destruct H as [H2 [H3 H4]].
    assert (a: n2 < length (t2 :: l2)).
    apply (permut2_wellformed _ _ n2 H1 (lt_O_Sn _ : 0 < length (t1 :: l1)) H3).
    rewrite (firstn_nth_skipn t1 (t2 :: l2) a).
    apply Pcons ; assumption.
  Qed.

  Lemma permut1_exists_rec (T: Set)(R: relation T)(l1 l2 : list T) : 
    permut1 R l1 l2 -> forall n1 d, n1 < length l1 -> exists n2,
    R (nth n1 l1 d) (nth n2 l2 d) /\ permut1 R (remel n1 l1) (remel n2 l2).
  Proof.
    intros H ; induction H as [|n1 n2 t l1 l2 H1 H2 H3 H4 IH].
    (* empty list *)
    intros n1 d HL.
    inversion HL.
    
    (* non empty list *)
    intros n1' d HL.
    rewrite (nth_indep _ t d H1), (nth_indep _ t d H2) in H3.
    elim (eq_nat_dec n1 n1') ; intros a.
    (* n1 = n1'*)
    rewrite <- a ; clear a ; exists n2 ; split ; assumption.
    
    (* n1 <> n1'*)
    destruct (IH (index_in_remel a) d (iir_length_remel a _ HL)) as [n2'IH H5]; clear IH.
    exists (index_from_remel n2 n2'IH).
    destruct H5 as [H6 H7].
    split.
    rewrite <- index_in_remel_ok3, <- index_from_remel_ok3 in H6.
    assumption.
     
    apply (P1cons d _ _ (iir_length_remel (not_eq_sym a) _ H1)
                        (iir_length_remel (ifr_not_eq _) _ H2)).
    do 2 rewrite <- index_in_remel_ok3.
    assumption.
    rewrite (remel_interchange _ l1), (remel_interchange _ l2).
    
    rewrite (index_in_remel_proof_irrel _ a), (index_in_from_remel _ (not_eq_sym _)).
    assumption.
  Qed.
  
  Lemma permut1_permut2 (T: Set)(R: relation T)(l1 l2 : list T) : 
    permut1 R l1 l2 -> permut2 R l1 l2.
  Proof.
    remember (length l1) as n.
    revert l1 l2 Heqn ; induction n as [|n IH] ; intros l1 l2 Heqn H.
    rewrite (length_nil _ (sym_eq Heqn)), 
    (length_nil _ (sym_eq (trans_eq Heqn (permut1_length H)))).
    apply permut2_nil.
    assert (H1 := permut1_exists_rec H).
    apply P2intro.
    apply (permut1_length H).
    intros n1 t HL.
    destruct (H1 n1 t HL) as [n2 H2]; clear H1.
    exists n2.
    destruct H2 as [H4 H5].
    split.
    assumption.
    apply IH ; try assumption.
    apply eq_add_S.
    rewrite length_remel ; assumption.
  Qed.
  
End Proofs_of_equivalence.

Section Equivalence_relations.

  Lemma permut1_trans (T: Set)(R: relation T)(Rtrans: Transitive R): Transitive (permut1 R).
  Proof.
    intros l1 l2 l3 H1 H2.
    apply permut1_permut2 in H1 ; apply permut1_permut2 in H2.
    apply permut_permut1, permut2_permut.
    apply (permut2_trans _ H1 H2).
  Qed.

  Lemma permut2_sym (T: Set)(R: relation T)(Rsym: Symmetric R): Symmetric (permut2 R).
  Proof.
    intros l1 l2 H1.
    apply permut2_permut, permut_permut1 in H1.
    apply permut1_permut2.
    apply (permut1_sym _ H1).
  Qed.

(* R.M.: now trivial *)
  Lemma permut2_refl (T: Set)(R: relation T)(Rrefl: Reflexive R): Reflexive (permut2 R).
  Proof.
    intros l1.
    apply permut1_permut2.
    apply permut1_refl.
    assumption.
  Qed.
  
  Add Parametric Relation (T: Set)(R: relation T)(EqT: Equivalence R): (list T)(permut1 R) 
    reflexivity proved by (permut1_refl _)
    symmetry proved by (permut1_sym _)
    transitivity proved by (permut1_trans _)
  as permut1Rel.

  Add Parametric Relation (T: Set)(R: relation T)(EqT: Equivalence R): (list T)(permut2 R) 
    reflexivity proved by (permut2_refl _)
    symmetry proved by (permut2_sym _)
    transitivity proved by (permut2_trans _)
  as permut2Rel.

(* R.M.: also interesting: *)
  Lemma permut2_cons (T: Set)(R: relation T)(Rrefl: Reflexive R)(t : T)(l1 l2 : list T): 
    permut2 R l1 l2 -> permut2 R (t::l1) (t::l2).
  Proof.
    intro H.
    apply permut2_permut in H.
    apply permut1_permut2, permut_permut1.
    change (t::l2) with (nil ++ t::l2). 
    apply Pcons.
    reflexivity.
    assumption.
  Qed.    

End Equivalence_relations.

