(** Fin.v Version 1.1.1 April 2016 *)
(** runs under V8.5pl1 *)

(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(**  provides a definition and various properties and lemmas 
     about the type Fin, among which, the injectivity of Fin *)

Require Export Arith.
Require Import Utf8.
Require Import Setoid.
Require Import List.
Require Import Morphisms.
Require Import Tools.

Set Implicit Arguments.

(* The idea here is to reuse the definition of Fin given by McBride & McKinna
   to represent sets of n elements *)

Section Fin_def_tools. 

(* According to McBride & McKinna, "The view from the left" *)
  Inductive Fin: nat -> Set :=
     first k : Fin (S k)
   | succ k: Fin k -> Fin (S k).
 
  (* The first thing we want to show is n = m <-> Fin n = Fin m. *)
  (* The following lemma shows the implication from left to rifht *)
  Definition Fin_n_m: forall n m: nat, n = m -> Fin n = Fin m.
  Proof.
    intros n m H.
    rewrite H.
    reflexivity.
  Defined.
(*
  Definition transformFin (n1 n2:nat)(h:n1=n2)(x:Fin n1): Fin n2 :=
    match h in (_=n) return Fin n with refl_equal => x end. 

  Definition transformFin2 (n1 n2:nat)(h:Fin n1=Fin n2)(x:Fin n1): Fin n2 :=
    match h in (_=f) return f with refl_equal => x end. 
    
  Lemma transformFin_refl_Id : 
    forall (n: nat) (x: Fin n), transformFin (refl_equal n) x = x.
  Proof.
    reflexivity.
  Qed.
*)
  Lemma Fin_S_pred : forall n: nat, n > 0 -> Fin n = Fin (S (pred n)).
  Proof.
    intros n h.
    rewrite <-(S_pred n 0 h). 
    reflexivity.
  Qed.    

  (* decode_Fin allows to associate an integer to an element of Fin n *)
  Fixpoint decode_Fin (n: nat)(f: Fin n): nat := match f with 
        first k => 0
      | succ f' => S ( decode_Fin f') 
  end.

  Definition decode_Fin_inf_n: forall (n: nat)(f: Fin n), decode_Fin f < n.
  Proof.
    intros n f.
    induction f as [ n | n f IHf].
    apply gt_Sn_O.
    apply (gt_n_S _ _ IHf).
  Defined.

  Definition decode_Fin_S_gt_O: 
    forall (n: nat)(f: Fin n), decode_Fin (succ f) > 0.
  Proof.
    intros n f.
    apply gt_Sn_O.
  Defined.

  Lemma decode_Fin_match : forall (n m: nat)(f: Fin n)(H: n = m), 
    decode_Fin f = decode_Fin (match H in (_ = l) return Fin l with 
      refl_equal => f end).  
  Proof.
    intros n m f H.
    destruct f as [ n | n f];
    rewrite <- H;  (* astonishingly, this works *)
    reflexivity.
  Qed.

  (* code_Fin associates an element of Fin n to an integer *)
  (* As its definition is not immediate, we had to define auxiliary
     functions. *)
  (* What's more, we also define various versions of code_Fin and prove their
     equivalence *)
  Fixpoint code_Fin1_aux (n: nat)(m: nat): option(Fin (S n)) := 
    match n return option(Fin (S n)) with
     | 0 => match m with 
              O => Some(first 0)
            | S m' => None
               end 
     | S n' => match m return option(Fin (S (S n'))) with
                O => Some(first (S n'))
              | S m' => option_map (succ (k:=(S n'))) (code_Fin1_aux n' m')
               end
    end. 

  Definition code_fin1_aux_def: forall n m: nat, m <= n -> 
    {f: Fin (S n) | code_Fin1_aux n m = Some f}.
  Proof.
    induction n as [ | n IHn]; intros m H ; destruct m as [ | m]; simpl.
    exists (first 0); reflexivity.
    destruct (le_Sn_O m H).
    exists (first (S n)); reflexivity.
    destruct (IHn m (le_S_n _ _ H)) as [f0 eq].
    exists (succ f0).
    rewrite eq.
    reflexivity.
  Defined.

  Definition code_Fin1_Sn (n m: nat)(h: m<=n): Fin (S n) := 
    proj1_sig (code_fin1_aux_def h).

  (* First version of code_Fin *)
  Definition code_Fin1 (n m: nat)(h: m<n): Fin n :=
    match n return (forall(m: nat)(h: m<n), Fin n) with 
      0 => fun (m : nat) (h : m < 0) =>
             match (lt_n_O m h) return (Fin 0) with end
    | S n0 => fun (m : nat) (h : m < S n0) => 
                code_Fin1_Sn (lt_n_Sm_le m n0 h)
    end m h.

  (* We prove a certain number of properties on code_Fin1 *)
  Lemma code_Fin1_Sn_0: forall (n:nat)(h:0<=n), code_Fin1_Sn h = first n.
  Proof.
    intros n h.
    destruct n as [ | n]; reflexivity.
  Qed.

  Lemma code_Fin1_Sn_S : forall (n m:nat)(h:S m<=S n),
    code_Fin1_Sn h = succ (code_Fin1_Sn (le_S_n m n h)).
  Proof.
    intros n m h.
    unfold code_Fin1_Sn.
    simpl proj1_sig.
    destruct (code_fin1_aux_def (le_S_n m n h)) as [x e].
    reflexivity.
  Qed.

  Lemma code_Fin1_Sn_proofirr:forall (n m:nat)(h1 h2:m<=n),
    code_Fin1_Sn h1 = code_Fin1_Sn h2.
  Proof.
    intros n m.
    revert n.
    induction m as [ | m IHm]; intros n h1 h2.
    do 2 rewrite code_Fin1_Sn_0.
    reflexivity.
    destruct n as [ | n].
    inversion h1.
    do 2 rewrite code_Fin1_Sn_S.
    f_equal.
    apply IHm.
  Qed.

  Lemma code_Fin1_Sn_proofirr2 : forall (n m1 m2:nat)(h1:m1<=n)(h2:m2<=n)(e: m1=m2),
    code_Fin1_Sn h1 = code_Fin1_Sn h2.
  Proof.
    induction n as [| n IHn]; 
    intros m1 m2 h1 h2 e;
    destruct m1 as [|m1]; destruct m2 as [|m2].
    do 2 rewrite code_Fin1_Sn_0.
    reflexivity.
    destruct (O_S m2 e).
    destruct (O_S m1 (sym_eq e)).
    inversion h1.
    do 2 rewrite code_Fin1_Sn_0.
    reflexivity.
    destruct (O_S m2 e).
    destruct (O_S m1 (sym_eq e)).
    do 2 rewrite code_Fin1_Sn_S.
    f_equal.
    apply (IHn _ _ _ _ (eq_add_S m1 m2 e)).
  Qed.

  Lemma code_Fin1_0_: forall (n:nat)(h:0<S n), code_Fin1 h = first n.
  Proof.
    intros n h.
    apply code_Fin1_Sn_0.
  Qed.

  Lemma code_Fin1_S: forall (n m:nat)(h:S m<S n),
    code_Fin1 h =  succ (code_Fin1 (lt_S_n m n h)).
  Proof.
    intros n m h.
    destruct n as [|n].
    apply False_rec.
    apply (le_Sn_O _ (gt_S_le _ _ h)).
    simpl.
    rewrite code_Fin1_Sn_S.
    f_equal.
    apply code_Fin1_Sn_proofirr.
  Qed.

  Lemma code_Fin1_proofirr : forall (n m:nat)(h1 h2:m< S n),
    code_Fin1 h1 = code_Fin1 h2.
  Proof.
    intros n m h1 h2.
    apply code_Fin1_Sn_proofirr.
  Qed.

  (* We give a characterization of the properties functions equal to 
     code_Fin1 have to fulfill *) 
  Lemma code_Fin1_char: forall (f: forall n m : nat, m < n → Fin n),
   (forall (n:nat)(h:0<S n), f (S n) 0 h = first n) ->
   (forall (n m:nat)(h:S m<S n),
     f (S n) (S m) h =  succ (f n m (lt_S_n m n h))) ->
   forall (n m:nat)(h:m<n), f n m h = code_Fin1 h.
  Proof.
    intros f Hyp0 HypS.
    induction n as [|n IHn]; 
    intros m h.
    inversion h.
    induction m as [|m IHm].
    rewrite Hyp0.
    rewrite code_Fin1_0_.
    reflexivity.
    rewrite HypS.
    rewrite code_Fin1_S.
    f_equal.
    apply IHn.
  Qed.

  Lemma Fin_0_empty: forall f: Fin 0, False.
  Proof.
    intro f.
    apply (lt_n_O (decode_Fin f) (decode_Fin_inf_n f)).
  Qed.

  (* Second version of code_Fin *)
  Definition code_Fin2: forall (n:nat) (m:nat) (h: m < n), Fin n.
  Proof.
    induction n as [|n IHn];
    intros m h.
    apply False_rec; apply (lt_n_O _ h).

    destruct m as [| m].
    exact (first n).
    exact (succ (IHn m (lt_S_n m n h))).
  Defined. 

  (* We prove the lemmas needed to be able to apply code_Fin1_char in order
     to prove that code_Fin1 = code_Fin2 *)
  Lemma code_Fin2_0 (n:nat)(h:0< S n): code_Fin2 h = first n.
  Proof.
    reflexivity.
  Qed.

  Lemma code_Fin2_S (n m:nat)(h:S m<S n): 
    code_Fin2 h =  succ (code_Fin2 (lt_S_n m n h)).
  Proof.
    reflexivity.
  Qed.    

  Lemma code_Fin2_proofirr: forall (n m:nat)(h1 h2:m < S n),
    code_Fin2 h1 = code_Fin2 h2.
  Proof.
    intros n m.
    revert n.
    induction m as [|m IHm]; intros n h1 h2.
    reflexivity.
    destruct n as [|n].
    apply False_rec.
    apply (le_Sn_O _ (gt_S_le _ _ h1)).
    do 2 rewrite code_Fin2_S.
    f_equal.
    apply IHm.
  Qed.

  (* We finally prove that code_Fin1 = code_Fin2 *)
  Lemma code1_code2_eq: forall (n m: nat)(h:m<n), code_Fin1 h = code_Fin2 h.
  Proof.
    induction n as [|n IHn].
    inversion h.
    destruct m as [|m]; intro h.
    rewrite (code_Fin2_0 h).
    simpl.
    rewrite code_Fin1_Sn_0.
    reflexivity.

    rewrite (code_Fin2_S h).
    simpl.
    destruct n as [|n].
    apply False_rec.
    apply (le_Sn_O _ (gt_S_le _ _ h)).
    rewrite code_Fin1_Sn_S.
    f_equal.
    rewrite <- (IHn m (lt_S_n m (S n) h)).
    apply code_Fin1_Sn_proofirr.
  Qed.
  
  (* Alternative proof using code_Fin1_char *)
  Lemma code1_code2_eq_ALT: 
    forall (n m: nat)(h: m<n), code_Fin1 h = code_Fin2 h.
  Proof.
    intros n m h.
    symmetry.
    apply (code_Fin1_char _ code_Fin2_0 code_Fin2_S).
  Qed.
  
  (* We prove that code_Fin1 and decode form a bijection *)
  Lemma code1_decode_Id: forall (n: nat)(f: Fin n), 
    (code_Fin1 (decode_Fin_inf_n f)) = f.
  Proof.
    induction f as [k | k f IHf]; simpl.
    rewrite code_Fin1_Sn_0; reflexivity.
    destruct k as [|k].
    inversion f.
    rewrite code_Fin1_Sn_S.
    f_equal.
    transitivity (code_Fin1_Sn
        (lt_n_Sm_le (decode_Fin f) k (decode_Fin_inf_n f))); try assumption.
    apply code_Fin1_Sn_proofirr.
  Qed.

  Lemma decode_code1_Id: forall (n m: nat)(h: m < n), 
    decode_Fin (code_Fin1 h) = m.
  Proof.
    induction n as [|n IHn].
    inversion h.
    unfold code_Fin1.
    destruct m as [|m]. 
    inversion h ; 
    rewrite code_Fin1_Sn_0 ;
    reflexivity.
    
    destruct n as [|n];
    intro h.
    apply False_rec.
    apply (le_Sn_O _ (gt_S_le _ _ h)).
    rewrite code_Fin1_Sn_S.
    simpl.
    f_equal.
    rewrite (code_Fin1_Sn_proofirr 
      (le_S_n m n (lt_n_Sm_le (S m) (S n) h)) 
                  (lt_n_Sm_le m n (lt_S_n m (S n) h))).
    apply (IHn m (lt_S_n m (S n) h)).
  Qed.

  (* Third definition of code_Fin *)
  (* It needs an auxiliary definition *)
  Definition code_Fin3_aux: forall (n:nat) (x:nat) (h: x < n), Fin n.
  Proof.
    induction n as [|n IHn]; 
    intros x h.
    apply False_rec; inversion h.
    
    elim (lt_eq_lt_dec x n) ; intros a.
    clear h.
    inversion_clear a as [H | H].
    assert (H0 := IHn x H).
    exact (succ H0).
    exact (first n).
    
    apply False_rec.
    inversion h as [e | y irr].
    rewrite e in a.
    apply (lt_irrefl _ a).
    apply (lt_irrefl x (lt_trans x (S x) x (lt_n_Sn x)
                                        (le_lt_trans (S x) n x irr a))).
  Defined.

  (* Proof of lemmmas on the auxiliary definition *)
  (* Needed to prove the lemmas on code_Fin3 *) 
  Definition code_Fin3 (n:nat) (x:nat) (h: x < n): Fin n:=
    code_Fin3_aux (lt_m_n_Sm_n h).

  Lemma code_Fin3_aux_n: forall (n:nat),
    code_Fin3_aux (lt_n_Sn n) = first n.
  Proof.
    intros n.
    simpl.
    unfold sumor_rec ; unfold sumor_rect.
    elim (lt_eq_lt_dec n n); intro a.
    destruct a as [H | _].
    apply False_rec; apply (lt_irrefl n H).
    reflexivity.
    apply False_rec; apply (lt_irrefl n a).
  Qed.

  Lemma code_Fin3_aux_0: forall (n:nat)(h:0< S n),
    code_Fin3_aux h = code_Fin2 (lt_n_Sn n).
  Proof.
    intros n h.
    induction n as [|n IHn].
    reflexivity.
    simpl.
    simpl in IHn.
    rewrite IHn.
    f_equal.
    elim n.
    reflexivity.
    intros n0 _.
    f_equal.
    apply code_Fin2_proofirr.
  Qed.
 
  Lemma code_Fin3_aux_S : forall (m n:nat)(h: S m < S n),
    code_Fin3_aux (lt_n_S m (S n) (lt_S _ _ (lt_S_n _ _ h))) = 
    succ (code_Fin3_aux h).
  Proof.
    intros m n h.
    destruct n as [|n].
    apply False_rec.
    apply (le_Sn_O _ (gt_S_le _ _ h)).
    simpl.
    unfold sumor_rec ; unfold sumor_rect.
    elim (lt_eq_lt_dec m (S n)); intros a.
    destruct a as [H|H]; simpl.
    f_equal.
    elim (lt_eq_lt_dec m n); intros a.
    destruct a as [H0|H0]; simpl;
    reflexivity.
    apply False_rec.
    apply (lt_irrefl _ (le_lt_trans _ _ _ (lt_le_S _ _ a) H)).
    apply False_rec.
    rewrite H in h.
    apply (lt_irrefl _ h).
    apply False_rec.
    apply (lt_irrefl _ (lt_trans _ _ _ (lt_n_S _ _ a) h)).
  Qed.

  Lemma code_Fin3_aux_proofirr: forall (n m:nat)(h1 h2:m < S n),
    code_Fin3_aux h1 = code_Fin3_aux h2.
  Proof.
    intros n m h1 h2.
    elim (lt_eq_lt_dec m n); intros a.
    destruct a as [H|e].
    destruct n as [|n].
    inversion H.
    simpl.
    destruct m as [|m].
    reflexivity.
    elim (lt_eq_lt_dec m n); intros a.
    destruct a as [H0|H0].
    elim (lt_eq_lt_dec (S m) (S n)); intros a.
    reflexivity.
    apply False_rec.
    apply (lt_irrefl _ (lt_trans _ _ _ a H)).
    elim (lt_eq_lt_dec (S m) (S n)); intros a.
    reflexivity.
    apply False_rec.
    apply (lt_irrefl _ (lt_trans _ _ _ a H)).
    elim (lt_eq_lt_dec (S m) (S n)); intros b.
    reflexivity.
    apply False_rec.
    apply (lt_irrefl _ (lt_trans _ _ _ b H)).

    destruct n as [|n]; destruct m as [|m].
    reflexivity.
    inversion e.
    inversion e.
    simpl.
    elim (lt_eq_lt_dec m n); intros a.
    destruct a as [H|H].
    apply False_rec.
    apply lt_n_S in H.
    rewrite e in H.
    apply (lt_irrefl _ H).
    reflexivity.
    apply False_rec.
    apply lt_n_S in a.
    rewrite e in a.
    apply (lt_irrefl _ a).

    destruct n as [|n]; destruct m as [|m].
    apply False_rec.
    apply (lt_irrefl _ a).
    apply False_rec.
    apply (le_Sn_O _ (gt_S_le _ _ h2)).
    inversion a.
    simpl.
    elim (lt_eq_lt_dec m n); intros b.
    destruct b as [H|H] ; reflexivity.
    apply False_rec.
    inversion a as [e | x H e].
    rewrite e in h2.
    apply (lt_irrefl _ h2).
    apply (lt_irrefl _ (lt_trans _ _ _ (lt_n_Sn _) 
                                       (lt_le_trans _ _ _ h2 H))).
  Qed.

  (* Proof of the lemmas on code_Fin3 in order to prove the 
     equivalence between code_Fin3 and code_Fin1 *)
  Lemma code_Fin3_0: forall (n:nat)(h:0< S n), code_Fin3 h = first n.
  Proof.
    intros n h.
    unfold code_Fin3; simpl.
    destruct n as [|n].
    reflexivity.
    elim (lt_eq_lt_dec (S n - 0) (S n)); intros a.
    destruct a as [H|H].
    apply False_rec.
    apply (lt_irrefl _ H).
    reflexivity.
    apply False_rec.
    apply (lt_irrefl _ a).
  Qed.

  Lemma code_Fin3_S: forall (n m:nat)(h:S m<S n),
    code_Fin3 h =  succ (code_Fin3 (lt_S_n m n h)).
  Proof.
    intros n m h.
    unfold code_Fin3.
    destruct n as [|n].
    apply False_rec.
    apply (le_Sn_O _ (gt_S_le _ _ h)).
    elim (lt_eq_lt_dec (S n - S m) (S n)); intros a.
    destruct a as [H|H].
    simpl.
    unfold sumor_rec; unfold sumor_rect.
    elim (lt_eq_lt_dec (n - m) (S n)); intros a.
    destruct a as [H0|H0].
    elim (lt_eq_lt_dec (n - m) n); intros a;
    [reflexivity | apply False_rec].
    inversion H0 as [H2 | x H2 H3].
    rewrite H2 in a.
    apply (lt_irrefl _ a).
    apply lt_n_S in a.
    apply le_lt_n_Sm in H2.
    apply (lt_irrefl _ (lt_trans _ _ _ a H2)).
    apply False_rec.
    rewrite <- Sn_Sm_eq_n_m in H0.
    rewrite H0 in H.
    apply (lt_irrefl _ H).
    apply False_rec.
    rewrite <- Sn_Sm_eq_n_m in a.
    apply (lt_irrefl _ (lt_trans _ _ _ a H)).
    apply False_rec.
    apply (lt_n_Sm_le (S m) (S n)) in h.
    apply (minus_reg_l h) in H.
    inversion H.
    apply False_rec.
    apply (lt_irrefl _ (lt_trans _ _ _ a 
      (lt_minus _ _ (lt_n_Sm_le (S m) (S n) h) (lt_O_Sn m)))).
  Qed.    

  Lemma code1_code3_eq: 
    forall (n m: nat)(h: m<n), code_Fin1 h = code_Fin3 h.
  Proof.
    intros n m h.
    symmetry.
    apply (code_Fin1_char _ code_Fin3_0 code_Fin3_S).
  Qed.

  Lemma decode_Fin_unique: forall (n: nat)(f1 f2: Fin n), 
    decode_Fin f1 = decode_Fin f2 -> f1 = f2.
  Proof.
    intros n f1 f2 h.
    rewrite <- (code1_decode_Id f1);
    rewrite <- (code1_decode_Id f2).
    destruct n as [|n].
    inversion f1.
    assert (h1 := decode_Fin_inf_n f1).
    rewrite (code_Fin1_proofirr _ h1).
    revert h1.
    rewrite h.
    intros h1.
    apply code_Fin1_proofirr.
  Qed.

  Lemma decode_Fin_0_first: 
    forall(n: nat) (f: Fin (S n)), decode_Fin f = 0 -> f = first n.
  Proof.
    intros n f H.
    apply decode_Fin_unique.
    rewrite H.
    reflexivity.
  Qed.

  Definition mkFinn : forall (n: nat), Fin (S n).
  Proof.
    intros n ; induction n as [|n IH].
    exact (first 0).
    exact (succ IH).
  Defined.

  Lemma decode_Fin_mkFinn_n : forall n, decode_Fin (mkFinn n) = n.
  Proof.
    induction n as [|n IH].
    reflexivity.
    simpl.
    rewrite IH ; reflexivity.
  Qed.

  Definition get_cons: forall (n: nat) (f: Fin (S n))(h: decode_Fin f > 0), Fin n.
  Proof.
    intros n f h.
    elim (O_or_S (decode_Fin f)); intro a.
    destruct a as [x e].
    assert (H: x < n).
    apply lt_S_n.
    rewrite e.
    apply (decode_Fin_inf_n f).
    exact (code_Fin1 H).
    rewrite a in h.
    apply False_rec.
    apply (lt_irrefl _ h).
  Defined.

  Lemma get_cons_ok: forall (n: nat)(f: Fin n), 
    get_cons (succ f) (decode_Fin_S_gt_O f) = f.
  Proof.
    intros n f.
    destruct n as [|n].
    inversion f.
    rewrite <- code1_decode_Id.
    unfold get_cons.
    simpl.
    apply code_Fin1_proofirr.
  Qed.

  Lemma get_cons_proofirr: forall (n: nat) (f: Fin (S n))(h h': decode_Fin f > 0), 
    get_cons f h = get_cons f h'.
  Proof.
    intros n f h h'.
    apply decode_Fin_unique.
    unfold get_cons, sumor_rec, sumor_rect.
    elim (O_or_S (decode_Fin f)) ; intros b.
    reflexivity.
    apply False_rec.
    rewrite <- b in h.
    inversion h.
  Qed.
 
  Lemma Fin_first_1: forall (f: Fin 1), f = first 0.
  Proof.
    intros f.
    rewrite <- (code1_decode_Id f).
    assert (h:= decode_Fin_inf_n f) ; rewrite (code_Fin1_proofirr _ h).
    elim (zerop (decode_Fin f)); intros a.
    revert h ; rewrite a; intro h.
    apply code_Fin1_0_.
    apply False_rec. 
    apply (lt_irrefl _ (lt_le_trans _ _ _ a (lt_n_Sm_le _ _ h))).
  Qed.

  Lemma decode_Fin_get_cons: forall (n: nat)(f: Fin (S n))(h: decode_Fin f > 0), 
    decode_Fin f = S (decode_Fin (get_cons f h)).
  Proof.
    intros n f h.
    unfold get_cons.
    simpl.
    unfold sumor_rec ; unfold sumor_rect.
    elim (O_or_S (decode_Fin f)) ; [intros [m h1] | intros a].
    rewrite decode_code1_Id.
    rewrite h1.
    reflexivity.
    apply False_rec.
    rewrite a in h.
    apply (lt_irrefl _ h).
  Qed.

  Lemma get_cons_ok1 (n: nat)(i: Fin (S n))(h: 0 < decode_Fin i) : 
    succ (get_cons _ h) = i.
  Proof.
    apply decode_Fin_unique, sym_eq, decode_Fin_get_cons.
  Qed.

  Lemma get_cons_ok2 (n: nat)(i: Fin n)(h: 0 < decode_Fin (succ i)) : 
    get_cons (succ i) h = i.
  Proof.
    rewrite (get_cons_proofirr _ _ (decode_Fin_S_gt_O i) ).
    apply get_cons_ok.
  Qed.

    (* Definition and lemma to create a list of all the elements of Fin n *)
    Definition makeListFin : forall (n: nat), list (Fin n).
    Proof.
      intros n.
      induction n as [|n IHn].
      exact nil.
      exact (cons (first n) (map (succ (k:= n)) IHn )).
    Defined.

    Fixpoint makeListFin' (n: nat): list (Fin n):= 
      match n with
        O => nil
      | S k => (first k) ::  (map (succ (k:= k)) (makeListFin' k))
      end.

    Lemma makeListFin_eq_makeListFin': forall n, makeListFin n = makeListFin' n.
    Proof.
      reflexivity.
    Qed.

    Lemma makeListFin_nb_elem_ok: 
      forall n: nat, (length (makeListFin n)) = n.
    Proof.
      intros n.
      induction n as [|n IHn].
      reflexivity.
      rewrite <- IHn at 3.
      simpl.
      rewrite map_length.
      reflexivity.
    Qed.
    
    Lemma all_Fin_n_in_makeListFin : forall (n: nat),
      forall f: Fin n, In f (makeListFin n).
    Proof.
      intros n f.
      induction f as [k | k f IHf] ; simpl.
      left; reflexivity.
      right.
      apply in_map.
      apply IHf.
    Qed.
	
    Lemma nth_makeListFin: forall (n m: nat)(h: m < n),
      code_Fin1 h = nth m (makeListFin n) (code_Fin1 h).
    Proof.
      induction n as [|n IHn]; 
      intros m h.
      inversion h.
      destruct m as [|m].
      apply code_Fin1_Sn_0.
      simpl.
      destruct n as [|n].
      apply False_rec.
      apply (le_Sn_O _ (gt_S_le _ _ h)).
      rewrite code_Fin1_Sn_S.
      rewrite map_nth.
      f_equal.
      unfold code_Fin1 in IHn.
      rewrite (code_Fin1_Sn_proofirr _ (lt_n_Sm_le m n (lt_S_n _ _ h))).
      apply IHn.
    Qed.

    Lemma nth_makeListFin_def: forall (n m: nat)(h: m < n)(d: Fin n),
      code_Fin1 h = nth m (makeListFin n) d.
    Proof.
      intros n m h f.
      rewrite (nth_indep (makeListFin n) f (code_Fin1 h)).
      apply nth_makeListFin.
      rewrite makeListFin_nb_elem_ok.
      assumption.
    Qed.

    Lemma makeListFin_S: forall n: nat, 
      makeListFin (S n) = (first n) :: (map (succ (k:= n)) (makeListFin n)).
    Proof.
      reflexivity.
    Qed.
      
    Lemma Fin_first_or_succ: forall (n: nat)(f: Fin (S n)),
      In f ((first n)::(map (succ (k:= n)) (makeListFin n))).
    Proof.
      intros n f.
      rewrite <- makeListFin_S.
      apply all_Fin_n_in_makeListFin.
    Qed.

End Fin_def_tools.

Section rewrite_Fins. 
  
   Lemma match_sym_eq_eq: forall (n1 n2: nat)(f: Fin n1)(e: n1 = n2), 
     f = match sym_eq e in (_ = l) return (Fin l) with refl_equal =>
     match e in (_ = l) return (Fin l) with refl_equal => f end end.
   Proof.
     intros n1 n2 f e.
     refine (match e return _ with refl_equal => _ end).
     reflexivity.
   Qed.
   
   Lemma match_eq_sym_eq: forall (n1 n2: nat)(f: Fin n1)(e: n2 = n1), 
     f = match e in (_ = l) return (Fin l) with refl_equal =>
     match sym_eq e in (_ = l) return (Fin l) with refl_equal => f end end.
   Proof.
     intros n1 n2 f e.
     refine ((match e as e' in (_ = l) return forall g: Fin l, _ 
       with refl_equal => _ end) f).
     reflexivity.
   Qed.

  (* crucial definition, but nothing more than an abbreviation *)
  Definition rewriteFins (n1 n2: nat)(H: n1 = n2)(f: Fin n1): Fin n2 :=
    match H in _ = l return Fin l with refl_equal => f end.

  (* this wraps decode_Fin_match and should be called differently *)
  Lemma decode_Fin_match' : forall (n m: nat)(f: Fin n)(H: n = m), 
    decode_Fin f = decode_Fin (rewriteFins H f).  
  Proof.
    apply decode_Fin_match. 
  Qed.
  
  Lemma rewriteFins_refl : forall (n: nat)(e: n = n)(f: Fin n), rewriteFins e f  = f.
  Proof.
    intros n e f.
    apply decode_Fin_unique, (sym_eq (decode_Fin_match' _ _)).
  Qed.

  Lemma rewriteFins_sym: forall (n1 n2: nat)(e: n1 = n2)(f: Fin n2),
    rewriteFins e (rewriteFins (sym_eq e) f) = f.
  Proof.
    intros n1 n2 e f.
    apply (sym_eq (match_eq_sym_eq f e)).
  Qed.

  Lemma rewriteFins_trans :forall (n1 n2 n3: nat) (e1: n1 = n2)(e2: n2 = n3)(f: Fin n1),
    rewriteFins e2 (rewriteFins e1 f) = rewriteFins (trans_eq e1 e2) f.
  Proof.
    intros n1 n2 n3 e1 e2 f.
    refine ((match e2 return _ with refl_equal => _ end) f).
    reflexivity.
  Qed.

  Lemma rewriteFins_proofirr (n1 n2: nat)(i: Fin n1) (h1 h2 : n1 = n2) : 
    rewriteFins h1 i = rewriteFins h2 i.
  Proof.
    apply decode_Fin_unique.
    do 2 rewrite <- decode_Fin_match'.
    reflexivity.
  Qed.
End rewrite_Fins.

Section Fin_injectivity.
  Lemma succ_first_neq (n n' : nat)(f: Fin (S n) -> Fin (S n'))
    (g: Fin (S n') -> Fin (S n))(H: Bijective f g): decode_Fin (f (first n)) = 0 -> 
      forall i, decode_Fin (f (succ i)) > 0.
  Proof.
    intros a i.
    apply neq_0_lt.
    intros H1.
    rewrite H1 in a.
    apply decode_Fin_unique, (bij_inj H) in a.
    inversion a.
  Qed.

  Lemma first_succ_neq (n n' : nat)(f: Fin (S n) -> Fin (S n'))
    (g: Fin (S n') -> Fin (S n))(H: Bijective f g)(i: Fin n): 
      decode_Fin (f (succ i)) = 0 -> decode_Fin (f (first n)) > 0.
  Proof.
    intros a.
    apply neq_0_lt.
    intros H1.
    assert (H2 := succ_first_neq H (sym_eq H1) i).
    rewrite a in H2 ; inversion H2.
  Qed.

  Definition FSnFSn'_FnFn' (n n' : nat)(f: Fin (S n) -> Fin (S n'))
    (g: Fin (S n') -> Fin (S n))(H: Bijective f g): Fin n -> Fin n'.
  Proof.
    intros i.
    elim (zerop (decode_Fin (f (succ i)))) ; intros a.
    exact (get_cons _ (first_succ_neq H i a)).
    exact (get_cons _ a).
  Defined.

  Lemma FSnFSn'_FnFn'_ok1 (n n' : nat)(f: Fin (S n) -> Fin (S n'))
    (g: Fin (S n') -> Fin (S n))(H: Bijective f g)(i: Fin n) 
    (H1: decode_Fin (f (succ i)) = 0) :
    FSnFSn'_FnFn' H i = get_cons _ (first_succ_neq H i H1).
  Proof.
     unfold FSnFSn'_FnFn', sumbool_rec, sumbool_rect.
     elim (zerop (decode_Fin (f (succ i)))) ; intros a.
     apply get_cons_proofirr.
     apply False_rec, (lt_0_neq _ a), sym_eq, H1.
  Qed.

  Lemma FSnFSn'_FnFn'_ok2 (n n' : nat)(f: Fin (S n) -> Fin (S n'))
    (g: Fin (S n') -> Fin (S n))(H: Bijective f g)(i: Fin n) 
    (H1: decode_Fin (f (succ i)) > 0) : FSnFSn'_FnFn' H i = get_cons _ H1.
  Proof.
     unfold FSnFSn'_FnFn', sumbool_rec, sumbool_rect.
     elim (zerop (decode_Fin (f (succ i)))) ; intros a.
     apply False_rec, (lt_0_neq _ H1), sym_eq, a.
     apply get_cons_proofirr.
  Qed.

  Lemma FSnFSn'_FnFn'_proofirr (n n' : nat)(f: Fin (S n) -> Fin (S n'))
    (g: Fin (S n') -> Fin (S n))(H1 H2: Bijective f g) : 
    forall i, FSnFSn'_FnFn' H1 i = FSnFSn'_FnFn' H2 i.
  Proof.
    intros i.
    elim (zerop (decode_Fin (f (succ i)))) ; intros a.
    rewrite (FSnFSn'_FnFn'_ok1 H1 _ a), (FSnFSn'_FnFn'_ok1 H2 _ a).
    apply get_cons_proofirr.
    rewrite (FSnFSn'_FnFn'_ok2 H1 _ a), (FSnFSn'_FnFn'_ok2 H2 _ a).
    apply get_cons_proofirr.
  Qed.

  Lemma succ_inj (n: nat)(i1 i2 : Fin n) : succ i1 = succ i2 -> i1 = i2.
  Proof.
    intros H.
    apply decode_Fin_unique, eq_add_S.
    change (decode_Fin (succ i1) = decode_Fin (succ i2)).
    rewrite H.
    reflexivity.
  Qed.

  Lemma FSnFSn'_FnFn'_aux_bij(n n' : nat)(f: Fin (S n) -> Fin (S n'))
    (g: Fin (S n') -> Fin (S n))(H1: Bijective f g)(H2 : Bijective g f) : 
    forall i, FSnFSn'_FnFn' H2 (FSnFSn'_FnFn' H1 i) = i.
  Proof.
    intros i ; destruct H1 as [H1 H3].
    elim (zerop (decode_Fin (f (succ i)))) ; intros a.
    rewrite (FSnFSn'_FnFn'_ok1 _ _ a).
    assert (b : decode_Fin (g (succ (get_cons (f (first n)) 
      (first_succ_neq (conj H1 H3) i a)))) = 0).
    rewrite get_cons_ok1, H1.
    reflexivity.
    rewrite (FSnFSn'_FnFn'_ok1 _ _ b).
    apply succ_inj.
    rewrite get_cons_ok1, <- (H1 (succ i)).
    f_equal.
    apply decode_Fin_unique, sym_eq, a.

    rewrite (FSnFSn'_FnFn'_ok2 _ _ a).
    assert (b : decode_Fin (g (succ (get_cons (f (succ i)) a))) > 0).
    rewrite (get_cons_ok1 _ a), H1.
    apply lt_0_Sn.
    rewrite (FSnFSn'_FnFn'_ok2 _ _ b).
    revert b ; rewrite (get_cons_ok1 _ a), H1 ; intros b.
    apply get_cons_ok2.
  Qed.

  Lemma FSnFSn'_FnFn'_bij(n n' : nat)(f: Fin (S n) -> Fin (S n'))
    (g: Fin (S n') -> Fin (S n))(H: Bijective f g) : 
    Bijective (FSnFSn'_FnFn' H) (FSnFSn'_FnFn' (Bij_sym H)).
  Proof.
    split ; intros i ; 
    apply FSnFSn'_FnFn'_aux_bij.
  Qed.

  Definition Fin_inj_aux: 
  forall (n n': nat) (f: Fin n -> Fin n')(g: Fin n' -> Fin n),
  Bijective f g -> n = n'.
  Proof.
    induction n as [|n IH] ; intros [|n'] f g H.
    reflexivity.
    assert (i := g (first n')).
    inversion i.
    assert (i := f (first n)).
    inversion i.
  
    f_equal.
    apply (IH _ (FSnFSn'_FnFn' H) (FSnFSn'_FnFn' (Bij_sym H))).
    apply FSnFSn'_FnFn'_bij.
  Defined.

  Definition FnFn' (n n' : nat)(H : Fin n = Fin n')(i : Fin n) := 
    match  H in _=l return l with refl_equal => i end. 
  
  Lemma FnFn'_Fn'Fn (n n' : nat)(H : Fin n = Fin n') : 
    forall i, FnFn' (sym_eq H) (FnFn' H i) = i.
  Proof.
    unfold FnFn' ; rewrite H.
    reflexivity.
  Qed.

  Lemma FnFn'_Fn'Fn_inv (n n' : nat)(H : Fin n = Fin n') : 
    forall i, FnFn' H (FnFn' (sym_eq H) i) = i.
  Proof.
    
    unfold FnFn' ; rewrite H.
    reflexivity.
  Qed.
  
  Definition Fin_inj: forall (n n': nat) , Fin n = Fin n' -> n = n'.
  Proof.
    intros n n' H.
    apply (Fin_inj_aux (conj (FnFn'_Fn'Fn H) (FnFn'_Fn'Fn_inv H))).
  Defined.

End Fin_injectivity.

Section minus_Fin.

Definition minusFin (n: nat)(i: Fin n): nat.
Proof.
  induction i as [n|n i IH].
  exact n.
  exact IH.
Defined.

Lemma minusFin1 (n: nat) : @minusFin (S n) (first n) = n.
Proof.
  reflexivity.
Qed.

Lemma minusFin2 (n: nat)(i: Fin n) : @minusFin (S n) (succ i) = @minusFin n i.
Proof.
  reflexivity.
Qed.

Lemma minusFin3 (n: nat) : @minusFin (S n) (code_Fin1 (lt_n_Sn n)) = 0.
Proof.
  induction n as [|n IH].
  reflexivity.
  assert (H1 : code_Fin1 (lt_n_Sn (S n)) = succ (code_Fin1 (lt_n_Sn n))).
  apply decode_Fin_unique.
  change (decode_Fin (code_Fin1 (lt_n_Sn (S n))) =
  S (decode_Fin (code_Fin1 (lt_n_Sn n)))).
  do 2 rewrite decode_code1_Id.
  reflexivity.
  rewrite H1.
  rewrite  minusFin2.
  assumption.
Qed.
End minus_Fin.


