(** IPPJustification.v Version 1.0 February 2012 *)
(** runs under V8.3, tested with 8.3pl3 *)

(** Ralph Matthes and Celia Picard, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(**  justification of the infinite pigeonhole principle used in Graphs.v 
     in the proof of Lemma TeqPerm_GeqPerm from the law of excluded middle *)

Require Import Fin.
Require Import Ilist.
Require Import GPerm.
Require Import IlistPerm. 
Require Import Tools.

Require Import List.
Require Import Le.
Require Import Plus.
Require Import Logic.ClassicalFacts. (* this does not assume classical axioms but only studies them *)
Require Import Logic.ChoiceFacts. (* this does not assume choice axioms but only studies them *)

Set Implicit Arguments.

Fixpoint FinIndex (n: nat)(e: Fin n): nat :=
  match e with first m => m | succ m e' => m end. 

Lemma FinIndexOk (n: nat)(e: Fin n):
  n = S (FinIndex e).
Proof.
  induction e; reflexivity.
Defined.

Lemma FinIndexOkCor (n: nat)(e: Fin n):
  n-1 = FinIndex e.
Proof.
  destruct n.
  inversion e.
  apply eq_add_S.
  rewrite <- FinIndexOk.
  destruct n; reflexivity.
Defined.

Lemma SkAux (k: nat): S k - 1 = k.
Proof.
  induction k;
  reflexivity.
Defined.

Lemma FinIndexOkCor2 (n: nat)(e: Fin (S n)):
  n = FinIndex e.
Proof.
  rewrite <- FinIndexOkCor.
  apply (sym_eq (SkAux n)).
Defined.  

(* a useless decomposition lemma: *)
Lemma FinDestruct (n: nat)(e: Fin n):
e = rewriteFins (sym_eq(FinIndexOk e)) (first (FinIndex e))
\/ exists e':(Fin(FinIndex e)), e = rewriteFins (sym_eq(FinIndexOk e))(succ e').
Proof.
  induction e.
  left.
  reflexivity.
  right.
  exists e.
  reflexivity.
Qed.

Definition FinCasesAux (A: Type)(a: A)(n: nat)(f: Fin (n-1) -> A): Fin n -> A.
Proof.
  intro e.
  refine ((match e in Fin k return (Fin (k-1) -> A) -> A with first _ => fun _ => a | succ _ e' => _ end) f).
  intro f'.
  rewrite SkAux in f'.
  exact (f' e').
Defined.

Definition FinCases (A: Type)(a: A)(n: nat)(f: Fin n -> A): Fin (S n) -> A.
Proof.
  intro e.
  revert f.
  rewrite <- (SkAux n).
  intro f.
  exact (FinCasesAux a f e).
Defined.

(* just an easier alternative through decode_Fin *)
Definition FinCases' (A: Type)(a: A)(n: nat)(f: Fin n -> A): Fin (S n) -> A.
Proof.
  intros i.
  elim (zerop (decode_Fin i)) ; intros H.
  exact a.
  exact (f (get_cons _ H)).
Defined.

Lemma FinCasesOK1 (A: Type)(a: A)(n: nat)(f: Fin n -> A):
  FinCases a f (first n) = a.
Proof.
  destruct n;
  reflexivity.
Qed.

Lemma FinCasesOK2 (A: Type)(a: A)(n: nat)(f: Fin n -> A)(e: Fin n):
  FinCases a f (succ e) =  f e.
Proof.
  destruct n;
  reflexivity.
Qed.

Lemma FinCasesElim (A: Type)(a: A)(n: nat)(f: Fin n -> A)(R: Fin (S n) -> A -> Prop):
    R (first n) a -> (forall (e: Fin n), R (succ e) (f e))  
     -> forall (e: Fin (S n)), R e (FinCases a f e).
Proof.
  intros Hyp1 Hyp2 e.
  elim (zerop (decode_Fin e)) ; intros H.
  rewrite (decode_Fin_0_first _ H).
  rewrite FinCasesOK1.
  assumption.
  rewrite (decode_Fin_unique _ _ (decode_Fin_get_cons _ H : decode_Fin e = decode_Fin (succ _))).
  rewrite FinCasesOK2.
  apply Hyp2.
Qed.
(* very bad situation where the support for Fin in Coq does not help *) 
  
Lemma FinCases_FinCases'(A: Type)(a: A)(n: nat)(f: Fin n -> A) :
  forall i, FinCases a f i = FinCases' a f i.
Proof.
  intros i ; unfold FinCases' ; elim (zerop (decode_Fin i)) ; intros H ; simpl.
  rewrite (decode_Fin_0_first _ H).
  apply FinCasesOK1.
  rewrite  (decode_Fin_unique _ _ (decode_Fin_get_cons _ H : _ = decode_Fin (succ _))) at 1.
  apply FinCasesOK2.
Qed.

(* FinCases' will no longer be used *)
 
Lemma FunctionalChoiceFin (m: nat): FunctionalChoice_on (Fin m) nat. 
Proof.
  red.
  induction m ; intros R H.
  exists (fun _ => 0).
  intro x; inversion x.
  set (R' := fun e => R (succ e)).
  destruct (IHm R') as [f Hyp];
  clear IHm.
  intro x.
  apply (H (succ x)).
  destruct (H (first m)) as [y0 Hyp0].
  clear H.
  exists (FinCases y0 f).
  apply FinCasesElim; assumption.
Qed.

Definition IP3ClCases (n: nat)(f: IlistPerm3Cert_list n -> nat): IlistPerm3Cert_list (S n) -> nat.
Proof.
  intros [[i1 i2] s].
  exact (decode_Fin i1 * (S n) * (S n) + decode_Fin i2 * (S n) + (f s)).
Defined.

(* we need to study some classical facts - without ever taking them as axioms *)

Definition DNE: Prop := forall P: Prop, ~~P -> P.

Lemma ExclMiddleImpDNE: excluded_middle -> DNE.
Proof.
  intros EM P H.
  destruct (EM P) as [H1|H1].
  assumption.
  apply False_rec.
  contradiction H.
Qed.

Lemma DeMorganExists: DNE -> forall (A: Type)(P: A -> Prop), 
  ~ (forall a: A, ~ P a) -> exists a: A, P a.
Proof.
  intros DNE A P Hyp.
  apply DNE.
  intro H.
  apply Hyp.
  intro a.
  intro H1.
  apply H.
  exists a.
  assumption.
Qed.

Fixpoint MaxFin (m: nat): (Fin m -> nat) -> nat :=
  match m return (Fin m  -> nat) -> nat with 
    | 0 => fun _ => 0 
    | S m' => fun f => f (first m') + MaxFin (fun e: Fin m' => f (succ e))
  end.

Lemma MaxFinOk (m: nat)(f: Fin m -> nat)(e: Fin m): MaxFin f >= f e.
Proof.
  revert f; induction e; intros.
  simpl.
  apply le_plus_l.
  simpl.
  eapply le_trans.
  eapply (IHe (fun e: Fin k => f (succ e))).
  apply le_plus_r.
Qed.

Definition MaxFin' (m: nat) (f: Fin m -> nat) : nat := max_list_nat (map f (makeListFin m)).

Lemma MaxFin'Ok (m: nat)(f: Fin m -> nat)(e: Fin m): MaxFin' f >= f e.
Proof.
  apply max_list_max.
  apply in_map.
  apply all_Fin_n_in_makeListFin.
Qed.

Definition IPPFin: Prop := forall (m: nat)(P: nat -> Fin m -> Prop), (forall n: nat, exists f: Fin m, P n f)
  -> exists f0: Fin m, forall n: nat, exists n': nat, n' >= n /\ P n' f0.

Lemma DNEImpIPPFin: DNE -> IPPFin.
Proof.
  intro DNE. 
  red.
  intros m P HH.
  apply (DeMorganExists DNE).
  intro H.
  assert (H0: forall f0 : Fin m, exists k: nat, forall n: nat, P n f0 -> ~ n >= k).
  intro.
  assert (H1 := H f0). clear H.
  apply (DeMorganExists DNE).
  intro H2.
  apply H1.
  intro k.
  apply (DeMorganExists DNE).
  intro H4.
  assert (H3 := H2 k). clear H2.
  apply H3.
  intros n Hyp1 Hyp2.
  apply (H4 n).
  split; assumption.
  clear H.
  apply FunctionalChoiceFin in H0.
  destruct H0 as [k' Hyp].
  assert (H: forall (n:nat), ~ n >= MaxFin' k').
  intro n.
  destruct (HH n) as [f fgood].
  intros H.
  apply (Hyp _ _ fgood).
  apply (le_trans _ (MaxFin' k')).
  apply MaxFin'Ok.
  assumption.
  apply (H (S (MaxFin' k'))).
  apply le_n_Sn.
Qed.

(* Thus, DNE (or excluded_middle) suffices to justify IPPFin, but we need to justify IPPIlistPerm3Cert.
   The only difference is that the latter uses IlistPerm3Cert_list m instead of Fin m. The following
   is the tedious proof that this is inessential. *)

Definition IPPGen (A: Set): Prop := forall (P: nat -> A -> Prop), (forall n: nat, exists f: A, P n f)
  -> exists f0: A, forall n: nat, exists n': nat, n' >= n /\ P n' f0.

Lemma IPPGen_gen: (forall m: nat, IPPGen (Fin m)) = IPPFin.
Proof.
  reflexivity.
Qed.

Lemma IPPGen_bij (A B: Set)(f: A -> B)(g: B -> A)(HypB: Bijective f g):  IPPGen A -> IPPGen B.
Proof.
  intro Hyp.
  red.
  intros.
  destruct HypB as [Hyp1 Hyp2].
  assert (H': forall n : nat, exists a : A, P n (f a)).
  intro n.
  destruct (H n) as [b bgood].
  exists (g b).
  rewrite Hyp2.
  assumption.
  destruct (Hyp _ H') as [a0 a0good].
  exists (f a0).
  assumption.
Qed.

Lemma FmFnFmn_aux(m n p : nat): p < m*n ->  p + n < (S m) * n.
Proof.
  rewrite plus_comm.
  apply plus_lt_compat_l.
Qed.

Definition FmFnFmn (m n: nat) : Fin m * Fin n -> Fin (m * n).
Proof.
  revert n ; induction m as [|m IH]; intros n [i1 i2].
  inversion i1.
  elim (zerop (decode_Fin i1)) ; intros H1.
  apply (@code_Fin1 _ (decode_Fin i2)), lt_plus_trans, decode_Fin_inf_n.
  apply (@code_Fin1 _ (decode_Fin (IH _ ((get_cons _ H1), i2)) + n)).
  apply FmFnFmn_aux, decode_Fin_inf_n.
Defined.

Lemma FmnFmFn_aux(m n p : nat): p < S m * n -> n <= p -> p - n < m * n.
Proof.
  intros h1 h2.
  apply (plus_lt_reg_l _ _ n).
  rewrite <- (le_plus_minus _ _ h2).
  apply h1.
Qed.

Definition FmnFmFn (m n: nat) : Fin (m * n) -> Fin m * Fin n.
Proof.
  revert n ; induction m as [|m IH]; intros n i.
  inversion i.
  elim (le_lt_dec n (decode_Fin i)) ; intros a.
  assert (H1 := FmnFmFn_aux _ (decode_Fin_inf_n i) a).
  exact (succ (fst (IH _ (code_Fin1 H1))), snd (IH _ (code_Fin1 H1))).
  exact (first m, code_Fin1 a).
Defined.

Lemma FmnFmFn_ok1 (m n :nat) (i: Fin ((S m)*n))(h1 : decode_Fin i < n): 
  FmnFmFn _ _ i = (first m, code_Fin1 h1).
Proof.
  simpl.
  unfold sumbool_rec, sumbool_rect.
  set (x := le_lt_dec n (decode_Fin i)).
  change (le_lt_dec n (decode_Fin i)) with x.
  elim x ; intros a.
  apply False_rec, (lt_irrefl n), (le_lt_trans _ _ _ a h1).
  f_equal.
  treatFinPure.
Qed.


Lemma FmnFmFn_ok2 (m n :nat) (i: Fin ((S m)*n))(h1 : n <= decode_Fin i): 
  FmnFmFn _ _ i = (succ (fst (FmnFmFn _ _ (code_Fin1 (FmnFmFn_aux _ (decode_Fin_inf_n i) h1)))), 
                        (snd (FmnFmFn _ _ (code_Fin1 (FmnFmFn_aux _ (decode_Fin_inf_n i) h1))))).
Proof.
  simpl.
  unfold sumbool_rec, sumbool_rect.
  set (x := le_lt_dec n (decode_Fin i)).
  change (le_lt_dec n (decode_Fin i)) with x.
  elim x ; intros a.
  do 3 f_equal ; try treatFinPure.
  f_equal ; treatFinPure.
  apply False_rec, (lt_irrefl n), (le_lt_trans _ _ _ h1 a).
Qed.

Lemma FmFnFmn_ok1 (m n :nat) (i1: Fin (S m)) (i2 : Fin n)(h1 : decode_Fin i1 = 0): 
  FmFnFmn (i1, i2) = code_Fin1 (lt_plus_trans  _ _ (m*n) (decode_Fin_inf_n i2)).
Proof.
  simpl.
  unfold sumbool_rec, sumbool_rect.
  elim (zerop (decode_Fin i1)) ; intros a.
  treatFinPure.
  apply False_rec, (lt_irrefl 0).
  rewrite h1 in a.
  assumption.
Qed.
  
Lemma FmFnFmn_ok2 (m n :nat) (i1: Fin (S m)) (i2 : Fin n)(h1 : 0 < decode_Fin i1): 
  FmFnFmn (i1, i2) = code_Fin1 (FmFnFmn_aux _ _ (decode_Fin_inf_n (FmFnFmn (get_cons _ h1, i2)))).
Proof.
  simpl.
  unfold sumbool_rec, sumbool_rect.
  elim (zerop (decode_Fin i1)) ; intros a.
  apply False_rec, (lt_irrefl 0).
  rewrite a in h1.
  assumption.
  assert (h2 : get_cons i1 a = get_cons i1 h1) by treatFinPure.
  rewrite h2.
  reflexivity.
Qed.

Lemma decode_FmFnFmn(m n: nat)(i1 : Fin m)(i2 : Fin n) : 
  decode_Fin (FmFnFmn (i1, i2)) = decode_Fin i1 * n + decode_Fin i2.
Proof.
  induction m as [|m].
  inversion i1.
  elim (zerop (decode_Fin i1)) ; intros H1.
  rewrite FmFnFmn_ok1 ; try assumption.
  rewrite decode_code1_Id, H1.
  rewrite mult_0_l.
  rewrite plus_O_n; reflexivity.
  rewrite (FmFnFmn_ok2 _ _ H1).
  rewrite decode_code1_Id.
  rewrite IHm.
  rewrite (decode_Fin_get_cons _ H1).
  simpl.
  rewrite plus_comm.
  apply plus_assoc.
Qed.

Lemma decode_FmnFmFn(m n: nat)(i : Fin (m*n)) : 
  decode_Fin (fst (FmnFmFn _ _ i)) * n +  decode_Fin (snd (FmnFmFn _ _ i))= decode_Fin i.
Proof.
  revert i ; induction m as [|m] ; intros i.
  inversion i.
  elim (le_lt_dec n (decode_Fin i)) ; intros a.
  rewrite (FmnFmFn_ok2 _ _ a).
  simpl.
  set (i' := code_Fin1 (FmnFmFn_aux m (decode_Fin_inf_n i) a)).
  change (n + decode_Fin (fst (FmnFmFn m n i')) * n + decode_Fin (snd (FmnFmFn m n i')) =
      decode_Fin i).
  rewrite <- plus_assoc.
  rewrite IHm.
  unfold i'.
  rewrite decode_code1_Id.
  apply le_plus_minus_r, a.
  
  rewrite (FmnFmFn_ok1 _ _ a).
  simpl.
  apply decode_code1_Id.
Qed.

Require Import Euclid.
Lemma le_exists (n m : nat) : 0 < m -> m <= n -> exists x, exists y, y < m /\ n = x * m + y.
Proof.
  intros H1 H2.
  destruct (quotient _ H1 n) as [x [y [H3 H4]]].
  exists x, y.
  split ; assumption.
Qed.

Lemma Fin_bij_mult (m n: nat): Bijective (@FmFnFmn m n) (@FmnFmFn m n).
Proof.
  revert n ; induction m as [|m IH] ; intros n ; split ; try intros [i1 i2] ; try intros i.
  inversion i1.
  inversion i.

  destruct (IH n) as [IH' _].
  elim (zerop (decode_Fin i1)); intros a.
  rewrite (FmFnFmn_ok1 _ _ a).
  assert (H1 : decode_Fin (code_Fin1 (lt_plus_trans (decode_Fin i2) n (m * n) (decode_Fin_inf_n i2))) < n).
  rewrite decode_code1_Id.
  apply decode_Fin_inf_n.
  rewrite (FmnFmFn_ok1 _ _ H1).
  rewrite (decode_Fin_0_first _ a).
  f_equal.
  treatFinPure.
  
  rewrite (FmFnFmn_ok2 _ _ a).
  assert (H1 : n <= decode_Fin (code_Fin1 (FmFnFmn_aux m n (decode_Fin_inf_n (FmFnFmn (get_cons i1 a, i2)))))).
  rewrite decode_code1_Id.
  apply le_plus_r.
  rewrite (FmnFmFn_ok2 _ _ H1).
  revert H1.
  set (x := code_Fin1 (FmFnFmn_aux m n (decode_Fin_inf_n (FmFnFmn (get_cons i1 a, i2))))).
  intros H1.
  assert (H2 : FmnFmFn m n (code_Fin1 (FmnFmFn_aux m (decode_Fin_inf_n x) H1)) = (get_cons _ a, i2)).
  rewrite <- IH'.
  f_equal.
  apply decode_Fin_unique.
  unfold x.
  repeat rewrite decode_code1_Id.
  rewrite plus_comm.
  apply minus_plus.
  rewrite H2.
  simpl.
  rewrite <- (decode_Fin_unique _ _ (decode_Fin_get_cons _ a :_ =  decode_Fin (succ _))).
  reflexivity.

  apply decode_Fin_unique.
  rewrite (surjective_pairing (FmnFmFn (S m) n i)).
  rewrite decode_FmFnFmn.
  apply decode_FmnFmFn.
Qed.

Lemma IlistPerm3Cert_list_bij_Fin (n: nat): exists m: nat, exists f: IlistPerm3Cert_list n -> Fin m, 
  exists g: Fin m -> IlistPerm3Cert_list n, Bijective f g.
Proof.
  induction n.
  exists 1.
  exists (fun c: IlistPerm3Cert_list 0 => first 0), (fun f: Fin 1 => tt).
  split; intro.
  destruct t.
  reflexivity.
  apply sym_eq, Fin_first_1.
  destruct IHn as [m0 [f0 [g0 HypB0]]].
  simpl.
  exists ((S n) * (S n) * m0).
  rewrite <- mult_assoc.
  exists (fun x => FmFnFmn ((fst (fst x)) , (FmFnFmn (snd (fst x), (f0 (snd x)))))),
  (fun i => 
    (fst (FmnFmFn _ _ i), fst (FmnFmFn _ _ (snd (FmnFmFn _ _ i))), g0 (snd (FmnFmFn _ _ (snd (FmnFmFn _ _ i)))))).
  destruct (Fin_bij_mult (S n) (S n * m0)) as [Fb1 Fb2].
  destruct (Fin_bij_mult (S n) m0) as [Fb1' Fb2'].
  split.
  intros [[i1 i2] s].
  rewrite Fb1.
  change ((i1, fst (FmnFmFn (S n) m0 (FmFnFmn (i2, f0 s))), g0 (snd (FmnFmFn (S n) m0 (FmFnFmn (i2, f0 s))))) = 
    (i1, i2, s)).
  rewrite Fb1'.
  repeat f_equal.
  apply HypB0.
  
  intros i.
  change (FmFnFmn (fst (FmnFmFn (S n) (S n * m0) i), FmFnFmn
    (fst (FmnFmFn (S n) m0 (snd (FmnFmFn (S n) (S n * m0) i))),
    f0 (g0 (snd (FmnFmFn (S n) m0 (snd (FmnFmFn (S n) (S n * m0) i))))))) = i).
  destruct HypB0 as [Hyp1 Hyp2].
  rewrite Hyp2.
  rewrite <- surjective_pairing.
  rewrite Fb2'.
  rewrite <- surjective_pairing.
  apply Fb2.
Qed.

Theorem IPPJustification: DNE -> IPPIlistPerm3Cert.
Proof.
  intros DNE m'.
  change (IPPGen (IlistPerm3Cert_list m')).
  destruct (IlistPerm3Cert_list_bij_Fin m') as [m [f [g H]]].
  apply Bij_sym in H.
  apply (IPPGen_bij H).
  unfold IPPGen.
  apply DNEImpIPPFin, DNE.
Qed.

(* for emphasis: *)

Corollary IPPJustification': (forall P: Prop, P \/ ~P) -> IPPIlistPerm3Cert.
Proof.
  intro Hyp.
  apply IPPJustification.
  apply ExclMiddleImpDNE.
  assumption.
Qed.


  

  
