(** NatSeg.v Version 0.9.1 April 2016 *)
(** runs under V8.5pl1 *)

(** Celia Picard with contributions by Ralph Matthes, 
    I.R.I.T.,  University of Toulouse and CNRS*)

(**  provides an implementation of the segments of natural numbers
     NatSeg. It also provides various properties 
     and lemmas about it *)

(** this is code that conforms to the description in the article
    " Coinductive graph representation: the problem of embedded lists"
    by the authors *)



Require Export Arith. 
Require Import Utf8.
Require Import Setoid.
Require Import Morphisms.

Set Implicit Arguments.

(* We represent segments of natural numbers. 
   NatSeg n is the Set containing all naturals number lower than n. *)
Definition NatSeg (n: nat):= {m | m < n}.

(* And we define basic operation over these segments *)
Definition elem (n: nat)(f: NatSeg n): nat := proj1_sig f.
Definition proof_lt(n: nat)(f: NatSeg n): elem f < n := proj2_sig f.

Lemma elem_lt_n: forall (n: nat)(ns: NatSeg n), elem ns < n.
Proof.
  intros n [m h].
  assumption.
Qed.

(* We define an equivalence relation over NatSeg. 
   And proove it is one. *)
Inductive natSeg_eq (n: nat) (ns1 ns2: NatSeg n): Prop :=
  is_natSeg_eq: elem ns1 = elem ns2 -> natSeg_eq ns1 ns2.

Infix "~" := natSeg_eq (at level 60).

Lemma natSeg_eq_refl(n: nat): forall (ns: NatSeg n), ns ~ ns.
Proof.
  intros ns.
  apply is_natSeg_eq.
  reflexivity.
Qed.

Lemma natSeg_eq_sym (n: nat): forall (ns1 ns2: NatSeg n), 
  ns1 ~ ns2 -> ns2 ~ ns1.
Proof.
  intros ns1 ns2 [h].
  apply is_natSeg_eq.
  apply (sym_eq h).
Qed.

Lemma natSeg_eq_trans (n: nat): forall (ns1 ns2 ns3: NatSeg n), 
  ns1 ~ ns2 -> ns2 ~ ns3 -> ns1 ~ ns3.
Proof.
  intros ns1 ns2 ns3 [h1] [h2].
  apply is_natSeg_eq.
  apply (trans_eq h1 h2).
Qed.

Add Parametric Relation (n: nat): (NatSeg n) (natSeg_eq (n:= n))
  reflexivity proved by (natSeg_eq_refl(n:= n))
  symmetry proved by (natSeg_eq_sym(n:= n))
  transitivity proved by (natSeg_eq_trans(n:= n))
   as natSeg_eq_Rel.

Add Parametric Morphism (n: nat): (elem(n:= n))
  with signature (natSeg_eq (n:= n)) ==> (eq (A:= nat))
  as elemM.
Proof.
  intros x y [h].
  assumption.
Qed.

Lemma NatSeg_0_empty: forall ns: NatSeg 0, False.
Proof.
  intros [n h].
  inversion h.
Qed.

(* We declare another relation that is more general, but that is not
   really an equivalence relation. *)

Inductive natSeg_eq_gen (n1 n2: nat) (ns1: NatSeg n1) (ns2: NatSeg n2): Prop:=
  is_natSeg_eq_gen: elem ns1 = elem ns2 -> natSeg_eq_gen ns1 ns2.

Infix "~~" := natSeg_eq_gen (at level 60).

Lemma natSeg_eq_gen_refl: forall (n: nat) (ns: NatSeg n), ns ~~ ns.
Proof.
  intros n ns.
  apply is_natSeg_eq_gen.
  reflexivity.
Qed.

Lemma natSeg_eq_gen_sym:
  forall (n1 n2: nat) (ns1: NatSeg n1) (ns2: NatSeg n2), 
  ns1 ~~ ns2 -> ns2 ~~ ns1.
Proof.
  intros n1 n2 ns1 ns2 [h].
  apply is_natSeg_eq_gen.
  apply (sym_eq h).
Qed.
  
Lemma natSeg_eq_gen_trans: forall (n1 n2 n3: nat) 
  (ns1: NatSeg n1) (ns2: NatSeg n2) (ns3: NatSeg n3), 
  ns1 ~~ ns2 -> ns2 ~~ ns3 -> ns1 ~~ ns3 .
Proof.
  intros n1 n2 n3 ns1 ns2 ns3 [h1] [h2].
  apply is_natSeg_eq_gen.
  apply (trans_eq h1 h2).
Qed.

(* Functions that allow to create a NatSeg *)
Definition makeNatSeg (m n: nat) (h: m < n): NatSeg n.
Proof.
  exists m.
  assumption.
Defined.

Program Definition makeNatSeg' (m n: nat) (h: m < n): NatSeg n := m.

(* Transforms a function i so that i 
   makeNatSeg ((n-1) < n) = makeNatSeg ((n'-1) < n') *)
Definition transformI (n n': nat)(i: NatSeg n -> NatSeg n')
  (ns: NatSeg n): NatSeg n'.
Proof.
  destruct n as [|n].
  apply False_rec.
  apply (NatSeg_0_empty ns).
  destruct n' as [|n'].
  apply False_rec.
  apply (NatSeg_0_empty (i ns)).
  elim (eq_nat_dec (elem (i ns)) n'); intros a.
  exact (i (makeNatSeg (lt_n_Sn n))).
  elim (le_lt_eq_dec (elem ns) n (lt_n_Sm_le (elem ns) n (proof_lt ns))); 
  intros b.
  exact (i ns ).
  exact ((makeNatSeg (lt_n_Sn n'))).
Defined.

(* Transforms a function i of type : NatSeg (S n) -> NatSeg n' into a 
   function of type NatSeg n -> NatSeg n', that for all ns: NatSeg n
   is worth (i ns) *)
Definition mkLessI(n n': nat)(i: NatSeg (S n) -> NatSeg n'): 
  NatSeg n -> NatSeg n'.
Proof.
  intros [m h].
  exact (i (makeNatSeg (lt_S m n h))).
Defined.

(* Function that allow to create an element of type (NatSeg n) from an 
   element of (NatSeg (S n)) *)
Definition transfoNs(n: nat)(ns: NatSeg (S n))(h: elem ns < n): NatSeg n :=
  makeNatSeg h.

Program Definition transfoNs' (n: nat)(ns: NatSeg (S n))(h: elem ns < n): 
  NatSeg n := elem ns.

Lemma transfoNseqNs': transfoNs = transfoNs'.
Proof.
  reflexivity.
Qed.

(* Function that allow to create an element of type (NatSeg (S n)) from an 
   element of (NatSeg n) *)
Definition transfoSNs (n: nat) (ns: NatSeg n): NatSeg (S n) :=
  makeNatSeg (lt_S (elem ns) n (proof_lt ns)).

Program Definition transfoSNs' (n: nat) (ns: NatSeg n): NatSeg (S n) :=
  (elem ns).
Next Obligation.
  apply lt_S.
  apply elem_lt_n.
Defined.

Lemma transfoSNseqSNs' (n: nat) (ns: NatSeg n): transfoSNs ns ~ transfoSNs' ns.
Proof.
  apply is_natSeg_eq.
  reflexivity.
Qed.

Definition mkLessI' (n n': nat)(i: NatSeg (S n) -> NatSeg n'): 
  NatSeg n -> NatSeg n' := fun ns => i (transfoSNs ns).

Lemma mkLessIeqI' (n n': nat) (i:  NatSeg (S n) -> NatSeg n')(ns: NatSeg n): 
  mkLessI i ns = mkLessI' i ns.
Proof.
  destruct ns as [m h].
  reflexivity.
Qed.


Add Parametric Morphism (n: nat): (transfoSNs(n:= n))
  with signature (natSeg_eq (n:= n)) ==> (natSeg_eq (n:= S n))
  as transfoNsM.
Proof.
  intros [n1 h1] [n2 h2] [h].
  apply is_natSeg_eq.
  assumption.
Qed.

(* Lemmas to check that transfoNs and transfoSNs are coherent *)
Lemma transfoSNs_transfoNs_Id: 
  forall (n: nat)(ns: NatSeg (S n))(h: elem ns < n), 
  transfoSNs (transfoNs ns h) ~ ns.
Proof.
  intros n ns h.
  apply is_natSeg_eq.
  reflexivity.
Qed.

Lemma elem_transfoSNs_n: forall (n: nat) (ns: NatSeg n), 
  elem (transfoSNs ns) < n.
Proof.
  intros n [m h].
  assumption.
Qed.

Lemma transfoNs_transfoSNs_Id: 
  forall (n: nat)(ns: NatSeg n), 
  transfoNs (transfoSNs ns) (elem_transfoSNs_n ns)  ~ ns.
Proof.
  intros n [m h].
  apply is_natSeg_eq.
  reflexivity.
Qed.

Lemma natSeg_eq_gen_transfo_ns: 
  forall (n: nat) (ns: NatSeg (S n))(h: elem ns < n), 
  elem ns = elem (transfoNs ns h).
Proof.
  reflexivity.
Qed.

Lemma elem_bij: forall (n: nat)(ns1 ns2: NatSeg n), 
  elem ns1 = elem ns2 <-> ns1 ~ ns2.
Proof.
  intros n ns1 ns2 ; 
  split; 
  intros h; 
  [apply is_natSeg_eq | destruct h as [h]];
  assumption.
Qed.

(* We show that makeNatSeg is consistent *)
Lemma makeNatSeg_ns: forall (n: nat)(ns: NatSeg n), 
  ns ~ makeNatSeg (proof_lt ns).
Proof.
  intros n [m h].
  apply is_natSeg_eq.
  reflexivity.
Qed.

Lemma mkLessI_i_Id: 
  forall (n n': nat)(ns: NatSeg (S n))(h: elem ns < n)
  (i: NatSeg (S n) -> NatSeg n')
  (H: forall x y: NatSeg (S n), x ~ y -> i x ~ i y), 
  (i ns) ~~ ((mkLessI i) (transfoNs ns h)).
Proof.
  intros n n' ns h i H .
  apply is_natSeg_eq_gen.
  simpl.
  rewrite elem_bij.
  apply H.
  apply is_natSeg_eq.
  reflexivity.
Qed.

(* Another way to create elements of (NatSeg n) without makeNatSeg is to 
   use 'exist'. We show here its consistency with the definition of 
   natSeg_eq *)
Lemma exist_id: forall (n:nat)(ns: NatSeg n), 
  ns ~ (exist (fun m : nat => m < n) (elem ns) (proof_lt ns)).
Proof.
  intros n ns.
  apply is_natSeg_eq.
  reflexivity.
Qed.

Lemma exist_id2: forall (n:nat)(ns: NatSeg n), 
  ns = (exist (fun m : nat => m < n) (elem ns) (proof_lt ns)).
Proof.
  intros n [m h].
  reflexivity.
Qed.

Lemma exist_id3: forall (n:nat)(ns: NatSeg n)(h: elem ns < n), 
  ns ~ (exist (fun m : nat => m < n) (elem ns) h).
Proof.
  intros n ns h.
  apply is_natSeg_eq.
  reflexivity.
Qed.

Notation Morphism R f := (Proper (R%signature) f).
Definition natSeg_morph (n n': nat) (i: NatSeg n -> NatSeg n'):= 
  Morphism(natSeg_eq(n:= n) ==> natSeg_eq(n:=n')) i.

(* Two lemmas to prove that for a 'good' i, ns1 ~ ns2 <-> i ns1 ~ i ns2 *)
Lemma natSeg_eq_surj: 
  forall (n n': nat) (ns1 ns2: NatSeg n) (i: NatSeg n -> NatSeg n')  
  (Hypi:natSeg_morph i), 
  ns1 ~ ns2 -> (i ns1) ~ (i ns2).
Proof.
  intros n n' ns1 ns2 i Hypi h.
  unfold natSeg_morph in Hypi.
  rewrite h.
  reflexivity.
Qed.
  
Lemma j_i_inj: forall (n n': nat) (ns1 ns2: NatSeg n)
  (i: NatSeg n -> NatSeg n')(j: NatSeg n' -> NatSeg n)
  (Hypj:natSeg_morph j),
  (forall ns: NatSeg n, (j (i ns)) ~ ns) ->
  (i ns1) ~ (i ns2) -> ns1 ~ ns2.
Proof.
  intros n n' ns1 ns2 i j Hypj H1 H2.
  rewrite <- (H1 ns1).
  rewrite <- (H1 ns2).
  unfold natSeg_morph in Hypj.
  rewrite H2.
  reflexivity.
Qed.

Lemma makeNatSeg_ns_natSegeq: forall (n m: nat)(ns: NatSeg n)(h: m < n), 
  elem ns = m <-> ns ~ (makeNatSeg h).
Proof.
  intros n m ns h ; split ; 
  [intros e; apply is_natSeg_eq | intros [e]];
  assumption.
Qed.

Ltac unfold_transformI := 
  unfold transformI ; 
  unfold sumbool_rec; 
  unfold sumbool_rect.

Ltac no_NatSeg_0 ns := apply False_rec; apply (NatSeg_0_empty ns).

(* We want to show that if the composition of two functions i and j 
   gives the identity, then the composition of the transformation of
   these functions with transformI still gives the identity *) 
Lemma transform_Id: forall (n n': nat) 
  (i: NatSeg n -> NatSeg n') (j: NatSeg n' -> NatSeg n)
  (Hypi:natSeg_morph i)(Hypj:natSeg_morph j), 
  (forall ns: NatSeg n, (j (i ns)) ~ ns) ->
  (forall ns': NatSeg n', (i (j ns')) ~ ns') ->
  (forall ns: NatSeg n, 
    (transformI j (transformI i ns)) ~ ns).
Proof.
  intros [|n] n' i j Hypi Hypj Idji Idij ns ;
  unfold natSeg_morph in Hypi;
  unfold natSeg_morph in Hypj.
  no_NatSeg_0 ns.
  destruct n' as [|n'].
  no_NatSeg_0 (i ns).
  unfold_transformI.
  elim (eq_nat_dec (elem (i ns)) n'); intros a.
  elim (eq_nat_dec (elem (j (i (makeNatSeg (lt_n_Sn n))))) n); 
  intros b.
  apply (makeNatSeg_ns_natSegeq (i ns) (lt_n_Sn n')) in a.
  rewrite <- a.
  apply Idji.
  rewrite Idji in b.
  contradiction b ; reflexivity.
  elim (le_lt_eq_dec (elem ns) n); intros b.
  elim (eq_nat_dec (elem (j (i ns))) n); intros c.
  rewrite Idji in c.
  rewrite c in b.
  apply False_rec.
  apply (lt_irrefl n b).
  elim (le_lt_eq_dec (elem (i ns)) n'); intros d.
  apply Idji.
  contradiction d ; reflexivity.
  elim (eq_nat_dec (elem (j (makeNatSeg (lt_n_Sn n')))) n); intros c.
  apply is_natSeg_eq.
  rewrite c.
  apply (sym_eq b).
  elim (le_lt_eq_dec (elem (makeNatSeg (lt_n_Sn n'))) n'); intros d.
  apply False_rec.
  apply (lt_irrefl n' d).
  symmetry.
  apply (makeNatSeg_ns_natSegeq ns (lt_n_Sn n)).
  assumption.
Qed.

Lemma not_NatSeg_eq: forall (n: nat)(ns1 ns2: NatSeg n), 
  not (ns1 ~ ns2) <-> elem ns1 <> elem ns2.
Proof.
  intros n ns1 ns2 ; split;
  intros H1 H2; 
  [ rewrite elem_bij in H2 | rewrite <- elem_bij in H2 ]; 
  apply (H1 H2).
Qed.

Lemma i_not_natSeg_eq: 
  forall (n n': nat)(ns1 ns2: NatSeg n)
  (i: NatSeg n -> NatSeg n')(j: NatSeg n' -> NatSeg n)
  (Hypj: natSeg_morph j), 
  (forall ns: NatSeg n, (j (i ns)) ~ ns) -> not (ns1 ~ ns2) -> 
  not (i ns1 ~ i ns2).
Proof.
  intros n n' ns1 ns2 i j Hypj H1 H2 H3.
  apply (H2 (j_i_inj ns1 ns2 i Hypj H1 H3)).
Qed.

Lemma transformI_lt_n: forall (n n': nat)(ns: NatSeg (S n))
  (i: NatSeg (S n) -> NatSeg (S n'))(j: NatSeg (S n') -> NatSeg (S n))
  (Hypj:natSeg_morph j), (forall ns: NatSeg (S n), (j (i ns)) ~ ns)-> 
  elem ns < n -> elem (transformI i ns) < n'.
Proof.
  intros n n' ns i j Hypj Idji h.
  unfold_transformI.
  elim (eq_nat_dec (elem (i ns)) n'); intros a.
  elim (eq_nat_dec (elem (ns)) (elem (makeNatSeg (lt_n_Sn n)))); intros b.
  rewrite b in h.
  apply False_rec.
  apply (lt_irrefl n h).
  elim (le_lt_eq_dec (elem (i (makeNatSeg (lt_n_Sn n)))) n') ;
  try (intro c).
  assumption.
  rewrite <- a in c.
  rewrite elem_bij in c.
  apply (j_i_inj (makeNatSeg (lt_n_Sn n)) ns i Hypj Idji) in c.
  destruct c as [c].
  rewrite c in b.
  contradiction b.
  reflexivity.
  apply lt_n_Sm_le.
  apply elem_lt_n.
  elim (le_lt_eq_dec (elem ns) n); intro b.
  elim (not_eq (elem (i ns)) n' a); intro c.
  assumption.
  apply False_rec.
  apply (lt_irrefl _ (lt_le_trans _ _ _ c (lt_n_Sm_le _ _ (elem_lt_n (i ns))))).
  rewrite b in h.
  apply False_rec.
  apply (lt_irrefl _ h).
Qed.

(* We define a function that given a function i: NatSeg (S n)-> NatSeg (S n'), 
   returns a function i': NatSeg n-> NatSeg n' that gives the same values as
   i *)
Definition mkLessI_transform(n n': nat) 
  (i: NatSeg (S n)-> NatSeg (S n'))(j: NatSeg (S n') -> NatSeg (S n))
  (Hypj:natSeg_morph j)(HInv: forall ns: NatSeg (S n), (j (i ns)) ~ ns) 
  (ns: NatSeg n): NatSeg n'.
Proof.
  assert (H: elem (transformI i (transfoSNs ns)) < n').
  apply (transformI_lt_n (transfoSNs ns) i Hypj HInv).
  destruct ns as [m h].
  assumption.
  exact (transfoNs (transformI i (transfoSNs ns)) H).
Defined.

Program Definition mkLessI_transform' (n n': nat) 
  (i: NatSeg (S n)-> NatSeg (S n'))(j: NatSeg (S n') -> NatSeg (S n))
  (Hypj:natSeg_morph j)(HInv: forall ns: NatSeg (S n), (j (i ns)) ~ ns) 
  (ns: NatSeg n): NatSeg n':= elem (transformI i (transfoSNs ns)).
Next Obligation.
  fold (transformI i (transfoSNs ns)).
  apply (transformI_lt_n (transfoSNs ns) i Hypj HInv).
  destruct ns as [m h].
  assumption.
Defined.

(* We prove various properties about mkLessI_transform *)
Lemma mkLessI_transform_transformI_id:
  forall (n n': nat) (ns: NatSeg n)
  (i: NatSeg (S n)-> NatSeg (S n'))(j: NatSeg (S n') -> NatSeg (S n))
  (Hypj: natSeg_morph j)(HInv: forall ns: NatSeg (S n), (j (i ns)) ~ ns), 
  transfoSNs (mkLessI_transform i Hypj HInv ns) ~ 
  transformI i (transfoSNs ns).
Proof.
  intros n n' ns i j Hypj HInv.
  apply transfoSNs_transfoNs_Id.
Qed.

Lemma mkLessI_transform_transformI_id2:
  forall (n n': nat) (ns: NatSeg n)
  (i: NatSeg (S n)-> NatSeg (S n'))(j: NatSeg (S n') -> NatSeg (S n))
  (Hypj: natSeg_morph j)(HInv: forall ns: NatSeg (S n), (j (i ns)) ~ ns), 
  mkLessI_transform i Hypj HInv ns ~ 
  transfoNs (transformI i (transfoSNs ns)) 
  (transformI_lt_n (transfoSNs ns) i Hypj HInv (elem_transfoSNs_n ns)).
Proof.
  intros n n' ns i j Hypj HInv.
  apply is_natSeg_eq.
  reflexivity.
Qed.

Lemma mkLessI_transform_transformI_elem_eq:
  forall (n n': nat) (ns: NatSeg n)
  (i: NatSeg (S n)-> NatSeg (S n'))(j: NatSeg (S n') -> NatSeg (S n))
  (Hypj: natSeg_morph j)(HInv: forall ns: NatSeg (S n), (j (i ns)) ~ ns), 
  elem (mkLessI_transform i Hypj HInv ns) = 
  elem (transformI i (transfoSNs ns)).
Proof.
  reflexivity.
Qed.

Add Parametric Morphism (n n': nat)(i: NatSeg n -> NatSeg n')
  (j: NatSeg n' -> NatSeg n)(Hypi: natSeg_morph i): 
  (transformI (n:= n) (n':= n') i)
  with signature (natSeg_eq (n:= n)) ==> (natSeg_eq (n:= n'))
  as transformIM.
Proof.
  intros x y h.
  unfold natSeg_morph in Hypi.
  destruct n as [|n].
  no_NatSeg_0 x.
  destruct n' as [|n'].
  no_NatSeg_0 (i x).
  unfold_transformI.
  elim (eq_nat_dec (elem (i x)) n'); 
  elim (eq_nat_dec (elem (i y)) n'); intros a b ; 
  try reflexivity.
  apply (natSeg_eq_surj Hypi) in h; 
  destruct h as [h].
  rewrite b in h.
  symmetry in h.
  contradiction a.
  apply (natSeg_eq_surj Hypi) in h; 
  destruct h as [h].
  rewrite a in h.
  contradiction b.
  elim (le_lt_eq_dec (elem x) n); elim (le_lt_eq_dec (elem y) n); intros c d.
  apply (natSeg_eq_surj Hypi) in h; 
  destruct h as [h].
  apply (is_natSeg_eq _ _ h).
  rewrite <- c in d.
  destruct h as [h].
  rewrite h in d.
  apply False_rec; apply (lt_irrefl _ d).
  rewrite <- d in c.
  destruct h as [h].
  rewrite h in c.
  apply False_rec; apply (lt_irrefl _ c).
  reflexivity.
Qed.

Lemma transform_bij: forall (n n': nat)(ns ns': NatSeg n)
  (i: NatSeg n -> NatSeg n') (j: NatSeg n' -> NatSeg n)
  (Hypi: natSeg_morph i)(Hypj: natSeg_morph j)
  (Idji: forall ns: NatSeg n, (j (i ns)) ~ ns), 
  transformI i ns ~ transformI i ns' <-> ns ~ ns'.
Proof.
  intros n n' ns ns' i j Hypi Hypj Idji.
  unfold natSeg_morph in Hypi; unfold natSeg_morph in Hypj.
  split.
  destruct n as [|n].
  no_NatSeg_0 ns.
  destruct n' as [|n'].
  no_NatSeg_0 (i ns).
  unfold_transformI.
  elim (eq_nat_dec (elem (i ns)) n'); elim (eq_nat_dec (elem (i ns')) n');
  intros a b.
  intro H.
  rewrite <- a in b.
  rewrite elem_bij in b.
  apply (j_i_inj ns ns' i Hypj Idji b).
  elim (le_lt_eq_dec (elem ns') n ); try (intros c H).
  apply (j_i_inj (makeNatSeg (lt_n_Sn n)) ns' i Hypj Idji) in H.
  rewrite <- H in c.
  apply False_rec.
  apply (lt_irrefl n c).
  rewrite (makeNatSeg_ns_natSegeq ns' (lt_n_Sn n)) in c.
  rewrite <- c in H.
  rewrite H in a.
  contradiction a; reflexivity.
  elim (le_lt_eq_dec (elem ns) n );
  intros c H.
  apply (j_i_inj ns (makeNatSeg (lt_n_Sn n)) i Hypj Idji) in H.
  rewrite H in c.
  apply False_rec. 
  apply (lt_irrefl n c).
  rewrite (makeNatSeg_ns_natSegeq ns (lt_n_Sn n)) in c.
  rewrite <- c in H.
  rewrite <- H in b.
  contradiction b; reflexivity.
  elim (le_lt_eq_dec (elem ns) n); elim (le_lt_eq_dec (elem ns') n); 
  intros c d H.
  apply (j_i_inj ns ns' i Hypj Idji H).
  rewrite H in b.
  contradiction b; reflexivity.
  rewrite <- H in a.
  contradiction a; reflexivity.
  apply is_natSeg_eq.
  rewrite c.
  assumption.
  intros H.
  assert (H1: natSeg_morph (transformI i)).
  exact (transformIM j Hypi).
  unfold natSeg_morph in H1.
  rewrite <- H.
  reflexivity.
Qed.

Lemma transform_exist: 
  forall (n n': nat)(ns: NatSeg n)(h: elem ns < n)
  (i: NatSeg n -> NatSeg n') (j: NatSeg n' -> NatSeg n)
  (Hypi: natSeg_morph i) (Hypj: natSeg_morph j)
  (Idji: forall ns: NatSeg n, (j (i ns)) ~ ns) , 
  transformI i (exist (fun m : nat => m < n) (elem ns) h) ~ transformI i ns.
Proof.
  intros n n' ns h i j Hypi Hypj Idji.
  rewrite (transform_bij (exist (fun m : nat => m < n) (elem ns) h) ns 
  Hypi Hypj Idji).
  symmetry.
  apply (exist_id3 ns h).
Qed.

Lemma mkLessI_transform_id: forall (n n': nat) 
  (i: NatSeg (S n) -> NatSeg (S n')) (j: NatSeg (S n') -> NatSeg (S n))
  (Hypi: natSeg_morph i)(Hypj: natSeg_morph j) 
  (Idji: forall ns: NatSeg (S n), (j (i ns)) ~ ns)
  (Idij: forall ns': NatSeg (S n'), (i (j ns')) ~ ns')(ns: NatSeg n),
  mkLessI_transform j Hypi Idij (mkLessI_transform i Hypj Idji ns) ~ ns.
Proof.
  intros n n' i j Hypi Hypj Idji Idij [m h].
  unfold natSeg_morph in Hypi.
  unfold natSeg_morph in Hypj.
  assert (HMi: natSeg_morph (transformI i)).
  exact (transformIM j Hypi).
  unfold natSeg_morph in HMi.
  assert (HMj: natSeg_morph (transformI j)).
  exact (transformIM i Hypj).
  unfold natSeg_morph in HMj.
  apply is_natSeg_eq.
  rewrite mkLessI_transform_transformI_elem_eq.
  assert (H: (exist (fun m : nat => m < S n')
  (elem (transformI i (exist (fun m : nat => m < S n) m (lt_S m n h))))
  (lt_S (elem 
  (transformI i (exist (fun m : nat => m < S n) m (lt_S m n h)))) n'
  (transformI_lt_n (exist (fun m : nat => m < S n) m (lt_S m n h)) i
  Hypj Idji h))) ~ 
  (transformI i (exist (fun m : nat => m < S n) m (lt_S m n h)))).
  apply is_natSeg_eq.
  reflexivity.
  rewrite H.
  apply (makeNatSeg_ns_natSegeq (transformI j
  (transformI i (exist (fun m : nat => m < S n) m (lt_S m n h)))) 
  (lt_S m n h)).
  apply (transform_Id Hypi Hypj Idji Idij).
Qed.  

Add Parametric Morphism (n n': nat)(i: NatSeg (S n) -> NatSeg (S n'))
  (j: NatSeg (S n') -> NatSeg (S n))
  (Hypi: natSeg_morph i)(Hypj: natSeg_morph j)
  (Idji: (forall ns: NatSeg (S n), (j (i ns)) ~ ns)): 
  (mkLessI_transform (n:= n) (n':= n') i Hypj Idji)
  with signature (natSeg_eq (n:= n)) ==> (natSeg_eq (n:= n'))
  as mkLessI_transformM.
Proof.
  intros x y H.
  unfold mkLessI_transform.
  assert (HMi: natSeg_morph (transformI i)).
  exact (transformIM j Hypi).
  unfold natSeg_morph in HMi.
  unfold natSeg_morph in Hypi.
  apply is_natSeg_eq.
  change (elem (transformI i (transfoSNs x)) =  
  (elem (transformI i (transfoSNs y)))).
  rewrite H.
  reflexivity.
Qed.

(* We show that if there is a bijection between NatSeg n and NatSeg n', then 
   n <= n' *)
Definition NatSeg_inj_aux: forall (n n':nat) 
  (i: NatSeg n -> NatSeg n')(j: NatSeg n' -> NatSeg n)
  (Hypi:natSeg_morph i)
  (Hypj:natSeg_morph j), 
  (forall ns: NatSeg n, j ( i ns) ~ ns) -> 
  (forall ns': NatSeg n', i ( j ns') ~ ns') -> n <= n'.
Proof.
  induction n as [|n IHn]; destruct n' as [|n']; 
  intros i j Hypi Hypj Idji Idij; 
  unfold natSeg_morph in Hypi ; unfold natSeg_morph in Hypj.
  apply le_refl.
  apply le_O_n.
  apply False_rec.
  apply (NatSeg_0_empty (i (makeNatSeg (lt_n_Sn n)))).
  apply (le_n_S n n').
  set (Hypi':= mkLessI_transformM Hypi Hypj Idji ).
  set (Hypj':= mkLessI_transformM Hypj Hypi Idij).
  apply (IHn n' (mkLessI_transform i Hypj Idji) (mkLessI_transform j Hypi Idij)
    Hypi' Hypj' (mkLessI_transform_id Hypi Hypj Idji Idij) 
    (mkLessI_transform_id Hypj Hypi Idij Idji)).
Defined.

(* Finally, we show that if there is a bijection between NatSeg n 
   and NatSeg n', then n = n' *)
Definition NatSeg_inj: forall (n n':nat) 
  (i: NatSeg n -> NatSeg n')(j: NatSeg n' -> NatSeg n)
  (Hypi:natSeg_morph i)
  (Hypj:natSeg_morph j), 
  (forall ns: NatSeg n, j ( i ns) ~ ns) -> 
  (forall ns': NatSeg n', i ( j ns') ~ ns') -> n = n'.
Proof.
  intros n n' i j Hypi Hypj Idji Idij.
  apply (le_antisym n n' 
    (NatSeg_inj_aux Hypi Hypj Idji Idij) (NatSeg_inj_aux Hypj Hypi Idij Idji)).
Defined.
