(*

-> Section 4 in paper
-> Union Types + Null + Intersection Types
-> Nominal types
-> Subtyping Distributivity

*)

Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import Metalib.FSetExtra.
Require Import Metalib.FSetWeakNotin.
Require Import Coq.MSets.MSets.
Require Import Metalib.CoqMSetDecide.
Require Import Lia.
Require equivalence.
Require typing.

Module Typ.

  Export equivalence.

  Definition eq_dec : forall x y : typ, {x = y} + {x <> y}.
  Proof.
    repeat decide equality.
  Defined.

  Definition t := typ.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

End Typ.

(* Automatically unfold Typ.eq *)
Global Arguments Typ.eq /.

(** Finite sets of types *)
Module Import TypSetImpl : FSetExtra.WSfun Typ :=
  FSetExtra.Make Typ.

Notation types :=
  TypSetImpl.t.

(** The [TypSetDecide] module provides the [fsetdec] tactic for
    solving facts about finite sets of atoms. *)

Module Export TypSetDecide := Coq.FSets.FSetDecide.WDecide_fun Typ TypSetImpl.

(** The [TypSetNotin] module provides the [destruct_notin] and
    [solve_notin] for reasoning about non-membership in finite sets of
    atoms, as well as a variety of lemmas about non-membership. *)

Module Export TypSetNotin := FSetWeakNotin.Notin_fun Typ TypSetImpl.

(** Given the [fsetdec] tactic, we typically do not need to refer to
    specific lemmas about finite sets.  However, instantiating
    functors from the FSets library makes a number of setoid rewrites
    available.  These rewrites are crucial to developments since they
    allow us to replace a set with an extensionally equal set (see the
    [Equal] relation on finite sets) in propositions about finite
    sets. *)

Module TypSetFacts := FSetFacts.WFacts_fun Typ TypSetImpl.
Module TypSetProperties := FSetProperties.WProperties_fun Typ TypSetImpl.

Export TypSetFacts.
Export Typ.
(******************************************************************************)
Notation "{{ }}" := empty (at level 0, only parsing).
Notation "{{ x }}" := (singleton x) (at level 0, only parsing).

Notation "E \union F" := (union E F)
  (at level 65, right associativity, format "E \union '/' F").
Notation "E \u F" := (E \union F).

Notation "E \inter F" := (inter E F)
                      (at level 65, right associativity, format "E  \inter  '/' F").

Notation "PG ||= A <: B" := (declarative_subtyping PG A B) (at level 80).

#[export] Hint Extern 1 => match goal with
                 | H: wft nil (t_prim _) |- _ => inverts H
                           end : FalseHd.

#[export] Hint Resolve FSetDecideTestCases.test_In_singleton union_2 union_3 inter_3 : core.

Local Ltac inter_inv H := forwards : inter_1 H; forwards : inter_2 H; clear H.

Local Ltac union_inv H := forwards [?|?]: union_1 H; clear H.
Local Ltac single_inv H := let Heq := fresh "Heq" in
                           forwards Heq: singleton_1 H; try injects Heq; subst; clear H.

#[export] Hint Extern 1 => match goal with
                 | H : In _ empty |- _ => false; applys notin_empty_1 H
                 | H : In _ (singleton _ ) |- _ => single_inv H; fail
                 end : FalseHd.

(****************************************)
(**********  FindSubtypes    ************)
(****************************************)

(* issupertype returns true if A <: B under l *)
(* and false otherwise *)
(* It works for the transitive closure *)
(* It works for supertypes having multiple unrelated subtypes *)
Function issupertype (l: envp) (A B: var) : bool :=
    match l with
    | nil => false
    | (i, t) :: xs => match A==i with
                      | left _ => match t with
                                  | t_top => false
                                  | t_prim t' => match B==t' with
                                                 | left _ => true
                                                 | right _ => issupertype xs t' B
                                                 end
                                  | _ => false
                                  end
                     | right _ => issupertype xs A B
                    end
    end.

Function get_all_subtypes (l : envp) (A : var) : types :=
  match l with
  | nil => {{ }}
  | (i, t) :: xs => match (issupertype l i A) with
                      | true  => {{ t_prim i }} \union (get_all_subtypes xs A)
                      | false => get_all_subtypes xs A
                      end
  end.

Function all_prim_types (l : envp) : types :=
  match l with
  | nil => {{ }}
  | (i, t) :: xs => {{ t_prim i }} \union (all_prim_types xs)
  end.

(* Find Least Ordinary Subtypes (LOS) *)

(* Non-arrow least ordinary subtypes. Function types are handled
   separately by ArrowRanges so two arrows can be disjoint. *)
Fixpoint FindSubtypes (PG:envp) (A: typ) : types :=
    match A with
    | t_top         =>  {{ t_int }} \u {{ t_unit }} \u (all_prim_types PG)
    | t_bot         => {{ }}
    | t_arrow A1 B1 => {{ }}
    | t_union A1 B1 => (FindSubtypes PG A1) \u (FindSubtypes PG B1)
    | t_and A1 B1   => (FindSubtypes PG A1) \inter (FindSubtypes PG B1)
    | t_prim i      => {{ t_prim i }} \u (get_all_subtypes PG i)
    | _ => {{ A }}
    end.

(* First-order ordinary ranges of the function part. Nested arrow
   ranges are decided by RangeDisj (peeling FunRange), not by this
   finite set — listing every ordinary arrow would be infinite. *)
Fixpoint ArrowRanges (PG:envp) (A: typ) : types :=
    match A with
    | t_top         => FindSubtypes PG t_top
    | t_bot         => {{ }}
    | t_int         => {{ }}
    | t_unit        => {{ }}
    | t_prim _      => {{ }}
    | t_arrow _ B   => FindSubtypes PG B
    | t_union A1 B1 => (ArrowRanges PG A1) \u (ArrowRanges PG B1)
    | t_and A1 B1   => (ArrowRanges PG A1) \inter (ArrowRanges PG B1)
    end.

(* Range of the function component. Empty sides are dropped so
   FunRange (Int ∨ (A→B)) = B, not ⊥∨B. *)
Fixpoint FunRange (A: typ) : typ :=
    match A with
    | t_top         => t_top
    | t_arrow _ B   => B
    | t_union A1 B1 =>
        match FunRange A1, FunRange B1 with
        | t_bot, R => R
        | R, t_bot => R
        | R1, R2 => t_union R1 R2
        end
    | t_and A1 B1   =>
        match FunRange A1, FunRange B1 with
        | t_bot, _ => t_bot
        | _, t_bot => t_bot
        | R1, R2 => t_and R1 R2
        end
    | _             => t_bot
    end.

(***********************************)
(****  FindSubtypes Properties  ****)
(***********************************)

Lemma is_supertype_in_domain : forall G n A,
  issupertype G n A = true -> n `in` dom G.
Proof with solve_false.
  introv Heq.
  induction G...
  destruct a.
  unfold issupertype in Heq.
  case_if.
  destruct t0...
  - case_if; subst; rewrite dom_cons; eauto.
  - rewrite dom_cons. forwards* : IHG Heq.
Qed.

Lemma is_supertype_weakening : forall p G n1 n2,
  issupertype G n1 n2 = true ->
  okenvp (p :: G) ->
  issupertype (p :: G) n1 n2 = true.
Proof.
  introv Hsup Ok.
  destruct p.
  unfolds.
  case_if.
  - forwards:  is_supertype_in_domain Hsup.
    apply okenvp_uniq in Ok. inverts Ok.
    subst. solve_false.
  - assumption.
Qed.

Lemma prim_type_in_all_prim_types : forall (A : typ) PG,
  In A (all_prim_types PG) ->
  exists i, A = t_prim i.
Proof with solve_false.
  introv H.
  induction PG; simpl in H; solve_false.
  - destruct a. repeat case_if...
    union_inv H.
    + single_inv H0. now eauto.
    + applys~ IHPG.
Qed.

Lemma prim_type_in_all_subtypes : forall (A : typ) PG n,
  In A (get_all_subtypes PG n) ->
  exists i, A = t_prim i.
Proof with solve_false.
  introv H.
  induction PG; simpl in H; solve_false.
  - destruct a. repeat case_if...
    + destruct* t0...
      case_if; subst...
      * union_inv H; subst.
        ** single_inv H0; subst*.
        ** applys~ IHPG.
      * union_inv H; subst.
        ** single_inv H0. now eauto.
        ** applys~ IHPG.
    + applys~ IHPG.
Qed.

Local Ltac prim_inv_1 H := let Heq := fresh "Heq" in
                           forwards (?&Heq): prim_type_in_all_prim_types H; try injects Heq; subst.

Local Ltac prim_inv_2 H := let Heq := fresh "Heq" in
                           forwards (?&Heq): prim_type_in_all_subtypes H; try injects Heq; subst.

Local Ltac auto_in_inv :=
  match goal with
  | H: In _ _ |- _ => union_inv H + single_inv H + inter_inv H
                      + prim_inv_1 H + prim_inv_2 H; clear H
  end.

Lemma arrow_not_in_findsubtypes : forall PG A B C,
    In (t_arrow A B) (FindSubtypes PG C) -> False.
Proof with solve_false.
  introv H.
  induction C; simpl in H; repeat auto_in_inv; solve_false; eauto.
Qed.

Local Ltac arrow_inv H := let Heq := fresh "Heq" in
                          forwards Heq: arrow_not_in_findsubtypes H; try injects Heq; subst.

Lemma prim_in_all : forall PG i,
    wft PG (t_prim i) -> In (t_prim i) (all_prim_types PG).
Proof.
  introv Wf.
  induction PG; simple.
  - inverts Wf. solve_false.
  - destruct a. case_eq (a==i); intros; subst*.
    apply wft_strenthen_prim in Wf; eauto.
Qed.

Lemma get_all_subtypes_subset : forall PG i j A,
    (get_all_subtypes PG i) [<=] (get_all_subtypes ((j, A) :: PG) i).
Proof.
  introv. gen i j.
  induction PG; intros; eauto.
  now simpl; repeat case_if; fsetdec.
  destruct a; simpl; repeat case_if; fsetdec.
Qed.

Lemma prim_in_subtypes_issuprtype: forall i PG j,
    In (t_prim i) (get_all_subtypes PG j) -> okenvp PG ->
    issupertype PG i j = true.
Proof with solve_false.
  introv Hin Ok.
  induction PG; simpl in Hin...
  destruct a.
  repeat case_if.
  - destruct t0; simpl in C...
    case_if; subst.
    + auto_in_inv.
      * auto_in_inv. simpl; repeat case_if; eauto.
      * forwards: IHPG H. inverts* Ok. rewrite* is_supertype_weakening.
    + simpl. repeat case_if; eauto.
      union_inv Hin.
      * false. apply C2. auto_in_inv...
      * applys~ IHPG. inverts~ Ok.
  - rewrite* is_supertype_weakening.
Qed.

Lemma prim_in_subtype : forall PG i j,
    declarative_subtyping PG (t_prim i) (t_prim j) ->
    In (t_prim i) (singleton (t_prim j) \u get_all_subtypes PG j).
Proof.
  introv Sub.
  apply dsub2asub in Sub. gen i j.
  induction PG; intros; inverts Sub; solve_false.
  - eauto.
  - forwards: IHPG H5.
    lets: get_all_subtypes_subset PG j i0 A.
    fsetdec.
  - forwards: IHPG H4.
    union_inv H.
    + auto_in_inv. simpl.
      case_eq (i==i); solve_false; intros.
      case_eq (j0==j0); solve_false; intros.
      eauto.
    + forwards* : prim_in_subtypes_issuprtype H0.
      simpl.
      repeat (case_if; solve_false; intros; eauto).
Qed.


Lemma okenvp_wft_inv : forall PG i A,
    okenvp ((i, A) :: PG) -> wft PG A.
Proof.
  introv Ok. inverts~ Ok.
Qed.

#[export] Hint Resolve okenvp_wft_inv : core.

Lemma in_prim_types_wft : forall PG A,
    okenvp PG ->
    In A (all_prim_types PG) -> wft PG A.
Proof.
  introv okp HIn. gen A.
  induction PG; intros; simpl in HIn.
  - solve_false.
  - destruct a. union_inv HIn.
    + auto_in_inv. now eauto.
    + eauto using wf_typ_weakening.
Qed.


Lemma get_all_subtypes_subset_all_prim : forall PG i,
    (get_all_subtypes PG i) [<=] (all_prim_types PG).
Proof.
  intros. induction PG; simpl; try fsetdec.
  - destruct a.
    1: repeat case_if.
    all: fsetdec.
Qed.

Lemma wft_prim_in_all_prim : forall PG i,
    wft PG (t_prim i) -> In (t_prim i) (all_prim_types PG).
Proof.
  introv Wf.
  inductions Wf.
  induction PG; solve_false.
  destruct a. forwards [ (?&?) | ? ]: binds_cons_1 H.
  - subst. simpl. eauto.
  - simpl. forwards* : IHPG H0.
Qed.

Lemma in_get_all_subtypes_wft : forall PG A i,
    okenvp PG ->
    In A (get_all_subtypes PG i) -> wft PG A.
Proof.
  introv okp HIn.
  lets HIn': get_all_subtypes_subset_all_prim HIn.
  lets~ : in_prim_types_wft PG A HIn'.
Qed.

#[export] Hint Immediate in_prim_types_wft in_get_all_subtypes_wft : core.


Lemma in_findsubtypes_wft : forall PG A B,
    okenvp PG ->
    In A (FindSubtypes PG B) -> wft PG B -> wft PG A.
Proof.
  introv okp HIn. gen A B.
  induction PG; intros.
  - induction B; simpl in HIn.
    all: try solve [repeat auto_in_inv; solve_false; eauto].
  - destruct a. induction B; simpl in HIn.
    all: try solve [repeat auto_in_inv; solve_false; eauto using wf_typ_weakening].
    repeat union_inv HIn.
    + auto_in_inv. eauto.
    + repeat union_inv H0; try solve [auto_in_inv; eauto].
      repeat union_inv H1; try solve [auto_in_inv; eauto].
      repeat union_inv H0; try solve [auto_in_inv; eauto].
      applys* wf_typ_weakening.
      apply okenvp_inv in okp.
      applys* in_prim_types_wft.
Qed.

#[export] Hint Immediate in_findsubtypes_wft : core.

Lemma wft_prim_inv : forall i n A PG,
  wft ((i, A) :: PG) (t_prim n) -> i=n \/ wft PG (t_prim n).
Proof.
  introv Wf.
  lets: wft_strenthen_prim Wf.
  case_eq (i==n); intros; subst*.
Qed.


Lemma FindSubtypes_subset_prim : forall PG n,
    wft PG (t_prim n) -> FindSubtypes PG (t_prim n) [<=] FindSubtypes PG t_top.
Proof.
  introv Wf. gen n.
  induction PG; intros.
  - solve_false.
  - lets: get_all_subtypes_subset_all_prim PG n.
    destruct a. forwards [?|?]: wft_prim_inv Wf; subst.
    + simpl. repeat case_if. destruct t0; solve_false. all: fsetdec.
    + forwards ~: wft_prim_in_all_prim PG n.
      simpl. repeat case_if. all: fsetdec.
Qed.

Lemma FindSubtypes_subset : forall PG A,
    wft PG A -> FindSubtypes PG A  [<=]  FindSubtypes PG t_top.
Proof.
  introv Wf.
  induction A; try solve [simpl; fsetdec].
  - inverts_all_wft.
    remember (FindSubtypes PG t_top) as Set1.
    forwards~ : IHA1. forwards~ : IHA2.
    simpl. fsetdec.
  - inverts_all_wft.
    remember (FindSubtypes PG t_top) as Set1.
    forwards~ : IHA1. forwards~ : IHA2.
    simpl. fsetdec.
  - applys~ FindSubtypes_subset_prim.
Qed.
#[export] Hint Resolve DS_refl DS_top DS_bot DS_arrow DS_or DS_orl DS_orr : core.


Lemma is_supertype_sound : forall G n1 n2,
  issupertype G n1 n2 = true ->
  okenvp G ->
  declarative_subtyping G (t_prim n1) (t_prim n2).
Proof.
  introv Heq Ok. gen n1 n2.
  induction G; intros; simpl in Heq; solve_false.
  destruct a. repeat case_if.
  - destruct t0; simpl; subst; solve_false.
    case_if; subst.
    + applys* DS_prim.
    + forwards*: IHG.
      applys DS_trans. now applys* DS_prim.
      applys dsub2asub. applys~ algo_sub_weakening. applys~ dsub2asub.
  - forwards*: IHG.
    applys dsub2asub. applys~ algo_sub_weakening. applys~ dsub2asub.
Qed.

Lemma issupertype_wft : forall PG i n,
    issupertype PG i n = true -> okenvp PG -> wft PG (t_prim n).
Proof.
  intros.
  forwards~: is_supertype_sound H.
  apply dsub2asub in H1. applys* algo_sub_wft.
Qed.

Lemma in_get_all_subtypes_wft_prim : forall B PG n,
    In B (get_all_subtypes PG n) -> okenvp PG -> wft PG (t_prim n).
Proof.
  introv HIn Ok. gen B.
  induction PG; intros; simpl in HIn; solve_false.
  destruct a. case_eq (n==a); intros; subst*.
  applys~ wf_typ_weakening.
  repeat case_if.
  - destruct t0; simpl; solve_false.
    case_if; intros; subst.
    + inverts~ Ok.
    + inverts~ Ok. applys* issupertype_wft.
  - apply okenvp_inv in Ok.
    forwards~ : IHPG Ok HIn.
Qed.

(******************************************************************************)
Import typing. (* for the definition of Ord *)

#[export] Hint Extern 1 => match goal with
                 | H: typing.Ord _ |- _ => inverts H; fail
end : FalseHd.

Lemma sub_and : forall PG A B C,
    declarative_subtyping PG A (t_and B C) ->
    (declarative_subtyping PG A B) /\ (declarative_subtyping PG A C).
Proof.
  intros.
  forwards Sub: H. apply dsub2asub in Sub. apply algo_sub_wft in Sub. destruct_conj.
  split; applys DS_trans H.
  applys* DS_andl.
  applys* DS_andr.
Qed.

(* Completeness of LOS *)

(* Lemma 20 — non-arrow ordinary types appear in FindSubtypes.
   Ordinary arrows are handled by FunRange / RangeDisj. *)

Lemma ord_in_findsubtypes : forall A PG B,
    Ord A -> declarative_subtyping PG A B ->
    (forall t1 t2, A <> t_arrow t1 t2) ->
    In A (FindSubtypes PG B).
Proof with destruct_conj; subst; simpl; auto; solve_false.
  introv Ord Sub NArr. gen PG B.
  induction Ord; intros...
  - (* int *)
    induction B...
    + apply ord_sub_or_unique in Sub...
      destruct Sub as [S|S].
      * apply union_2. apply IHB1; auto.
      * apply union_3. apply IHB2; auto.
    + apply sub_and in Sub. destruct Sub.
      apply inter_3; auto.
  - (* unit — arrow case is discharged by NArr *)
    induction B...
    + apply ord_sub_or_unique in Sub...
      destruct Sub as [S|S].
      * apply union_2. apply IHB1; auto.
      * apply union_3. apply IHB2; auto.
    + apply sub_and in Sub. destruct Sub.
      apply inter_3; auto.
  - (* prim *)
    induction B...
    + assert (wft PG (t_prim i)).
      { apply dsub2asub in Sub. apply algo_sub_wft in Sub. tauto. }
      eauto using prim_in_all.
    + apply ord_sub_or_unique in Sub...
      destruct Sub as [S|S].
      * apply union_2. apply IHB1; auto.
      * apply union_3. apply IHB2; auto.
    + apply sub_and in Sub. destruct Sub.
      apply inter_3; auto.
    + apply prim_in_subtype in Sub. auto.
Qed.

(* Soundness of LOS *)

(* Lemma 19 *)

Lemma elem_in_findsubtypes_sub : forall PG A B,
    okenvp PG ->
    wft PG A ->
    wft PG B ->
    In B (FindSubtypes PG A) -> declarative_subtyping PG B A.
Proof.
  introv Ok Wf1 Wf2 HIn.
  induction A.
  all: try solve [simpl in HIn; solve_false; auto_in_inv; eauto].
  - inverts_all_wft. simpl in HIn. union_inv HIn.
    now forwards* :IHA1; applys* DS_trans.
    now forwards* :IHA2; applys* DS_trans.
  - inverts_all_wft. simpl in HIn. inter_inv HIn.
    forwards* :IHA1. forwards* :IHA2.
    applys~ DS_and.
  - simpl in HIn. union_inv HIn.
    + auto_in_inv. eauto.
    + gen n. induction PG; intros; solve_false.
      destruct a.
      simpl in H. repeat case_if.
      * destruct t0; solve_false.
        assert (declarative_subtyping PG (t_prim n0) (t_prim n)). {
          case_if; subst; eauto using is_supertype_sound.
        }
        repeat union_inv H.
        ** auto_in_inv; eauto.
           applys DS_trans. applys~ DS_prim.
           applys dsub2asub. applys~ algo_sub_weakening. applys~ dsub2asub.
        ** applys dsub2asub. applys~ algo_sub_weakening. applys dsub2asub.
           applys* IHPG.
           apply in_get_all_subtypes_wft in H1; auto.
           apply okenvp_inv in Ok; auto.
           apply dsub2asub in H0. applys~ algo_sub_wft.
      * applys dsub2asub. applys~ algo_sub_weakening. applys dsub2asub.
        applys* IHPG.
        apply in_get_all_subtypes_wft in H; auto.
        apply okenvp_inv in Ok; auto.
        forwards [?|?]: wft_prim_inv Wf1; subst*.
        applys* in_get_all_subtypes_wft_prim.
Qed.

(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

Definition DisjSpec PG A B := forall C, Ord C -> not (declarative_subtyping PG C (t_and A B)).
Notation "PG |- A *s B" := (DisjSpec PG A B) (at level 80).

(****************************************)
(**********  Dijoint Algo    ************)
(****************************************)

(* Algorithmic disjointness (Theorem 18): non-arrow LOS of A∧B
   is empty, and function-range components are disjoint.
   FunRange peels one arrow layer (range rule). *)
Inductive DisjAlgo (PG:envp) : typ -> typ -> Prop :=
| da_nfun_l : forall A B,
    FindSubtypes PG (t_and A B) [=] empty ->
    FunRange A = t_bot ->
    DisjAlgo PG A B
| da_nfun_r : forall A B,
    FindSubtypes PG (t_and A B) [=] empty ->
    FunRange B = t_bot ->
    DisjAlgo PG A B
| da_peel : forall A B,
    FindSubtypes PG (t_and A B) [=] empty ->
    DisjAlgo PG (FunRange A) (FunRange B) ->
    DisjAlgo PG A B.

Notation "PG |- A *a B" := (DisjAlgo PG A B) (at level 80).

(* Old Thm 18 used FindSubtypes (A∧B) = ∅ with ⊤→⊥ ∈ LOS of every
   arrow. Official statement is now *a ⇔ *s1 via FunRange peeling. *)
#[export] Hint Constructors DisjAlgo : core.

Lemma arrowranges_and : forall PG A B,
  ArrowRanges PG (t_and A B) [=] (ArrowRanges PG A \inter ArrowRanges PG B).
Proof.
  intros. simpl. fsetdec.
Qed.

Lemma wft_funrange : forall PG A, wft PG A -> wft PG (FunRange A).
Proof.
  induction 1; simpl; auto.
  - destruct (FunRange A) eqn:?; destruct (FunRange B) eqn:?; auto.
  - destruct (FunRange A) eqn:?; destruct (FunRange B) eqn:?; auto.
Qed.

Lemma in_fs_ord : forall PG A C,
  In C (FindSubtypes PG A) -> Ord C.
Proof.
  intros PG A C HIn.
  induction A; simpl in HIn; repeat auto_in_inv; try constructor; auto; solve_false.
Qed.

Lemma ord_sub_bot_false : forall PG C,
  Ord C -> declarative_subtyping PG C t_bot -> False.
Proof.
  introv OrdC Sub.
  induction OrdC; eauto using int_sub_bot_false, arrow_sub_bot_false,
    null_sub_bot_false, prim_sub_bot_false.
Qed.

Lemma funrange_union_eq : forall A B,
  FunRange A <> t_bot ->
  (FunRange B = t_bot /\ FunRange (t_union A B) = FunRange A) \/
  (FunRange B <> t_bot /\ FunRange (t_union A B) = t_union (FunRange A) (FunRange B)).
Proof.
  intros A B NA.
  destruct (Typ.eq_dec (FunRange B) t_bot) as [EB|EB].
  - left. split; auto.
    simpl. destruct (FunRange A) eqn:?; destruct (FunRange B) eqn:?;
      try congruence; reflexivity.
  - right. split; auto.
    simpl. destruct (FunRange A) eqn:?; destruct (FunRange B) eqn:?;
      try congruence; reflexivity.
Qed.

Lemma funrange_and_eq : forall A B,
  FunRange A <> t_bot -> FunRange B <> t_bot ->
  FunRange (t_and A B) = t_and (FunRange A) (FunRange B).
Proof.
  intros A B NA NB.
  simpl. destruct (FunRange A) eqn:?; destruct (FunRange B) eqn:?;
    try congruence; reflexivity.
Qed.

Lemma sub_funrange_union_l : forall PG C A B,
  Ord C -> okenvp PG -> wft PG A -> wft PG B ->
  declarative_subtyping PG C (FunRange A) ->
  declarative_subtyping PG C (FunRange (t_union A B)).
Proof.
  introv OrdC Ok WfA WfB Sub.
  destruct (Typ.eq_dec (FunRange A) t_bot) as [EA|EA].
  - exfalso. rewrite EA in Sub. eapply ord_sub_bot_false; eauto.
  - destruct (funrange_union_eq A B EA) as [[EB Eq]|[_ Eq]].
    + rewrite Eq. auto.
    + rewrite Eq. apply DS_trans with (B:=FunRange A); auto.
      apply DS_orl; auto using wft_funrange.
Qed.

Lemma sub_funrange_union_r : forall PG C A B,
  Ord C -> okenvp PG -> wft PG A -> wft PG B ->
  declarative_subtyping PG C (FunRange B) ->
  declarative_subtyping PG C (FunRange (t_union A B)).
Proof.
  introv OrdC Ok WfA WfB Sub.
  destruct (Typ.eq_dec (FunRange B) t_bot) as [EB|EB].
  - exfalso. rewrite EB in Sub. eapply ord_sub_bot_false; eauto.
  - destruct (Typ.eq_dec (FunRange A) t_bot) as [EA|EA].
    + assert (Eq: FunRange (t_union A B) = FunRange B).
      { simpl. destruct (FunRange A) eqn:?; destruct (FunRange B) eqn:?;
        try congruence; reflexivity. }
      rewrite Eq. auto.
    + destruct (funrange_union_eq A B EA) as [[EBbot _]|[_ Eq]].
      * congruence.
      * rewrite Eq. apply DS_trans with (B:=FunRange B); auto.
        apply DS_orr; auto using wft_funrange.
Qed.

Lemma sub_funrange_and : forall PG C A B,
  Ord C -> okenvp PG -> wft PG A -> wft PG B ->
  declarative_subtyping PG C (FunRange A) ->
  declarative_subtyping PG C (FunRange B) ->
  declarative_subtyping PG C (FunRange (t_and A B)).
Proof.
  introv OrdC Ok WfA WfB SubA SubB.
  destruct (Typ.eq_dec (FunRange A) t_bot) as [EA|EA].
  - exfalso. rewrite EA in SubA. eapply ord_sub_bot_false; eauto.
  - destruct (Typ.eq_dec (FunRange B) t_bot) as [EB|EB].
    + exfalso. rewrite EB in SubB. eapply ord_sub_bot_false; eauto.
    + rewrite (funrange_and_eq A B EA EB). apply DS_and; auto.
Qed.

Lemma arrow_sub_funrange : forall PG t1 t2 A,
  Ord t2 ->
  okenvp PG -> wft PG A ->
  declarative_subtyping PG (t_arrow t1 t2) A ->
  declarative_subtyping PG t2 (FunRange A).
Proof.
  introv Ord2 Ok WfA Sub. gen t1 t2.
  induction A; intros.
  - exfalso. eapply arrow_sub_int_false; eauto.
  - simpl. apply DS_top; auto.
    apply dsub2asub in Sub. apply algo_sub_wft in Sub.
    destruct Sub as [_ [WfArr _]]. inverts WfArr. auto.
  - exfalso. eapply arrow_sub_bot_false; eauto.
  - simpl. apply dsub2asub in Sub. apply algo_sub_arrow_inv in Sub.
    destruct Sub. apply dsub2asub. auto.
  - inverts WfA.
    apply ord_sub_or_unique with (A:=t_arrow t1 t2) in Sub; auto.
    destruct Sub as [S|S].
    + apply sub_funrange_union_l; auto. eapply IHA1; eauto.
    + apply sub_funrange_union_r; auto. eapply IHA2; eauto.
  - inverts WfA. apply sub_and in Sub. destruct Sub.
    apply sub_funrange_and; auto; (eapply IHA1 || eapply IHA2); eauto.
  - exfalso. eapply arrow_sub_null_false; eauto.
  - exfalso. eapply arrow_sub_prim_false; eauto.
Qed.

Lemma fs_empty_no_nona : forall PG A B C,
  okenvp PG -> wft PG A -> wft PG B ->
  FindSubtypes PG (t_and A B) [=] empty ->
  Ord C -> declarative_subtyping PG C (t_and A B) ->
  exists t1 t2, C = t_arrow t1 t2.
Proof.
  introv Ok WfA WfB Hfs OrdC Sub.
  induction OrdC.
  - assert (In t_int (FindSubtypes PG (t_and A B))).
    { apply ord_in_findsubtypes; auto; intros; discriminate. }
    rewrite Hfs in H. solve_false.
  - exists t1 t2. reflexivity.
  - assert (In t_unit (FindSubtypes PG (t_and A B))).
    { apply ord_in_findsubtypes; auto; intros; discriminate. }
    rewrite Hfs in H. solve_false.
  - assert (In (t_prim i) (FindSubtypes PG (t_and A B))).
    { apply ord_in_findsubtypes; auto; intros; discriminate. }
    rewrite Hfs in H. solve_false.
Qed.

(* Theorem 18 (a) *)

Lemma Disj_soundness : forall PG A B,
  okenvp PG -> wft PG A -> wft PG B ->
  PG |- A *a B -> PG |- A *s B.
Proof.
  intros PG A B Ok WfA WfB DA.
  unfold DisjSpec. unfold not.
  induction DA; intros C OrdC Sub.
  - assert (Hex: exists t1 t2, C = t_arrow t1 t2)
      by (apply fs_empty_no_nona with (PG:=PG) (A:=A) (B:=B); auto).
    destruct Hex as (t1&t2&Heq); subst.
    inverts OrdC. apply sub_and in Sub. destruct Sub.
    forwards SubR: arrow_sub_funrange t1 t2 A; eauto.
    rewrite H0 in SubR. eapply ord_sub_bot_false; eauto.
  - assert (Hex: exists t1 t2, C = t_arrow t1 t2)
      by (apply fs_empty_no_nona with (PG:=PG) (A:=A) (B:=B); auto).
    destruct Hex as (t1&t2&Heq); subst.
    inverts OrdC. apply sub_and in Sub. destruct Sub.
    forwards SubR: arrow_sub_funrange t1 t2 B; eauto.
    rewrite H0 in SubR. eapply ord_sub_bot_false; eauto.
  - assert (Hex: exists t1 t2, C = t_arrow t1 t2)
      by (apply fs_empty_no_nona with (PG:=PG) (A:=A) (B:=B); auto).
    destruct Hex as (t1&t2&Heq); subst.
    inverts OrdC. apply sub_and in Sub. destruct Sub as [SubA SubB].
    eapply IHDA; eauto using wft_funrange.
    apply DS_and; eauto using arrow_sub_funrange.
Qed.

Lemma fs_and_empty_from_spec : forall PG A B,
  okenvp PG -> wft PG A -> wft PG B ->
  PG |- A *s B ->
  FindSubtypes PG (t_and A B) [=] empty.
Proof.
  introv OK WFT1 WFT2 Disj.
  unfold DisjSpec in Disj.
  apply TypSetProperties.empty_is_empty_1.
  intros D HIn.
  apply (Disj D).
  - apply in_fs_ord with (A:=t_and A B) (PG:=PG). exact HIn.
  - apply elem_in_findsubtypes_sub with (A:=t_and A B); auto.
    apply in_findsubtypes_wft with (B:=t_and A B); auto.
Qed.

Fixpoint tsize (A:typ) : nat :=
  match A with
  | t_arrow A B | t_union A B | t_and A B => S (tsize A + tsize B)
  | _ => 1
  end.

Lemma tsize_pos : forall A, 1 <= tsize A.
Proof.
  induction A; simpl; auto; lia.
Qed.

Lemma tsize_funrange : forall A, tsize (FunRange A) <= tsize A.
Proof.
  induction A; simpl.
  - lia.
  - lia.
  - lia.
  - lia.
  - destruct (FunRange A1); destruct (FunRange A2); simpl in *;
      pose proof (tsize_pos A1); pose proof (tsize_pos A2); lia.
  - destruct (FunRange A1); destruct (FunRange A2); simpl in *;
      pose proof (tsize_pos A1); pose proof (tsize_pos A2); lia.
  - lia.
  - lia.
Qed.

Lemma int_sub_toplike : forall PG A,
  okenvp PG -> wft PG A ->
  FunRange A <> t_bot ->
  tsize (FunRange A) >= tsize A ->
  declarative_subtyping PG t_int A.
Proof.
  introv Ok WfA Nz Ge.
  induction A.
  - (* int: FR = bot *) simpl in Nz. congruence.
  - (* top *) apply DS_top; auto.
  - (* bot *) simpl in Nz. congruence.
  - (* arrow: size strictly decreases *)
    pose proof (tsize_funrange A2). simpl in Ge. lia.
  - (* union *)
    inverts WfA.
    destruct (Typ.eq_dec (FunRange A1) t_bot) as [E1|E1].
    + assert (FunRange (t_union A1 A2) = FunRange A2).
      { simpl. destruct (FunRange A1) eqn:?; destruct (FunRange A2) eqn:?;
        try congruence; reflexivity. }
      rewrite H in Ge. pose proof (tsize_funrange A2). simpl in Ge. lia.
    + destruct (Typ.eq_dec (FunRange A2) t_bot) as [E2|E2].
      * assert (FunRange (t_union A1 A2) = FunRange A1).
        { simpl. destruct (FunRange A1) eqn:?; destruct (FunRange A2) eqn:?;
          try congruence; reflexivity. }
        rewrite H in Ge. pose proof (tsize_funrange A1). simpl in Ge. lia.
      * destruct (funrange_union_eq A1 A2 E1) as [[? _]|[_ Eq]].
        -- congruence.
        -- rewrite Eq in Ge. simpl in Ge.
           apply DS_trans with (B:=A1).
           ++ apply IHA1; auto. pose proof (tsize_funrange A1).
              pose proof (tsize_funrange A2). lia.
           ++ apply DS_orl; auto.
  - (* and *)
    inverts WfA.
    destruct (Typ.eq_dec (FunRange A1) t_bot) as [E1|E1].
    + simpl in Nz. rewrite E1 in Nz. simpl in Nz.
      destruct (FunRange A2); congruence.
    + destruct (Typ.eq_dec (FunRange A2) t_bot) as [E2|E2].
      * simpl in Nz. rewrite E2 in Nz. simpl in Nz.
        destruct (FunRange A1); congruence.
      * rewrite (funrange_and_eq A1 A2 E1 E2) in Ge. simpl in Ge.
        apply DS_and.
        -- apply IHA1; auto. pose proof (tsize_funrange A1).
           pose proof (tsize_funrange A2). lia.
        -- apply IHA2; auto. pose proof (tsize_funrange A1).
           pose proof (tsize_funrange A2). lia.
  - (* unit *) simpl in Nz. congruence.
  - (* prim *) simpl in Nz. congruence.
Qed.

Lemma funrange_top_arrow : forall PG A C,
  Ord C ->
  okenvp PG -> wft PG A -> wft PG C ->
  FunRange A <> t_bot ->
  declarative_subtyping PG C (FunRange A) ->
  declarative_subtyping PG (t_arrow t_top C) A.
Proof.
  introv OrdC Ok WfA WfC Nz Sub. gen C.
  induction A; intros; simpl in Nz.
  - (* int *) congruence.
  - (* top *) apply DS_top; auto.
  - (* bot *) congruence.
  - (* arrow *)
    simpl in Sub. apply DS_arrow; auto using DS_top.
  - (* union *)
    inverts WfA.
    destruct (Typ.eq_dec (FunRange A1) t_bot) as [E1|E1].
    + apply DS_trans with (B:=A2).
      * apply IHA2; auto.
        -- rewrite E1 in Nz. simpl in Nz. auto.
        -- assert (Eq: FunRange (t_union A1 A2) = FunRange A2).
           { simpl. destruct (FunRange A1) eqn:?; destruct (FunRange A2) eqn:?;
             try congruence; reflexivity. }
           rewrite Eq in Sub. auto.
      * apply DS_orr; auto.
    + destruct (Typ.eq_dec (FunRange A2) t_bot) as [E2|E2].
      * apply DS_trans with (B:=A1).
        -- apply IHA1; auto.
           ++ assert (Eq: FunRange (t_union A1 A2) = FunRange A1).
              { simpl. destruct (FunRange A1) eqn:?; destruct (FunRange A2) eqn:?;
                try congruence; reflexivity. }
              rewrite Eq in Sub. auto.
        -- apply DS_orl; auto.
      * destruct (funrange_union_eq A1 A2 E1) as [[? _]|[_ Eq]].
        -- congruence.
        -- rewrite Eq in Sub. apply ord_sub_or_unique in Sub; auto.
           destruct Sub as [S|S].
           ++ apply DS_trans with (B:=A1).
              ** apply IHA1; auto.
              ** apply DS_orl; auto.
           ++ apply DS_trans with (B:=A2).
              ** apply IHA2; auto.
              ** apply DS_orr; auto.
  - (* and *)
    inverts WfA.
    destruct (Typ.eq_dec (FunRange A1) t_bot) as [E1|E1].
    + rewrite E1 in Nz. simpl in Nz. destruct (FunRange A2); congruence.
    + destruct (Typ.eq_dec (FunRange A2) t_bot) as [E2|E2].
      * rewrite E2 in Nz. simpl in Nz. destruct (FunRange A1); congruence.
      * rewrite (funrange_and_eq A1 A2 E1 E2) in Sub.
        apply sub_and in Sub. destruct Sub.
        apply DS_and.
        -- apply IHA1; auto.
        -- apply IHA2; auto.
  - (* unit *) congruence.
  - (* prim *) congruence.
Qed.

Lemma spec_ranges : forall PG A B,
  okenvp PG -> wft PG A -> wft PG B ->
  FunRange A <> t_bot -> FunRange B <> t_bot ->
  PG |- A *s B ->
  PG |- (FunRange A) *s (FunRange B).
Proof.
  introv Ok WfA WfB NzA NzB Disj.
  unfold DisjSpec in *. unfold not in *.
  intros C OrdC Sub.
  apply sub_and in Sub. destruct Sub as [SubA SubB].
  apply (Disj (t_arrow t_top C)).
  - apply o_arrow. auto.
  - assert (WfC: wft PG C).
    { apply dsub2asub in SubA. apply algo_sub_wft in SubA. tauto. }
    apply DS_and.
    + eapply funrange_top_arrow; eauto.
    + eapply funrange_top_arrow; eauto.
Qed.

(* Theorem 18 (b) *)

Lemma Disj_completeness_n : forall n PG A B,
  tsize A + tsize B <= n ->
  okenvp PG -> wft PG A -> wft PG B ->
  PG |- A *s B -> PG |- A *a B.
Proof.
  induction n; introv Le Ok WfA WfB Disj.
  - forwards S1: tsize_pos A. forwards S2: tsize_pos B. lia.
  - destruct (Typ.eq_dec (FunRange A) t_bot) as [EA|EA].
    + apply da_nfun_l; auto. applys fs_and_empty_from_spec; eauto.
    + destruct (Typ.eq_dec (FunRange B) t_bot) as [EB|EB].
      * apply da_nfun_r; auto. applys fs_and_empty_from_spec; eauto.
      * apply da_peel.
        -- applys fs_and_empty_from_spec; eauto.
        -- destruct (lt_dec (tsize (FunRange A) + tsize (FunRange B))
                            (tsize A + tsize B)) as [Lt|Ge].
           ++ apply IHn; auto using wft_funrange; [lia|].
              apply spec_ranges; auto.
           ++ exfalso.
              pose proof (tsize_funrange A). pose proof (tsize_funrange B).
              apply (Disj t_int).
              ** apply o_int.
              ** apply DS_and.
                 --- apply int_sub_toplike; auto; lia.
                 --- apply int_sub_toplike; auto; lia.
Qed.

Lemma Disj_completeness : forall PG A B,
  okenvp PG -> wft PG A -> wft PG B ->
  PG |- A *s B -> PG |- A *a B.
Proof.
  intros. eapply Disj_completeness_n; eauto.
Qed.

(* Positive example: Int→Int and Unit→Unit are disjoint. *)
Lemma arrow_int_unit_disjoint : forall PG,
  okenvp PG ->
  PG |- (t_arrow t_top t_int) *a (t_arrow t_bot t_unit).
Proof.
  intros. apply da_peel.
  - simpl. fsetdec.
  - apply da_nfun_l.
    + apply TypSetProperties.empty_is_empty_1.
      intros x Hx. simpl in Hx.
      inter_inv Hx. single_inv H0. single_inv H1. discriminate.
    + reflexivity.
Qed.
