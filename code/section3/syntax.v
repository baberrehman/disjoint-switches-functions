
(*

-> Section 3 of paper
-> Union types + Null types

*)

Require Import TLC.LibLN.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
From Coq Require Export Lists.List.
Export ListNotations.
Require Import Coq.Strings.String.

(** syntax *)

Inductive typ : Set :=  (*r type *)
 | t_top : typ
 | t_int : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_union : typ -> typ -> typ
 | t_unit : typ.

Inductive exp : Set :=  (*r expression *)
 | e_var_b  : nat -> exp
 | e_var_f  : var -> exp
 | e_lit    : nat -> exp
 | e_abs    : typ -> typ -> exp -> exp (*r λ(x:A):B. e *)
 | e_app    : exp -> exp -> exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp
 | e_null   : exp.

(** Binding are mapping to term variables.
 [x ~: T] is a typing assumption *)

 Inductive bind : Set :=
 | bind_typ : typ -> bind.

Notation "x ~: T" := (x ~ T)
 (at level 23, left associativity) : env_scope.

(** Environment is an associative list of bindings. *)

 Definition env := LibEnv.env typ.

Inductive okt : env -> Prop :=
| okt_empty :
     okt empty
| okt_typ : forall E x T,
     okt E-> x # E -> okt (E & x ~: T).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => If (k = nat) then e_5 else (e_var_b nat)
  | (e_var_f x) => e_var_f x
  | (e_lit i5) => e_lit i5
  | (e_abs A B e) => e_abs A B (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (open_exp_wrt_exp_rec k e_5 e) A (open_exp_wrt_exp_rec (S k) e_5 e1) B (open_exp_wrt_exp_rec (S k) e_5 e2)
  | (e_null) => e_null
end.


Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_exp_wrt_exp t (e_var_f x)) (at level 67).


(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall i5,
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (L:vars) (A B:typ) (e:exp),
      ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs A B e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_typeof : forall (L:vars) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp),
     (lc_exp e) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e1 (e_var_f x) )  ) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e2 (e_var_f x) )  ) ->
     (lc_exp (e_typeof e A e1 B e2))
 | lec_e_null :
     lc_exp e_null.

(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => \{}
  | (e_var_f x) => \{x}
  | (e_lit i5) => \{}
  | (e_abs A B e) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_typeof e A e1 B e2) => (fv_exp e) \u (fv_exp e1) \u (fv_exp e2)
  | (e_null) => \{}
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (If x = x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs A B e) => e_abs A B (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (subst_exp e_5 x5 e) A (subst_exp e_5 x5 e1) B (subst_exp e_5 x5 e2)
  | (e_null) => e_null
end.

(* defns Subtyping *)
Reserved Notation "A <: B" (at level 80).
Inductive subtyping : typ -> typ -> Prop :=    (* defn subtyping *)
 | s_top : forall A, 
   A <: t_top
 | s_int :
     t_int <: t_int
 | s_unit :
    t_unit <: t_unit
 | s_arrow : forall (A1 A2 B1 B2:typ),
     B1 <: A1 ->
     A2 <: B2 ->
     (t_arrow A1 A2) <: (t_arrow B1 B2)
 | s_ora : forall (A1 A2 A:typ),
     A1 <: A ->
     A2 <: A ->
     (t_union A1 A2) <: A
 | s_orb : forall (A A1 A2:typ),
     A <: A1 ->
     A <: (t_union A1 A2)
 | s_orc : forall (A A1 A2:typ),
     A <: A2 ->
     A <: (t_union A1 A2)
 | s_bot : forall A,
     t_bot <: A
where "A <: B" := (subtyping A B) : env_scope.

#[export]
Hint Constructors subtyping lc_exp ok okt : core.

Lemma sub_or : forall A B C, (t_union A B) <: C -> A <: C /\ B <: C.
Proof.
intros; inductions H; try solve [split*].
specialize (IHsubtyping A B).
forwards* : IHsubtyping.
specialize (IHsubtyping A B).
forwards* : IHsubtyping.
Defined.

(**********************************)
(*****  Subtyping Properties  *****)
(**********************************)

Lemma sub_refl : forall A, A <: A.
  induction A; eauto.
Defined.

#[export]
Hint Resolve sub_refl : core.

Lemma sub_transitivity : forall B A C, A <: B -> B <: C -> A <: C.
Proof.
induction B; intros;
generalize H0 H; clear H0; clear H; generalize A; clear A.
- intros; inductions H0; eauto. 
- intros; inductions H; eauto.
- intros; inductions H; eauto.
- induction C; intros; try solve [inverts* H0].
  induction A; try solve[inverts* H].
  inverts* H0. inverts* H. 
- intros. apply sub_or in H0. destruct H0.
  inductions H; eauto.
- intros; inductions H; eauto.
Defined.

Lemma bot_sub_all : forall A, t_bot <: A.
Proof.
  intros.
  dependent induction A; eauto.
Qed.

(****************************************)
(**********  Dijointness    *************)
(****************************************)

(* defns BottomLike *)
Inductive bottomlike : typ -> Prop :=    (* defn bottomlike *)
 | bl_bot :
     bottomlike t_bot
 | bl_or : forall (A B:typ),
     bottomlike A ->
     bottomlike B ->
     bottomlike (t_union A B).

(* Types with no ordinary inhabitant (bot, empty unions, arrows
   whose range is uninhabited). Distinct from bottomlike: A→⊥
   is uninhabited but A→⊥ <: Int does not hold, so it is not
   bottomlike (BL_soundness would fail). *)
Inductive uninhabited : typ -> Prop :=
 | uh_bot :
     uninhabited t_bot
 | uh_or : forall (A B:typ),
     uninhabited A ->
     uninhabited B ->
     uninhabited (t_union A B)
 | uh_arrow : forall (A B:typ),
     uninhabited B ->
     uninhabited (t_arrow A B).

(*************************)
(***** Ordinary Types ****)
(*************************)

(* Changed from the paper: an arrow is ordinary only when its
   range is ordinary. ⊤→⊥ is therefore no longer a witness of
   overlap between every pair of function types. *)
Inductive Ord : typ -> Prop :=
| o_int   : Ord t_int
| o_arrow : forall t1 t2, Ord t2 -> Ord (t_arrow t1 t2)
| o_unit  : Ord t_unit.

#[export]
Hint Constructors bottomlike uninhabited Ord : core.

(* Old bottomlike spec, kept for Lemma 3. No longer equivalent
   to ordinary-type disjointness (Lemma 12) once ⊤→⊥ is not Ord. *)
Definition DisjSpec A B := forall C, C <: A /\ C <: B -> bottomlike C.
Notation "A *s B" := (DisjSpec A B) (at level 80).

(* Official specification (was DisjSpec1 / Lemma 12). *)
Definition DisjSpec1 A B := forall C, Ord C -> not (C <: A /\ C <:  B).
Notation "A *s1 B" := (DisjSpec1 A B) (at level 80).

Definition inhabited A := exists C, Ord C /\ C <: A.

(* Disjointness Algorithm *)

(* defns Disjointness
   New rules vs the paper:
   - ad_arrow: ranges disjoint ⇒ function types disjoint
   - ad_uninh_l / ad_uninh_r: an uninhabited type is disjoint
     from everything (needed for completeness of *s1, e.g. (A→⊥) * ⊤) *)
Reserved Notation "A *a B" (at level 80).
Inductive disjointness : typ -> typ -> Prop :=    (* defn disjointness *)
 | ad_btmr : forall (A:typ),
      A *a t_bot
 | ad_btml : forall (A:typ),
     t_bot *a A
 | ad_uninh_l : forall (A B:typ),
     uninhabited A ->
     A *a B
 | ad_uninh_r : forall (A B:typ),
     uninhabited B ->
     A *a B
 | ad_intl : forall (A B:typ),
     t_int *a (t_arrow A B)
 | ad_intr : forall (A B:typ),
     (t_arrow A B) *a t_int
 | ad_unit_intl :
      t_unit *a t_int
 | ad_unit_intr :
      t_int *a t_unit
 | ad_unit_arrowl: forall A B,
      t_unit *a (t_arrow A B)
 | ad_unit_arrowr: forall A B,
      (t_arrow A B) *a t_unit
 | ad_arrow : forall (A1 B1 A2 B2:typ),
     B1 *a B2 ->
     (t_arrow A1 B1) *a (t_arrow A2 B2)
 | ad_orl : forall (A B C:typ),
     A *a C ->
     B *a C ->
     (t_union A B) *a C
 | ad_orr : forall (C A B:typ),
     A *a C ->
     B *a C ->
     C *a (t_union A B)
where "A *a B" := (disjointness A B).

#[export]
Hint Constructors disjointness : core.

(************************************************)
(**********  Disjointness Properties  ***********)
(************************************************)

(* Lemma 3 *)

Lemma BL_soundness : forall A, bottomlike A -> forall C, A <: C.
Proof.
intros. inductions H. auto. eauto.
Qed.

Lemma BL_completeness : forall A, (forall C, A <: C) -> bottomlike A.
Proof.
inductions A; intro; eauto.
 - specialize (H t_bot).
   inversion H.
 - specialize (H t_bot).
   inversion H.
 - specialize (H t_bot).
   inversion H.
 - constructor.
   apply IHA1. intros.
   specialize (H C).
   apply sub_or in H. destruct~ H.
   apply IHA2. intros.
   specialize (H C).
   apply sub_or in H. destruct~ H.
 - specialize (H t_bot).
   inversion H.
Qed.

Require Import Program.Equality.

Lemma sub_arrow_inv : forall A1 A2 B1 B2,
  (t_arrow A1 A2) <: (t_arrow B1 B2) -> B1 <: A1 /\ A2 <: B2.
Proof.
  intros. inverts* H.
Qed.

Lemma ord_sub_bot_false : forall C,
  Ord C -> C <: t_bot -> False.
Proof.
  introv OrdC Sub. inductions OrdC; inverts Sub.
Qed.

Lemma ord_sub_union : forall C A B,
  Ord C -> C <: (t_union A B) -> C <: A \/ C <: B.
Proof.
  introv OrdC Sub.
  inductions Sub; try solve [inverts OrdC]; eauto.
Qed.

Lemma int_sub_arrow_false : forall A B,
  t_int <: (t_arrow A B) -> False.
Proof.
  intros. inverts H.
Qed.

Lemma unit_sub_arrow_false : forall A B,
  t_unit <: (t_arrow A B) -> False.
Proof.
  intros. inverts H.
Qed.

Lemma arrow_sub_int_false : forall A B,
  (t_arrow A B) <: t_int -> False.
Proof.
  intros. inverts H.
Qed.

Lemma arrow_sub_unit_false : forall A B,
  (t_arrow A B) <: t_unit -> False.
Proof.
  intros. inverts H.
Qed.

Lemma uninhabited_ord_false : forall A C,
  uninhabited A -> Ord C -> C <: A -> False.
Proof.
  introv UH OrdC Sub. gen C.
  induction UH; intros.
  - eapply ord_sub_bot_false; eauto.
  - apply ord_sub_union in Sub; auto.
    destruct Sub; eauto.
  - inverts OrdC.
    + inverts Sub.
    + apply sub_arrow_inv in Sub. destruct Sub.
      eapply IHUH; eauto.
    + inverts Sub.
Qed.

Lemma uninhabited_complete : forall A,
  (forall C, Ord C -> C <: A -> False) -> uninhabited A.
Proof.
  inductions A; intros Hno.
  - exfalso. apply (Hno t_int); auto.
  - exfalso. apply (Hno t_int); auto.
  - apply uh_bot.
  - apply uh_arrow. apply IHA2. intros C OrdC SubC.
    apply (Hno (t_arrow t_top C)); auto.
  - apply uh_or.
    + apply IHA1. intros C OrdC SubC.
      apply (Hno C); auto.
    + apply IHA2. intros C OrdC SubC.
      apply (Hno C); auto.
  - exfalso. apply (Hno t_unit); auto.
Qed.

Lemma inhabited_arrow : forall A B,
  inhabited B -> inhabited (t_arrow A B).
Proof.
  intros A B [C [OrdC Sub]].
  exists (t_arrow t_top C). split; auto.
Qed.

Lemma inhabited_sub : forall A B,
  inhabited A -> A <: B -> inhabited B.
Proof.
  intros A B [C [OrdC Sub]] SubAB.
  exists C. split; auto.
  eapply sub_transitivity; eauto.
Qed.

(* Theorem 5 (a) — now soundness against ordinary-type disjointness. *)

Lemma Disj_soundness : forall A B, A *a B -> A *s1 B.
Proof.
  induction 1; unfold DisjSpec1; unfold not; intros D OrdD [SubA SubB].
  - eapply ord_sub_bot_false; eauto.
  - eapply ord_sub_bot_false; eauto.
  - eapply uninhabited_ord_false; eauto.
  - eapply uninhabited_ord_false; eauto.
  - (* int * arrow *)
    inversion OrdD; subst; try solve [inversion SubA | inversion SubB].
  - (* arrow * int *)
    inversion OrdD; subst; try solve [inversion SubA | inversion SubB].
  - (* unit * int *)
    inversion OrdD; subst; try solve [inversion SubA | inversion SubB].
  - (* int * unit *)
    inversion OrdD; subst; try solve [inversion SubA | inversion SubB].
  - (* unit * arrow *)
    inversion OrdD; subst; try solve [inversion SubA | inversion SubB].
  - (* arrow * unit *)
    inversion OrdD; subst; try solve [inversion SubA | inversion SubB].
  - (* arrow * arrow *)
    inversion OrdD; subst; try solve [inversion SubA | inversion SubB].
    apply sub_arrow_inv in SubA. apply sub_arrow_inv in SubB.
    destruct SubA. destruct SubB.
    eapply IHdisjointness; eauto.
  - apply ord_sub_union in SubA; auto.
    destruct SubA. eapply IHdisjointness1; eauto. eapply IHdisjointness2; eauto.
  - apply ord_sub_union in SubB; auto.
    destruct SubB. eapply IHdisjointness1; eauto. eapply IHdisjointness2; eauto.
Qed.

Lemma BL_disj : forall A, bottomlike A -> forall B, A *a B.
  induction 1; intros; eauto.
Defined.

Lemma uninhabited_disj : forall A, uninhabited A -> forall B, A *a B.
Proof.
  intros. apply* ad_uninh_l.
Qed.

Lemma Disj_sym : forall A B, A *a B -> B *a A.
Proof.
  induction 1; eauto.
Qed.

(* Theorem 5 (b) — completeness against *s1. *)

Lemma Disj_completeness : forall A B, A *s1 B -> A *a B.
Proof.
  intros A. induction A; intros B Disj.
  - (* top *)
    apply ad_uninh_r. apply uninhabited_complete.
    intros C OrdC SubC.
    unfold DisjSpec1, not in Disj.
    apply (Disj C OrdC). split; auto.
  - (* int *)
    induction B.
    + unfold DisjSpec1, not in Disj. exfalso. apply (Disj t_int); auto.
    + unfold DisjSpec1, not in Disj. exfalso. apply (Disj t_int); auto.
    + apply ad_btmr.
    + apply ad_intl.
    + apply ad_orr; apply Disj_sym.
      * apply IHB1. unfold DisjSpec1, not in *. intros C OrdC [S1 S2].
        apply (Disj C OrdC). split; auto.
      * apply IHB2. unfold DisjSpec1, not in *. intros C OrdC [S1 S2].
        apply (Disj C OrdC). split; auto.
    + apply ad_unit_intr.
  - (* bot *)
    apply ad_btml.
  - (* arrow A1 A2 *)
    induction B.
    + apply ad_uninh_l. apply uninhabited_complete.
      intros C OrdC SubC.
      unfold DisjSpec1, not in Disj.
      apply (Disj C OrdC). split; auto.
    + apply ad_intr.
    + apply ad_btmr.
    + apply ad_arrow. apply IHA2.
      unfold DisjSpec1, not in *. intros C OrdC [S1 S2].
      apply (Disj (t_arrow t_top C)); auto.
    + apply ad_orr; apply Disj_sym.
      * apply IHB1. unfold DisjSpec1, not in *. intros C OrdC [S1 S2].
        apply (Disj C OrdC). split; auto.
      * apply IHB2. unfold DisjSpec1, not in *. intros C OrdC [S1 S2].
        apply (Disj C OrdC). split; auto.
    + apply ad_unit_arrowr.
  - (* union *)
    apply ad_orl.
    + apply IHA1. unfold DisjSpec1, not in *. intros C OrdC [S1 S2].
      apply (Disj C OrdC). split; auto.
    + apply IHA2. unfold DisjSpec1, not in *. intros C OrdC [S1 S2].
      apply (Disj C OrdC). split; auto.
  - (* unit *)
    induction B.
    + unfold DisjSpec1, not in Disj. exfalso. apply (Disj t_unit); auto.
    + apply ad_unit_intl.
    + apply ad_btmr.
    + apply ad_unit_arrowl.
    + apply ad_orr; apply Disj_sym.
      * apply IHB1. unfold DisjSpec1, not in *. intros C OrdC [S1 S2].
        apply (Disj C OrdC). split; auto.
      * apply IHB2. unfold DisjSpec1, not in *. intros C OrdC [S1 S2].
        apply (Disj C OrdC). split; auto.
    + unfold DisjSpec1, not in Disj. exfalso. apply (Disj t_unit); auto.
Qed.

Lemma disj_disj1 : forall A B, A *s B -> A *s1 B.
Proof.
  intros.
  unfold DisjSpec in H.
  unfold DisjSpec1. unfold not. intros.
  specialize (H C).
  forwards*: H.
  inductions H2.
  inversion H0.
  inversion H0.
Qed.

(* Lemma 12 of the paper (DisjSpec1 ↔ DisjSpec) no longer holds:
   ⊤→⊥ <: every arrow but is not ordinary, so two arrows can be
   *s1-disjoint while sharing the non-ordinary subtype ⊤→⊥.
   Official equivalence is now *a ↔ *s1 (Theorem 5). *)

Lemma arrow_disj_from_range : forall A1 B1 A2 B2,
  B1 *a B2 -> (t_arrow A1 B1) *a (t_arrow A2 B2).
Proof.
  intros. apply* ad_arrow.
Qed.

(* Positive example: Int→Int and Unit→Unit are disjoint. *)
Lemma arrow_int_unit_disjoint :
  (t_arrow t_top t_int) *a (t_arrow t_bot t_unit).
Proof.
  apply ad_arrow. apply ad_unit_intr.
Qed.