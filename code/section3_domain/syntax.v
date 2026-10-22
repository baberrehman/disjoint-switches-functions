
(*

-> Section 3 of paper + domain-based function disjointness
-> Union types + Null types
-> ad_arrow_dom: A1 * A2 ⇒ (A1→B1) * (A2→B2)
-> Ordinary *s1 is not sound for that rule (contravariant domains:
   Top→Int inhabits Int→Int and Unit→Int).
-> *s2 is the sound and complete spec for *a: arrows overlap iff
   domains overlap AND ranges overlap. Inhabitation of A→B follows
   the range only (Bot→Int is inhabited). Then *a ⇔ *s2.
-> typeof uses *s2. A value can still inhabit both branches
   (Top→Int <: Int→Int and Top→Int <: Unit→Int), so the right
   branch steps only when the runtime tag is not a subtype of the left.

*)

Require Import TLC.LibLN.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
From Coq Require Export Lists.List.
Export ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Lia.

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

(* Decidable subtyping. The right branch of typeof steps only when
   the runtime tag is not a subtype of the left branch. *)

Fixpoint typ_size (A : typ) : nat :=
  match A with
  | t_arrow A B | t_union A B => S (typ_size A + typ_size B)
  | _ => O
  end.

(* Fuelled because the union-right clause recurses on the same left type. *)
Fixpoint sub_bf (n : nat) (A B : typ) : bool :=
  match n with
  | O => false
  | S n =>
      match A, B with
      | _, t_top => true
      | t_bot, _ => true
      | t_int, t_int => true
      | t_unit, t_unit => true
      | t_arrow A1 A2, t_arrow B1 B2 => andb (sub_bf n B1 A1) (sub_bf n A2 B2)
      | t_union A1 A2, B => andb (sub_bf n A1 B) (sub_bf n A2 B)
      | _, t_union B1 B2 => orb (sub_bf n A B1) (sub_bf n A B2)
      | _, _ => false
      end
  end.

Definition sub_b (A B : typ) : bool :=
  sub_bf (S (typ_size A + typ_size B)) A B.

Lemma sub_bf_sound : forall n A B, sub_bf n A B = true -> A <: B.
Proof.
  induction n as [|n IH]; intros A B Hb; [discriminate|].
  destruct A; destruct B; simpl in Hb;
    first [
      discriminate |
      apply s_top |
      apply s_bot |
      apply s_int |
      apply s_unit |
      (apply andb_prop in Hb; destruct Hb as [Hl Hr];
       apply s_arrow; [apply IH; exact Hl | apply IH; exact Hr]) |
      (apply andb_prop in Hb; destruct Hb as [Hl Hr];
       apply s_ora; [apply IH; exact Hl | apply IH; exact Hr]) |
      (apply orb_prop in Hb; destruct Hb as [Hl | Hr];
       [apply s_orb; apply IH; exact Hl | apply s_orc; apply IH; exact Hr])
    ].
Qed.

Lemma sub_b_sound : forall A B, sub_b A B = true -> A <: B.
Proof.
  intros A B H. unfold sub_b in H. eapply sub_bf_sound; eauto.
Qed.

Lemma sub_bf_pos_top : forall n A, sub_bf (S n) A t_top = true.
Proof. intros. destruct A; reflexivity. Qed.

Lemma sub_bf_pos_bot : forall n B, sub_bf (S n) t_bot B = true.
Proof. intros. destruct B; reflexivity. Qed.

Lemma sub_bf_through_top : forall A C n,
  typ_size A < n ->
  sub_bf (S n) A (t_union t_top C) = true.
Proof.
  induction A; intros C n Hsz; destruct n; simpl in Hsz; try lia; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply andb_true_intro. split; [apply IHA1 | apply IHA2]; lia.
  - reflexivity.
Qed.

Lemma sub_bf_widen_r : forall A B C n,
  typ_size A + typ_size B < n ->
  sub_bf n A B = true ->
  sub_bf (S n) A (t_union B C) = true.
Proof.
  induction A; intros B C n Hsz H; destruct n; try (simpl in Hsz; lia).
  - destruct B; simpl in H; simpl.
    + reflexivity.
    + discriminate.
    + discriminate.
    + discriminate.
    + rewrite H. reflexivity.
    + discriminate.
  - destruct B; simpl in H; simpl.
    + reflexivity.
    + reflexivity.
    + discriminate.
    + discriminate.
    + rewrite H. reflexivity.
    + discriminate.
  - simpl. reflexivity.
  - destruct B; simpl in H; simpl.
    + reflexivity.
    + discriminate.
    + discriminate.
    + rewrite H. reflexivity.
    + rewrite H. reflexivity.
    + discriminate.
  - simpl in Hsz. destruct B; simpl in H; simpl.
    + apply andb_true_intro. split; apply sub_bf_through_top; lia.
    + apply andb_prop in H. destruct H as [H1 H2].
      apply andb_true_intro. split; [apply IHA1 | apply IHA2]; lia || assumption.
    + apply andb_prop in H. destruct H as [H1 H2].
      apply andb_true_intro. split; [apply IHA1 | apply IHA2]; lia || assumption.
    + apply andb_prop in H. destruct H as [H1 H2].
      apply andb_true_intro. split; [apply IHA1 | apply IHA2]; lia || assumption.
    + apply andb_prop in H. destruct H as [H1 H2].
      apply andb_true_intro. split; [apply IHA1 | apply IHA2]; lia || assumption.
    + apply andb_prop in H. destruct H as [H1 H2].
      apply andb_true_intro. split; [apply IHA1 | apply IHA2]; lia || assumption.
  - destruct B; simpl in H; simpl.
    + reflexivity.
    + discriminate.
    + discriminate.
    + discriminate.
    + rewrite H. reflexivity.
    + reflexivity.
Qed.

Lemma sub_bf_widen_l : forall A B C n,
  typ_size A + typ_size C < n ->
  sub_bf n A C = true ->
  sub_bf (S n) A (t_union B C) = true.
Proof.
  induction A; intros B C n Hsz H; destruct n; try (simpl in Hsz; lia).
  - destruct C; simpl in H; simpl.
    + rewrite orb_true_r. reflexivity.
    + discriminate.
    + discriminate.
    + discriminate.
    + rewrite H. rewrite orb_true_r. reflexivity.
    + discriminate.
  - destruct C; simpl in H; simpl.
    + rewrite orb_true_r. reflexivity.
    + rewrite orb_true_r. reflexivity.
    + discriminate.
    + discriminate.
    + rewrite H. rewrite orb_true_r. reflexivity.
    + discriminate.
  - simpl. reflexivity.
  - destruct C; simpl in H; simpl.
    + rewrite orb_true_r. reflexivity.
    + discriminate.
    + discriminate.
    + rewrite H. rewrite orb_true_r. reflexivity.
    + rewrite H. rewrite orb_true_r. reflexivity.
    + discriminate.
  - simpl in Hsz. destruct C; simpl in H; simpl.
    + apply andb_true_intro. split.
      * apply IHA1 with (C := t_top). lia.
        destruct n; [lia | apply sub_bf_pos_top].
      * apply IHA2 with (C := t_top). lia.
        destruct n; [lia | apply sub_bf_pos_top].
    + apply andb_prop in H. destruct H as [H1 H2].
      apply andb_true_intro. split; [apply IHA1 | apply IHA2]; lia || assumption.
    + apply andb_prop in H. destruct H as [H1 H2].
      apply andb_true_intro. split; [apply IHA1 | apply IHA2]; lia || assumption.
    + apply andb_prop in H. destruct H as [H1 H2].
      apply andb_true_intro. split; [apply IHA1 | apply IHA2]; lia || assumption.
    + apply andb_prop in H. destruct H as [H1 H2].
      apply andb_true_intro. split; [apply IHA1 | apply IHA2]; lia || assumption.
    + apply andb_prop in H. destruct H as [H1 H2].
      apply andb_true_intro. split; [apply IHA1 | apply IHA2]; lia || assumption.
  - destruct C; simpl in H; simpl.
    + rewrite orb_true_r. reflexivity.
    + discriminate.
    + discriminate.
    + discriminate.
    + rewrite H. rewrite orb_true_r. reflexivity.
    + rewrite orb_true_r. reflexivity.
Qed.

Lemma sub_bf_complete_fuel : forall A B,
  A <: B -> forall n, typ_size A + typ_size B < n -> sub_bf n A B = true.
Proof.
  induction 1; intros n Hn.
  - destruct n; [lia | apply sub_bf_pos_top].
  - destruct n; [lia | reflexivity].
  - destruct n; [lia | reflexivity].
  - destruct n; [simpl in Hn; lia |]. simpl.
    apply andb_true_intro. split.
    + apply IHsubtyping1. simpl in Hn. lia.
    + apply IHsubtyping2. simpl in Hn. lia.
  - destruct n; [simpl in Hn; lia |].
    destruct A; simpl in *.
    + reflexivity.
    + apply andb_true_intro; split; [apply IHsubtyping1; lia | apply IHsubtyping2; lia].
    + apply andb_true_intro; split; [apply IHsubtyping1; lia | apply IHsubtyping2; lia].
    + apply andb_true_intro; split; [apply IHsubtyping1; lia | apply IHsubtyping2; lia].
    + apply andb_true_intro; split; [apply IHsubtyping1; lia | apply IHsubtyping2; lia].
    + apply andb_true_intro; split; [apply IHsubtyping1; lia | apply IHsubtyping2; lia].
  - destruct n; [simpl in Hn; lia |].
    apply sub_bf_widen_r. simpl in Hn. lia.
    apply IHsubtyping. simpl in Hn. lia.
  - destruct n; [simpl in Hn; lia |].
    apply sub_bf_widen_l. simpl in Hn. lia.
    apply IHsubtyping. simpl in Hn. lia.
  - destruct n; [lia | apply sub_bf_pos_bot].
Qed.

Lemma sub_b_complete : forall A B, A <: B -> sub_b A B = true.
Proof.
  intros. unfold sub_b. apply sub_bf_complete_fuel; [assumption | lia].
Qed.

Lemma sub_dec : forall A B, {A <: B} + {~ (A <: B)}.
Proof.
  intros A B. destruct (sub_b A B) eqn:E.
  - left. apply sub_b_sound. exact E.
  - right. intro S. apply sub_b_complete in S. congruence.
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

(* Sound + complete spec for *a, including ad_arrow_dom (DisjSpec2).
   Ordinary *s1 asks for a common subtype; arrow subtyping is
   contravariant in the domain, so Top→Int overlaps Int→Int with Unit→Int.
   *s2 treats arrows as overlapping only when domains AND ranges overlap.
   Inhabitation of A→B follows the range only, matching uninhabited /
   inhabited (Bot→Int is inhabited; Int→Bot is not). *)
Fixpoint cov_inhabited_b (A : typ) : bool :=
  match A with
  | t_top | t_int | t_unit => true
  | t_bot => false
  | t_arrow _ B => cov_inhabited_b B
  | t_union A B => orb (cov_inhabited_b A) (cov_inhabited_b B)
  end.

Fixpoint overlaps_b (A : typ) : typ -> bool :=
  fix go (B : typ) : bool :=
    match A, B with
    | t_bot, _ => false
    | _, t_bot => false
    | t_top, X => cov_inhabited_b X
    | X, t_top => cov_inhabited_b X
    | t_int, t_int => true
    | t_unit, t_unit => true
    | t_arrow A1 A2, t_arrow B1 B2 =>
        andb (overlaps_b A1 B1) (overlaps_b A2 B2)
    | t_union A1 A2, _ =>
        orb (overlaps_b A1 B) (overlaps_b A2 B)
    | _, t_union B1 B2 =>
        orb (go B1) (go B2)
    | _, _ => false
    end.

Definition DisjSpec2 A B := overlaps_b A B = false.
Notation "A *s2 B" := (DisjSpec2 A B) (at level 80).

(* Disjointness Algorithm *)

(* defns Disjointness
   New rules vs the paper / section3:
   - ad_arrow: ranges disjoint ⇒ function types disjoint
   - ad_arrow_dom: domains disjoint ⇒ function types disjoint
     (sound and complete for *s2, not sound for *s1)
   - ad_uninh_l / ad_uninh_r: an uninhabited type is disjoint
     from everything (needed for completeness, e.g. (A→Bot) * Top) *)
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
 | ad_arrow_dom : forall (A1 B1 A2 B2:typ),
     A1 *a A2 ->
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

(* Range rule is still *s1-sound. The domain rule is not (see
   arrow_dom_unsound); so *a ⇔ *s1 fails in this extension. *)

Lemma Disj_soundness_range : forall A1 B1 A2 B2,
  B1 *s1 B2 -> (t_arrow A1 B1) *s1 (t_arrow A2 B2).
Proof.
  intros A1 B1 A2 B2 Disj.
  unfold DisjSpec1, not in *.
  intros D OrdD [SubA SubB].
  inversion OrdD; subst; try solve [inversion SubA | inversion SubB].
  apply sub_arrow_inv in SubA. apply sub_arrow_inv in SubB.
  destruct SubA. destruct SubB.
  eapply Disj; eauto.
Qed.

(* Int→Int and Unit→Int are *a by ad_arrow_dom, but both contain
   the ordinary function ⊤→Int, so they are not *s1. *)
Lemma arrow_dom_unsound :
  disjointness (t_arrow t_int t_int) (t_arrow t_unit t_int) /\
  ~ DisjSpec1 (t_arrow t_int t_int) (t_arrow t_unit t_int).
Proof.
  split.
  - apply ad_arrow_dom. apply ad_unit_intr.
  - unfold DisjSpec1, not. intros H.
    apply (H (t_arrow t_top t_int)); auto.
Qed.

(* ---------- *s2 is sound for the full algorithm, including domains ---------- *)

Lemma overlaps_b_bot_r : forall A, overlaps_b A t_bot = false.
Proof. destruct A; reflexivity. Qed.

Lemma overlaps_b_bot_l : forall A, overlaps_b t_bot A = false.
Proof. destruct A; reflexivity. Qed.

Lemma overlaps_b_top_r : forall A, overlaps_b A t_top = cov_inhabited_b A.
Proof. destruct A; reflexivity. Qed.

Lemma overlaps_b_top_l : forall A, overlaps_b t_top A = cov_inhabited_b A.
Proof. destruct A; reflexivity. Qed.

Lemma overlaps_b_union_l : forall A B C,
  overlaps_b (t_union A B) C = orb (overlaps_b A C) (overlaps_b B C).
Proof.
  intros. destruct C; simpl.
  - rewrite !overlaps_b_top_r. reflexivity.
  - reflexivity.
  - rewrite !overlaps_b_bot_r. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma overlaps_b_union_r : forall A B C,
  overlaps_b A (t_union B C) = orb (overlaps_b A B) (overlaps_b A C).
Proof.
  induction A; intros.
  - simpl. rewrite !overlaps_b_top_l. reflexivity.
  - destruct B; destruct C; reflexivity.
  - rewrite !overlaps_b_bot_l. reflexivity.
  - destruct B; destruct C; reflexivity.
  - rewrite !overlaps_b_union_l.
    rewrite IHA1, IHA2.
    destruct (overlaps_b A1 B); destruct (overlaps_b A1 C);
      destruct (overlaps_b A2 B); destruct (overlaps_b A2 C); reflexivity.
  - destruct B; destruct C; reflexivity.
Qed.

Lemma uninh_not_cin : forall A, uninhabited A -> cov_inhabited_b A = false.
Proof.
  induction 1; simpl; auto.
  rewrite IHuninhabited1, IHuninhabited2. reflexivity.
Qed.

Lemma cin_false_uninh : forall A, cov_inhabited_b A = false -> uninhabited A.
Proof.
  induction A; simpl; intro H; try discriminate.
  - apply uh_bot.
  - apply uh_arrow. auto.
  - destruct (cov_inhabited_b A1); destruct (cov_inhabited_b A2);
      simpl in H; try discriminate; auto.
Qed.

Lemma uninh_overlaps_b : forall A, uninhabited A -> forall B, overlaps_b A B = false.
Proof.
  induction 1; intros C.
  - apply overlaps_b_bot_l.
  - rewrite overlaps_b_union_l, IHuninhabited1, IHuninhabited2. reflexivity.
  - induction C.
    + simpl. rewrite (uninh_not_cin B) by assumption. reflexivity.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IHuninhabited. apply andb_false_r.
    + rewrite overlaps_b_union_r, IHC1, IHC2. reflexivity.
    + reflexivity.
Qed.

Lemma uninh_overlaps_b_r : forall B, uninhabited B -> forall A, overlaps_b A B = false.
Proof.
  induction 1; intros T.
  - apply overlaps_b_bot_r.
  - rewrite overlaps_b_union_r, IHuninhabited1, IHuninhabited2. reflexivity.
  - induction T.
    + simpl. rewrite (uninh_not_cin B) by assumption. reflexivity.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IHuninhabited. apply andb_false_r.
    + rewrite overlaps_b_union_l, IHT1, IHT2. reflexivity.
    + reflexivity.
Qed.

Lemma overlaps_b_sym : forall A B, overlaps_b A B = overlaps_b B A.
Proof.
  induction A; intros B.
  - rewrite overlaps_b_top_l, overlaps_b_top_r. reflexivity.
  - induction B.
    + rewrite overlaps_b_top_r, overlaps_b_top_l. reflexivity.
    + reflexivity.
    + rewrite overlaps_b_bot_r, overlaps_b_bot_l. reflexivity.
    + reflexivity.
    + rewrite overlaps_b_union_r, IHB1, IHB2, overlaps_b_union_l. reflexivity.
    + reflexivity.
  - rewrite overlaps_b_bot_l, overlaps_b_bot_r. reflexivity.
  - induction B.
    + rewrite overlaps_b_top_r, overlaps_b_top_l. reflexivity.
    + reflexivity.
    + rewrite overlaps_b_bot_r, overlaps_b_bot_l. reflexivity.
    + simpl. rewrite IHA1, IHA2. reflexivity.
    + rewrite overlaps_b_union_r, IHB1, IHB2, overlaps_b_union_l. reflexivity.
    + reflexivity.
  - rewrite overlaps_b_union_l, IHA1, IHA2, <- overlaps_b_union_r. reflexivity.
  - induction B.
    + rewrite overlaps_b_top_r, overlaps_b_top_l. reflexivity.
    + reflexivity.
    + rewrite overlaps_b_bot_r, overlaps_b_bot_l. reflexivity.
    + reflexivity.
    + rewrite overlaps_b_union_r, IHB1, IHB2, overlaps_b_union_l. reflexivity.
    + reflexivity.
Qed.

Lemma Disj_soundness2 : forall A B, A *a B -> A *s2 B.
Proof.
  unfold DisjSpec2.
  induction 1.
  - apply overlaps_b_bot_r.
  - apply overlaps_b_bot_l.
  - apply uninh_overlaps_b; auto.
  - apply uninh_overlaps_b_r; auto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHdisjointness. apply andb_false_r.
  - simpl. rewrite IHdisjointness. reflexivity.
  - rewrite overlaps_b_union_l, IHdisjointness1, IHdisjointness2. reflexivity.
  - rewrite overlaps_b_union_r, (overlaps_b_sym C A), (overlaps_b_sym C B).
    rewrite IHdisjointness1, IHdisjointness2. reflexivity.
Qed.

(* The *s1 counterexample is *s2-disjoint: domains Int and Unit do not overlap. *)
Lemma arrow_dom_s2 :
  (t_arrow t_int t_int) *s2 (t_arrow t_unit t_int).
Proof.
  unfold DisjSpec2. reflexivity.
Qed.

(* Completeness fix: Bot→Int is inhabited, so it overlaps Top. *)
Lemma top_not_s2_bot_arrow :
  ~ (t_top *s2 (t_arrow t_bot t_int)).
Proof.
  unfold DisjSpec2. simpl. discriminate.
Qed.

Lemma overlaps_union_false_l : forall A B C,
  overlaps_b (t_union A B) C = false ->
  overlaps_b A C = false /\ overlaps_b B C = false.
Proof.
  intros. rewrite overlaps_b_union_l in H.
  destruct (overlaps_b A C); destruct (overlaps_b B C); simpl in H; auto.
Qed.

Lemma overlaps_union_false_r : forall A B C,
  overlaps_b A (t_union B C) = false ->
  overlaps_b A B = false /\ overlaps_b A C = false.
Proof.
  intros. rewrite overlaps_b_union_r in H.
  destruct (overlaps_b A B); destruct (overlaps_b A C); simpl in H; auto.
Qed.

Lemma uninhabited_disj : forall A, uninhabited A -> forall B, A *a B.
Proof.
  intros. apply* ad_uninh_l.
Qed.

Lemma Disj_sym : forall A B, A *a B -> B *a A.
Proof.
  induction 1; eauto.
Qed.

(* Completeness of *s2, including the domain rule. *)
Lemma Disj_completeness2 : forall A B, A *s2 B -> A *a B.
Proof.
  unfold DisjSpec2.
  intros A. induction A; intros B Disj.
  - apply ad_uninh_r. apply cin_false_uninh.
    rewrite overlaps_b_top_l in Disj. exact Disj.
  - induction B.
    + simpl in Disj. discriminate.
    + simpl in Disj. discriminate.
    + apply ad_btmr.
    + apply ad_intl.
    + destruct (overlaps_union_false_r _ _ _ Disj).
      apply ad_orr; apply Disj_sym; auto.
    + apply ad_unit_intr.
  - apply ad_btml.
  - induction B.
    + apply ad_uninh_l. apply uh_arrow. apply cin_false_uninh.
      rewrite overlaps_b_top_r in Disj. exact Disj.
    + apply ad_intr.
    + apply ad_btmr.
    + simpl in Disj.
      destruct (overlaps_b A1 B1) eqn:HA; destruct (overlaps_b A2 B2) eqn:HB;
        simpl in Disj; try discriminate.
      * apply ad_arrow. apply IHA2. exact HB.
      * apply ad_arrow_dom. apply IHA1. exact HA.
      * apply ad_arrow. apply IHA2. exact HB.
    + destruct (overlaps_union_false_r _ _ _ Disj).
      apply ad_orr; apply Disj_sym; auto.
    + apply ad_unit_arrowr.
  - destruct (overlaps_union_false_l _ _ _ Disj).
    apply ad_orl; auto.
  - induction B.
    + simpl in Disj. discriminate.
    + apply ad_unit_intl.
    + apply ad_btmr.
    + apply ad_unit_arrowl.
    + destruct (overlaps_union_false_r _ _ _ Disj).
      apply ad_orr; apply Disj_sym; auto.
    + simpl in Disj. discriminate.
Qed.

Lemma Disj_equiv2 : forall A B, A *a B <-> A *s2 B.
Proof.
  split; [apply Disj_soundness2 | apply Disj_completeness2].
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

(* Completeness *s1 ⇒ *a still holds (the range rule is enough).
   Soundness *a ⇒ *s1 does not, because of ad_arrow_dom.
   The spec that is both sound and complete is *s2 (Disj_equiv2). *)

Lemma arrow_disj_from_range : forall A1 B1 A2 B2,
  B1 *a B2 -> (t_arrow A1 B1) *a (t_arrow A2 B2).
Proof.
  intros. apply* ad_arrow.
Qed.

Lemma arrow_disj_from_domain : forall A1 B1 A2 B2,
  A1 *a A2 -> (t_arrow A1 B1) *a (t_arrow A2 B2).
Proof.
  intros. apply* ad_arrow_dom.
Qed.

(* Range example (same as section3): different ranges. *)
Lemma arrow_int_unit_disjoint :
  (t_arrow t_top t_int) *a (t_arrow t_bot t_unit).
Proof.
  apply ad_arrow. apply ad_unit_intr.
Qed.

(* Domain example: same range, disjoint domains. *)
Lemma arrow_int_unit_dom_disjoint :
  (t_arrow t_int t_int) *a (t_arrow t_unit t_int).
Proof.
  apply ad_arrow_dom. apply ad_unit_intr.
Qed.