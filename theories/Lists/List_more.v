Require Export List.
Require Import PeanoNat.
Require Import Lt Le Plus Max.
Require Import Lia.


(* not for stdlib *)
Ltac list_simpl :=
  repeat (
    repeat simpl ;
    repeat rewrite <- app_assoc ;
    repeat rewrite <- app_comm_cons ;
    repeat rewrite app_nil_r ;
    repeat rewrite <- map_rev ;
    repeat rewrite rev_involutive ;
    repeat rewrite rev_app_distr ;
    repeat rewrite rev_unit ;
    repeat rewrite map_app ).
Ltac list_simpl_hyp H :=
  repeat (
    repeat simpl in H ;
    repeat rewrite <- app_assoc in H ;
    repeat rewrite <- app_comm_cons in H ;
    repeat rewrite app_nil_r in H ;
    repeat rewrite <- map_rev in H ;
    repeat rewrite rev_involutive in H ;
    repeat rewrite rev_app_distr in H ;
    repeat rewrite rev_unit in H ;
    repeat rewrite map_app in H ).
Tactic Notation "list_simpl" "in" hyp(H) := list_simpl_hyp H.
Ltac list_simpl_hyps :=
  match goal with
  | H : _ |- _ => list_simpl in H ; revert H ; list_simpl_hyps ; intro H
  | _ => idtac
  end.
Ltac list_simpl_all := list_simpl_hyps ; list_simpl.

(* not for stdlib *)
Lemma cons_is_app {A} : forall (x:A) l, x :: l = (x :: nil) ++ l.
Proof.
reflexivity.
Qed.
Ltac cons2app :=
  repeat
  match goal with
  | |- context [ cons ?x ?l ] =>
         lazymatch l with
         | nil => fail
         | _ => rewrite (cons_is_app x l)
           (* one could prefer
                 change (cons x l) with (app (cons x nil) l)
              which leads to simpler generated term
              but does work not with existential variables *)
         end
  end.
Ltac cons2app_hyp H :=
  repeat
  match type of H with
  | context [ cons ?x ?l ]  =>
      lazymatch l with
      | nil => fail
      | _ =>  rewrite (cons_is_app x l) in H
           (* one could prefer
                 change (cons x l) with (app (cons x nil) l) in
              which leads to simpler generated term
              but does work not with existential variables *)
      end
  end.
Tactic Notation "cons2app" "in" hyp(H) := cons2app_hyp H.
Ltac cons2app_hyps :=
  match goal with
  | H : _ |- _ => cons2app in H ; revert H ; cons2app_hyps ; intro H
  | _ => idtac
  end.
Ltac cons2app_all := cons2app_hyps ; cons2app.

(* not for stdlib *)
Ltac unit_vs_elt_inv H :=
  match type of H with
  | ?a :: nil = ?l1 ++ ?x :: ?l2 =>
      let H1 := fresh H in
      let H2 := fresh H in
        destruct l1 ; inversion H as [[H1 H2]] ;
        [ (try subst x) ; (try subst l2)
        | destruct l1 ; inversion H2 ]
  end.

(* not for stdlib *)
Lemma dichot_app {A} : forall (l1 : list A) l2 l3 l4,
  l1 ++ l2 = l3 ++ l4 ->
     (exists l2', l1 ++ l2' = l3 /\ l2 = l2' ++ l4)
  \/ (exists l4', l1 = l3 ++ l4' /\ l4' ++ l2 = l4).
Proof with try assumption ; try reflexivity.
induction l1 ; induction l3 ; intros ;
  simpl in H ; inversion H ; subst.
- right.
  exists (@nil A).
  split ; simpl...
- left.
  exists (a::l3).
  split...
- right.
  exists (a::l1).
  split ; simpl...
- inversion H.
  apply IHl1 in H1.
  destruct H1 as [(l2' & H2'1 & H2'2) | (l4' & H4'1 & H4'2)] ;
    [left | right].
  + exists l2'.
    split...
    simpl.
    rewrite H2'1...
  + exists l4'.
    split...
    simpl.
    rewrite H4'1...
Qed.
Ltac dichot_app_exec H :=
  match type of H with
  | _ ++ _ = _ ++ _ => apply dichot_app in H ;
                         let l2 := fresh "l" in
                         let l4 := fresh "l" in
                         let H1 := fresh H in
                         let H2 := fresh H in
                         destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  end.

(* not for stdlib *)
Lemma dichot_elt_app {A} : forall l1 (a : A) l2 l3 l4,
  l1 ++ a :: l2 = l3 ++ l4 ->
     (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4)
  \/ (exists l4', l1 = l3 ++ l4' /\ l4' ++ a :: l2 = l4).
Proof with try reflexivity.
induction l1 ; induction l3 ; intros ;
  simpl in H ; inversion H ; subst.
- right.
  exists (@nil A).
  split ; simpl...
- left.
  exists l3.
  split...
- right.
  exists (a::l1).
  split ; simpl...
- inversion H.
  apply IHl1 in H1.
  destruct H1 as [(l' & H'1 & H'2) | (l' & H'1 & H'2)] ;
    [left | right] ;
    exists l' ;
    (split ; try assumption) ;
    simpl ;
    rewrite H'1...
Qed.
Ltac dichot_elt_app_exec H :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ => apply dichot_elt_app in H ;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  | _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H ;
                            apply dichot_elt_app in H ;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  end.

(* not for stdlib *)
Lemma trichot_elt_app {A} : forall l1 (a : A) l2 l3 l4 l5,
  l1 ++ a :: l2 = l3 ++ l4 ++ l5 ->
      (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4 ++ l5)
   \/ (exists l2' l2'', l1 = l3 ++ l2' /\ l2' ++ a :: l2'' = l4 /\ l2 = l2'' ++ l5)
   \/ (exists l5', l1 = l3 ++ l4 ++ l5' /\ l5' ++ a :: l2 = l5).
Proof with try reflexivity ; try assumption.
induction l1 ; induction l3 ; intros ;
  simpl in H ; inversion H ; subst.
- destruct l4 ; inversion H.
  + right ; right ; exists nil ; split...
  + right ; left ; exists nil ; exists l4 ; split ; [ | split ]...
- left ; exists l3 ; split...
- destruct l4 ; inversion H ; subst.
  + right ; right ; exists (a :: l1) ; split...
  + dichot_elt_app_exec H3 ; subst.
    * right ; left ; exists (a1 :: l1) ; exists l ; split ; [ | split ]...
    * right ; right ; exists l0 ; split...
- apply IHl1 in H2.
  destruct H2 as [(l' & H'1 & H'2) | [ (l2' & l2'' & H'2 & H'3) | (l' & H'1 & H'2) ]] ;
    [ left | right ; left | right ; right ].
  + exists l' ; try rewrite <- H'1 ; split...
  + destruct H'3 ; subst ; exists l2' ; exists l2'' ; split ; [ | split ]...
  + exists l' ; try rewrite H'1 ; split...
Qed.
Ltac trichot_elt_app_exec H :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ ++ _ => apply trichot_elt_app in H ;
                                   let l2 := fresh "l" in
                                   let l4 := fresh "l" in
                                   let H1 := fresh H in
                                   let H2 := fresh H in
                                   destruct H as [ (l2 & H1 & H2)
                                                 | [ (l2 & l4 & H1 & H2) | (l4 & H1 & H2) ]]
  | _ ++ _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H ;
                                   apply trichot_elt_app in H ;
                                   let l2 := fresh "l" in
                                   let l4 := fresh "l" in
                                   let H1 := fresh H in
                                   let H2 := fresh H in
                                   destruct H as [ (l2 & H1 & H2)
                                                 | [ (l2 & l4 & H1 & H2) | (l4 & H1 & H2) ]]
  end.

(* not for stdlib *)
Lemma trichot_elt_elt {A} : forall l1 (a : A) l2 l3 b l4,
  l1 ++ a :: l2 = l3 ++ b :: l4 ->
      (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ b :: l4)
   \/ (l1 = l3 /\ a = b /\ l2 = l4)
   \/ (exists l4', l1 = l3 ++ b :: l4' /\ l4' ++ a :: l2 = l4).
Proof with try assumption ; try reflexivity.
intros l1 a l2 l3 b l4 Heq.
change (b :: l4) with ((b :: nil) ++ l4) in Heq.
apply trichot_elt_app in Heq ;
  destruct Heq as [ | [ (l2' & l2'' & H'1 & H'2 & H'3) | ]] ; subst ;
  [ left | right ; left | right ; right ]...
destruct l2' ; inversion H'2 ; subst ; [ | destruct l2' ; inversion H1 ].
split ; [ | split ]...
rewrite app_nil_r...
Qed.
Ltac trichot_elt_elt_exec H :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l1 ++ ?x :: ?l2 =>
      apply trichot_elt_elt in H ;
        let l' := fresh "l" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        destruct H as [(l' & H1 & H2) | [(H1 & H2 & H3) | (l' & H1 & H2)]] ;
        [ (try subst l1) ; (try subst lr)
        | (try subst x) ; (try subst l1) ; (try subst l2)
        | (try subst l2) ; (try subst lh) ]
  end.








Lemma remove_cons {A} : forall Hdec l (x : A), remove Hdec x (x :: l) = remove Hdec x l.
Proof. induction l; simpl; intros x; destruct (Hdec x x); try reflexivity; now exfalso. Qed.

Lemma remove_app {A} : forall Hdec l1 l2 (x : A),
  remove Hdec x (l1 ++ l2) = remove Hdec x l1 ++ remove Hdec x l2.
Proof.
induction l1; intros l2 x; simpl.
- reflexivity.
- destruct (Hdec x a).
  + apply IHl1.
  + rewrite <- app_comm_cons; f_equal.
    apply IHl1.
Qed.

Lemma remove_remove_eq {A} : forall Hdec l (x : A), remove Hdec x (remove Hdec x l) = remove Hdec x l.
Proof.
induction l; simpl; intros x; [ reflexivity | ].
destruct (Hdec x a).
- apply IHl.
- simpl; destruct (Hdec x a).
  + now exfalso.
  + now rewrite IHl.
Qed.

Lemma remove_remove_neq {A} : forall Hdec l (x y: A), x <> y ->
  remove Hdec x (remove Hdec y l) = remove Hdec y (remove Hdec x l).
Proof.
induction l; simpl; intros x y Hneq; [ reflexivity | ].
destruct (Hdec y a); simpl; destruct (Hdec x a); subst.
- now apply IHl.
- rewrite remove_cons; now apply IHl.
- now apply IHl.
- simpl; destruct (Hdec y a).
  + now exfalso.
  + now rewrite IHl.
Qed.

Lemma in_remove {A} : forall Hdec l (x y : A), In x (remove Hdec y l) -> In x l /\ x <> y.
Proof.
induction l; intros x y Hin.
- inversion Hin.
- simpl in Hin.
  destruct (Hdec y a); subst; split.
  + right; now apply IHl with a.
  + intros Heq; revert Hin; subst; apply remove_In.
  + inversion Hin; subst; [left; reflexivity|right].
    now apply IHl with y.
  + inversion Hin; subst.
    * now intros Heq; apply n.
    * intros Heq; revert H; subst; apply remove_In.
Qed.

Lemma in_in_remove {A} : forall Hdec l (x y : A), x <> y -> In x l -> In x (remove Hdec y l).
Proof.
induction l; simpl; intros x y Hneq Hin.
- inversion Hin.
- destruct (Hdec y a); subst.
  + destruct Hin.
    * exfalso; now apply Hneq.
    * now apply IHl.
  + simpl; destruct Hin; [now left|right].
    now apply IHl.
Qed.


(** ** Decomposition of [map] *)

(* not for stdlib ? *)
Lemma app_eq_map {A B} : forall (f : A -> B) l1 l2 l3,
  l1 ++ l2 = map f l3 ->
    exists l1' l2', l3 = l1' ++ l2' /\ l1 = map f l1' /\ l2 = map f l2'.
Proof with try assumption ; try reflexivity.
intros f.
induction l1 ; intros.
- exists (@nil A) ; exists l3.
  split ; [ | split]...
- destruct l3 ; inversion H.
  apply IHl1 in H2.
  destruct H2 as (? & ? & ? & ? & ?) ; subst.
  exists (a0::x) ; exists x0.
  split ; [ | split]...
Qed.

(* not for stdlib ? *)
Lemma cons_eq_map {A B} : forall (f : A -> B) a l2 l3,
  a :: l2 = map f l3 ->
    exists b l2', l3 = b :: l2' /\ a = f b /\ l2 = map f l2'.
Proof.
intros f a l2 l3 H.
destruct l3 ; inversion H ; subst.
eexists ; eexists ; split ; [ | split] ;
  try reflexivity ; try eassumption.
Qed.

(* not for stdlib ? *)
Ltac decomp_map_eq H Heq :=
  match type of H with
  | _ ++ _ = map _ _ => apply app_eq_map in H ;
                          let l1 := fresh "l" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as (l1 & l2 & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_eq H1 Heq ; decomp_map_eq H2 Heq
  | _ :: _ = map _ _ => apply cons_eq_map in H ;
                          let x := fresh "x" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as (x & l2 & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_eq H2 Heq
  | _ => idtac
  end.
Ltac decomp_map H :=
  match type of H with
  | _ = map _ ?l => let l' := fresh "l" in
                    let Heq := fresh H in
                    remember l as l' eqn:Heq in H ;
                    decomp_map_eq H Heq ;
                    let H' := fresh H in
                    clear l' ;
                    rename Heq into H'
  end.




(** ** [Forall] and [Exists] *)

Lemma Forall_fold_right {A} : forall P (l : list A),
  Forall P l <-> fold_right (fun x Q => and (P x) Q) True l.
Proof.
induction l; simpl; split; intros H.
- constructor.
- constructor.
- inversion H as [ | ? ? Ha Hl ]; subst; apply IHl in Hl; now split.
- destruct H as [Ha Hl]; apply IHl in Hl; now constructor.
Qed.

Lemma Exists_fold_right {A} : forall P (l : list A),
  Exists P l <-> fold_right (fun x Q => or (P x) Q) False l.
Proof.
induction l; simpl; split; intros H.
- inversion H.
- inversion H.
- inversion H as [ ? ? Ha | ? ? Hl ]; subst.
  + now left.
  + apply IHl in Hl; now right.
- destruct H as [Ha | Hl]; [ | apply IHl in Hl]; now constructor.
Qed.

Lemma Forall_app {A} : forall P (l1 : list A) l2,
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof with try assumption.
induction l1 ; intros...
inversion H ; subst.
apply IHl1 in H0...
constructor...
Qed.

Lemma Forall_app_inv {A} : forall P (l1 : list A) l2,
  Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2.
Proof with try assumption.
induction l1 ; intros.
- split...
  constructor.
- inversion H ; subst.
  apply IHl1 in H3.
  destruct H3.
  split...
  constructor...
Qed.

Lemma Forall_elt {A} : forall P l1 l2 (a : A), Forall P (l1 ++ a :: l2) -> P a.
Proof.
intros P l1 l2 a HF.
eapply Forall_forall ; try eassumption.
apply in_elt.
Qed.

Lemma Forall_nth {A} : forall P l,
  Forall P l -> forall i (a : A), i < length l -> P (nth i l a).
Proof with try assumption.
induction l ; intros.
- inversion H0.
- destruct i ; inversion H...
  simpl in H0.
  apply IHl...
  apply lt_S_n...
Qed.

(* not for stdlib ? *)
Lemma exists_Forall {A B} : forall (P : A -> B -> Prop) l,
  (exists k, Forall (P k) l) -> Forall (fun x => exists k, P k x) l .
Proof with try eassumption ; try reflexivity.
induction l ; intros ; constructor ;
  destruct H as [k H] ; inversion H ; subst.
- eexists...
- apply IHl...
  eexists...
Qed.

Lemma Forall_image {A B} : forall (f : A -> B) l,
  Forall (fun x => exists y, x = f y) l <-> exists l0, l = map f l0.
Proof with try reflexivity.
induction l ; split ; intro H.
- exists (@nil A)...
- constructor.
- inversion H ; subst.
  destruct H2 as [y Hy] ; subst.
  apply IHl in H3.
  destruct H3 as [l0 Hl0] ; subst.
  exists (y :: l0)...
- destruct H as [l0 Heq].
  destruct l0 ; inversion Heq ; subst.
  constructor.
  + exists a0...
  + apply IHl.
    exists l0...
Qed.

Lemma map_ext_Forall {A B} : forall (f g : A -> B) l,
  Forall (fun x => f x = g x) l -> map f l = map g l.
Proof.
intros ; apply map_ext_in ; apply Forall_forall ; assumption.
Qed.

Lemma Forall_rev {A} : forall P (l : list A), Forall P l -> Forall P (rev l).
Proof with try assumption.
induction l ; intros HP.
- constructor.
- inversion HP ; subst.
  apply IHl in H2.
  apply Forall_app...
  constructor...
  constructor.
Qed.

(* not for stdlib ? *)
Lemma inc_Forall {A} : forall (P : nat -> A -> Prop) l i j,
  (forall i j a, P i a -> i <= j -> P j a) ->
    Forall (P i) l -> i <= j -> Forall (P j) l.
Proof with try eassumption.
intros P l i j Hinc.
induction l ; intros H Hl ; constructor ; inversion H.
- eapply Hinc...
- apply IHl...
Qed.

Lemma Exists_app {A} : forall (P : A -> Prop) l1 l2,
  Exists P l1 \/ Exists P l2 -> Exists P (l1 ++ l2).
Proof with try assumption.
induction l1 ; intros...
- destruct H...
  inversion H.
- destruct H.
  + inversion H ; subst.
    * apply Exists_cons_hd...
    * apply Exists_cons_tl.
      apply IHl1.
      left...
  + apply Exists_cons_tl.
    apply IHl1.
    right...
Qed.

Lemma Exists_app_inv {A} : forall (P : A -> Prop) l1 l2,
  Exists P (l1 ++ l2) -> Exists P l1 \/ Exists P l2.
Proof with try assumption.
induction l1 ; intros.
- right...
- inversion H ; subst.
  + left.
    apply Exists_cons_hd...
  + apply IHl1 in H1.
    destruct H1.
    * left.
      apply Exists_cons_tl...
    * right...
Qed.

Lemma Exists_rev {A} : forall P (l : list A), Exists P l -> Exists P (rev l).
Proof with try assumption.
induction l ; intros HP ; inversion HP ; subst ;
  apply Exists_app.
- right ; constructor...
- left.
  apply IHl...
Qed.

(** ** [In] *)


Lemma in_flat_map_Exists {A B : Type} : forall (f : A -> list B) x l,
  In x (flat_map f l) <-> Exists (fun y => In x (f y)) l.
Proof. intros f x l; rewrite in_flat_map; split; apply Exists_exists. Qed.

Lemma notin_flat_map_Forall {A B : Type} : forall (f : A -> list B) x l,
  ~ In x (flat_map f l) <-> Forall (fun y => ~ In x (f y)) l.
Proof. intros f x l; rewrite Forall_Exists_neg; apply not_iff_compat, in_flat_map_Exists. Qed.


(** ** Map for functions with two arguments : [map2] *)

Fixpoint map2 {A B C} (f : A -> B -> C) l1 l2 :=
  match l1 , l2 with
  | nil , _ => nil
  | _ , nil => nil
  | a1::r1 , a2::r2 => (f a1 a2)::(map2 f r1 r2)
  end.

Lemma map2_length {A B C} : forall (f : A -> B -> C) l1 l2,
  length l1 = length l2 -> length (map2 f l1 l2) = length l2.
Proof with try assumption ; try reflexivity.
induction l1 ; intros...
destruct l2.
+ inversion H.
+ simpl in H.
  injection H ; intro H'.
  apply IHl1 in H'.
  simpl...
  rewrite H'...
Qed.

Lemma length_map2 {A B C} : forall (f : A -> B -> C) l1 l2,
  length (map2 f l1 l2) <= length l1 /\ length (map2 f l1 l2) <= length l2.
Proof.
induction l1 ; intros.
- split ; apply le_0_n.
- destruct l2.
  + split ; apply le_0_n.
  + destruct (IHl1 l2) as [H1 H2].
    split ; simpl ; apply le_n_S ; assumption.
Qed.

Lemma nth_map2 {A B C} : forall (f : A -> B -> C) l1 l2 i a b c,
  i < length (map2 f l1 l2) ->
    nth i (map2 f l1 l2) c = f (nth i l1 a) (nth i l2 b).
Proof with try assumption ; try reflexivity.
induction l1 ; intros.
- inversion H.
- destruct l2.
  + inversion H.
  + destruct i...
    simpl.
    apply IHl1.
    simpl in H.
    apply lt_S_n...
Qed.


(** ** Sum of elements of a list of [nat] : [list_sum] *)

Definition list_sum l := fold_right plus 0 l.

Lemma list_sum_app : forall l1 l2,
   list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof with try reflexivity.
induction l1 ; intros l2...
simpl ; rewrite IHl1.
rewrite plus_assoc...
Qed.

(** ** Max of elements of a list of [nat] : [list_max] *)

Definition list_max l := fold_right max 0 l.

Lemma list_max_app : forall l1 l2,
   list_max (l1 ++ l2) = max (list_max l1) (list_max l2).
Proof with try reflexivity.
induction l1 ; intros l2...
simpl ; rewrite IHl1.
rewrite max_assoc...
Qed.

(* Properties on nth *)
Lemma nth_nth {A} : forall (l1 : list nat) (l2 : list A) a0 k0 k,
    k < length l1 ->
    nth (nth k l1 k0) l2 a0 = nth k (map (fun x => nth x l2 a0) l1) a0.
Proof with try assumption; try reflexivity.
  induction l1; intros l2 a0 k0 k Hlt.
  - inversion Hlt.
  - destruct k...
    simpl.
    apply IHl1.
    simpl in Hlt.
    lia.
Qed.

Lemma nth_plus {A} : forall (l1 : list A) l2 k0 k,
    nth (length l1 + k) (l1 ++ l2) k0 = nth k l2 k0.
Proof with try reflexivity; try assumption.
  induction l1; intros k2 k0 k...
  simpl.
  apply IHl1...
Qed.

Lemma nth_middle {A} : forall la lb (a : A) a0,
    nth (length la) (la ++ a :: lb) a0 = a.
Proof with try reflexivity.
  induction la; intros lb a' a0...
  simpl.
  apply IHla.
Qed.

Lemma list_ext {A} : forall l1 l2,
    length l1 = length l2 ->
    (forall n (a0 : A), nth n l1 a0 = nth n l2 a0) ->
    l1 = l2.
Proof with try reflexivity.
  induction l1; intros l2 Hlen H.
  - destruct l2; try now inversion Hlen...
  - destruct l2; try now inversion Hlen.
    replace a0 with a.
    2:{ change a with (nth 0 (a :: l1) a).
        change a0 with (nth 0 (a0 :: l2) a).
        apply H. }
    apply Nat.succ_inj in Hlen.
    specialize (IHl1 l2 Hlen).
    clear Hlen.
    replace l2 with l1...
    apply IHl1.
    intros n a1.
    refine (H (S n) a1).
Qed.

Lemma nth_split_Type {A} n l (d:A) : n < length l ->
    {' (l1,l2) : _ & l = l1 ++ nth n l d :: l2 & length l1 = n }.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|a l] H; try (exfalso; easy).
    - exists (nil,l); now simpl.
    - destruct (IH l) as [(l1,l2) Hl Hl1]; auto with arith.
      exists (a::l1,l2); simpl; now f_equal.
  Qed.

(* fold_right *)
Lemma fold_right_app_assoc2 {A B} f (g : B -> A) h (e : A) l1 l2 :
    (forall x y z, h (g x) (f y z) = f (h (g x) y) z) ->
    (f e (fold_right (fun x => h (g x)) e l2) = (fold_right (fun x => h (g x)) e l2)) ->
  fold_right (fun x => h (g x)) e (l1 ++ l2) =
  f (fold_right (fun x => h (g x)) e l1) (fold_right (fun x => h (g x)) e l2).
Proof.
intros Hassoc Hunit.
rewrite fold_right_app.
remember (fold_right (fun x => f (g x)) e l2) as r.
induction l1; simpl.
- symmetry; apply Hunit.
- rewrite <- Hassoc.
  f_equal; assumption.
Qed.

Lemma fold_right_app_assoc {A} f (e : A) l1 l2 :
  (forall x y z, f x (f y z) = f (f x y) z) -> (forall x, f e x = x) ->
  fold_right f e (l1 ++ l2) = f (fold_right f e l1) (fold_right f e l2).
Proof. intros Hassoc Hunit; apply fold_right_app_assoc2; [ assumption | apply Hunit ]. Qed.

(* fold_left max *)
Lemma fold_left_max_r : forall f a, a <= fold_left max f a.
Proof with try reflexivity.
  induction f; intros k...
  simpl.
  transitivity (max k a).
  - apply Nat.le_max_l.
  - apply IHf.
Qed.

Lemma fold_left_max_le_r : forall l i j, i <= j -> fold_left max l i <= fold_left max l j.
Proof with try reflexivity; try assumption.
  clear; induction l; intros i j Hle...
  simpl.
  apply IHl.
  lia.
Qed.

Lemma fold_left_max_indep : forall i l, i < fold_left max l i ->
  forall j, fold_left max l i <= fold_left max l j.
Proof with try assumption; try reflexivity.
  intros i l; revert i; induction l; intros i Hlt j.
  - simpl in Hlt.
    exfalso; lia.
  - simpl in *.
    case_eq (max i a <? fold_left max l (max i a)); intros Hcase.
    + apply Nat.ltb_lt in Hcase.
      apply IHl...
    + apply Nat.ltb_nlt in Hcase.
      assert (i < a) by lia.
      replace (max i a) with a in * by lia.
      apply fold_left_max_le_r.
      lia.
Qed.

Lemma fold_left_max_le : forall l i j, fold_left max l i <= j -> fold_left max l j <= j.
Proof with try assumption;try reflexivity.
  induction l; intros i j Hle...
  simpl.
  simpl in Hle.
  replace j with (max j a) at 2.
  2:{ apply Nat.max_l.
      transitivity (max i a) ; [lia | ].
      transitivity (fold_left max l (max i a)).
      - apply fold_left_max_r.
      - apply Hle. }
  apply IHl with (max i a).
  transitivity j; lia.
Qed.

Lemma fold_left_max_app : forall k l1 l2,
  fold_left max (l1 ++ l2) k = max (fold_left max l1 k) (fold_left max l2 k).
Proof with try assumption; try reflexivity.
  intros k l1; revert k; induction l1; intros k l2.
  - simpl.
    symmetry.
    apply Nat.max_r.
    apply fold_left_max_r.
  - simpl.
    rewrite IHl1.
    case_eq (fold_left max l2 k <=? max k a); intros Hcase.
    + transitivity (fold_left max l1 (max k a)).
      * apply Nat.max_l.
        apply Nat.leb_le in Hcase.
        transitivity (max k a).
        -- apply fold_left_max_le with k...
        -- apply fold_left_max_r.
      * symmetry.
        apply Nat.max_l.
        apply Nat.leb_le in Hcase.
        transitivity (max k a)...
        apply fold_left_max_r.
    + replace (fold_left max l2 k) with (fold_left max l2 (max k a))...
      apply Nat.le_antisymm.
      * apply fold_left_max_indep.
        apply Nat.leb_nle in Hcase.
        apply Nat.lt_le_trans with (fold_left max l2 k).
        -- lia.
        -- apply fold_left_max_le_r.
           lia.
      * apply fold_left_max_le_r.
        lia.
Qed.



(** ** Definition and properties of the constant list *)
(* not for stdlib ? *)
Fixpoint const_list {A} n (a : A) :=
  match n with
  | 0 => nil
  | S n => a :: (const_list n a)
  end.

(* not for stdlib ? *)
Lemma const_list_length {A} : forall n (a : A),
  length (const_list n a) = n.
Proof with try reflexivity.
intros n a; induction n...
simpl; rewrite IHn...
Qed.

(* not for stdlib ? *)
Lemma const_list_cons {A} : forall n (a : A),
  a :: const_list n a = const_list n a ++ (a :: nil).
Proof with try reflexivity.
induction n; intros a...
simpl; rewrite IHn...
Qed.

(* not for stdlib ? *)
Lemma const_list_to_concat {A} : forall n (a : A),
  const_list n a = concat (const_list n (a :: nil)).
Proof with try reflexivity.
induction n; intros a...
simpl; rewrite IHn...
Qed.

(* not for stdlib ? *)
Lemma In_const_list {A} : forall n (a : A) b,
  In b (const_list n a) -> b = a.
Proof.
induction n; intros a b Hin; inversion Hin; subst; [ reflexivity | now apply IHn ].
Qed.
