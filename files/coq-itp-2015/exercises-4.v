Require Import Coq.Lists.List.
Import ListNotations.

(* Heterogeneous lists *)
(***********************)
Section hlist.
(* Heterogeneous lists are lists where the elements of the
 * list can have different types. In Coq, we can define
 * heterogeneous lists by indexing an inductive type by
 * a list of types, one for each element. For convenience
 * in the future however, we will index our type by an
 * a type [iT] and a function (F) that computes a type from
 * [iT]. This will make our definition a little bit easier
 * to use in the next exercise.
 *)
Variable iT : Type.
Variable F : iT -> Type.

Inductive hlist : list iT -> Type :=
| Hnil : hlist nil
| Hcons : forall {T Ts}, F T -> hlist Ts -> hlist (T :: Ts).

(* Exercise: Implement the head and tail functions for hlists.
 *)
Definition hlist_hd {T Ts} (h : hlist (T :: Ts)) : F T.
Admitted.

Definition hlist_tl {T Ts} (h : hlist (T :: Ts)) : hlist Ts.
Admitted.

(* If we want to compute the nth-element of an hlist, we need
 * a way to write the type that we are going to get back.
 * One way to do this is to use computation in types.
 *
 * Exercise: Implement this function.
 *)
Fixpoint hlist_nth' {Ts} {h : hlist Ts} (n : nat)
: option match nth_error Ts n with
         | None => Empty_set
         | Some T => F T
         end.
Admitted.

(* An alternative solution is to build an inductive
 * type that carries the information about the value that
 * we find at a particular location in the list.
 *)
Inductive mem {T : Type} (t : T) : list T -> Type :=
| MO : forall {ts}, mem t (t :: ts)
| MS : forall {t' ts}, mem t ts -> mem t (t' :: ts).

Arguments MO {_ _ _}.
Arguments MS {_ _ _ _} _.

(* Exercise: Implement hlist_nth with the following type.
 *)
Fixpoint hlist_nth {T Ts} (h : hlist Ts) (n : mem T Ts) : F T.
Admitted.

End hlist.

Arguments hlist {_} _ _.
Arguments hlist_hd {_ _ _ _} _.
Arguments hlist_tl {_ _ _ _} _.
Arguments hlist_nth {_ _ _ _} _ _.
Arguments Hnil {_ _}.
Arguments Hcons {_ _ _ _} _ _.

Arguments MO {_ _ _}.
Arguments MS {_ _ _ _} _.

Section mem_dec.
  Variable T : Type.
  (* In order to implement decidable equality for [mem], we
   * need decidable equality for the type T. The reason for
   * this is a little bit unintuitive but it turns out to be
   * true.
   *)
  Variable T_dec : forall a b : T, a = b \/ a <> b.

  Lemma MS_inj : forall t t' ts (m m' : mem t ts),
      @MS T t t' ts m = MS m' ->
      m = m'.
  Proof.
    intros.
    refine
      match H in _ = M
            return match M in mem _ ts return mem _ (tl ts) -> Prop with
                   | MO _ => fun _ => True
                   | MS _ _ m'' => fun m => m = m''
                   end m
      with
      | eq_refl => eq_refl
      end.
  Defined.

  (* A theorem in Coq tells us that decidable equality on
   * a type [T] implies proof irrelevence for proofs of equality
   * of values of type [T].
   *)
  Require Import Coq.Logic.Eqdep_dec.

  Fixpoint mem_dec {ts : list T} {t : T} (a : mem t ts)
  : forall b : mem t ts, {a = b} + {a <> b}.
  refine
    match a as a in mem _ ts
          return forall b : mem t ts, {a = b} + {a <> b}
    with
    | MO _ => fun b =>
      match b as b in mem _ ts
            return match ts as ts return mem t ts -> Type with
                   | nil => fun _ => unit
                   | t' :: ts => fun b =>
                                   forall pf : t' = t,
                                     {MO = match pf with
                                           | eq_refl => b
                                           end} +
                                     {MO <> match pf with
                                            | eq_refl => b
                                            end}
                   end b
      with
      | MO _ => fun _ => left _
      | MS _ _ m'' => fun _ => right _
      end eq_refl
    | MS t' ts' m' => fun (b : mem t (t' :: ts')) =>
      match b as b in mem _ ts
            return forall m' : mem t (tl ts),
          (forall b, {m' = b} + {m' <> b}) ->
          match ts as ts return mem t ts -> mem t (tl ts) -> Type with
          | nil => fun _ _ => unit
          | t'' :: ts'' => fun (b : mem t (t'' :: ts'')) m' =>
                             {MS m' = b} +
                             {MS m' <> b}
          end b m'
      with
      | MO _ => fun _ _ => right _
      | MS _ _ m'' => fun _ rec =>
                        match rec m'' with
                        | left _ => left _
                        | right _ => right _
                        end
      end m' (fun b => mem_dec _ _ m' b)
    end.
  Proof.
  { eapply K_dec with (p := pf); auto. }
  { subst. intro. inversion H. }
  { clear. red; intro. inversion H. }
  { f_equal. assumption. }
  { clear - n. intro. apply n.
    eapply MS_inj in H. assumption. }
  Defined.
End mem_dec.

(* A simple Lambda-calculus *)
(****************************)

(* We can use dependent types to describe "well-typed" terms.
 * We start with a type of types.
 *)
Inductive type : Type :=
| Nat
.

(* I've started a simple definition with just constants, addition
 * and variables.
 *)
Inductive expr (ts : list type) : type -> Type :=
| ConstNat : nat -> expr ts Nat
| Plus     : expr ts Nat -> expr ts Nat -> expr ts Nat
| Var      : forall {t}, mem t ts -> expr ts t.

Arguments ConstNat {_} _.
Arguments Plus {_} _ _.
Arguments Var {_ _} _.

(* We can now write functions that map the syntactic definitions
 * into semantic ones.
 *)
Fixpoint typeD (t : type) : Type :=
  match t with
  | Nat => nat
  end.

Fixpoint exprD {ts : list type} {t : type} (e : expr ts t)
: hlist typeD ts -> typeD t :=
  match e in expr _ t return hlist typeD ts -> typeD t with
  | ConstNat n => fun _ => n
  | Plus a b => fun e => exprD a e + exprD b e
  | Var _ v => fun e => hlist_nth e v
  end.

Eval simpl in exprD (ConstNat 3) Hnil.
Eval simpl in exprD (Plus (ConstNat 3) (ConstNat 6)) Hnil.
Eval simpl in fun x : typeD Nat =>
                  exprD (Plus (Var MO) (ConstNat 6)) (Hcons x Hnil).

(* Exercise: Implement semi-decidable equality for this type.
 * (We can implement decidable equality, but it is a bit annoying
 *  due to constructing proofs of disequality.)
 * Avoid using tactics except to construct values whose type is
 * in Prop, i.e. only use tactics to prove equalities and
 * disequalities.
 *)
Fixpoint type_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2} :=
  match t1 as t1 , t2 as t2
        return {t1 = t2} + {t1 <> t2}
  with
  | Nat , Nat => left eq_refl
  end.

Fixpoint expr_dec {ts t} (e1 e2 : expr ts t) : option (e1 = e2).
Admitted.

(* Exercise: Implement a function that simplifies expressions.
 *)
Fixpoint simplify {ts t} (e : expr ts t) : expr ts t.
Admitted.

(* For example, you should optimize (1 + (2 + 3)) to 6. *)

(* Hint: It will be helpful to write a separate function that
 * performs simplification and use the simplify function to
 * apply this function recursively.
 *)

(* Exercise: The dependent types tell us that [simplify] preserves
 * typedness. Can you prove that it also preserves semantic meaning.
 *)
Theorem simplify_sound : forall ts t (e : expr ts t),
    forall env, exprD (simplify e) env = exprD e env.
Proof.
Admitted.

(* Exercise: Enrich the type language with booleans and the
 * expression language with boolean constants and if expressions.
 * Re-do all of the above functions/proofs.
 *
 * Note: expr_dec becomes a bit more complicated especially in the
 * constant cases.
 *
 * The simplifier should do simplifications of conditionals, i.e.
 *     [If (ConstBool true) tr fa] = [tr]
 *     [If (ConstBool false) tr fa] = [fa]
 *     [If test tr tr] = [tr]
 *)

(* Functional Dependent Types *)
(******************************)

(* In addition to defining types inductively, we can also define types
 * using definitions and fixpoints. A simple example is n-tuples.
 *)
Section tuple.
Variable T : Type.

Fixpoint tuple (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => T * tuple n
  end%type.

(* Exercise: Implement head, tail, and tappend for tuples. *)

Definition tappend (a b : nat) (va : tuple a) (vb : tuple b)
: tuple (a + b).
Admitted.

Arguments tappend {_ _} _ _.

(* You will need to convert this definition into a fixpoint. What
 * are you doing induction on? How does this effect the performance?
 *)

(* [tuple n] is isomorphic to [vector T n].
 * Exercise: Write the two functions that witness this isomorphism
 * and prove that they form an isomorphism.
 *
 * I've repeated the definition of vector (from the lecture) here.
 *)
Inductive vector : nat -> Type :=
| Vnil : vector 0
| Vcons : forall {n}, T -> vector n -> vector (S n).

Definition tuple_to_vector {n} (t : tuple n) : vector n.
Admitted.

Definition vector_to_tuple {n} (t : vector n) : tuple n.
Admitted.

Theorem vector_tuple : forall n (v : vector n),
    tuple_to_vector (vector_to_tuple v) = v.
Admitted.

Theorem tuple_vector : forall n (t : tuple n),
    vector_to_tuple (tuple_to_vector t) = t.
Proof.
Admitted.

(* Exercise: Prove that tappend and vappend are related *)
Fixpoint vappend {a b} (va : vector a) (vb : vector b)
: vector (a + b) :=
  match va in vector a return vector (a + b) with
  | Vnil => vb
  | Vcons _ v vs => Vcons v (vappend vs vb)
  end.

Theorem vappend_tappend
: forall {a b} (va : vector a) (vb : vector b),
    vappend va vb =
    tuple_to_vector (tappend (vector_to_tuple va) (vector_to_tuple vb)).
Proof.
Admitted.
End tuple.

(* Step Indexed Types *)
(**********************)

(* One way to use functional dependent types is to create types that
 * Coq can not determine are strictly positive. These types can get
 * pretty complicated, but we can show the basic idea using a simple
 * tree data type.
 *)
Fixpoint mu (n : nat) (F : Type -> Type) : Type :=
  match n with
  | 0 => Empty_set
  | S n => F (mu n F)
  end.

Inductive treeF (T : Type) (Rec : Type) : Type :=
| Empty
| Branch : Rec -> T -> Rec -> treeF T Rec.

Arguments Empty {_ _}.
Arguments Branch {_ _} _ _ _.

(* Now we can use mu to take an approximation of the fixpoint.
 *)
Eval compute in mu 0 (treeF nat).
Eval compute in mu 1 (treeF nat).

(* To make the construction more transparent, we can wrap the
 * result in a dependent record.
 *)
Definition tree (T : Type) : Type :=
  { n : nat & mu n (treeF T) }.

(* Here are some constructors.
 *)
Definition empty {T} : tree T :=
  @existT _ _ 1 Empty.

(* Making a branch is a little more complicated because we need
 * to join the results since we don't have a true fixpoint.
 * To do this we can write some functions generic to mu
 *)

(* We can lift 'mu's as long as [F] has an fmap operation.
 * We'll need lifting so that we can make two subtrees the same
 * size.
 *)
Section lifting.
  Variable F : Type -> Type.
  Variable fmap : forall {T U}, (T -> U) -> F T -> F U.

  Fixpoint mu_lift (n : nat) (m : nat) {struct n}
  : mu n F -> mu (n + m) F :=
    match n as n return mu n F -> mu (n + m) F with
    | 0 => fun x : Empty_set => match x with end
    | S n => fun val : F (mu n F) =>
               @fmap _ _ (@mu_lift _ _) val
    end.
End lifting.

Theorem plus_comm : forall a b, a + b = b + a.
Proof.
  induction a.
  { induction b.
    { reflexivity. }
    { simpl. f_equal. assumption. } }
  { induction b; simpl.
    { f_equal. apply IHa. }
    { simpl. f_equal.
      rewrite IHa. rewrite <- IHb.
      simpl. f_equal. symmetry. apply IHa. } }
Defined.

Definition Functor_treeF {X} (T U : Type) (f : T -> U) (v : treeF X T)
: treeF X U :=
  match v with
  | Empty => Empty
  | Branch l v r => Branch (f l) v (f r)
  end.

(* Finally, we can implement branch.
 *)
Definition branch {T} (l : tree T) (v : T) (r : tree T) : tree T :=
  match l , r with
  | existT nl vl , existT nr vr =>
    let join := nl + nr in
    @existT _ (fun n => mu n (treeF T)) (1 + join)
            (Branch (@mu_lift _ Functor_treeF nl nr vl)
                    v
                    match eq_sym (plus_comm nl nr) with
                    | eq_refl => mu_lift _ Functor_treeF nr nl vr
                    end)
  end.

(* Optional Exercise: This definition works but it is a little bit clunky.
 * In particular, we only need [1 + max nl nr] "steps" to build the
 * new tree. Can you change the above definition to accomplish this?
 * Note, that in order to make it compute, you'll need to transparent proofs
 * about [max].
 *)

(* We can now build trees in the usual way.
 *)
Eval compute in branch empty 1 empty.
Eval compute in branch empty 3 (branch empty 7 empty).

(* Exercise: Prove that tree is a functor.
 * (Note, above we showed that treeF is a functor, that is what allowed
 *  us to lift the sub-trees.)
 * (Hint: You will want to prove a generic lemma about mu)
 *)
Definition Functor_tree {T U} (f : T -> U) : tree T -> tree U.
Admitted.

(* Exercise: Implement a fold function for trees.
 *)
Definition Fold_tree {T U} (at_leaf : U) (at_branch : U -> T -> U -> U)
: tree T -> U.
Admitted.

(* Exercise: The naive definition of equality for these trees is wrong
 * because it requires two trees to have exactly the same step size.
 * What is a better definition that ignores the steps?
 *)
Definition eq_tree {T} (a b : tree T) : Prop.
Admitted.

(* Can you prove that this proposition is decidable?
 * Hint: While not optimal, it is probably easy to lift the two trees to
 * the same index before performing the comparison.
 *)

(* In a later tutorial we'll learn how we can use Coq's setoid features
 * to reason about trees and this relation.
 *)

(* The Lambda Calculus *)
(***********************)

(* Optional Exercise: Enrich the expression language with application and
 * lambda abstraction.
 * Re-do all of the functions/proofs.
 *)

(* Optional Exercise: Change the operator [Plus] into an expression, e.g.
 *    Plus : expr ts (Arr Nat (Arr Nat Nat))
 * Re-do all of the functions/proofs.
 *)
