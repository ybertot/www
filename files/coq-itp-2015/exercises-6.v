Require Import Bool.
Set Implicit Arguments.

Obligation Tactic := idtac.

Module SimpleEqTypeClass.
(*********************************************************)
(* Ex 1: A common example, a Leibniz decidable Equality *)
(*********************************************************)

(* Eq typeclass *)
Class Eq A := eqop : A -> A -> bool.
Notation "x == y" := (eqop x y) (at level 10).

(* instanciate for basic structures *)
Instance Eq_bool : Eq bool := Bool.eqb.
Instance Eq_nat : Eq nat := ...
(* There are dependencies in the Eq of the argument now *)
Instance Eq_option A ... : Eq (option A) :=
Instance Eq_pair ... 
Instance Eq_list ...

(* EqDec typeclass *)
Class EqDec A := {
  EqDecOp :> Eq A;
  eqP : forall x y, (x == y = true) <-> (x = y)
}.

Require Program.

(* Instanciate the additional field, i.e. the property eqP *)
Program Instance EqDec_bool : EqDec bool := ...
Program Instance EqDec_nat ...
Program Instance EqDec_option ...
Program Instance EqDec_pair ...
Program Instance EqDec_list ...

(* Make up an example to check you can derive the eqP property *)

End SimpleEqTypeClass.

Module RelationClasses.
(*************************)
(* Ex 2: Order relations *)
(*************************)

Delimit Scope relation_scope with rel.
Local Open Scope relation_scope.

Definition relation A := A -> A -> Prop.

Class Reflexive {A} (R : relation A) := reflexive : forall x : A, R x x.
Class Symmetric {A} (R : relation A) :=
  symmetric : forall x y : A, R x y -> R y x.
Class Transitive {A} (R : relation A) :=
  transitive : forall y x z : A, R x y -> R y z -> R x z.

Class Equivalence {A} (R : relation A) := {
  Equiv_Reflexive :> Reflexive R;
  Equiv_Symmetric :> Symmetric R;
  Equiv_Transitive :> Transitive R
}.

Class Setoid A := {
  equiv : relation A;
  Equivalence_equiv :> Equivalence equiv
}.
Infix "==" := equiv (at level 70, no associativity) : relation_scope.

(* Define a preorder *)
Class Preorder {A} (R : relation A) := {
                                      ...
}.

(* A Preordered Setoid is simply a type with a preorder *)
Class POSetoid A := {
   le : relation A;
   Preorder_le :> Preorder le
}.
Infix "<=" := le (at level 70, no associativity) : relation_scope.

(* Define the Antisymmetric class *)
Class Antisymmetric {A} {SA : Setoid A} (R : relation A) :=

(* Define Order *)
Class Order {A} (SA : Setoid A) (R : relation A) := {
...
}.

(* Define an equivalence relation from a preorder *)
Definition preorder_equiv {A} (R : relation A) : relation A := ...

(* Check that it is an equivalence *)
Program Instance Equivalence_preorder_equiv {A} {R : relation A} :
  Preorder R -> Equivalence (preorder_equiv R).
Next Obligation.
Admitted.

(* Show that Setoid is a subclass of POSetoid *)
Instance POSetoid_Setoid A : ...

(* pick sets of natural numbers as a example *)
Definition nat_set := nat -> Prop.
Program Instance subset : POSetoid nat_set ...
Qed.

Definition natset_empty : nat_set := fun _ => False.
Definition nat_singleton n : nat_set := @eq nat n.

Check (nat_singleton 3 == natset_empty).

End RelationClasses.

Module Bags.
(**************************)
(* Ex 3: Bags as a Setoid *)
(**************************)

Require Import Relation_Definitions Setoid.
Require Import Morphisms Equivalence SetoidClass.
Require Import List.

Section Bags.
Context (T : Type) {ST : Setoid T}.

Definition bag := list T.

(* define bag equivalence, Hint: one can use an inductive predicate
Count x l n, which states that l has exactly n occurence of x *)
Definition bag_eq (A B : bag) : Prop := ...

(* prove it is an equivalence *)
Instance Equivalence_eqbag : Equivalence bag_eq.

(* Implement bag merging *)
Definition bag_add (A B : bag) := ...

(* Show that the Count predicate is a morphism *)
Instance Proper_Count : Proper (equiv ==> bag_eq ==> eq ==> iff) Count.

(* Show that bag_add is a morphism, you might need intermediate lemmas
about Count *)
Instance Proper_add :
  Proper (bag_eq ==> bag_eq ==> bag_eq) bag_add.

End Bags.
End Bags.

(****************)
(* Ex 4: Monads *)
(****************)
Module Monads.
(* We import FunctionalExtensionality for the sake of simplicity *)
Require Import FunctionalExtensionality.
(* we now have that (forall x, f x = g x) -> f = g *)

Delimit Scope monad_scope with M.
Local Open Scope monad_scope.

Notation "f1 \; f2" := (fun x => f2 (f1 x))
  (at level 60, right associativity, format "f1  \;  f2").
Notation "f1 \o f2" := (fun x => f1 (f2 x))
  (at level 50, left associativity, format "f1  \o  f2").

Reserved Notation "'letM' x := e 'in' c "
         (at level 100, x ident, e at next level, c at next level,
          format "'letM'  x  :=  e  'in'  c").
Reserved Notation "x >>= f"
  (at level 60, right associativity, format "x  >>=  f").
Reserved Notation "f1 >=> f2"
  (at level 60, right associativity, format "f1  >=>  f2").

(* The laws of a monad *)
Class Monad (M : Type -> Type) := {
   retM : forall {A : Type}, A -> M A;
   bindM : forall {A B : Type}, M A -> (A -> M B) -> M B;
   bindretM : forall {A B} (a : A) (f : A -> M B), bindM (retM a) f = f a;
   bindMret : forall {A} (m : M A), bindM m retM = m;
   bindMA : forall {A B C} (m : M A) (f : A -> M B) (g : B -> M C),
            bindM (bindM m f) g = bindM m (fun x => bindM (f x) g)
}. 

Notation "x >>= f" := (bindM x f) : monad_scope.
Notation "'letM' x := e 'in' c" := (e >>= fun x => c) : monad_scope.

(* Define Haskell style Functor, with one operation (fmap) and properties *)
Class Functor (F : Type -> Type) := {
  fmap : ...;
         ..
}.

(* Show that Monads ar Functors *)
Program Instance Functor_Monad M {MonadM : Monad M} : Functor M := ...

(* Define joinM in the Monad *)
Definition joinM M {MonadM : eMonad M} {A : Type} : M (M A) -> M A ...

(* Establish properties of join *)
Lemma joinMret M {MonadM : Monad M} {A : Type} (ma : M A) :
  joinM (retM ma) = ma.

(* Define Kleisli composition *)
Definition compM M {MonadM : Monad M} {A B C} 
  (f : A -> M B) (g : B -> M C) (a : A) := ...
Notation  "f >=> g" := (compM f g) : monad_scope.

(* And the identities *)
Lemma compretM M {MonadM : Monad M} {A B}
  (f : A -> M B) : (retM >=> f) = f.
Lemma compMret M {MonadM : Monad M} {A B}
  (f : A -> M B) : (f >=> retM) = f.
Lemma compMA M {MonadM : Monad M} {A B C D}
  (f : A -> M B) (g : B -> M C) (h : C -> M D) :
  ((f >=> g) >=> h) = (f >=> (g >=> h)).

(* Show that option is a Monad *)
Program Instance Monad_option : Monad option.

(* Show that list is a Monad *)
Program Instance Monad_list : Monad list := ...

(* Test *)
Eval compute in fmap (fun x => x * 2) (cons 1 (cons 3 (cons 2 nil))).
Eval compute in joinM (cons (cons 1 (cons 2 nil)) (cons (retM 3) nil)).

(* Extend with Reader/Writer/State Monad *)

End Monads.

Module Algebra.
(***********************************************************)
(* Ex 5: Rewrite the algebra in the course, but on Setoids *)
(***********************************************************)

Require Import Relation_Definitions Setoid.
Require Import Morphisms Equivalence SetoidClass.
Require Import List.

Unset Implicit Arguments.

(* We can define the symbols without any properties and attach them
later *)
Class Zero A := zero : A.
Class One A := one : A.
Class Neg A {SA : Setoid A} := {
  neg : A -> A;
  Proper_neg :> Proper (equiv ==> equiv) neg
}.
(*...*)

(* Finally, we can write symbols and apply derived theorems *)
Goal forall x : nat, x + 0 == x.
Proof. apply right_neutral. Qed.

End Algebra.

Module Reification.
(**********************************************************************)
(* Ex 5: use typeclasses to do reification of the                     *)
(* algebraic operators of the course, and write a reflexive tactic to *)
(* simplify expressions.                                              *)
(**********************************************************************)

Require Import Relation_Definitions Setoid.
Require Import Morphisms Equivalence SetoidClass.
Require Import List.
Import Algebra.
Unset Implicit Arguments.
Local Open Scope algebra_scope.

Section Reification.

Context (A : Type) {SetoidA : Setoid A}
        {ZeroA : Zero A} {OneA : One A}
        {AddA : Add A} {MulA : Mul A}.

Inductive alg_exp  :=
| VarE : A -> alg_exp
| ZeroE
| OneE
| AddE : alg_exp -> alg_exp -> alg_exp
| MulE : alg_exp -> alg_exp -> alg_exp.

Fixpoint interp (exp : alg_exp) := ...

Class Reify (a : A) (exp : alg_exp) := reify : a == interp exp.

Fixpoint simp_alg_exp (exp : alg_exp) : exp :=

Lemma simp_alg_exp_correct {SemiRingA : SemiRing A 0 1 add mul} exp :
  interp (simp_alg_exp exp) == interp exp.
Proof.
Admitted.

Lemma simplify {SemiRingA : SemiRing A 0 1 add mul}
      (a : A) (exp : alg_exp) {ra : Reify a exp} :
  a == interp (simp_alg_exp exp).
Proof. now rewrite simp_alg_exp_correct, reify. Qed.

End Reification.

Goal forall x : nat, (x + 0) * 1 = x.
Proof.
Admitted.

End Reification.  


