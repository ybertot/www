Require Import Bool.
Set Implicit Arguments.

Obligation Tactic := idtac.

Module SimpleEqTypeClass.
(********************************************************)
(* Ex 1: A common example, a Leibniz decidable Equality *)
(********************************************************)

(* Eq typeclass *)
Class Eq A := eqop : A -> A -> bool.
Notation "x == y" := (eqop x y) (at level 10).

Instance Eq_bool : Eq bool := Bool.eqb.
Instance Eq_nat : Eq nat := fix nat_eqb x y :=
  match x, y with
    | S a, S b => nat_eqb a b
    | 0, 0 => true
    | _, _ => false
  end.

Instance Eq_option A {EqA : Eq A} : Eq (option A) := fun x y =>
  match x, y with
    | Some a, Some b => a == b
    | None, None => true
    | _, _ => false
  end.

Instance Eq_pair A B {EqA : Eq A} {EqB : Eq B} : Eq (A * B) := fun x y =>
  match x, y with
    | (a, a'), (b, b') => (a == b) && (a' == b')
  end.
 
Instance Eq_list A `{Eq A} : Eq (list A) := 
  fix eq_list xs ys :=
  match xs, ys with
    | cons x xs, cons y ys => (x == y) && (eq_list xs ys)
    | nil, nil => true
    | _, _ => false
  end.

(* EqDec typeclass *)
Class EqDec A := {
  EqDecOp :> Eq A;
  eqP : forall x y, (x == y = true) <-> (x = y)
}.

Require Program.

Program Instance EqDec_bool : EqDec bool.
Next Obligation. now destruct x, y; intuition. Qed.

Program Instance EqDec_nat : EqDec nat.
Next Obligation.
revert y; elim x; destruct y; try (split; auto; discriminate).
unfold eqop; simpl; rewrite H.
split.
- now intro ny; rewrite ny.
- now intro ny; injection ny.
Qed.

Program Instance EqDec_option A {EqDecA : EqDec A} : EqDec (option A).
Next Obligation.
destruct x, y; auto; try (unfold eqop; simpl; intuition; try discriminate).
- now rewrite eqP in H; rewrite H.
- now rewrite eqP; injection H.
Qed.  

Program Instance EqDec_pair A B {EqDecA : EqDec A} {EqDecB : EqDec B} :
  EqDec (A * B).
Next Obligation.
unfold eqop; simpl; rewrite andb_true_iff.
repeat rewrite eqP; split; intro H.
  now destruct H; f_equal.
now injection H; intuition.
Qed.
  
Program Instance EqDec_list A {EqDecA : EqDec A} : EqDec (list A).
Next Obligation.
revert y; elim x; destruct y; try (split; auto; discriminate).
unfold eqop; simpl.
change (Eq_list A l y) with (l == y).
rewrite andb_true_iff, H, eqP.
split.
- now destruct 1; rewrite H0, H1.
- now intro Hal; injection Hal; intuition.
Qed.
End SimpleEqTypeClass.

Module RelationClassesEx.
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

Class Preorder {A} (R : relation A) := {
  Preorder_Reflexive :> Reflexive R;
  Preorder_Transitive :> Transitive R
}.

Class POSetoid A := {
   le : relation A;
   Preorder_le :> Preorder le
}.
Infix "<=" := le (at level 70, no associativity) : relation_scope.

Class Antisymmetric {A} {SA : Setoid A} (R : relation A) :=
  antisymmetric : forall x y : A, R x y -> R x y -> x == y.

Class Order {A} (SA : Setoid A) (R : relation A) := {
  Order_Preorder :> Preorder R;
  Order_Antisymmetric :> Antisymmetric R
}.

Definition preorder_equiv {A} (R : relation A) : relation A :=
  fun x y => R x y /\ R y x.

Program Instance Equivalence_preorder_equiv {A} {R : relation A} :
  Preorder R -> Equivalence (preorder_equiv R).
Next Obligation.
now intro x; unfold preorder_equiv; intuition.
Qed.
Next Obligation.
now intros x y; unfold preorder_equiv; intuition.
Qed.
Next Obligation.
intros y x z; unfold preorder_equiv.
destruct 1 as [Rxy Ryx]; destruct 1 as [Ryz Rzy].
now split; apply (transitive y).
Qed.

Instance POSetoid_Setoid A : POSetoid A -> Setoid A.
Proof.
intro POA; eexists.
now auto with typeclass_instances.
Qed.

Definition nat_set := nat -> Prop.
Program Instance subset : POSetoid nat_set := {
  le := fun A B => forall x, A x -> B x
}.
Next Obligation.
constructor.
- now intros A.
- now intros B A C AB BC x Ax; apply BC; apply AB.
Qed.

Definition natset_empty : nat_set := fun _ => False.
Definition nat_singleton n : nat_set := @eq nat n.

Check (nat_singleton 3 == natset_empty).

End RelationClassesEx.

Module Bags.
(**************************)
(* Ex 3: Bags as a Setoid *)
(**************************)

Require Import Relation_Definitions Setoid.
Require Import Morphisms Equivalence SetoidClass.
Require Import List.

Print relation.
Print Equivalence.
Print Reflexive.
Print Symmetric.
Print Transitive.
Print Setoid.
Print Proper.

(* look for Proper, Equivalence, ... *)
Print HintDb typeclass_instances.

(* alternatively *)
Print Instances Proper.
Print Instances Equivalence.
Print Instances Reflexive.

Section Bags.
Context (T : Type) {ST : Setoid T}.

Definition bag := list T.

Require ssreflect.

Inductive Count x : list T -> nat -> Prop :=
| CountNil : Count x nil 0
| CountConsIn : forall y l n, x == y ->
                              Count x l n -> Count x (cons y l) (S n)
| CountConsNotIn : forall y l n, ~ (x == y) ->
                              Count x l n -> Count x (cons y l) n.

Definition bag_eq (A B : bag) : Prop := 
  forall x n, Count x A n <-> Count x B n.

Instance Equivalence_eqbag : Equivalence bag_eq.
Proof.
constructor.
- now intros A x; intuition.
- now intros A B eqAB x n; symmetry.
- now intros A B C eqAB eqBC x n; rewrite (eqAB x).
Qed.

Definition bag_add (A B : bag) := A ++ B.

Instance Proper_Count : Proper (equiv ==> bag_eq ==> eq ==> iff) Count.
Proof. 
intros x y eqxy A B eqAB n m eqnm; rewrite <- eqnm, <- (eqAB y n).
cut (forall x y, x == y -> Count x A n -> Count y A n). 
  now intro Hwlog; split; apply Hwlog; intuition.
clear; intros x y eqxy.
induction 1 as [ | z l n neq_xz cx | z l n eq_xz cx];
  now constructor; try rewrite <- eqxy.
Qed.

Lemma Count_add x l l' n m :
 Count x l n -> Count x l' m -> Count x (l ++ l') (n + m).
Proof.
intros cl cl'.
induction cl as [ | z s p neq_xz cs| z s' p eq_xz cs] in l', m, cl' |- *;
  simpl; auto.
- now constructor; auto.
- now constructor; auto.
Qed.

Lemma ex_Count_add x l l' n :
 Count x (l ++ l') n ->
 exists p, exists m, n = p + m /\ (Count x l p /\ Count x l' m).
Proof.
intro cll'.
remember (l ++ l').
induction cll' as [ | z s p neq_xz cs| z s' p eq_xz cs] in l, l', Heql0 |- *.
  - exists 0, 0; repeat split; auto.
    + now induction l; constructor.
    + induction l'; constructor;
      now apply app_cons_not_nil in Heql0.
  - destruct l.
    + destruct l'; [discriminate|].
      injection Heql0; intros eq_s eq_z.
      destruct (IHcs nil l'); [exact|].
      destruct H; destruct H; destruct H0.
      exists x0, (S x1); rewrite H; intuition.
      now constructor; auto; rewrite <- eq_z.
    + injection Heql0; intros eq_s eq_z.
      destruct (IHcs l l'); [exact|].
      destruct H; destruct H; destruct H0.
      exists (S x0), x1; rewrite H; intuition.
      now constructor; auto; rewrite <- eq_z.
  - destruct l.
    + destruct l'; [discriminate|].
      injection Heql0; intros eq_s eq_z.
      destruct (IHcs nil l'); [exact|].
      destruct H; destruct H; destruct H0.
      exists x0, x1; rewrite H; intuition.
      now constructor; auto; rewrite <- eq_z.
    + injection Heql0; intros eq_s eq_z.
      destruct (IHcs l l'); [exact|].
      destruct H; destruct H; destruct H0.
      exists x0, x1; rewrite H; intuition.
      now constructor; auto; rewrite <- eq_z.
Qed.
    
Lemma Count_add_iff x l l' n :
  Count x (l ++ l') n <->
 exists p, exists m, n = p + m /\ (Count x l p /\ Count x l' m).
Proof.
split; [now apply ex_Count_add|].
destruct 1.
destruct H.
destruct H.
destruct H0.
rewrite H.
now apply Count_add; auto.
Qed.


Instance Proper_add :
  Proper (bag_eq ==> bag_eq ==> bag_eq) bag_add.
Proof.
intros x x' eq_x y y' eq_y z n; unfold bag_add.
repeat rewrite Count_add_iff.
setoid_rewrite eq_x.
setoid_rewrite eq_y.
reflexivity.
Qed.

End Bags.
End Bags.

(****************)
(* Ex 4: Monads *)
(****************)
Module Monads.
Require Import FunctionalExtensionality.

Delimit Scope monad_scope with M.
Local Open Scope monad_scope.

Notation "f1 \; f2" := (fun x => f2 (f1 x))
  (at level 60, right associativity, format "f1  \;  f2").
Notation "f1 \o f2" := (fun x => f1 (f2 x))
  (at level 50, left associativity, format "f1  \o  f2").

Class Functor (F : Type -> Type) := {
  fmap : forall {A B : Type}, (A -> B) -> F A -> F B;
  fmap_id : forall {A}, fmap (@id A) = (@id (F A));
  fmap_comp : forall {A B C} (f : B -> C) (g : A -> B),
             fmap (f \o g) = ((fmap f) \o (fmap g))
}.

Reserved Notation "'letM' x := e 'in' c "
         (at level 100, x ident, e at next level, c at next level,
          format "'letM'  x  :=  e  'in'  c").
Reserved Notation "x >>= f"
  (at level 60, right associativity, format "x  >>=  f").
Reserved Notation "f1 >=> f2"
  (at level 60, right associativity, format "f1  >=>  f2").

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

Program Instance FunctorMonad M {MonadM : Monad M} : Functor M := {
  fmap A B f m := letM y := m in retM (f y)
}.
Next Obligation.
apply functional_extensionality; intro x.
now rewrite bindMret.
Qed.
Next Obligation.
apply functional_extensionality; intro x.
rewrite bindMA; f_equal.
apply functional_extensionality; intro y.
now rewrite bindretM.
Qed.

Definition joinM M {MonadM : Monad M} {A : Type} : M (M A) -> M A :=
  fun x => letM y := x in y.

Lemma joinMret M {MonadM : Monad M} {A : Type} (ma : M A) :
  joinM (retM ma) = ma.
Proof. now unfold joinM; rewrite bindretM. Qed.

Definition compM M {MonadM : Monad M} {A B C} 
  (f : A -> M B) (g : B -> M C) (a : A) := letM b := f a in g b.
Notation  "f >=> g" := (compM f g) : monad_scope.

Lemma compretM M {MonadM : Monad M} {A B}
  (f : A -> M B) : (retM >=> f) = f.
Proof. now apply functional_extensionality; intro x; apply bindretM. Qed.

Lemma compMret M {MonadM : Monad M} {A B}
  (f : A -> M B) : (f >=> retM) = f.
Proof. now apply functional_extensionality; intro x; apply bindMret. Qed.

Lemma compMA M {MonadM : Monad M} {A B C D}
  (f : A -> M B) (g : B -> M C) (h : C -> M D) :
  ((f >=> g) >=> h) = (f >=> (g >=> h)).
Proof. now apply functional_extensionality; intro x; apply bindMA. Qed.

(* option is a Monad *)
Program Instance Monad_option : Monad option := {
  retM A a := Some a;
  bindM A B x f := match x with Some y => f y | None => None end
}.
Next Obligation.
now destruct m.
Qed.
Next Obligation.
now destruct m.
Qed.

(* list is a Monad *)

Program Instance Monad_list : Monad list := {
  retM A a := cons a nil;
  bindM A B l f := List.flat_map f l
}.
Next Obligation.
now rewrite List.app_nil_r.
Qed.
Next Obligation.
now elim m; auto; intros a l Hl; simpl; rewrite Hl.
Qed.
Next Obligation.
elim m; auto; intros a l Hl; simpl; rewrite <- Hl.
induction (f a) as [|b x Hx]; auto.
now simpl; rewrite Hx, List.app_assoc.
Qed.

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
Class Add A {SA : Setoid A} := {
  add : A -> A -> A;
  Proper_add :> Proper (equiv ==> equiv ==> equiv) add
}.
Arguments Add A {SA}.
Class Mul A {SA : Setoid A} := {
  mul : A -> A -> A;
  Proper_mul :> Proper (equiv ==> equiv ==> equiv) mul
}.
Arguments Mul A {SA}.

Delimit Scope algebra_scope with A.
Local Open Scope algebra_scope.
Notation "0" := (@zero _ _) : algebra_scope.
Notation "1" := (@one _ _) : algebra_scope.
Notation "- x" := (neg x) : algebra_scope.
Infix "+" := add : algebra_scope.
Infix "*" := mul : algebra_scope.

(* This style is called unbundled because the operations are now
parameters for each "axiom *)
Class LeftNeutral A {SA : Setoid A} (neutral : A) (op : A -> A -> A) :=
  left_neutral x : op neutral x == x.
Class RightNeutral A {SA : Setoid A} (neutral : A) (op : A -> A -> A) :=
  right_neutral x : op x neutral == x.
Class LeftAbsorbant A {SA : Setoid A} (absorbant : A) (op : A -> A -> A) :=
  left_absorbant x : op absorbant x == absorbant.
Class RightAbsorbant A {SA : Setoid A} (absorbant : A) (op : A -> A -> A) :=
  right_absorbant x : op x absorbant == absorbant.
Class Commutative A {SA : Setoid A} (op : A -> A -> A) :=
  commutative x y : op x y == op y x.
Class Associative A {SA : Setoid A} (op : A -> A -> A) :=
  associative x y z : op x (op y z) == op (op x y) z.
Class LeftDistributive A {SA : Setoid A} (op1 : A -> A -> A) (op2 : A -> A -> A) :=
  left_distributive x y z : op1 x (op2 y z) == op1 (op2 x y) (op2 x z).
Class RightDistributive A {SA : Setoid A} (op1 : A -> A -> A) (op2 : A -> A -> A) :=
  right_distributive x y z : op1 (op2 x y) z == op1 (op2 x z) (op2 y z).

(* We can combine/bundle those properties into bigger entities *)
Class Monoid A {SA : Setoid A} (neutral : A) op := {
  Monoid_LeftNeutral :> LeftNeutral A neutral op;
  Monoid_RightNeutral :> RightNeutral A neutral op;
  Monoid_Associative :> Associative A op
}.

(* And combine the bigger entities *)
Class CommutativeMonoid A {SA : Setoid A} (neutral : A) op := {
  ComMonoid_Monoid :> Monoid A neutral op;
  ComMonoid_Commutative :> Commutative A op
}.

(* We can provide an alternative way to create commutative monoids,
skipping the RightNeutral property *)
Definition Build_Commutative_Monoid A {SA : Setoid A} (neutral : A) op :
 Commutative A op -> LeftNeutral A neutral op -> Associative A op ->
 CommutativeMonoid A neutral op.
Proof.
intros; constructor; auto; constructor; auto; intro x.
now rewrite commutative, left_neutral.
Qed.

(* SemiRing is a combination of those *)
Class SemiRing A {SA : Setoid A} (zero : A) one add mul := {
  SemiRing_AdditiveMonoid :> CommutativeMonoid A zero add;
  SemiRing_MultiplicativeMonoid :> Monoid A one mul;
  SemiRing_LeftAbsorbant :> LeftAbsorbant A zero mul;
  SemiRing_RightAbsorbant :> RightAbsorbant A zero mul;
  SemiRint_LeftDistributive :> LeftDistributive A mul add;
  SemiRint_RightDistributive :> RightDistributive A mul add
}.

(* One can gradualy instanciate operations for nat *)
Global Instance Setoid_nat : Setoid nat := {equiv := eq}.
Global Instance Zero_nat : Zero nat := 0%nat.
Global Instance One_nat : One nat := 1%nat.
Global Instance Add_nat : Add nat := {add := plus}.
Global Instance Mul_nat : Mul nat := {mul := mult}.

(* One can gradualy instanciate thorems for nat ... *)
Global Instance : LeftNeutral nat 0 add.
Proof. now intro x. Qed.
Global Instance : Commutative nat add.
Proof. now intros x y; apply Plus.plus_comm. Qed.
Global Instance : Associative nat add.
Proof. now intros x y z; apply Plus.plus_assoc. Qed.

Global Instance : SemiRing nat 0 1 add mul.
Proof.
constructor.
- apply Build_Commutative_Monoid; auto with typeclass_instances.
- admit.
Admitted.

(* Finally, we can write symbols and apply derived theorems *)
Goal forall x : nat, x + 0 == x.
Proof. apply right_neutral. Qed.

End Algebra.

Module Reification.
(**********************************************************************)
(* Ex 5 (very difficult): use typeclasses to do reification of the    *)
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

Global Instance Setoid_alg_exp : Setoid alg_exp := {equiv := eq}.
Global Instance Zero_alg_exp : Zero alg_exp := {zero := ZeroE}.
Global Instance One_alg_exp : One alg_exp := {one := OneE}.
Global Instance Add_alg_exp : Add alg_exp := {add := AddE}.
Global Instance mul_alg_exp : Mul alg_exp := {mul := MulE}.

Fixpoint interp (exp : alg_exp) :=
  match exp with
    | VarE a => a
    | ZeroE => 0
    | OneE => 1
    | AddE x y => interp x + interp y
    | MulE x y => interp x * interp y
  end.

Class Reify (a : A) (exp : alg_exp) := reify : a == interp exp.

Global Instance Reify_zero : Reify 0 0.
Proof. unfold Reify; reflexivity. Qed.

Global Instance Reify_one : Reify 1 1.
Proof. unfold Reify; reflexivity. Qed.

Global Instance Reify_add a b ra rb :
  Reify a ra -> Reify b rb -> Reify (a + b) (ra + rb).
Proof.
intros eq_a eq_b; unfold Reify; simpl.
now repeat rewrite reify.
Qed.

Global Instance Reify_mul a b ra rb :
  Reify a ra -> Reify b rb -> Reify (a * b) (ra * rb).
Proof.
intros eq_a eq_b; unfold Reify; simpl.
now repeat rewrite reify.
Qed.

Global Instance Reify_var a : Reify a (VarE a) | 100.
Proof. unfold Reify; reflexivity. Qed.

Fixpoint simp_alg_exp (exp : alg_exp) :=
  match exp with
      | AddE x y => match simp_alg_exp x, simp_alg_exp y with
                      | ZeroE, sy => sy
                      | sx, ZeroE => sx
                      | sx, sy => AddE sx sy
                    end
      | MulE x y => match simp_alg_exp x, simp_alg_exp y with
                      | ZeroE, sy => ZeroE
                      | sx, ZeroE => ZeroE
                      | OneE, sy => sy
                      | sx, OneE => sx
                      | sx, sy => MulE sx sy
                    end
      | u => u
  end.

Lemma simp_alg_exp_correct {SemiRingA : SemiRing A 0 1 add mul} exp :
  interp (simp_alg_exp exp) == interp exp.
Proof.
induction exp; simpl; try reflexivity.
- rewrite <- IHexp1, <- IHexp2.
  destruct (simp_alg_exp exp1), (simp_alg_exp exp2);
    solve [reflexivity | now rewrite right_neutral 
           | now rewrite left_neutral].
- rewrite <- IHexp1, <- IHexp2.
  destruct (simp_alg_exp exp1), (simp_alg_exp exp2);
    solve [reflexivity | now rewrite right_neutral 
           | now rewrite left_neutral
           | now rewrite right_absorbant
           | now rewrite left_absorbant].
Qed.

Lemma simplify {SemiRingA : SemiRing A 0 1 add mul}
      (a : A) (exp : alg_exp) {ra : Reify a exp} :
  a == interp (simp_alg_exp exp).
Proof. now rewrite simp_alg_exp_correct, reify. Qed.

End Reification.

Goal forall x : nat, (x + 0) * 1 = x.
Proof.
intro x.
rewrite (simplify nat ((x + 0) * 1)).
2: auto with typeclass_instances.
reflexivity.
Qed.

End Reification.  

