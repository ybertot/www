Require Import Bool.
Set Implicit Arguments.

Obligation Tactic := idtac.

Module Part1Dot1.
(* Please Ignore the "Module" here, this is only used for delimiting
the scope of identifiers *)

(***************************)
(* Typeclasses and Setoids *)
(***************************)

(* When comming to overloading in Coq, one has two choices:        *)
(* - Modules, second class objects                                 *)
(* - Records, first class objects                                  *)
(*                                                                 *)
(* We do not give details about modules here and focus on records. *)
(* One can use records to regroup definitions and properties.      *)

Record SemiRing A := {
  zero : A;
  one : A;
  add : A -> A -> A;
  mul : A -> A -> A;
  
  add0r : forall x, add zero x = x;
  addrC : forall x y, add x y = add y x;
  addrA : forall x y z, add x (add y z) = add (add x y) z;

  mul0r : forall x, mul zero x = zero;
  mul1r : forall x, mul one x = x;
  mulr0 : forall x, mul x zero = zero;
  mulr1 : forall x, mul x one = x;
  mulrA : forall x y z, mul x (mul y z) = mul (mul x y) z;
  mulrDl :  forall n m p, mul (add n m) p = add (mul n p) (mul m p);
  mulrDr :  forall n m p, mul p (add n m) = add (mul m p) (mul n p)
}.

(* We may want to share some notations for all semi rings *)
Delimit Scope algebra_scope with A.
Local Open Scope algebra_scope.
Notation "'`0' s" := (@zero _ s)
  (at level 0, s at level 0, format "'`0' s") : algebra_scope.
Notation "'`1' s" := (@one _ s)
  (at level 0, s at level 0, format "'`1' s") : algebra_scope.
Notation "x +_ s y" := (add s x y)
  (at level 50, s at level 0, y at next level,
   format "x  +_ s  y") : algebra_scope.
Notation "x *_ s y" := (mul s x y)
  (at level 40, s at level 0, y at next level,
   format "x  *_ s  y") : algebra_scope.
(* Note that there is no way to guess what s is *)

(* We can make a theory about semirings *)
(* i.e. develop all the theorems that we know about semirings *)
Section SemiRingTheory.
Variables (A : Type) (s : SemiRing A).
Implicit Types x y z : A.

(* We have to provide s explicitly everywhere, in big statements, this
becomes unmanagable *)
Lemma addr0 x : x +_s `0s = x.  Proof. now
rewrite addrC, add0r. Qed.

(* ... *)

End SemiRingTheory.

(* Then we can Instanciate it *)
(* Which means, we provide types we know are semirings *)
(* We have to provide both the operators and the axiomatic *)
Section SemiRingInstances.

(* we use Program to interactively define records *)
(* the first part of the record is give explicitly *)
Program Definition SemiRing_nat := {|
  zero := 0;
  one  := 1;
  add  := plus;
  mul  := mult
|}.
(* the second part are propositions, we enter interactive mode *)
(* with Program, Proof. is replaced by a sequence of Next Obligation *)
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

(* We provide another instance *)
Program Definition SemiRing_bool := {|
  zero := false;
  one  := true;
  add  := xorb;
  mul  := andb
|}.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x, y, z. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct n, m, p. Qed.
Next Obligation. now destruct n, m, p. Qed.

End SemiRingInstances.

(* We have to provide the instantiations explicitly everywhere, in big
statements, this becomes unmanagable *)
Check (`0SemiRing_bool +_SemiRing_bool `1SemiRing_bool).
Eval compute in (`0SemiRing_bool +_SemiRing_bool `1SemiRing_bool).

End Part1Dot1.

Module Part1Dot2.
(* Instead we tag the previous record as a class, and its element as *)
(* instances, which indexes them and gives them a special status. *)
Class SemiRing A := {
  zero : A;
  one : A;
  add : A -> A -> A;
  mul : A -> A -> A;
  
  add0r : forall x, add zero x = x;
  addrC : forall x y, add x y = add y x;
  addrA : forall x y z, add x (add y z) = add (add x y) z;

  mul0r : forall x, mul zero x = zero;
  mul1r : forall x, mul one x = x;
  mulr0 : forall x, mul x zero = zero;
  mulr1 : forall x, mul x one = x;
  mulrA : forall x y z, mul x (mul y z) = mul (mul x y) z;
  mulrDl :  forall n m p, mul (add n m) p = add (mul n p) (mul m p);
  mulrDr :  forall n m p, mul p (add n m) = add (mul m p) (mul n p)
}.

(* Since the candidate for SemiRing A will be searched by the proof
engine, we omit it in the notation, making them lighter *)
Delimit Scope algebra_scope with A.
Local Open Scope algebra_scope.
Notation "0" := (@zero _ _) : algebra_scope.
Notation "1" := (@one _ _) : algebra_scope.
Infix "+" := add : algebra_scope.
Infix "*" := mul : algebra_scope.

(* We can make a theory about semirings *)
Section SemiRingTheory.
Context (A : Type) {s : SemiRing A}.
Implicit Types x y z : A.

Lemma addr0 x : x + 0 = x.
Proof. now rewrite addrC, add0r. Qed.

(* ... *)

End SemiRingTheory.

Section SemiRingInstances.

(* Now in order to instanciate these, we use the Vernacular Command
Instance, instead of a simple definition *)
Global Program Instance SemiRing_nat : SemiRing nat := {|
  zero := 0%nat : nat;
  one  := 1%nat : nat;
  add  := plus;
  mul  := mult
|}.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.


Program Definition SemiRing_bool : SemiRing bool := {|
  zero := false;
  one  := true;
  add  := xorb;
  mul  := andb
|}.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x, y, z. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct x. Qed.
Next Obligation. now destruct n, m, p. Qed.
Next Obligation. now destruct n, m, p. Qed.

(* A definition can be made an instance a posteriori *)
Global Existing Instance SemiRing_bool.

(* One can list all the instances of SemiRing *)
Print Instances SemiRing.

(* One can also check the HintDb *)
Print HintDb typeclass_instances.

End SemiRingInstances.

(* Now, everything works if we are explicit enough about the type *)
Check (0 + 1 : bool).
Eval compute in (0 + 1 : bool).
Goal ((0 + 1)%A = (1 : bool)).
reflexivity.
Qed.

End Part1Dot2.

Module Part1Dot2'.
(* Let's be a little be more modular and show an example of inheritance. *)

Class AdditiveMonoid A := {
  zero : A;
  add : A -> A -> A;

  add0r : forall x, add zero x = x;
  addrC : forall x y, add x y = add y x;
  addrA : forall x y z, add x (add y z) = add (add x y) z
}.


Class SemiRing A := {
  SemiRing_AdditiveMonoid : AdditiveMonoid A;

  one : A;
  mul : A -> A -> A;

  mul0r : forall x, mul zero x = zero;
  mul1r : forall x, mul one x = x;
  mulr0 : forall x, mul x zero = zero;
  mulr1 : forall x, mul x one = x;
  mulrA : forall x y z, mul x (mul y z) = mul (mul x y) z;
  mulrDl :  forall n m p, mul (add n m) p = add (mul n p) (mul m p);
  mulrDr :  forall n m p, mul p (add n m) = add (mul m p) (mul n p)
}.

(* Inheritance can be declared after the face using Instance *)
Existing Instance SemiRing_AdditiveMonoid.
Print Instances AdditiveMonoid.
(* but it could have been declared during the definition of SemiRing:
  SemiRing_AdditiveMonoid :> AdditiveMonoid A;
*)

(* Beware of duplication ! *)

End Part1Dot2'.

Module Part1Dot3.

(*************************************************************************)
(* We have seen how to define typeclasses, but we defined semirings in a *)
(* monolythic way. We can take advantage of typeclasses to share symbols *)
(* across many different algebraic structures and to share properties    *)
(* between the structures.                                               *)
(*                                                                       *)
(* The following style is call unbundled                                 *)
(* (cf math-classes library, Spitters &  van der Weegen                  *)
(*************************************************************************)

(* We can define the symbols without any properties and attach them
later *)
Class Zero A := zero : A.
Class One A := one : A.
Class Neg A := neg : A -> A.
Class Add A := add : A -> A -> A.
Class Mul A := mul : A -> A -> A.

Delimit Scope algebra_scope with A.
Local Open Scope algebra_scope.
Notation "0" := (@zero _ _) : algebra_scope.
Notation "1" := (@one _ _) : algebra_scope.
Notation "- x" := (neg x) : algebra_scope.
Infix "+" := add : algebra_scope.
Infix "*" := mul : algebra_scope.

(* This style is called unbundled because the operations are now
parameters for each "axiom *)
Class LeftNeutral A (neutral : A) (op : A -> A -> A) :=
  left_neutral x : op neutral x = x.
Class RightNeutral A (neutral : A) (op : A -> A -> A) :=
  right_neutral x : op x neutral = x.
Class LeftAbsorbant A (absorbant : A) (op : A -> A -> A) :=
  left_absorbant x : op absorbant x = absorbant.
Class RightAbsorbant A (absorbant : A) (op : A -> A -> A) :=
  right_absorbant x : op x absorbant = absorbant.
Class Commutative A (op : A -> A -> A) :=
  commutative x y : op x y = op y x.
Class Associative A (op : A -> A -> A) :=
  associative x y z : op x (op y z) = op (op x y) z.
Class LeftDistributive A (op1 : A -> A -> A) (op2 : A -> A -> A) :=
  left_distributive x y z : op1 x (op2 y z) = op1 (op2 x y) (op2 x z).
Class RightDistributive A (op1 : A -> A -> A) (op2 : A -> A -> A) :=
  right_distributive x y z : op1 (op2 x y) z = op1 (op2 x z) (op2 y z).

(* We can combine/bundle those properties into bigger entities *)
Class Monoid A (neutral : A) op := {
  Monoid_LeftNeutral :> LeftNeutral neutral op;
  Monoid_RightNeutral :> RightNeutral neutral op;
  Monoid_Associative :> Associative op
}.

(* And combine the bigger entities *)
Class CommutativeMonoid A (neutral : A) op := {
  ComMonoid_Monoid :> Monoid neutral op;
  ComMonoid_Commutative :> Commutative op
}.

(* We can provide an alternative way to create commutative monoids,
skipping the RightNeutral property *)
Definition Build_Commutative_Monoid A (neutral : A) op :
 Commutative op -> LeftNeutral neutral op -> Associative op ->
 CommutativeMonoid neutral op.
Proof.
intros; constructor; auto; constructor; auto; intro x.
now rewrite commutative, left_neutral.
Qed.

(* SemiRing is a combination of those *)
Class SemiRing A (zero : A) one add mul := {
  SemiRing_AdditiveMonoid :> CommutativeMonoid zero add;
  SemiRing_MultiplicativeMonoid :> Monoid one mul;
  SemiRing_LeftAbsorbant :> LeftAbsorbant zero mul;
  SemiRing_RightAbsorbant :> RightAbsorbant zero mul;
  SemiRint_LeftDistributive :> LeftDistributive mul add;
  SemiRint_RightDistributive :> RightDistributive mul add
}.

(* One can gradualy instanciate operations for nat *)
Instance Zero_nat : Zero nat := 0%nat.
Instance One_nat : One nat := 1%nat.
Instance Add_nat : Add nat := plus.
Instance Mul_nat : Mul nat := mult.

(* One can gradualy instanciate thorems for nat ... *)
Instance : @LeftNeutral nat 0 add.
Proof. now intro x. Qed.
Instance : @Commutative nat add.
Proof.
unfold add, Add_nat; intros x y; induction x in y |- *; auto; simpl.
now rewrite IHx.
Qed.
Instance : @Associative nat add.
Proof.
unfold add, Add_nat; intros x y z; induction x in y, z |- *; auto; simpl.
now rewrite IHx.
Qed.

(* ... or not that gradually *)
Instance : @SemiRing nat 0 1 add mul.
Proof.
constructor.
- apply Build_Commutative_Monoid; auto with typeclass_instances.
- admit.
Admitted.

(* Finally, we can write symbols and apply derived theorems *)
Goal forall x : nat, x + 0 = x.
Proof. apply right_neutral. Qed.

End Part1Dot3.

Module Part2.

(**********************************************************************)
(* We introduce Setoid from the point of view of typeclasses.  We     *)
(* redefine temporarly a number of predefined concepts, to illustrate *)
(* where they come from.                                              *)
(**********************************************************************)

Delimit Scope relation_scope with rel.
Local Open Scope relation_scope.

Definition relation A := A -> A -> Prop.

Class Reflexive {A} (R : relation A) := reflexive : forall x : A, R x x.
Class Symmetric {A} (R : relation A) :=
  symmetric : forall x y : A, R x y -> R y x.
Class Transitive {A} (R : relation A) :=
  transitive : forall y x z : A, R x y -> R y z -> R x z.

(* An equivalence relation *)
Class Equivalence {A} (R : relation A) := {
  Equiv_Reflexive :> Reflexive R;
  Equiv_Symmetric :> Symmetric R;
  Equiv_Transitive :> Transitive R
}.

(* A setoid is simply a type, together with an equivalence relation *)
Class Setoid A := {
  equiv : relation A;
  Equivalence_equiv :> Equivalence equiv
}.
Infix "==" := equiv (at level 70, no associativity) : relation_scope.

(* We say x is proper with regard to a relation if it is related to
itself through this relation *)
Class Proper {A} (R : relation A) x := proper : R x x.  Delimit Scope
signature_scope with sig.  Arguments Proper A R%sig x.

(* Combined with respectful, it allow to express Morphisms *)
Definition respectful {A B} (RA : relation A) (RB : relation B) : 
  relation (A -> B) := fun f g => forall a a', RA a a' -> RB (f a) (g a').
Notation " R ==> R' " := (@respectful _ _ (R%sig) (R'%sig))
    (right associativity, at level 55) : signature_scope.

(********************************************)
(* Indeed, f : A -> B is a morphism if      *)
(*                                          *)
(* forall a a', RA a a' -> RB (f a) (f a'). *)
(*                                          *)
(* i.e.                                     *)
(*                                          *)
(* Proper (RA ==> RB) f                     *)
(********************************************)

(* In particular, equiv is proper with regard to its signature *)
Instance Proper_equiv A {SA : Setoid A} :
  Proper (equiv ==> equiv ==> iff) equiv.
Proof.
intros a a' eq_a b b' eq_b.
split.
  intro eq_ab; apply (transitive a); [now apply symmetric|].
  now apply (transitive b).
intro eq_a'b'; apply (transitive b'); [|now apply symmetric].
now apply (transitive a').
Qed.

End Part2.

Module Part3.

(************************************************************************)
(* We now use the Setoid predefined mechanisms of Coq, with the example *)
(* of sets, defined as a setoid of lists together with a well chosen    *)
(* equivalence relation                                                 *)
(************************************************************************)

Require Import Relation_Definitions Setoid.
Require Import Morphisms Equivalence.
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

Section fset.
Context (T : Type).

Definition fset := list T.

(* Equality of sets, represented by lists *)
Definition fset_eq (A B : fset) : Prop := 
  forall x, In x A <-> In x B.

(* Check this is an equivalence relation *)
Instance Equivalence_eqfset : Equivalence fset_eq.
Proof.
constructor.
- now intros A x; intuition.
- now intros A B eqAB x; symmetry.
- now intros A B C eqAB eqBC x; rewrite (eqAB x).
Qed.

Definition fset_union (A B : fset) := A ++ B.

Instance Proper_In : Proper (eq ==> fset_eq ==> iff) (@In T).
Proof. now intros x y eqxy A B eqAB; rewrite eqxy. Qed.

Instance Proper_app :
  Proper (fset_eq ==> fset_eq ==> fset_eq) fset_union.
Proof.
intros x x' eq_x y y' eq_y z; unfold fset_union.
now repeat rewrite in_app_iff; rewrite eq_x, eq_y.
Qed.

End fset.
End Part3.


