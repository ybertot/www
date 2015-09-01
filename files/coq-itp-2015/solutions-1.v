(******************************************************************)
(* An exercise file to be launch with coqide exercise1.v          *)
(******************************************************************)

(** * Stating and proving simple propositions *)

(* Prove the following *)

Lemma composition : forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).
Proof.
intros * H1 H2 HA.
apply H2, H1, HA.
Qed.

Lemma tautology : forall (A:Type) (P:A -> Prop) (a:A), P a ->  P a.
Proof.
intros * HPa.
assumption.
Qed.

(** * Looking at some examples of inductive definitions and 
      definitions defined in the automatically loaded prelude of Coq *)

(** * Some basic inductive propositions *)

(* Let us look (again) at how is the [True] proposition (inductively) defined *)
(* Observe that [True] is an inductive definition with one constructor *)
(* with no argument. Hence, it can always be proved (being inhabited). *)
Print True.

(* Let us look at how is the [False] proposition (inductively) defined *)
(* Observe that [False] is an inductive definition with no constructor at all *)
(* Hence, it can never be proved (being inhabited) *)
Print False.

(* Let us look at how is the conjunction of propositions is inductively defined *)
(* Observe that [and A B] is bound to a notation, "A /\ B" *)
(* Observe that [and A B] has a single constructor expecting two arguments: a proof of A and a proof of B *)
(* Observe that [and A B] comes with "implicit" arguments *)
Print and.

(* Since [and] is bound to the notation "\/", we can as well say *)
Print "/\".

(* Let us look at how is the disjunction of propositions is inductively defined *)
(* Observe that [or A B] is bound to a notation, "A \/ B" *)
(* Observe that [or A B] has two constructors expecting each one argument, *)
(* either a proof of A or a proof of B *)
(* Observe that [and] comes with "implicit" arguments *)
Print or.

(* Let us look as how the negation is defined in terms of [False] *)
Print not.

(* It happens that "not A" is bound to a notation "~ A" as witnessed by the
following *)
Print "~".

(* Let us look as how iff is defined in terms of [and] and [->] *)
Print iff.

(* It happens that "iff A B" is bound to a notation "A <-> B" as witnessed by the
following *)
Print "<->".

(* Exercice: define inductively a ternary conjunction on the model of the binary one *)
Inductive and3 (A B C : Prop) : Prop :=
  conj3 : A -> B -> C -> and3 A B C.

(* Show that this ternary conjunction is equivalent to two binary ones *)
Lemma and3_decomposition : forall A B C : Prop, and3 A B C <-> A /\ B /\ C.
Proof.
intros *; split.
- intros (HA,HB,HC).
  split.
  + assumption.
  + split; assumption.
- intros (HA,(HB,HC)).
  (* We can repeat a tactic *)
  repeat split; assumption.
Qed.

(* Sections allow to introduce a local assumption which will later be discharged *)

Section Classical_reasoning.

(* We assert the classical principle of double negation elimination *)

Variable DNE : forall A:Prop, ~~A -> A.

Lemma excluded_middle : forall A:Prop, A \/ ~A.
Proof.
intro.
apply DNE.
intro H.
apply H.
right.
intro HA.
apply H.
left.
apply HA.
Qed.

Lemma drinker_paradox :forall P:nat -> Prop, exists x:nat, forall y:nat, P x -> P y.
Proof.
intro P.
(* We give a proof directly using DNE *)
apply DNE. intro H. apply H.
exists 0.
intros y HP0.
apply DNE. intro H'. apply H'.
exfalso.
apply H.
exists y.
intros y' HPy.
exfalso.
apply H', HPy.
Qed.

(* This closes the section, discharging over DNE *)
End Classical_reasoning.

(* Check the statement of drinker_paradox out of the section *)
Check drinker_paradox.
