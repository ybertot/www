(***********************************************************************)
(** Basic tactics for dealing with logical connectives                 *)
(** Revised version, 2015/8/29                                         *)
(***********************************************************************)

(** Checking well-formedness and typing *)

Check forall A:Prop, A -> A.

(** Stating a theorem *)

Theorem simple_theorem : forall A:Prop, A -> A.

(** Starting a proof; "Proof" is a no-op for better structuring proofs *)
Proof.

(* intro is the tactic for proving "forall" statement: to prove a
   "forall x:T, B" we take some arbitrary x:T (here an A:Prop) and
   try to prove B *)
intro A.

(* intro is also the tactic for proving "->" statement: to prove a 
   "A -> B" we assume that A holds, here naming its proof HA, and 
   try to prove B *)
intro HA.

(* assumption: tactic for directly using an assumption, here HA *)
assumption.

(* Ending the proof, registering the theorem *)
Qed.

(* Verifying what the theorem proves *)
Check simple_theorem.

(* Showing its proof *)
Print simple_theorem.

(** A slightly more complex theorem *)

Theorem S : forall A B C:Prop, (A -> B -> C) -> (A -> B) -> A -> C.
Proof.

(* intro can be iterated *)
intros A B C H1 H2 HA.

(* apply: tactic for using an assumption, or an already defined
   constant, or an axiom *)
apply H1.

(* Focusing on subgoals using a "bullet" for each subgoal (not
   necessary but gives control on the structure of the proof) *)
- apply HA.
- apply H2.
  apply HA.

Qed.

(** Using conjunction *)

(* [and] is defined as an inductive type with one constructor *)
Print and.

Theorem and_commute : forall A B:Prop, A /\ B -> B /\ A.
Proof.

(* An advanced form of intros: * intros all forthcoming dependent variables *)
intros * Hyp.

(* Tactic for proving a statement built from an inductive type which
   is itself built from a single constructor, as [/\] is *)
split.

(* A tactic for destructing an assumption in an inductive type *)
- destruct Hyp.
  apply H0.

(* We do the same on the second goal, but this time naming ourselves
   the hypotheses for better control on names *)
- destruct Hyp as (HA,HB).
  apply HA.

Qed.

(** Using disjunction *)

(* [or] is defined as an inductive type with two constructors *)
Print or.

Theorem or_commute : forall A B:Prop, A \/ B -> B \/ A.
Proof.
intros * Hyp.

(* We need to know whether A or B holds to be able to say that B or A holds *)
destruct Hyp as [HA|HB].

(* To prove the right-hand side of an inductive type with two
   constructors such as [\/] *)
- right.
  apply HA.

(* Similarly with the left-hand side *)
- left.
  apply HB.

Qed.

(** Using negation, falsity and iff *)

Theorem iff_or : forall A B : Prop, A /\ B \/ ~A /\ ~B -> (A <-> B).
Proof.

(* We can chain tactics with ";" *)
intros * Hyp; destruct Hyp as [Hyp'|Hyp']; destruct Hyp'.

(* We can also combine intros and destruct using so-called
   introduction patterns of the form ( pat , ... , pat ) for
   destructing expressions in inductive types which have a single
   constructor and more generally [ pat ... pat | ... | pat ... pat ]
   for destructing expressions in arbitrary inductive types *)

(* But first Undo previous step *)
Undo.
intros * [(HA,HB)|(HnA,HnB)].

(* Let us go back to the definition of [iff] *)
- unfold iff.
  split.

  (* Let us open a second block of structure *)
  (* and discard the second hypothesis A *)
  + intros _.
    assumption.
  + intros _.
    assumption.

- unfold iff.
  split.

  (* We shall use here a second level of bullets "+" for structuring
     the proof *)

  + intros HA.

    (* Go back to the definition of [not] *)
    unfold not in HnA.

    (* Prove by ex falso quodlibet (i.e. the property False -> A, for any A) *)
    exfalso.
    apply HnA.
    apply HA.

  (* The other case is similar *)

  + intros HB.
    unfold not in HnB.
    exfalso.

    (* We can also chain apply *)
    apply HnB, HB.

Qed.

(** Using existential *)

Theorem forall_exists : forall P : nat -> Prop, forall x : nat, P x -> exists y : nat, P y.
Proof.
(* As usual, to prove "forall", we use intro to set assumptions *)
intros P x Hyp.

(* Now proving the existential statement using "x" *)
exists x.
assumption.
Qed.


