Require Import Arith.
Require Import List.
Require Import Coq.omega.Omega.

(******************************
   Lecture 3 : 
  Inductive datatypes
 ******************************)

(**************************)
(* Inductive declarations *)
(**************************)

(*
Inductive types in Coq can be seen as the 
generalization of similar type constructions in 
more common programming languages.

They are in fact an extremely rich way of defining 
data-types, operators, connectives, specifications,...

They are at the core of powerful programming and 
reasoning techniques.
*)

  Print bool.

  Print nat.

(* Each such rule is called a constructor. *)

(*********************************)
(* Inductive declarations in Coq *)
(*********************************)

(*********************)
(** Enumerated types *)
(*********************)

(* Enumerated types are types which list and name
   exhaustively their inhabitants.
*)

Inductive color : Type :=
  white | black | yellow | cyan | magenta 
| red | blue | green.

Check cyan.

(* Labels refer to distinct elements. *)


(** Enumerated types: program by case analysis *)

Print bool.

Definition my_negb (b : bool) :=
  match b with true => false | false => true end.

Definition is_black_or_white (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | _ => false
  end.

Compute (is_black_or_white blue).

(** Enumerated types: reason by case analysis *)

(*
Reason by covering all cases

destruct is the basic tactic
- generates one goal per data constructor
- the expression is replaced by 
  constructor values, in the conclusion
- the argument to the constructor becomes a 
  universally quantified variable
*)

(** Examples  *)

Lemma bool_case : 
forall b : bool, b = true \/ b = false.
Proof.
destruct b.
 -   left; auto.
 -   right; auto.
Qed.

Lemma is_black_or_whiteP : forall c : color,
  is_black_or_white c = true ->
  c = black \/ c = white.
Proof.
destruct c; simpl; intros H. 
 - right; auto.
 - left; auto.
 - 
   (* Let's try with try congruence ! *)
Admitted.

(****)

Definition pred (x : nat) := 
match x with 0 => x | S p => p end.

Lemma S_pred : forall x, x <> 0 -> 
               S (pred x) = x.
Proof.
destruct x.
 - intros H0. destruct H0. auto.
 - intros HS. simpl. auto.
Qed.

(**********************)
(**  Recursive types  *)
(**********************)

Print nat.

Print list.

About nil.

Check cons blue nil.

Check blue :: white :: red :: yellow :: nil.

Locate "::".

(* Base case constructors do not feature 
   self-reference to the type.

   Recursive case constructors do.
*)

Inductive natBinTree : Type :=
  Leaf: nat -> natBinTree
| Node: nat -> natBinTree -> natBinTree -> natBinTree.

Definition example1 := Node 5 (Leaf 1) (Leaf 10).
Check example1.
Check Node 9 example1 example1.

Inductive term : Type :=
  Zero : term
| One : term
| Plus : term -> term -> term
| Mult : term -> term -> term.

Definition example2 := Mult One (Plus One Zero). 
Check example2.
Check Plus example2 example2.

Definition isNotTwo (n:nat) : bool :=
match n with
      S (S O) => false
    | _ => true
end.

Definition is_single_nBT (t : natBinTree) : bool :=
match t with
   Leaf _ => true
 | _ => false
end.

(* Constructors are injective. *)
Check Leaf.

Lemma inj_leaf : forall x y, Leaf x = Leaf y -> x = y.
Proof.
  congruence.
Qed.


(*** Recursive functions and induction *)

(*
When a function is recursive, calls are usually 
made on direct subterms.

The structure of the proof is imposed by the 
data-type.
 *)

(**  Example proof on a recursive function *)

Fixpoint add n m :=
match n with 
   0 => m 
 | S p => add p (S m) 
end.

Lemma addnS : forall n m, 
add n (S m) = S (add n m).
Proof.
intros n m.
induction n.
- simpl. auto.

- simpl.
admit.
(*  apply IHn.
Qed. *)

(** Avoid abusive use of intros *)

(*
The previous proof fails if we start with
intros n m; induction n.

The statement to prove is less general (easier).

But the induction hypothesis becomes weaker.
 *)

(*
The tactic induction assumes a simple form of recursion:
- direct pattern-matching on the main variable
- recursive calls on direct subterms

Coq recursion allows deeper recursive calls.

Need for specialized induction principles

*)

(** E X E R C I S E *)
Lemma addn0 : forall n, add n 0 = n.
Proof.
  (* TO DO *)
  admit.
(* E N D   E X E R C I S E *)

(*** Proofs on functions on lists **)

(*
Tactic destruct also works.
Values a and tl in a::tl are added to the context in 
  destruct.

Induction on lists works like induction on 
natural numbers
- nil plays the same role as 0: 
  base case of proofs by induction
- a::tl plays the same role as S
   * Induction hypothesis on tl
   * Fits with recursive calls on tl
*)

(** Example proof on lists *)

Print rev.

Fixpoint rev_app (A : Type)(l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | a :: tl => rev_app A tl (a :: l2)
  end.

Arguments rev_app [A] _ _ .
Print Implicit rev_app.

Compute (rev_app (1::2::3::4::nil) (5::6::nil)).
Compute (rev_app (1::2::3::4::nil)).

(*** E X E R C I S E *)
Lemma my_app_nil_r: forall (A : Type) (l : list A), 
l ++ nil = l.
Proof.
(* TO DO *)
admit.
(* E N D   E X E R C I S E *)

Lemma rev_app_nil : forall A (l1 : list A), 
rev_app l1 nil = rev l1.
Proof.
intros A l1.
assert (Htmp: forall l2, rev_app l1 l2 = rev l1 ++ l2).

- induction l1; intros l2.
  + simpl. auto.
  + simpl.
    Check app_assoc_reverse . 
    SearchPattern (_  ++ _ = _).

    rewrite app_assoc_reverse.
    simpl.
    apply IHl1.

- rewrite Htmp. 
SearchPattern (_ ++ nil = _).
Check app_nil_r. 
rewrite app_nil_r.
auto.
Qed.

(* Proofs about computation 

Reason about functional correctness

- State properties about computation results
  Show consistency between several computations

- Follow the structure of functions
     * Proving is akin to symbolic debugging
     * A proof is a guarantee that all cases 
       have been covered
*)

(**************************)
(* Recursive types :      *)
(*   structural induction *)
(**************************)

Check nat_ind.

(* Induction principle generated by Coq *)

Print term.

(* 
Given P : term -> Prop, how to prove the theorem
forall t : term, P t ?

It is sufficient to prove that :
- P holds for the base cases
- P is transmitted inductively

The type term is the smallest type containing Zero 
and One, and closed under Plus and Mult.
*)

Check term_ind.

(*
The induction principles generated at definition time 
by the system allow to :
- Program by recursion (Fixpoint)
- Prove by induction (induction)
*)

(**************************)
(* Recursive types:       *)
(* program by structural  *)
(*   induction            *)
(**************************)

Print natBinTree.

Fixpoint size (t : natBinTree) : nat :=
match t with
    Leaf _ => 1
  | Node _ t1 t2 => (size t1) + (size t2) + 1
end.

(* Structural recursion: t1 and t2 are subterms of t 
*)

Fixpoint height (t : natBinTree) : nat :=
match t with
 | Leaf _ => 0
 | Node _ t1 t2 => Max.max (height t1) (height t2) + 1
end.

(* Require Import ZArith. *)

(* A proof by structural induction on binary trees *)
Lemma le_height_size : forall t : natBinTree,
              height t <= size t.
Proof.
induction t; simpl.
-  auto.

-  Check plus_le_compat_r.
   apply plus_le_compat_r.
   Check Max.max_case. 
   apply Max.max_case; omega.
Qed. 

(*****************)
(** Option types *)
(*****************)

(* A polymorphic (like list) non recursive type *)

Print option.

(* Use it to lift a type to a copy of this type but 
   with a default value. *)

Fixpoint olast (A : Type)(l : list A) : option A :=
match l with
   nil => None
 | a :: nil => Some a
 | a :: l => olast A l
end.

(*******************************)
(* Application:                *)
(* A toy imperative language   *)
(*******************************)

(* Expressions *)

Definition ident := nat.

Inductive toy_op := toy_plus | toy_mult.

Inductive expr := Econst (i:nat) | 
                  Evar (v:ident) |
                  Eop (op:toy_op) (e1 e2: expr).

(* Alternative notation *)
Inductive expr2 : Type := 
   Econst2: nat -> expr2
 | Evar2: ident -> expr2
 | Eop2: toy_op -> expr2 -> expr2 -> expr2.

(* Commands *)

Inductive cmd := 
   Cassign (v:ident)(e:expr) 
 | Cseq (s s1: cmd) 
 | Csimple_loop (e:expr)(s : cmd).

(* A first program *)

Definition X: ident := 0.
Definition Y := 1.
Definition Z := 2.

(* TO DO
- DEFINE the expression xplus1 ("X+1").
- DEFINE the expression ytimesx ("Y*X").
- Reuse the two previous definitions to DEFINE
  the command cmd12 representing "X=X+1; Y=Y*X".
*)
Definition xplus1 : expr := (**) (Econst 1). 

Definition ytimesx := (**) (Evar X). 

Definition cmd12: cmd := (**)
.

(* TO DO: write the right definition of cmd12 *)

Definition factorial_Z_program :=
 Cseq (Cassign X (Econst 0))
(Cseq (Cassign Y (Econst 1))
      (Csimple_loop (Evar Z) cmd12)
).
