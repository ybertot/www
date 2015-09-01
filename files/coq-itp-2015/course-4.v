Require Coq.Arith.Plus.
(** Dependent Inductive Types **)
(*******************************)

Section vectors.
  Variable T : Type.

  (* We can use dependent types to enrich types with their properties.
   * For example the type of 'lists with a given length'.
   * Traditionally, length-indexed lists are called 'vectors'.
   *)
  Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall {n}, T -> vector n -> vector (S n).

  Arguments Vcons {_} _ _.
  Arguments Vnil.

  (** Let's define some more notation *)
  Local Notation "[|  |]" := Vnil.
  Local Notation "[|  x ; .. ; y  |]" := (@Vcons _ x (.. (@Vcons _ y Vnil) ..)).

  Section vector_examples.
    Variables a b c : T.

    Check [| |].
    Check [| a |].
    Check [| a ; b ; c |].
  End vector_examples.

  (* When we define dependent types inductively, we learn
   * information about the index (in this case the nat) when
   * we inspect the value.
   *
   * Coq's 'in'-clause allows us to express how the return
   * type depends on the indices
   *)

  Fixpoint append (l1 : list T) (l2 : list T) : list T.
  destruct l1.
  apply l2.
  apply cons. apply t. apply append. apply l1. apply l2.
  Defined.

  Require Import List.
  Theorem append_eq_app : append = @List.app T.
  reflexivity.
  Qed.

  (* 'in'-clause pattern matching *)
  Fixpoint vappend {n m : nat} (v1 : vector n) (v2 : vector m) {struct v1}
  : vector (n + m).
  refine
    match v1 in vector l' return vector (l' + m) with
    | Vnil => v2
    | Vcons n' x xs => Vcons x (vappend _ _ xs v2)
    end.
  Defined.
  
  Section test2.
    Variables a b c : T.
    Eval compute in vappend [| a ; b |] [| c |].
  End test2.

  (* Can you implement appending a single element to the vector? *)
  Fixpoint vsnoc {n : nat} (x : T) (v : vector n)
  : vector (S n) :=
    match v
          in vector l'
          return vector (S l')
    with
    | Vnil => [| x |]
    | Vcons n' x' xs => Vcons x' (vsnoc x xs)
    end.

  Variables a b c : T.
  Eval compute in vsnoc c [| a ; b |].

  (* If we want to prove these two functions are related
   * in the obvious way, we run into a problem.
   *)
(*
  Theorem vappend_vsnoc : forall n x (v : vector n),
      vsnoc x v = vappend v [| x |].
*)











  (* The problem lies in the type of the theorem.
   * [vsnoc x v] has type [vector (S n)] while
   * [vappend v [| x |]] has type [vector (n + 1)].
   * While [S n = n + 1] is *provable* the two are
   * not definitionally equal.
   *
   * To state the above theorem, we need to use a
   * proof that [S n = n + 1] to 'cast'
   * [vappend v [| x |]] into the type [vector (S n)].
   * We can do this using dependent pattern matching
   * on equality types.
   *)
  Print eq.

  (* Dependent pattern matching on this type is quite
   * similar to dependent pattern matching on vectors.
   * Let's take a look by implementing [Vcast].
   *)
  Definition Vcast (n m : nat) (pf : n = m)
  : vector n -> vector m :=
    match pf with
    | eq_refl => fun x => x
    end.



  (* We can use dependent pattern matching on equality
   * proofs to state the associativity of [vappend].
   *)
  Theorem vappend_assoc
  : forall a b c (va : vector a) (vb : vector b) (vc : vector c),
      vappend (vappend va vb) vc
      = match Plus.plus_assoc a b c in @eq _ _ X return vector X with
        | eq_refl => vappend va (vappend vb vc)
        end.
  Proof.
    induction va.
    - simpl. admit.
    - simpl. intros. rewrite IHva.
      admit.
  Abort.




  (* Everything will work out if we have a transparent definition of
   * plus_assoc.
   *)
  Lemma plus_assoc_trans : forall n m p : nat, n + (m + p) = n + m + p.
  Proof.
    induction n.
    { reflexivity. }
    { simpl. intros. f_equal. eapply IHn. }
  Defined.

  Theorem vappend_assoc
  : forall a b c (va : vector a) (vb : vector b) (vc : vector c),
      vappend (vappend va vb) vc
      = match plus_assoc_trans a b c in _ = X return vector X with
        | eq_refl => vappend va (vappend vb vc)
        end.
  Proof.
    induction va.
    - simpl. reflexivity.
    - simpl. intros. rewrite IHva.
      clear IHva.
      generalize dependent (plus_assoc_trans n b0 c0).
      destruct e. simpl. reflexivity.
  Qed.







  (* In some cases, the value of the index guarantees that
   * certain cases are not possible. For example, getting
   * the first element of a non-empty vector.
   *
   * Coq still requires that we address all the cases.
   *)
  Definition vhd {n : nat} (v : vector (S n)) : T :=
    match v
          in vector l'
          return match l' return Type with
                 | 0 => unit
                 | S _ => T
                 end
    with
    | Vnil => tt
    | Vcons n' x' xs' => x'
    end.

  (* The technique above shows how to express "impossible"
   * cases by making the 'return' clause return easy to
   * construct types in those cases.
   *
   * Can you implement the tail function for vectors?
   *)
  Definition vtl {n : nat} (v : vector (S n)) : vector n.
  Admitted.




  (* Understanding a dependent pattern matching is important
   * when it comes to implementing functions/proving theorems
   * about eta-expansion (as well as many other properties).
   *)
  Theorem vector_eta n (v : vector (S n))
  : v = Vcons (vhd v) (vtl v).
  Proof. Admitted.

  (* Note that here, we need to pass [v'] from the outside so
   * that learning additional information about [n'] updates
   * refines the type of [v'].
   *)

  (* Can you use a similar strategy to prove that [Vcons]
   * is injective?
   *
   * Note that [inversion] does not help here due to the
   * dependency.
   *)
  Theorem Vcons_inj : forall n (a b : T) (v v' : vector n),
      Vcons a v = Vcons b v' ->
      a = b /\ v = v'.
  Proof. Admitted.


  (* We'll need a similar trick when we implement a decision
   * procedure for equality.
   *)
  Section dec.
    Variable T_dec : forall a b : T, {a = b} + {a <> b}.
(*
    Definition vector_dec {n} (v1 v2 : vector n)
    : {v1 = v2} + {v1 <> v2}.
      decide equality.
*)
    (* [decide equality] is not helpful here because of the
     * dependent types. Can you implement the function on your
     * own?
     *
     * Note, functions like this can, unfortuantely, get
     * quite long. Luckily, we can use tactics to discharge
     * the final obligations.
     *
     * Considering the computation, it is often best to
     * only use tactics to construct propositions, and
     * to construct the computational part of the function
     * explicitly.
     *)
    Fixpoint vector_dec {n} (v1 : vector n)
    : forall v2 : vector n, {v1 = v2} + {v1 <> v2}.
    Admitted.
  End dec.

  (************************** END LECTURE *****************************)

  (* Getting the nth-element of a vector
   * The most difficult part of getting the nth-element
   * of a vector is describing when it is possible.
   * There are a several ways to do it. For example,
   *)
  Definition vnth_nat {n : nat} (v : vector n) (m : nat) : m < n -> T.
  Admitted.


  (* Implementing this function, however is a bit cumbersome.
   * We can simplify the task by building a new inductive type
   * that encodes "valid indices" into a vector. This type is
   * often called 'fin', for "a finite type with n elements".
   *)
  Inductive fin : nat -> Type :=
  | FO : forall {n}, fin (S n)
  | FS : forall {n}, fin n -> fin (S n).

  (* Some examples are helpful for understanding how this works.
   *)
  Definition zero_of_one : fin 1 := FO.
  Definition one_of_two : fin 2 := FS FO.
  Definition three_of_eight : fin 8 := FS (FS (FS FO)).

  (* Using this definition, we can recurse over the
   * index and extract the appropriate value.
   *)
  Fixpoint vnth_fin {l : nat} (vs : vector l) (f : fin l) {struct f}
  : T :=
    match f in fin l return vector l -> T with
    | FO n => fun v => vhd v
    | FS _ f => fun v => vnth_fin (vtl v) f
    end vs.

  Section examples_vnth_fin.
    Variables a b c : T.

    Eval compute in vnth_fin [| a ; b ; c |] (FS (FS FO)).

    Eval compute in vnth_fin [| a ; b ; c |] (FS FO).
  End examples_vnth_fin.

  (* It is also possible (though a bit more difficult)
   * to recurse over the vector. The reason for this
   * is that when we match on the vector, we need to
   * handle the case where the vector is empty. In this
   * case, we need to prove that [fin 0] implies a
   * contradiction.
   *)
  Fixpoint vnth_fin' {l : nat} (vs : vector l) (f : fin l) {struct vs}
  : T :=
    match vs in vector l return fin l -> T with
    | Vnil => fun f : fin 0 => match f with
                               | FO _ => tt
                               | FS _ _ => tt
                               end
    | Vcons n v vs => fun f : fin (S n) =>
                        match f with
                        | FO _ => fun _ => v
                        | FS _ f' => fun vs => vnth_fin' vs f'
                        end vs
    end f.

  Section examples_vnth_fin'.
    Variables a b c : T.

    Eval compute in vnth_fin' [| a ; b ; c |] (FS (FS FO)).

    Eval compute in vnth_fin' [| a ; b ; c |] (FS FO).
  End examples_vnth_fin'.


  (* More functions *)
  (******************)

  (* To get more of a flavor of using dependent pattern
   * matching, try implementing some more functions and
   * verifying properties about them.
   *)
  Fixpoint vrev {n : nat} (v : vector n)
  : vector n.
  Admitted.

  Fixpoint vlength {n : nat} (v : vector n) : nat.
  Admitted.

  Theorem vlength_is_length
  : forall n (v : vector n),
      vlength v = n.
  Proof. Admitted.

  Theorem vappend_Vnil
  : forall a (va : vector a),
      match plus_n_O_trans a in _ = X return vector X with
      | eq_refl => va
      end = vappend va [| |].
  Proof. Admitted.

  Theorem vsnoc_append
  : forall b a (va : vector a) (vb : vector b) x,
      vsnoc x (vappend va vb) =
      match eq_sym (plus_n_Sm_trans a b) in _ = X return vector X with
      | eq_refl => vappend va (vsnoc x vb)
      end.
  Proof. Admitted.

  Theorem vrev_append
    : forall a b (va : vector a) (vb : vector b),
      vrev (vappend va vb)
      = match eq_sym (plus_comm_trans a b) in _ = X return vector X with
        | eq_refl => vappend (vrev vb) (vrev va)
        end.
  Proof. Admitted.

End vectors.
