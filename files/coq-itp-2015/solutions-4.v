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
Definition hlist_hd {T Ts} (h : hlist (T :: Ts)) : F T :=
  match h with
  | Hcons _ _ x _ => x
  | Hnil => tt
  end.

Definition hlist_tl {T Ts} (h : hlist (T :: Ts)) : hlist Ts :=
  match h with
  | Hcons _ _ _ xs => xs
  | Hnil => tt
  end.

(* If we want to compute the nth-element of an hlist, we need
 * a way to write the type that we are going to get back.
 * One way to do this is to use computation in types.
 *
 * Exercise: Implement this function.
 *)
Fixpoint hlist_nth' {Ts} (h : hlist Ts) (n : nat)
: option match nth_error Ts n with
         | None => Empty_set
         | Some T => F T
         end :=
  match h in hlist Ts , n
        return option match nth_error Ts n with
                      | None => Empty_set
                      | Some T => F T
                      end
  with
  | Hnil , _ => None
  | Hcons _ _ x _ , 0 => Some x
  | Hcons _ _ _ xs , S n => hlist_nth' xs n
  end.

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
Fixpoint hlist_nth {T Ts} (h : hlist Ts) (n : mem T Ts) : F T :=
  match n in mem _ Ts return hlist Ts -> F T with
  | MO _ => hlist_hd
  | MS _ _ m => fun h => hlist_nth (hlist_tl h) m
  end h.

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

Arguments mem_dec {_} _ {_ _} _ _.

(* A simple Lambda-calculus *)
(****************************)

(* We can use dependent types to describe "well-typed" terms.
 * We start with a type of types.
 *)
Inductive type : Type :=
| Nat
| Bool
| Arr (d c : type)
.

(* I've started a simple definition with just constants, addition
 * and variables.
 *)
Inductive expr (ts : list type) : type -> Type :=
| ConstNat  : nat -> expr ts Nat
| Plus      : expr ts Nat -> expr ts Nat -> expr ts Nat
| ConstBool : bool -> expr ts Bool
| If        : forall t, expr ts Bool -> expr ts t -> expr ts t -> expr ts t
| App       : forall d c, expr ts (Arr d c) -> expr ts d -> expr ts c
| Abs       : forall d c, expr (d :: ts) c -> expr ts (Arr d c)
| Var       : forall {t}, mem t ts -> expr ts t
| PlusE     : expr ts (Arr Nat (Arr Nat Nat)).

Arguments ConstNat {_} _.
Arguments Plus {_} _ _.
Arguments ConstBool {_} _.
Arguments If {_ _} _ _ _.
Arguments App {_ _ _} _ _.
Arguments Abs {_ _ _} _.
Arguments Var {_ _} _.
Arguments PlusE {_}.

(* We can now write functions that map the syntactic definitions
 * into semantic ones.
 *)
Fixpoint typeD (t : type) : Type :=
  match t with
  | Nat => nat
  | Bool => bool
  | Arr l r => typeD l -> typeD r
  end.

Fixpoint exprD {ts : list type} {t : type} (e : expr ts t)
: hlist typeD ts -> typeD t :=
  match e in expr _ t return hlist typeD ts -> typeD t with
  | ConstNat n => fun _ => n
  | Plus a b => let aD := exprD a in let bD := exprD b in
                fun env => aD env + bD env
  | ConstBool b => fun _ => b
  | If _ t tr fa => let tD := exprD t in
                    let trD := exprD tr in
                    let faD := exprD fa in
                    fun env =>
                      if tD env then trD env else faD env
  | App _ _ f x => let fD := exprD f in
                   let xD := exprD x in
                   fun env => (fD env) (xD env)
  | Abs _ _ body => let bodyD := exprD body in
                    fun env => (fun x => bodyD (Hcons x env))
  | Var _ v => fun e => hlist_nth e v
  | PlusE => fun e => plus
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
Definition type_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
decide equality.
Defined.

Definition nat_dec : forall a b : nat, {a = b} + {a <> b}.
decide equality.
Defined.

Definition bool_dec : forall a b : bool, {a = b} + {a <> b}.
decide equality.
Defined.

Definition type_decidable (t1 t2 : type) : (t1 = t2) \/ (t1 <> t2) :=
  match type_dec t1 t2 with
  | left pf => or_introl pf
  | right pf => or_intror pf
  end.

Definition domain (t : type) : type :=
  match t with
  | Arr a _ => a
  | _ => t
  end.

Definition codomain (t : type) : type :=
  match t with
  | Arr _ b => b
  | _ => t
  end.

Fixpoint expr_dec {ts t} (e1 : expr ts t)
: forall e2 : expr ts t, option (e1 = e2).
refine
  match e1 as e1 in expr _ t
        return forall e2 : expr ts t, option (e1 = e2)
  with
  | ConstNat n => fun e2 =>
    match e2 as e2 in expr _ t
          return option (match t as t return expr ts t -> Prop with
                         | Nat => fun e2 => ConstNat n = e2
                         | _ => fun _ => False
                         end e2) with
    | ConstNat m =>
      match nat_dec n m with
      | left pf => Some match pf with
                        | eq_refl => eq_refl
                        end
      | right _ => None
      end
    | _ => None
    end
  | Plus l r => fun e2 =>
    match e2 as e2 in expr _ t
          return forall a b : expr ts Nat,
        option (match t as t return expr ts t -> Prop with
                | Nat => fun e2 => Plus a b = e2
                | _ => fun _ => False
                end e2)
    with
    | Plus l' r' => fun l r =>
      match expr_dec _ _ l l' , expr_dec _ _ r r' with
      | Some pf1 , Some pf2 => Some match pf1 , pf2 with
                                    | eq_refl , eq_refl => eq_refl
                                    end
      | _ , _ => None
      end
    | _ => fun _ _ => None
    end l r
  | ConstBool b => fun e2 =>
    match e2 as e2 in expr _ t
          return option (match t as t return expr ts t -> Prop with
                         | Bool => fun e2 => ConstBool b = e2
                         | _ => fun _ => False
                         end e2)
    with
    | ConstBool m =>
      match bool_dec b m with
      | left pf => Some match pf with
                        | eq_refl => eq_refl
                        end
      | right _ => None
      end
    | _ => None
    end
  | If _ t tr fa => fun e2 =>
    match e2 as e2 in expr _ T
          return forall (t : expr ts Bool) (tr fa : expr ts T),
        option (If t tr fa = e2)
    with
    | If _ t' tr' fa' => fun t tr fa =>
      match expr_dec _ _ t t'
          , expr_dec _ _ tr tr'
          , expr_dec _ _ fa fa'
      with
      | Some pf , Some pf' , Some pf'' =>
        Some match pf , pf' , pf'' with
             | eq_refl , eq_refl , eq_refl => eq_refl
             end
      | _ , _ , _ => None
      end
    | _ => fun _ _ _ => None
    end t tr fa
  | App d c f x => fun e2 =>
    match e2 as e2 in expr _ t
          return forall (f : expr ts (Arr d t))
                        (x : expr ts d)
                        (rec_f : forall e, option (f = e))
                        (rec_x : forall e, option (x = e)),
        option (App f x = e2)
    with
    | App d' c' f' x' =>
      match type_dec d' d with
      | right _ => fun _ _ _ _ => None
      | left pf =>
        match pf in _ = X
              return forall f' x'
                            (f : expr ts (Arr X c'))
                            (x : expr ts X)
                            (rec_f : forall e, option (f = e))
                            (rec_x : forall e, option (x = e)),
            option (App f x = App f' x')
        with
        | eq_refl => fun f' x' _ _ rec_f rec_x =>
                       match rec_f f' , rec_x x' with
                       | Some pf , Some pf' =>
                         Some match pf , pf' with
                              | eq_refl , eq_refl => eq_refl
                              end
                       | _ , _ => None
                       end
        end f' x'
      end
    | _ => fun _ _ _ _ => None
    end f x (fun y => expr_dec _ _ f y) (fun y => expr_dec _ _ x y)
  | Abs d c body => fun e2 =>
    match e2 as e2 in expr _ t
          return forall (body : expr (domain t :: ts) (codomain t))
                        (rec : forall e, option (body = e)),
        option (match t as t
                      return expr (domain t :: ts) (codomain t) -> expr ts t -> Prop
                with
                | Arr d' c' => fun body e2 => Abs body = e2
                | _ => fun _ _ => False
                end body e2)
    with
    | Abs d' c' body' => fun _ rec =>
                           match rec body' with
                           | None => None
                           | Some pf => Some match pf with
                                             | eq_refl => eq_refl
                                             end
                           end
    | _ => fun _ _ => None
    end body (fun y => expr_dec _ _ body y)
  | Var _ v => fun e2 =>
    match e2 as e2 in expr _ t
          return forall v : mem t ts, option (Var v = e2)
    with
    | Var _ v' => fun v =>
      match mem_dec type_decidable v v' with
      | left pf => Some match pf in _ = X with
                        | eq_refl => eq_refl
                        end
      | right _ => None
      end
    | _ => fun _ => None
    end v
  | PlusE => fun e2 : expr ts (Arr Nat (Arr Nat Nat)) =>
    match e2 as e2 in expr _ t
          return option (match t as t return expr ts t -> Prop with
                         | Arr Nat (Arr Nat Nat) => fun e2 => PlusE = e2
                         | _ => fun _ => False
                         end e2)
    with
    | PlusE => Some eq_refl
    | _ => None
    end
  end.
Defined.

(* Exercise: Implement a function that simplifies expressions.
 *)
Definition reduce1 {ts t} (e : expr ts t) : expr ts t :=
  match e in expr _ t return expr ts t -> expr ts t with
  | Plus (ConstNat x) (ConstNat y) => fun _ => ConstNat (x + y)
  | App Nat Nat (App Nat (Arr Nat Nat) PlusE (ConstNat x)) (ConstNat y) =>
    fun _ => ConstNat (x + y)
  | If _ (ConstBool true) tr _ => fun _ => tr
  | If _ (ConstBool false) _ fa => fun _ => fa
  | If _ t tr fa => fun e =>
    if expr_dec tr fa then tr else e
  | _ => fun x => x
  end e.

Lemma if_same : forall T (x : bool) (a : T),
    (if x then a else a) = a.
Proof. destruct x; reflexivity. Qed.

Lemma expr_case_Arr : forall d c ts (e : expr ts (Arr d c)),
    (exists body, e = Abs body) \/
    (exists test tr fa, e = If test tr fa) \/
    (exists d' f x, e = @App ts d' (Arr d c) f x) \/
    (exists m, e = Var m) \/
    (exists (pf : Nat = d) (pf' : Arr Nat Nat = c),
        e = match pf , pf' with
            | eq_refl , eq_refl => PlusE
            end).
Proof.
  intros.
  refine
    match e as e in expr _ t
          return match t as t return expr ts t -> Prop with
                 | Arr d c => fun e =>
                                (exists body : expr (d :: ts) c, e = Abs body) \/
                                (exists (test : expr ts Bool) (tr fa : expr ts (Arr d c)),
                                    e = If test tr fa) \/
                                (exists (d' : type) (f : expr ts (Arr d' (Arr d c))) 
                                        (x : expr ts d'), e = App f x) \/
                                (exists m : mem (Arr d c) ts, e = Var m) \/
                                (exists (pf : Nat = d) (pf' : Arr Nat Nat = c),
                                    e =
                                    match pf in (_ = t) return (expr ts (Arr t c)) with
                                    | eq_refl =>
                                      match pf' in (_ = t) return (expr ts (Arr Nat t)) with
                                      | eq_refl => PlusE
                                      end
                                    end)
                 | _ => fun _ => True
                 end e
    with
    | ConstNat _ => I
    | Plus _ _ => I
    | ConstBool _ => I
    | _ => _
    end.
  { destruct t; eauto 10. }
  { destruct c0; eauto 10. }
  { eauto. }
  { destruct t; eauto 10. }
  { repeat right. exists eq_refl. exists eq_refl. reflexivity. }
Qed.

Theorem reduce1_sound : forall ts t (e : expr ts t),
    forall env, exprD (reduce1 e) env = exprD e env.
Proof.
  destruct e; simpl; auto.
  { refine
      match e1 as e1 in expr _ X1
          , e2 as e2 in expr _ X2
            return match X1 as X1 , X2 as X2
                         return expr ts X1 -> expr ts X2 -> Prop
                   with
                   | Nat , Nat => fun e1 e2 =>
                                    forall env : hlist typeD ts,
                                      exprD
                                        (match e1 with
                                         | ConstNat a =>
                                           match e2 with
                                           | ConstNat b => fun _ : expr ts Nat => ConstNat (a + b)
                                           | _ => fun e' : expr ts Nat => e'
                                           end
                                         | _ => fun e' : expr ts Nat => e'
                                         end (Plus e1 e2)) env =
                                      exprD e1 env + exprD e2 env
                   | _ , _ => fun _ _ => True
                   end e1 e2
      with
      | ConstNat _ , ConstNat _ => fun _ => eq_refl
      | _ , _ => _
      end; try solve [ reflexivity | destruct t; reflexivity ].
    destruct c; trivial. destruct c; trivial. }
  { refine
      match e1 as e1 in expr _ X1
            return match X1 as X1 return expr ts X1 -> Prop with
                   | Bool => fun e1 => forall env : hlist typeD ts,
                       exprD
                         (match e1 with
                          | ConstNat _ => fun e : expr ts t => if expr_dec e2 e3 then e2 else e
                          | Plus _ _ => fun e4 : expr ts t => if expr_dec e2 e3 then e2 else e4
                          | ConstBool true => fun _ : expr ts t => e2
                          | ConstBool false => fun _ : expr ts t => e3
                          | If _ _ _ _ => fun e5 : expr ts t => if expr_dec e2 e3 then e2 else e5
                          | App _ _ _ _ => fun e : expr ts t => if expr_dec e2 e3 then e2 else e
                          | Abs _ _ _ => fun e : expr ts t => if expr_dec e2 e3 then e2 else e
                          | Var _ _ => fun e : expr ts t => if expr_dec e2 e3 then e2 else e
                          | PlusE => fun e : expr ts t => if expr_dec e2 e3 then e2 else e
                          end (If e1 e2 e3)) env =
                       (if exprD e1 env then exprD e2 env else exprD e3 env)
                   | _ => fun _ => True
                   end e1
      with
      | ConstBool true => fun _ => eq_refl
      | ConstBool false => fun _ => eq_refl
      | ConstNat _ => I
      | Plus _ _ => I
      | Abs _ _ _ => I
      | _ => _
      end;
    repeat (match goal with
            | |- match ?X with _ => _ end _ => destruct X
            end; trivial; simpl; intros);
    destruct (expr_dec e2 e3); simpl; subst; try rewrite if_same; reflexivity. }
  { (* This case is a little bit ugly due to the deep pattern matching.
     * A more modular optimization approach simplifies this case substantially.
     *)
    specialize (expr_case_Arr _ _ _ e1); intros;
    repeat match goal with
           | H : _ \/ _ |- _ => destruct H
           | H : exists x, _ |- _ => destruct H
           end; subst; try solve [ simpl; auto | destruct c; auto ].
    { destruct d; auto. destruct c; auto. }
    { destruct d; auto. destruct c; auto. }
    { specialize (expr_case_Arr _ _ _ x0); intros;
      repeat match goal with
             | H : _ \/ _ |- _ => destruct H
             | H : exists x, _ |- _ => destruct H
             end; subst; simpl.
      { destruct d; auto. destruct c; auto. destruct x; auto. }
      { destruct d; auto. destruct c; auto. destruct x; auto. }
      { destruct d; auto. destruct c; auto. destruct x; auto. }
      { destruct d; auto. destruct c; auto. destruct x; auto. }
      { inversion x3. subst.
        eapply K_dec with (p:=x3). eapply type_decidable.
        simpl. clear.
        refine
          match x1 as e1 in expr _ X1
                            , e2 as e2 in expr _ X2
                return match X1 as X1 , X2 as X2
                             return expr ts X1 -> expr ts X2 -> Prop
                       with
                       | Nat , Nat => fun e1 e2 =>
                         exprD
                           (match e1 with
                            | ConstNat a =>
                              match e2 with
                              | ConstNat b => fun _ : expr ts Nat => ConstNat (a + b)
                              | _ => fun e' : expr ts Nat => e'
                              end
                            | _ => fun e' : expr ts Nat => e'
                            end (App (App PlusE e1) e2)) env =
                         exprD e1 env + exprD e2 env
                       | _ , _ => fun _ _ => True
                       end e1 e2
          with
          | ConstNat _ , ConstNat _ => _
          | _ , _ => _
          end; try solve [ reflexivity | destruct c ; auto | destruct t; auto ]. } }
    { destruct d; auto. destruct c; auto. } }
Qed.

Fixpoint simplify {ts t} (e : expr ts t) : expr ts t :=
  reduce1
    match e in expr _ t return expr ts t with
    | ConstNat n => ConstNat n
    | Plus a b => Plus (simplify a) (simplify b)
    | ConstBool b => ConstBool b
    | If _ a b c => If (simplify a) (simplify b) (simplify c)
    | App _ _ f x => App (simplify f) (simplify x)
    | Abs _ _ body => Abs (simplify body)
    | Var _ v => Var v
    | PlusE => PlusE
    end.

(* For example, you should optimize (1 + (2 + 3)) to 6. *)

Eval compute in simplify (ts:=[]) (Plus (ConstNat 1) (Plus (ConstNat 2) (ConstNat 3))).

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
  Opaque reduce1.
  induction e; simpl; intros; auto; try rewrite reduce1_sound; simpl;
  repeat match goal with
         | H : _ |- _ => rewrite H
         end; try reflexivity.
  Require Coq.Logic.FunctionalExtensionality.
  apply FunctionalExtensionality.functional_extensionality.
  auto.
  Transparent reduce1.
Qed.

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
Definition tuple_hd {a} : tuple (S a) -> T :=
  @fst _ _.
Definition tuple_tl {a} : tuple (S a) -> tuple a :=
  @snd _ _.

Fixpoint tappend (a b : nat) (va : tuple a) (vb : tuple b) {struct a}
: tuple (a + b) :=
  match a as a return tuple a -> tuple (a + b) with
  | 0 => fun _ => vb
  | S a => fun x => (tuple_hd x, tappend _ _ (tuple_tl x) vb)
  end va.

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

Fixpoint tuple_to_vector {n} : tuple n -> vector n :=
  match n as n return tuple n -> vector n with
  | 0 => fun _ => Vnil
  | S n => fun t => Vcons (tuple_hd t) (tuple_to_vector (tuple_tl t))
  end.

Fixpoint vector_to_tuple {n} (t : vector n) : tuple n :=
  match t in vector n return tuple n with
  | Vnil => tt
  | Vcons _ x xs => (x, vector_to_tuple xs)
  end.

Theorem vector_tuple : forall n (v : vector n),
    tuple_to_vector (vector_to_tuple v) = v.
Proof.
  induction v; simpl; auto.
  rewrite IHv. reflexivity.
Qed.

Theorem tuple_vector : forall n (t : tuple n),
    vector_to_tuple (tuple_to_vector t) = t.
Proof.
  induction n; simpl; auto.
  { destruct t; auto. }
  { destruct t; simpl. f_equal; auto. }
Qed.

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
  induction va; simpl; intros.
  { rewrite vector_tuple. reflexivity. }
  { f_equal. auto. }
Qed.
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

Definition BiFunctor_treeF {X Y T U : Type} (f : T -> U) (g : X -> Y)
           (v : treeF X T)
: treeF Y U :=
  match v with
  | Empty => Empty
  | Branch l v r => Branch (f l) (g v) (f r)
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

Let demo1 := Eval compute in branch empty 1 empty.
Let demo2 := Eval compute in branch demo1 3 demo1.

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

Section functor_mu.
  Context {T U : Type} {F : Type -> Type -> Type}.
  Variable f : forall x y, (x -> y) -> F T x -> F U y.
  Fixpoint Functor_mu n  {struct n} : mu n (F T) -> mu n (F U) :=
    match n as n return mu n (F T) -> mu n (F U) with
    | 0 => fun x : Empty_set => x
    | S n => fun x : F T (mu n (F T)) =>
               f _ _ (Functor_mu _) x
    end.
End functor_mu.

(* Exercise: Prove that tree is a functor.
 * (Note, above we showed that treeF is a functor, that is what allowed
 *  us to lift the sub-trees.)
 * (Hint: You will want to prove a generic lemma about mu)
 *)
Definition Functor_tree {T U} (f : T -> U) (t : tree T) : tree U :=
  let '(existT n t) := t in
  existT _ n
         (@Functor_mu T U treeF (fun _ _ g => BiFunctor_treeF g f) _ t).

(* Exercise: Implement a fold function for trees.
 *)
Section mu_folder.
  Context {U : Type}.
  Context {F : Type -> Type}.
  Variable (do : F U -> U).
  Variable (func : forall {x y}, (x -> y) -> F x -> F y).

  Fixpoint Fold_mu n : mu n F -> U :=
    match n as n return mu n F -> U with
    | 0 => fun x : Empty_set => match x with end
    | S n => fun x : F (mu n F) =>
               do (func _ _ (Fold_mu n) x)
    end.
End mu_folder.

Section tree_folder.
  Context {T U : Type}.
  Variables (at_leaf : U) (at_branch : U -> T -> U -> U).

  Definition Fold_treeF n : mu n (treeF T) -> U :=
    @Fold_mu U (treeF T)
             (fun x => match x with
                       | Empty => at_leaf
                       | Branch l d r => at_branch l d r
                       end)
             Functor_treeF n.

  Definition Fold_tree (t : tree T) : U :=
    Fold_treeF (projT1 t) (projT2 t).
End tree_folder.

Eval compute in Fold_tree 0 (fun x y z => x + y + z)
                          (branch (branch empty 3 empty)
                                  4
                                  (branch empty 7 empty)).


(* Exercise: The naive definition of equality for these trees is wrong
 * because it requires two trees to have exactly the same step size.
 * What is a better definition that ignores the steps?
 *)
Section eq_tree.
  Context {T : Type}.
  Inductive eq_treeF : forall {n m}, mu n (treeF T) -> mu m (treeF T) -> Prop :=
  | Eq_Leaf : forall n m, @eq_treeF (S n) (S m) Empty Empty
  | Eq_Branch : forall n m l d r l' r',
      eq_treeF l l' ->
      eq_treeF r r' ->
      @eq_treeF (S n) (S m) (Branch l d r) (Branch l' d r').

  Definition eq_tree (a b : tree T) : Prop :=
    eq_treeF (projT2 a) (projT2 b).


  Definition eq_treeF_not {n m} (a : mu (S n) (treeF T)) (b : mu (S m) (treeF T)) :
    match a with
    | Empty => true
    | Branch _ _ _ => false
    end <> match b with
           | Empty => true
           | Branch _ _ _ => false
           end ->
    ~eq_treeF a b.
  Proof.
    red.
    intros. revert H.
    refine
      match H0 in @eq_treeF n m L R
            return match n as n , m as m
                         return mu n (treeF T) -> mu m (treeF T) -> Prop
                   with
                   | S n , S m => fun L R =>
                       match L with
                       | Empty => true
                       | Branch _ _ _ => false
                       end <> match R with
                              | Empty => true
                              | Branch _ _ _ => false
                              end -> False
                   | _ , _ => fun _ _ => True
                   end L R
      with
      | Eq_Leaf _ _ => fun pf => pf eq_refl
      | Eq_Branch _ _ _ _ _ _ _ _ _ => fun pf => pf eq_refl
      end.
  Qed.

  Definition eq_treeF_get {n m} a b c d e f :
    @eq_treeF (S n) (S m) (Branch a b c) (Branch d e f) ->
    eq_treeF a d /\ b = e /\ eq_treeF c f :=
    fun H =>
      match H in @eq_treeF n m L R
            return match n as n , m as m
                         return mu n (treeF T) -> mu m (treeF T) -> Prop
                   with
                   | S n , S m => fun L R =>
                     match L , R with
                     | Branch ll ld lr , Branch rl rd rr =>
                       eq_treeF ll rl /\ ld = rd /\ eq_treeF lr rr
                     | _ , _ => True
                     end
                   | _ , _ => fun _ _ => True
                   end L R
      with
      | Eq_Leaf _ _ => I
      | Eq_Branch _ _ _ _ _ _ _ pf pf' => conj pf (conj eq_refl pf')
      end.
End eq_tree.

(* Can you prove that this proposition is decidable?
 * Hint: While not optimal, it is probably easy to lift the two trees to
 * the same index before performing the comparison.
 *)
Section decidable.
  Context {T : Type}.
  Variable T_dec : forall a b : T, a = b \/ a <> b.
  Fixpoint eq_treeF_dec (n m : nat)  {struct n}
  : forall (a : mu n (treeF T)) (b : mu m (treeF T)), eq_treeF a b \/ ~eq_treeF a b.
  refine
    match n as n
          return forall (a : mu n (treeF T)) (b : mu m (treeF T)),
        eq_treeF a b \/ ~eq_treeF a b
    with
    | 0 => fun l : Empty_set => match l with end
    | S n => fun l : treeF T (mu n (treeF T)) =>
               match m as m
                     return forall (b : mu m (treeF T)), @eq_treeF T (S n) m l b \/ ~@eq_treeF T (S n) m l b
               with
               | 0 => fun r : Empty_set => match r with end
               | S m => fun r : treeF T (mu m (treeF T)) =>
                          match l as l , r as r
                                return @eq_treeF T (S n) (S m) l r \/ ~@eq_treeF T (S n) (S m) l r
                          with
                          | Empty , Empty => or_introl (Eq_Leaf _ _)
                          | Branch ll ld lr , Branch rl rd rr =>
                            match eq_treeF_dec _ _ ll rl
                                  , T_dec ld rd
                                  , eq_treeF_dec _ _ lr rr
                            with
                            | or_introl pf , or_introl pf' , or_introl pf'' => or_introl _
                            | _ , _ , _ => or_intror _
                            end
                          | _ , _ => or_intror _
                          end
               end
    end; try solve [ apply eq_treeF_not; compute; congruence ].
  { subst. constructor; eauto. }
  { intro. apply eq_treeF_get in H. intuition. }
  { intro. apply eq_treeF_get in H. intuition. }
  { intro. apply eq_treeF_get in H. intuition. }
  Qed.
End decidable.


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
