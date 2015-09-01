(* -------------------------------------------------------------------- *)
Require Import Omega.

Require Import List.

SearchAbout app.

(* preliminary definitions and lemmas *)

Require Import String.
Require Import OrderedType.

Declare Module String_as_OT : OrderedType
    with Definition t := string
    with Definition eq := @eq string.

Require Import Ensembles.

Arguments Union [_] _ _ _.
Arguments Empty_set [_] _.
Arguments Singleton [_] _ _.
Arguments In [_] _ _.

Section BIGCUP.

Context {A : Type}.

Fixpoint BIGCUP (n : nat) (f : nat -> A) : Ensemble A :=
  match n with
  | O => Singleton (f 0)
  | S m => Union (Singleton (f n)) (BIGCUP m f)
  end.

Variable f : nat -> A.

Lemma In_BIGCUP X n : n <= X -> In (BIGCUP X f) (f n).
Proof.
induction X.
  destruct n; [intros _| now auto].
  simpl.
  now apply In_singleton.
intros.
simpl.
rewrite NPeano.Nat.le_succ_r in H.
destruct H as [nX | ?]; [ | subst n].
  now apply Union_intror, IHX.
now apply Union_introl, In_singleton.
Qed.

Lemma In_BIGCUP_inv t X : In (BIGCUP X f) t -> exists n, n <= X /\ t = f n.
Proof.
induction X.
  simpl.
  inversion_clear 1.
  now exists 0.
simpl.
inversion_clear 1.
  exists (S X).
  split; [ now auto | ].
  now inversion_clear H0.
destruct (IHX H0) as [n [nX tfn]].
exists n.
split; [ | now auto].
now apply le_S.
Qed.

End BIGCUP.

Require Import FMapList.
Require FMapFacts.

Module Type STATE.

Parameter state : Type.
Definition assert := state -> Prop.
Definition entails (P Q : assert) : Prop := forall s, P s -> Q s.
Parameter exp : Type.
Parameter bexp : Type.
Parameter eval : exp -> state -> nat.
Parameter beval : bexp -> state -> Prop.

End STATE.

Module Type CMD0 (S : STATE).

Parameter cmd0 : Type.
Parameter exec0 : S.state -> cmd0 -> option S.state -> Prop.
Parameter hoare0 : S.assert -> cmd0 -> S.assert -> Prop.

End CMD0.

Module Procs := FMapList.Make (String_as_OT).
Module ProcsFacts := FMapFacts.Facts Procs.

Definition proc := Procs.key.

Module Cmd (S : STATE) (Cmd0 : CMD0 S).

Let state := S.state.
Let exp := S.exp.
Let bexp := S.bexp.

Let assert := S.state -> Prop.

Local Notation "P ===> Q" := (S.entails P Q) (at level 89, no associativity).

Let beval := S.beval.

Local Notation "'[' e ']b_' s" := (beval e s) (at level 9, format "'[' [  e  ]b_ s ']'", no associativity).

Inductive cmd : Type :=
| basic : Cmd0.cmd0 -> cmd
| seq : cmd -> cmd -> cmd
| ifte : bexp -> cmd -> cmd -> cmd
| while : bexp -> cmd -> cmd
| call : proc -> cmd.

Local Notation "c .; d" := (seq c d) (at level 81, right associativity).

Local Notation "'If' e 'Then' c1 'Else' c2" := (ifte e c1 c2)
  (at level 200, right associativity, format
"'[v' '[' 'If'  e  'Then' ']' '//'   '[' c1 ']' '//' '[' 'Else' ']' '//'   '[' c2 ']' '//' ']'").

Definition procs := Procs.t cmd.

Reserved Notation "l |~ s >- c ---> t" (at level 70, s, c, t at next level, no associativity).

Inductive exec (l : procs) : state -> cmd -> option state -> Prop :=
| exec_basic : forall s c0 s1, Cmd0.exec0 s c0 s1 ->
  l |~ s >- basic c0 ---> s1
| exec_seq : forall s s1 s2 c d,
  l |~ s >- c ---> Some s1 -> l |~ s1 >- d ---> s2 ->
  l |~ s >- c .; d ---> s2
| exec_ifte_true : forall s s1 b c d, [ b ]b_ s ->
  l |~ s >- c ---> s1 -> l |~ s >- If b Then c Else d ---> s1
| exec_ifte_false : forall s s1 b c d, ~ [ b ]b_ s ->
  l |~ s >- d ---> s1 -> l |~ s >- If b Then c Else d ---> s1
| exec_while_true : forall s s1 s2 b c,
  [ b ]b_ s -> l |~ s >- c ---> Some s1 ->
  l |~ s1 >- while b c ---> s2 -> l |~ s >- while b c ---> s2
| exec_while_false : forall s b c,
  ~ [ b ]b_ s -> l |~ s >- while b c ---> Some s
| exec_call : forall s s1 p c, Procs.MapsTo p c l ->
  l |~ s >- c ---> s1 -> l |~ s >- call p ---> s1
| exec_call_err : forall s p,
  Procs.find p l = None ->
  l |~ s >- call p ---> None
where "l |~ s >- c ---> t" := (exec l s c t).

Reserved Notation "l '|~' s '>-' c '-^' n '->' t" (at level 70, s, c, n, t at next level, no associativity).

Inductive iexec (l : procs) : nat -> state -> cmd -> option state -> Prop :=
| iexec_cmd0 : forall n s c s1, Cmd0.exec0 s c s1 -> l |~ s >- basic c -^ n -> s1
| iexec_seq : forall n s s1 s2 c d,
  l |~ s >- c -^ n -> Some s1 -> l |~ s1 >- d -^ n -> s2 -> l |~ s >- c .; d -^ n -> s2
| iexec_ifte_true : forall n s s1 b c d, [ b ]b_ s ->
  l |~ s >- c -^ n -> s1 ->
  l |~ s >- If b Then c Else d -^ n -> s1
| iexec_ifte_false : forall n s s1 b c d, ~ [ b ]b_ s ->
  l |~ s >- d -^ n -> s1 ->
  l |~ s >- If b Then c Else d -^ n -> s1
| iexec_while_true : forall n s s1 s2 b c, [ b ]b_ s ->
  l |~ s >- c -^ n -> Some s1 ->
  l |~ s1 >- while b c -^ n -> s2 -> l |~ s >- while b c -^ n -> s2
| iexec_while_false : forall n s t c,
  ~ [ t ]b_ s -> l |~ s >- while t c -^ n -> Some s
| iexec_call : forall n s s1 p c,
    Procs.MapsTo p c l ->
    l |~ s >- c -^ n -> s1 ->
    l |~ s >- call p -^ S n -> s1
| iexec_call_err : forall n s p,
    Procs.find p l = None ->
    l |~ s >- call p -^ S n -> None
where "l '|~' s >- c '-^' n '->' t" := (iexec l n s c t).

Lemma iexec_S n l s prg s1 : l |~ s >- prg -^ n -> s1 ->
  forall m, n <= m -> l |~ s >- prg -^ m -> s1.
Proof.
induction 1; intros m nm.
Admitted.

Lemma iexec_exec n l s c t : l |~ s >- c -^ n -> t -> l |~ s >- c ---> t.
Proof.
induction 1.
Admitted.

Lemma iexec_incr l n s s1 c :
  l |~ s >- c -^ n -> s1 ->
  forall m, n <= m ->
  l |~ s >- c -^ m -> s1.
Proof.
induction 1; intros m nm.
Admitted.

Lemma iexec_seq_exists l n1 s s1 c :
  l |~ s >- c -^ n1 -> Some s1 ->
  forall n2 d s2,
  l |~ s1 >- d -^ n2 -> s2 ->
  exists n, l |~ s >- c .; d -^ n -> s2.
Proof.
intros Hc n2 d s2 Hd.
exists (max n1 n2).
Admitted.

Lemma exec_iexec l s c t : l |~ s >- c ---> t -> exists n, l |~ s >- c -^ n -> t.
Proof.
induction 1.
Admitted.

Record spec := Spec {
  pre : assert ;
  callee : proc ;
  post : assert}.

Reserved Notation "l \^ E |~{[ P ]} c {[ Q ]}"
  (at level 70, E, P, c, Q at next level, no associativity, format "l  \^  E  |~{[  P  ]}  c  {[  Q  ]}").

Inductive hoare (l  : procs) : Ensemble spec -> assert -> cmd -> assert -> Prop :=
| hoare_basic : forall E P Q c, Cmd0.hoare0 P c Q ->
  l \^ E |~{[ P ]} basic c {[ Q ]}
| hoare_seq : forall E P Q R c d,
  l \^ E |~{[ P ]} c {[ Q ]} -> l \^ E |~{[ Q ]} d {[ R ]} ->
  l \^ E |~{[ P ]} c .; d {[ R ]}
| hoare_conseq : forall E c (P Q : assert),
  (forall s, P s -> exists P' Q',
    l \^ E |~{[ P' ]} c {[ Q' ]} /\ P' s /\ (Q' ===> Q)) ->
  l \^ E |~{[ P ]} c {[ Q ]}
| hoare_while : forall E P b c,
  l \^ E |~{[ fun s => P s /\ [ b ]b_ s ]} c {[ P ]} ->
  l \^ E |~{[ P ]} while b c {[ fun s => P s /\ ~ [ b ]b_ s ]}
| hoare_ifte : forall E P Q b c d,
  l \^ E |~{[ fun s => P s /\ [ b ]b_ s ]} c {[ Q ]} ->
  l \^ E |~{[ fun s => P s /\ ~ [ b ]b_ s ]} d {[ Q ]} ->
  l \^ E |~{[ P ]} If b Then c Else d {[ Q ]}
| hoare_call : forall E P Q p E',
  In E' (Spec P p Q) ->
  (forall t, In E' t -> exists c, Procs.MapsTo (callee t) c l /\
     l \^ Union E E' |~{[ pre t ]} c {[ post t ]}) ->
  l \^ E |~{[ P ]} call p {[ Q ]}
| hoare_call2 : forall E P Q p, In E (Spec P p Q) ->
  l \^ E |~{[ P ]} call p {[ Q ]}
where "l \^ E |~{[ P ]} c {[ Q ]}" := (hoare l E P c Q).

(* usual consequence lemmas *)

Lemma hoare_conseq_spec l E P P' Q Q' c : P ===> P' -> Q' ===> Q ->
  l \^ E |~{[ P' ]} c {[ Q' ]} -> l \^ E |~{[ P ]} c {[ Q ]}.
Proof.
Admitted.

Lemma hoare_stren l E P P' Q c : P ===> P' ->
  l \^ E |~{[ P' ]} c {[ Q ]} -> l \^ E |~{[ P ]} c {[ Q ]}.
Proof.
Admitted.

Lemma hoare_weak l E P Q Q' c : Q' ===> Q ->
  l \^ E |~{[ P ]} c {[ Q' ]} -> l \^ E |~{[ P ]} c {[ Q ]}.
Proof.
Admitted.

Lemma hoare_ind2 : forall l (G : Ensemble spec -> assert -> cmd -> assert -> Prop),
 (forall E P Q c, Cmd0.hoare0 P c Q -> G E P (basic c) Q) ->
 (forall E P Q R c d, l \^ E |~{[ P ]} c {[ Q ]} ->
   G E P c Q -> l \^ E |~{[ Q ]} d {[ R ]} -> G E Q d R -> G E P (c.; d) R) ->
 (forall E c (P Q : assert) ,
   (forall s, P s ->
   exists P' Q', G E P' c Q' /\ (*l \^ E |~{[ P']} c {[Q']} /\*) P' s /\ (Q' ===> Q)) ->
 G E P c Q) ->
 (forall E P b c,
   l \^ E |~{[ fun s => P s /\ [ b ]b_ s ]} c {[ P ]} ->
   G E (fun s => P s /\ [ b ]b_ s) c P ->
   G E P (while b c) (fun s => P s /\ ~ [ b ]b_ s)) ->
 (forall E (P : state -> _) Q b c d,
  l \^ E |~{[ fun s => P s /\ [ b ]b_ s ]} c {[Q]} ->
  G E (fun s => P s /\ [ b ]b_ s) c Q ->
  l \^ E |~{[ fun s => P s /\ ~ [ b ]b_ s ]} d {[Q]} ->
  G E (fun s => P s /\ ~ [ b ]b_ s) d Q ->
  G E P (If b Then c Else d) Q) ->
  (forall E P Q p E',
    In E' (Spec P p Q) ->
    (forall t0,
     In E' t0 -> exists c,
       Procs.MapsTo (callee t0) c l /\ (* l \^ Union E E' |~{[ C.fpre t0]} pro {[C.fpost t0]}*)
       G (Union E E') (pre t0) c (post t0)) ->
   G E P (call p) Q) ->
  (forall E P Q p,
   In E (Spec P p Q) -> G E P (call p) Q) ->
  forall E P c Q, l \^ E |~{[ P ]} c {[ Q ]} -> G E P c Q.
Proof.
(* induction w.r.t. l \^ E |~{[ P ]} c {[ Q ]} *)
fix 14.
intros.
destruct H6.
- now apply H.
- apply H0 with Q; try auto.
  apply hoare_ind2 with l; try auto.
  apply hoare_ind2 with l; try auto.
- apply H1; try auto.
  intros s P0s.
  destruct (H6 _ P0s) as [P' [Q' K]].
  exists P', Q'.
  split.
  apply hoare_ind2 with l; try auto.
  tauto.
  tauto.
- apply H2; try auto.
  apply hoare_ind2 with l; try auto.
- apply H3; try auto.
  apply hoare_ind2 with l; try auto.
  apply hoare_ind2 with l; try auto.
- apply H4 with E'; try auto.
  intros t0 Ht0.
  destruct (H7 _ Ht0) as [pro [Hpro1 Hpro2]].
  exists pro.
  split; [now auto | ].
  now apply hoare_ind2 with l; try auto.
- now apply H5.
Qed.

Definition hoare_sem l P c (Q : assert) : Prop :=
  forall s, P s -> ~ l |~ s >- c ---> None /\
    (forall s1, l |~ s >- c ---> Some s1 -> Q s1).

Local Notation "l |={{ P }} c {{ Q }}" := (hoare_sem l P c Q)
  (at level 70, P, c, Q at next level, format "l  |={{  P  }}  c  {{  Q  }}").

Definition hoare_sem_ctxt l E P c Q :=
  (forall t, In E t -> l |={{ pre t }} call (callee t) {{ post t }}) ->
  l |={{ P }} c {{ Q }}.

Local Notation "l \^ E |={{ P }} c {{ Q }}" := (hoare_sem_ctxt l E P c Q)
  (at level 70, E, P, c, Q at next level, format "l  \^  E  |={{  P  }}  c  {{  Q  }}").

Definition hoare_sem_n l n P c (Q : assert) : Prop :=
  forall s, P s -> ~ l |~ s >- c -^ n -> None /\
    (forall s1, l |~ s >- c -^ n -> Some s1 -> Q s1).

Local Notation "l |= n {{ P }} c {{ Q }}" := (hoare_sem_n l n P c Q)
  (at level 70, n, P, c, Q at next level, format "l  |=  n  {{  P  }}  c  {{  Q  }}").

Lemma hoare_sem_Sn n P l prg Q : l |= S n {{ P }} prg {{ Q }} ->
  l |= n {{ P }} prg {{ Q }}.
Proof.
(* use iexec_S *)
Admitted.

Lemma hoare_sem_n_sem l P c Q :
  l |={{ P }} c {{ Q }} <-> forall n, l |= n {{ P }} c {{ Q }}.
Proof.
(* use iexec_exec and exec_iexec *)
Admitted.

Definition hoare_sem_ctxt_n l E n P c Q :=
  (forall t, In E t -> l |= n {{ pre t }} call (callee t) {{ post t }}) ->
  l |= n {{ P }} c {{ Q }}.

Local Notation "l \^ E |= n {{ P }} c {{ Q }}" := (hoare_sem_ctxt_n l E n P c Q)
  (at level 70, E, n, P, c, Q at next level, format "l  \^  E  |=  n  {{  P  }}  c  {{  Q  }}").

Lemma hoare_sem_ctxt_n_sem_ctxt l E P c Q :
  (forall n, l \^ E |= n {{ P }} c {{ Q }}) ->
  l \^ E |={{ P }} c {{ Q }}.
Proof.
(* use hoare_sem_n_sem *)
Admitted.

Lemma hoare_sound_n E P Q l c :
  (forall P Q l c, Cmd0.hoare0 P c Q -> forall n, l |= n {{ P }} basic c {{ Q }}) ->
  l \^ E |~{[ P ]} c {[ Q ]} -> forall n, l \^ E |= n {{ P }} c {{ Q }}.
Proof.
intro Hcmd0.
induction 1 using hoare_ind2.
- admit.
- admit.
- admit.
- (* case while *) intros n Hn s Ps; split.
  + assert (Htmp : exists d, d = while b c) by (eexists; reflexivity).
    destruct Htmp as [d Hd].
    rewrite <- Hd.
    assert (Htmp : exists S, S = @None state) by (eexists; reflexivity).
    destruct Htmp as [S HS].
    rewrite <- HS.
    intros execd.
    revert Hd HS.
    induction execd; try discriminate.
    admit.
  + intros s1.
    assert (Htmp : exists C, C = while b c) by (eexists; reflexivity).
    destruct Htmp as [C HC].
    rewrite <- HC.
    assert (Htmp : exists S1, S1 = Some s1) by (eexists; reflexivity).
    destruct Htmp as [S1 HS1].
    rewrite <- HS1.
    intros execC.
    revert s1 HC HS1.
    induction execC; try discriminate.
    * admit.
    * admit.
- admit.
- (* case call *) intro n.
  unfold hoare_sem_ctxt_n.
  (* generalization *)
  cut ((forall t,
    In E t -> l |= n {{ pre t }} call (callee t) {{ post t }}) ->
    forall P' Q' p,
    In E' (Spec P' p Q') -> l |= n {{ P' }} call p {{ Q' }}).
    intros GenGoal H_.
    now apply GenGoal.
  induction n.
  + (* n = 0 *) admit.
  + (* n > 0 *) intros nisSn P' Q' p' p'_E'.
    assert (nisn : forall t, In E t ->
      l |= n {{ pre t }} call (callee t) {{ post t }}).
      intros t' t'_E.
      apply hoare_sem_Sn.
      now apply nisSn.
    clear nisSn.
    assert (IHn_ : forall t, In E' t ->
       exists c, Procs.MapsTo (callee t) c l /\
        l |= n {{ pre t }} c {{ post t }}).
      intros t' t'_E'.
      destruct (H0 _ t'_E') as [c [H01 H02]].
      exists c.
      split; [now auto|].
      apply H02.
      intros t''.
      inversion_clear 1.
        now apply nisn.
      apply (IHn nisn).
      now destruct t''.
    clear nisn IHn.
    destruct (IHn_ _ p'_E') as [c [c_l Hc]].
    clear IHn_.
    intros s1 P1.
    red in Hc.
    apply Hc in P1.
    destruct P1 as [P1' P1''].
    split.
    * contradict P1'.
      inversion_clear P1'.
        generalize (ProcsFacts.MapsTo_fun H1 c_l); intro c0_c.
        now rewrite <- c0_c.
      apply Procs.find_1 in c_l.
      simpl in c_l.
      now rewrite c_l in H1.
    * intros s.
      inversion_clear 1.
      generalize (ProcsFacts.MapsTo_fun H2 c_l); intros ?; subst c.
      now apply P1'' in H3.
- admit.
Admitted.

Lemma hoare_sound E P Q l c :
  (forall P Q l c, Cmd0.hoare0 P c Q -> l |={{ P }} basic c {{ Q }}) ->
  l \^ E |~{[ P ]} c {[ Q ]} -> l \^ E |={{ P }} c {{ Q }}.
Proof.
(* use hoare_sound_n and hoare_sem_n_sem *)
Admitted.

End Cmd.

(* expression language *)

Module Vars := FMapList.Make (String_as_OT).

Module VarsFacts := FMapFacts.Facts Vars.

Definition var := Vars.key.

Inductive exp :=
| exp_var : var -> exp
| add : exp -> exp -> exp
| mul : exp -> exp -> exp
| sub : exp -> exp -> exp
| cst : nat -> exp.

Coercion cst : nat >-> exp.

Notation "% v" := (exp_var v) (at level 4).
Notation "a \- b" := (sub a b) (at level 65).
Notation "a \+ b" := (add a b) (at level 65).
Notation "a \* b" := (mul a b) (at level 58).

Inductive bexp :=
| equa : exp -> exp -> bexp
| neg : bexp -> bexp.

Notation "a \= b" := (equa a b) (at level 64).
Notation "a \!= b" := (neg (equa a b)) (at level 64).

Module state <: STATE.

Definition state := Vars.t nat.
Definition assert := state -> Prop.
Definition entails (P Q : assert) : Prop := forall s, P s -> Q s.
Definition exp := exp.
Definition bexp := bexp.
Fixpoint eval e s :=
  match e with
  | % v => match Vars.find v s with Some x => x | _ => 0 end
  | e1 \+ e2 => eval e1 s + eval e2 s
  | e1 \* e2 => eval e1 s * eval e2 s
  | e1 \- e2 => eval e1 s - eval e2 s
  | cst c => c
  end.

Fixpoint beval b s :=
  match b with
    | e1 \= e2 => eval e1 s = eval e2 s
    | neg b => ~ beval b s
  end.

Definition upd v (n : nat) s := Vars.add v n s.

Local Notation "'[' e ']_' s" := (state.eval e s) (at level 9, format "'[' [  e  ]_ s ']'", no associativity).

Lemma eval_upd_same str v s : [ % str ]_(state.upd str v s) = v.
Proof.
unfold state.eval at 1.
rewrite VarsFacts.add_eq_o; now auto.
Qed.

Lemma eval_upd_diff str str' v s : str <> str' -> [ % str ]_(state.upd str' v s) = [ % str ]_s.
Proof.
intros H.
unfold state.eval at 1.
rewrite VarsFacts.add_neq_o; now auto.
Qed.

End state.

Notation "P ===> Q" := (state.entails P Q) (at level 89, no associativity) : hoare_scope.

Arguments state.eval e s : simpl never.

Notation "'[' e ']_' s" := (state.eval e s) (at level 9, format "'[' [  e  ]_ s ']'", no associativity).

Notation "'[' e ']b_' s" := (state.beval e s) (at level 9, format "'[' [  e  ]b_ s ']'", no associativity) : hoare_scope.

Module cmd0 <: CMD0 state.

Inductive cmd0' :=
| assign : var -> state.exp -> cmd0'.
Definition cmd0 := cmd0'.

Local Notation "x <- e" := (cmd0.assign x e) (at level 80).

Inductive exec0' : state.state -> cmd0 -> option state.state -> Prop :=
| exec0_assign : forall s v e, exec0' s (v <- e) (Some (state.upd v ([ e ]_s) s)).
Definition exec0 := exec0'.

Inductive wp_assign v e P : state.assert :=
| wp_assign_c : forall s, P (state.upd v ([ e ]_s) s) -> wp_assign v e P s.

Inductive hoare0' : state.assert -> cmd0 -> state.assert -> Prop :=
| hoare0_assign : forall (Q : state.assert) v e, hoare0' (wp_assign v e Q) (v <- e) Q.
Definition hoare0 := hoare0'.

End cmd0.

Notation "x <- e" := (cmd0.assign x e) (at level 80) : hoare_scope.

Module C := Cmd state cmd0.

Coercion cmd0_cmd (c : cmd0.cmd0') : C.cmd := C.basic c.

Notation "c .; d" := (C.seq c d) (at level 81, right associativity, format "'[v' c '.;' '//' d ']'") : hoare_scope.

Notation "'If' e 'Then' c1 'Else' c2" := (C.ifte e c1 c2)
  (at level 200, right associativity, format
"'[v' '[' 'If'  e  'Then' ']' '//'   '[' c1 ']' '//' '[' 'Else' ']' '//'   '[' c2 ']' '//' ']'") : hoare_scope.

Notation "l '|~' s '>-' c '-^' n '->' t" := (C.iexec l n s c t)
  (at level 70, s, c, n, t at next level, no associativity) : hoare_scope.

Notation "l |={{ P }} c {{ Q }}" := (C.hoare_sem l P c Q)
  (at level 70, P, c, Q at next level, format "l  |={{  P  }}  c  {{  Q  }}") : hoare_scope.

Local Open Scope hoare_scope.

Lemma sound0 P Q l c : cmd0.hoare0 P c Q -> l |={{ P }} C.basic c {{ Q }}.
Proof.
Admitted.

Notation "l \^ E |= n {{ P }} c {{ Q }}" := (C.hoare_sem_ctxt_n l E n P c Q)
  (at level 70, E, n, P, c, Q at next level, format "l  \^  E  |=  n  {{  P  }}  c  {{  Q  }}") : hoare_scope.

Notation "l \^ E |~{[ P ]} c {[ Q ]}" := (C.hoare l E P c Q)
  (at level 70, E, P, c, Q at next level, no associativity,
  format "l  \^  E  |~{[  P  ]}  c  {[  Q  ]}") : hoare_scope.

Notation "l |={{ P }} c {{ Q }}" := (C.hoare_sem l P c Q) (at level 70, P, c, Q at next level,
  format "l  |={{  P  }}  c  {{  Q  }}") : hoare_scope.

Notation "l \^ E |={{ P }} c {{ Q }}" := (C.hoare_sem_ctxt l E P c Q)
  (at level 70, E, P, c, Q at next level, format "l \^ E |={{  P  }}  c  {{  Q  }}").

Notation "l |~ s >- c ---> t" := (C.exec l s c t) (at level 70, s, c, t at next level, no associativity).

(** Example *)

Require Import Factorial.

Lemma fact_fact n : 1 <= n -> fact (n - 1) * n = fact n.
Proof.
destruct n; [omega | intros _].
simpl.
rewrite NPeano.Nat.sub_0_r, NPeano.Nat.mul_succ_r, NPeano.Nat.mul_comm.
omega.
Qed.

Module FactorialWhile.

Definition facto :=
  (C.while (% "x" \!= 0)
    ("ret" <- % "ret" \* % "x" .;
     "x" <- % "x" \- 1))%string.

Lemma facto_fact X :
  (Procs.empty _ \^
  @Empty_set _
  |~{[ fun s => [% "x" ]_s = X /\ [% "ret" ]_s = 1 ]}
  facto
  {[ fun s => [ % "ret" ]_ s = fact X ]})%string.
Proof.
apply C.hoare_stren with (fun s =>
  [ % "ret" ]_ s * fact ([ % "x" ]_ s) = fact X)%string.
  admit.
apply C.hoare_weak with (fun s =>
  ([ % "ret" ]_ s * fact ([ % "x" ]_ s) = fact X ) /\
  ~ [ % "x" \!= 0 ]b_ s)%string.
  admit.
apply C.hoare_while.
apply C.hoare_seq with (fun s =>
  [ % "ret" ]_ s * fact ([ % "x" ]_ s - 1) = fact X /\ 0 <= [ % "x" ]_ s - 1)%string.
  apply C.hoare_stren with (cmd0.wp_assign "ret"%string (% "ret"%string \* % "x"%string) (fun s =>
                                                [ % "ret"%string ]_s *
                                                fact ([ % "x"%string ]_s - 1) =
                                                fact X /\
                                                0 <= [ % "x"%string ]_s - 1)).
    admit.
  apply C.hoare_basic.
  now apply cmd0.hoare0_assign.
apply C.hoare_stren with (cmd0.wp_assign "x"%string  (% "x"%string \- 1) (fun s =>
   [ % "ret"%string ]_s * fact [ % "x"%string ]_s = fact X)).
  admit.
apply C.hoare_basic.
now apply cmd0.hoare0_assign.
Admitted.

End FactorialWhile.

Module FactorialRec.

Definition facto : C.cmd :=
  (If (% "x" \= 0) Then
    "ret" <- 1
  Else
   "x" <- % "x" \- 1 .;
   C.call "facto" .;
   "x" <- % "x" \+ 1 .;
   "ret" <- % "ret" \* % "x")%string.

Definition factospec x := (C.Spec
  (fun s => [ %"x" ]_s = x)
  "facto"
  (fun s => [ %"x" ]_s = x /\ [ % "ret" ]_ s = fact x))%string.

Lemma facto_fact X : (Procs.add "facto" facto (Procs.empty _) \^
                      @Empty_set _
                      |~{[ fun s => [% "x" ]_s = X ]}
                      C.call "facto"
                      {[ fun s => [% "x" ]_s = X /\ [ % "ret" ]_ s = fact X ]})%string.
Proof.
(* call facto *)
apply C.hoare_call with (E' := BIGCUP X factospec).
  admit.
intros t InSpecs.
destruct (In_BIGCUP_inv _ _ _ InSpecs) as [n [nX tn]].
exists facto.
rewrite tn.
clear InSpecs tn.
split.
  now apply Procs.add_1.
unfold facto at 2.
(* if x = 0 then ... else ... *)
apply C.hoare_ifte.
  apply C.hoare_stren with (cmd0.wp_assign "ret"%string 1 (C.post (factospec n))).
    admit.
  admit.
simpl.
(* x <- x - 1; call; ... *)
apply C.hoare_seq with (fun s => [% "x"%string ]_s = n - 1 /\ 1 <= n).
  apply C.hoare_stren with (cmd0.wp_assign "x" (% "x" \- 1) (fun s => [ % "x" ]_s = n - 1 /\ 1 <= n))%string.
    admit.
  admit.
(* call; x <- x + 1; ... *)
apply C.hoare_seq with (fun s => [% "x" ]_s = n - 1 /\ [ % "ret" ]_ s = fact (n - 1) /\ 1 <= n)%string.
  apply C.hoare_conseq.
  admit.
(* x <- x + 1; ret <- ret * x *)
apply C.hoare_seq with (fun s => [% "x" ]_s = n /\ [ % "ret" ]_s = fact (n - 1) /\ 1 <= n)%string.
  apply C.hoare_stren with (cmd0.wp_assign "x" (% "x" \+ 1)
                         (fun s => [ % "x" ]_s = n /\ [ % "ret" ]_s = fact (n - 1) /\ 1 <= n))%string.
    admit.
  admit.
(* ret <- ret * x *)
apply C.hoare_stren with (cmd0.wp_assign "ret" (% "ret" \* % "x")
  (fun s => [ % "x" ]_s = n /\ [ % "ret" ]_s = fact n))%string.
  admit.
admit.
Admitted.

End FactorialRec.
