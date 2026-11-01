
From Stdlib.Lists Require Import List.
From MetaRocq.Erasure Require EAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Universes.
From MetaRocq.Erasure Require Import EPrimitive.
From MetaRocq.Common Require Import Primitive.
From Equations Require Import Equations.

(* The term AST represent embed the entire lambdabox, along with new
   constructors dealing with the allocation, mutation and extraction of data from
   memory cases. As of now we only support primitive array operations. We
   automatically detect lambdabox terms that have patterns of usage that can be
   converted to mutable arrays without changing the external behaviour.

   This procedure makes a few assumptions:
   - Mutable arrays and immutable ones are supposed to be different types
     (despite being the same on the lambdabox side). This is to enable backend to
     compile them to different datastructures (from example to use differential
     arrays for immutable ones).
   - Whenever an array is passed to a function, or returned from one, we assume
     it is an immutable one. This means the interface in unchanged compared to a
     compilation without the mutable arrays.
   - We make some assumption on the order of evaluation: we assume function
     term and arguments are fully evaluated left to right before calling the
     function, and that in a match the term matched is fully evaluated before any of
     the branches.
   - We force variables captured in lambdas or lazy blocks to be immutable
     arrays, because we cannot control when/where it is going to be evaluated.

   It proceeds in four steps:
   - `import_term` convert a lambdabox term to a local term without making any
     transformation.
   - `parray_ops` inspects the term for anything that looks like primitive
     array operations, and convert them into the allocate, read and mutate
     constructors. The resulting term is invalid, since it always use mutable
     operations, even when it would lead to a behaviour that is not consistent with
     the initial term.
   - `find_linear` enumerates every let binding, match nodes and allocation
     nodes, and creates a union-find structure on them linking together nodes that
     should have the same mutability status. It does so by pushing down information
     about the expected mutability of the term, briging up information on if it can
     be realised, and checking the linearity of the usage of variables. The
     resulting union-find structure connect any enumerated node that must not be
     linear to the 0 node.
   - `extract_impl` uses the previous union-find structure to transfrom the
     term into a valid one, by transforming mutable operations into immutable ones
     when they happen in places that must produce immutable values.

   Finally, the `optimize_arrays` connects all those operation to transfrom a
   lambdabox term into a valid term with primitive array manipulation converted
   into mutable operations where it is correct to do so. *)

Declare Scope erasure.
Local Open Scope erasure.

(* Semantics: tAllocate create mutable values. These values can only
   be mutated through tMemoryUpdate operations, and information read from them
   only through tMemoryRead. *)

Inductive allocate {T : Set} : Set :=
| aArrayNew (s b : T) (* Array of size s with cases filled with b *)
.

Inductive read_memory {T : Set} : Set :=
| rArrayGet (a i : T) (* Get idx-th element from array *)
| rArrayLength (a : T) (* Array length *)
.

Inductive update_memory {T : Set} : Set :=
| uArraySet (a i x : T) (* a[i] := x *)
.

Inductive term : Set :=
| tBox (* Represents all proofs *)
| tRel (n : nat)
| tVar (i : ident) (* For free variables (e.g. in a goal) *)
| tEvar (n : nat) (l : list term)
| tLambda (na : name) (t : term)
| tLetIn (na : name) (b t : term) (* let na := b : B in t *)
| tApp (u v : term)
| tConst (k : kername)
| tConstruct (ind : inductive) (n : nat) (args : list term)
| tCase (indn : inductive * nat (* # of parameters *)) (c : term  (* discriminee *)) (brs : list (list name * term) (* branches *))
| tProj (p : projection) (c : term)
| tFix (mfix : EAst.mfixpoint term) (idx : nat)
| tCoFix (mfix : EAst.mfixpoint term) (idx : nat)
| tPrim (prim : prim_val term)
| tLazy (t : term)
| tForce (t : term)
| tAllocate (a : @allocate term) (* Create new mutable memory space *)
| tMemoryRead (r : @read_memory term)
| tMemoryUpdate (u : @update_memory term) (* Memory update return the memory position that has been updated *)
.

(* A value is either a functional value, or a memory case *)

Definition map_def' {term term': Set} (f : term -> term') (d : EAst.def term) :=
  {| EAst.dname := d.(EAst.dname); EAst.dbody := f d.(EAst.dbody); EAst.rarg := d.(EAst.rarg) |}.

(* Trivially import an EAst.term to a term, without any transformation *)
Fixpoint import_term (t : EAst.term) : term := match t with
| EAst.tBox => tBox
| EAst.tRel n => tRel n
| EAst.tVar i => tVar i
| EAst.tEvar n l => tEvar n (map import_term l)
| EAst.tLambda na t => tLambda na (import_term t)
| EAst.tLetIn na b t => tLetIn na (import_term b) (import_term t)
| EAst.tApp u v => tApp (import_term u) (import_term v)
| EAst.tConst k => tConst k
| EAst.tConstruct ind n args => tConstruct ind n (map import_term args)
| EAst.tCase indn c brs =>
    tCase indn (import_term c) (map (fun br => (fst br, import_term (snd br))) brs)
| EAst.tProj p c => tProj p (import_term c)
| EAst.tFix mfix idx => tFix (map (map_def' import_term) mfix) idx
| EAst.tCoFix mfix idx => tCoFix (map (map_def' import_term) mfix) idx
| EAst.tPrim prim =>
    let import_prim prim := match prim.π2 return prim_val term with
    | primIntModel f => (primInt; primIntModel f)
    | primFloatModel f => (primFloat; primFloatModel f)
    | primStringModel f => (primString; primStringModel f)
    | primArrayModel a =>
        (primArray;
         primArrayModel {| array_default := import_term (array_default a);
                           array_value := map import_term (array_value a) |})
    end in tPrim (import_prim prim)
| EAst.tLazy t => tLazy (import_term t)
| EAst.tForce t => tForce (import_term t)
end.

From MetaRocq.Common Require Kernames.
From Stdlib Require Import Lists.List.

Fixpoint list_eqb {A : Type}
    (eqb : A -> A -> bool)
    (xs ys : list A) : bool :=
  match xs, ys with
  | nil, nil => true
  | x :: xs', y :: ys' => eqb x y && list_eqb eqb xs' ys'
  | _, _ => false
  end.

Definition is_parray_op (op : ident) (t : term) : bool := match t with
| tConst (Kernames.MPfile fl, i) =>
    list_eqb String.eqb fl ["PrimArray"; "Array"; "Corelib"] && String.eqb i op
| _ => false
end.

(* Transform any primitive array operation into term constructors, even if their
   usage would be invalid. After applying this function, you should find_linear
   and correct_term to revert this transformation on the wrong terms *)
Fixpoint parray_ops (t : term) : term := match t with
(* Interesting case *)
| tApp u v => match u with
  | tApp u' v' => match u' with
    | tApp u'' v'' =>
        if is_parray_op "set" u''
        then tMemoryUpdate (uArraySet (parray_ops v'') (parray_ops v') (parray_ops v))
        else tApp (parray_ops u) (parray_ops v)
    | _ =>
        if is_parray_op "make" u'
        then tAllocate (aArrayNew (parray_ops v') (parray_ops v))
        else if is_parray_op "get" u'
        then tMemoryRead (rArrayGet (parray_ops v') (parray_ops v))
        else tApp (parray_ops u) (parray_ops v)
    end
  | _ =>
    if is_parray_op "length" u
    then tMemoryRead (rArrayLength (parray_ops v))
    else tApp (parray_ops u) (parray_ops v)
  end

(* Propagating trough pure constructors *)
| tBox => tBox
| tRel n => tRel n
| tVar i => tVar i
| tEvar n l => tEvar n (map parray_ops l)
| tLambda na t => tLambda na (parray_ops t)
| tLetIn na b t => tLetIn na (parray_ops b) (parray_ops t)
| tConst k => tConst k
| tConstruct ind n args => tConstruct ind n (map parray_ops args)
| tCase indn c brs =>
    tCase indn (parray_ops c) (map (fun br => (fst br, parray_ops (snd br))) brs)
| tProj p c => tProj p (parray_ops c)
| tFix mfix idx => tFix (map (map_def' parray_ops) mfix) idx
| tCoFix mfix idx => tCoFix (map (map_def' parray_ops) mfix) idx
| tPrim prim =>
    let import_prim prim := match prim.π2 return prim_val term with
    | primIntModel f => (primInt; primIntModel f)
    | primFloatModel f => (primFloat; primFloatModel f)
    | primStringModel f => (primString; primStringModel f)
    | primArrayModel a =>
        (primArray;
         primArrayModel {| array_default := parray_ops (array_default a);
                           array_value := map parray_ops (array_value a) |})
    end in tPrim (import_prim prim)
| tLazy t => tLazy (parray_ops t)
| tForce t => tForce (parray_ops t)

(* Assume the operation has already been done on impure operations *)
| _ => t
end.

(* For each term constructor, we determine if each subterm appear in a position
   where a memory case can be used instead of a plain value. This property depends
   on whether the term itself is in a position where a memory case can be used. We
   push this information down, and we bring up how variables are used. Variables
   will be realised as memory location if:
     - they are only used in places where memory locations are expected
     - their usage is linear
     - they are defined as a term that produces a memory location
   *)

From Stdlib Require MSets.MSetAVL.
From Stdlib Require Import Structures.OrdersEx.

Module VarsSet := MSetAVL.Make(Nat_as_OT).
Definition vars_set := VarsSet.t.

Fixpoint unions_vars (ss : list vars_set) : vars_set := match ss with
  | [] => VarsSet.empty
  | s :: ss' => VarsSet.union s (unions_vars ss')
  end.

(* We always have read_only_variables <= linear_variables <= used_variables *)
Record variables_status :=
  { read_only_variables : vars_set; (* Variables that are only used in read position *)
    linear_variables : vars_set; (* Variables used in correct linear fashion *)
    used_variables : vars_set (* Any used variable *)
  }.

Definition is_read_only (vs : variables_status) (n : nat) : bool :=
  VarsSet.mem n (read_only_variables vs).
Definition is_linear (vs : variables_status) (n : nat) : bool :=
  VarsSet.mem n (linear_variables vs).
Definition is_used (vs : variables_status) (n : nat) : bool :=
  VarsSet.mem n (used_variables vs).

Definition mk_read_only (n : nat) : variables_status :=
  {| read_only_variables := VarsSet.singleton n;
     linear_variables := VarsSet.singleton n;
     used_variables := VarsSet.singleton n
  |}.
Definition mk_linear (n : nat) : variables_status :=
  {| read_only_variables := VarsSet.empty;
     linear_variables := VarsSet.singleton n;
     used_variables := VarsSet.singleton n
  |}.
Definition mk_used (n : nat) : variables_status :=
  {| read_only_variables := VarsSet.empty;
     linear_variables := VarsSet.empty;
     used_variables := VarsSet.singleton n
  |}.

Definition pop_binder_in_rel (n : nat) : vars_set -> vars_set :=
  match n with
  | O => id
  | S m => VarsSet.add m
  end.

Definition pop_binder_in_set (v : vars_set) : vars_set :=
  VarsSet.fold (fun x acc => pop_binder_in_rel x acc) v VarsSet.empty.

Definition pop_binder (tv : variables_status) : variables_status :=
  {| read_only_variables := pop_binder_in_set (read_only_variables tv);
     linear_variables := pop_binder_in_set (linear_variables tv);
     used_variables := pop_binder_in_set (used_variables tv)
  |}.

Fixpoint pop_binders (n:nat) (tv : variables_status) : variables_status :=
  match n with
  | O => tv
  | S n' => pop_binders n' (pop_binder tv)
  end.

Definition empty_status : variables_status :=
  {| read_only_variables := VarsSet.empty;
     linear_variables := VarsSet.empty;
     used_variables := VarsSet.empty
  |}.

Definition generic_compose
  (mkLinear : vars_set -> vars_set -> vars_set -> vars_set -> vars_set -> vars_set -> vars_set)
  (tv1 tv2 : variables_status) : variables_status :=
  {| read_only_variables := 
       unions_vars [
         VarsSet.inter (read_only_variables tv1) (read_only_variables tv2);
         VarsSet.diff (read_only_variables tv1) (used_variables tv2);
         VarsSet.diff (read_only_variables tv2) (used_variables tv1)
       ];
     linear_variables :=
       let lin := mkLinear (read_only_variables tv1)
                           (read_only_variables tv2)
                           (linear_variables tv1)
                           (linear_variables tv2)
                           (used_variables tv1)
                           (used_variables tv2) in
       VarsSet.union lin
         (VarsSet.union
           (VarsSet.diff (linear_variables tv1) (used_variables tv2))
           (VarsSet.diff (linear_variables tv2) (used_variables tv1)));
     used_variables := VarsSet.union (used_variables tv1) (used_variables tv2)
  |}.

(* Variable usage from the result of two actions executed one after another *)
Definition seq_compose : variables_status -> variables_status -> variables_status :=
  generic_compose (fun ro1 ro2 lin1 lin2 used1 used2 => VarsSet.inter ro1 lin2).

(* Variable usage from the result of two actions executed in undefined order *)
Definition undefined_compose : variables_status -> variables_status -> variables_status :=
  generic_compose (fun ro1 ro2 lin1 lin2 used1 used2 => VarsSet.inter ro1 ro2).

Fixpoint undefined_compose_many (tvs : list variables_status) : variables_status :=
  match tvs with
  | [] => empty_status
  | tv :: tvs' => undefined_compose tv (undefined_compose_many tvs')
  end.

(* Variable usage from the result of two actions, one of which is executed *)
Definition one_of_compose : variables_status -> variables_status -> variables_status :=
  generic_compose (fun ro1 ro2 lin1 lin2 used1 used2 => VarsSet.inter lin1 lin2).

Definition one_of_compose_many (tvs : list variables_status) : variables_status :=
  match tvs with
  | [] => empty_status
  | v :: vs => fold_left one_of_compose vs v
  end.

(* Helpers *)
Definition inspect {A : Type} (a : A) :
  {b : A | a = b} :=
  exist _ a eq_refl.
Notation "x 'eqn:' p" :=
  (exist _ x p)
  (only parsing, at level 20).

From Stdlib Require Import FSets.FMapAVL.
From Stdlib Require Import FSets.FMapFacts.
From Stdlib Require Structures.OrderedTypeEx.
(* Very basic and unoptimised union-find *)
Module UF.
  Module NM := FMapAVL.Make(OrderedTypeEx.Nat_as_OT).
  Module NMF := FMapFacts.WFacts_fun Nat_as_OT NM.
  Definition well_founded_map (mp : NM.t nat) : Prop :=
    forall (n : nat),
      match NM.find n mp with
      | None => True
      | Some m => m < n
      end.
  Definition t := { mp: NM.t nat & well_founded_map mp }.

  Equations? empty : t :=
  empty := existT _ (NM.empty nat) _.
  Proof. unfold well_founded_map. intro n. simpl. auto. Qed.

  Equations? lookup (uf : t) (n : nat) : nat by wf n lt :=
  lookup uf n with inspect (NM.find n (projT1 uf)) := {
    | Some m eqn:H => lookup uf m
    | None   eqn:H => n
  }.
  Proof.
    pose proof (Huf := projT2 uf n). simpl in Huf. unfold well_founded_map in Huf.
    unfold well_founded_map in H. rewrite H in Huf. exact Huf.
  Qed.

  Definition check (uf : t) (n1 n2 : nat) : bool := (lookup uf n1) =? (lookup uf n2).
  Equations? connect (uf : t) (n1 n2 : nat) : t :=
  connect uf n1 n2 with inspect (lookup uf n1 ?= lookup uf n2) := {
    | Lt eqn:H => existT _ (NM.add (lookup uf n2) (lookup uf n1) (projT1 uf)) _
    | Eq eqn:H => uf
    | Gt eqn:H => existT _ (NM.add (lookup uf n1) (lookup uf n2) (projT1 uf)) _
  }.
  Proof.
    - unfold well_founded_map. intro n.
      destruct (Nat.eq_dec n (lookup uf n2)) as [Heq | Hneq].
      + rewrite Heq. rewrite NMF.add_eq_o; try reflexivity.
        apply Nat.compare_lt_iff. assumption.
      + rewrite NMF.add_neq_o; try auto. exact (projT2 uf n).
    - unfold well_founded_map. intro n.
      destruct (Nat.eq_dec n (lookup uf n1)) as [Heq | Hneq].
      + rewrite Heq. rewrite NMF.add_eq_o; try reflexivity.
        apply Nat.compare_gt_iff. assumption.
      + rewrite NMF.add_neq_o; try auto. exact (projT2 uf n).
  Qed.
End UF.

Inductive mutability_status :=
  | mutable_read (mut_if : option nat)
  | mutable_write (mut_if : option nat)
  | immutable.

Fixpoint padvars (n : nat) (l : list nat) : list nat := match n with
| O => l
| S n' => padvars n' (0 :: l)
end.

Definition connect_if_some uf (n : option nat) (m : nat) := match n with
| None => uf
| Some n' => UF.connect uf n' m
end.

Equations find_linear
  (* The natural is used to enumerate all bound variables, case and allocation
     within the term, starting from 1. Two locations are connected in the union-find
     is they must have the same mutability. Locations are connected to 0 to show
     they must be immutable *)
  (iuf : nat * UF.t)
  (* Map De Bruijn indices to variable enumeration *)
  (vars : list nat)
  (* Indicate if we're within a mutable context, a immutable 
     one, or one that depends on a variable *)
  (mut : mutability_status)
  (* The term to inspect *)
  (t : term)
  (* The variables_status is the usage of the local variable in the sub term,
     especially if their usage is linear. The boolean indicates if the term can
     construct a mutable array. It also returns updates to the binder counting and
     the union-find. *)
  : (variables_status * bool) * (nat * UF.t)
  by struct t :=

(* The main case: propagate a variable status and mark it as immutable if its
   usage is not linear *)
find_linear (i, uf) vars mut (tLetIn na b t) :=
  let '((vsb, tmut), iuf') := find_linear (i+1, uf) vars (mutable_write (Some i)) b in
  let '((vst, bmut), iuf'') := find_linear iuf' (i :: vars) mut t in
  let (i'', uf'') := iuf'' in
  let uf''' := if tmut && is_linear vst 0 then uf'' else UF.connect uf'' i 0 in
  ((seq_compose vsb (pop_binder vst), bmut), (i'', uf'''));

find_linear (i, uf) vars mut (tRel n) :=
  let var := nth n vars 0 in
  match mut with
  | mutable_read mut_if => ((mk_read_only n, true), (i, connect_if_some uf mut_if var))
  | mutable_write mut_if => ((mk_linear n, true), (i, connect_if_some uf mut_if var))
  | immutable => ((mk_used n, false), (i, UF.connect uf var 0))
  end;

find_linear (i, uf) vars mut (tCase indn c brs) :=
  let (nmut,uf') := match mut with
  | mutable_read mut_if => (mutable_read (Some i), connect_if_some uf mut_if i)
  | mutable_write mut_if => (mutable_write (Some i), connect_if_some uf mut_if i)
  | immutable => (immutable, UF.connect uf 0 i)
  end in
  let '((vsc, _), iuf') := find_linear (i + 1, uf') vars immutable c in
  let accum := (fun (acc : ((nat * UF.t) * variables_status * bool)) br =>
    let '((iuf, vs), amut) := acc in
    let toshift := length (fst br) in
    let '((vst, rmut), iuf') := find_linear iuf (padvars toshift vars) nmut (snd br) in
    ((iuf', one_of_compose vs (pop_binders toshift vst)), amut && rmut)) in
  let '((iuf'', vsbrs), rmut) := fold_left accum brs ((iuf', empty_status), true) in
  let (i'', uf'') := iuf'' in
  let uf''' := if rmut then uf'' else UF.connect uf'' i 0 in
  ((seq_compose vsc vsbrs, rmut), (i'', uf'''));

(* Mutable cases *)
find_linear (i, uf) vars mut (tAllocate (aArrayNew s b)) :=
  let (rmut,uf') := match mut with
  | mutable_read mut_if => (true, connect_if_some uf mut_if i)
  | mutable_write mut_if => (true, connect_if_some uf mut_if i)
  | immutable => (false, UF.connect uf 0 i)
  end in
  let '((vss, _), iuf') := find_linear (i + 1, uf') vars immutable s in
  let '((vsb, _), iuf'') := find_linear iuf' vars immutable b in
  ((seq_compose vss vsb, rmut), iuf'');

find_linear iuf vars _ (tMemoryRead (rArrayGet a i)) :=
  let '((vsa, _), iuf') := find_linear iuf vars (mutable_read None) a in
  let '((vsi, _), iuf'') := find_linear iuf' vars immutable i in
  ((seq_compose vsa vsi, false), iuf'');

find_linear iuf vars _ (tMemoryRead (rArrayLength a)) :=
  let '((vsa, _), iuf') := find_linear iuf vars (mutable_read None) a in
  ((vsa, false), iuf');

find_linear iuf vars mut (tMemoryUpdate (uArraySet a i x)) :=
  let '((vsa, rmut), iuf') := find_linear iuf vars mut a in
  let '((vsi, _), iuf'') := find_linear iuf' vars immutable i in
  let '((vsx, _), iuf''') := find_linear iuf'' vars immutable x in
  ((seq_compose (seq_compose vsa vsi) vsx, rmut), iuf''');

(* Other cases *)
find_linear iuf vars _ (tEvar _ l) := 
  let l' := map (fun t => used_variables (fst (fst (find_linear iuf vars immutable t)))) l in
  ( ({| read_only_variables := VarsSet.empty;
        linear_variables := VarsSet.empty;
        used_variables := unions_vars l'
     |}, false), iuf);

find_linear iuf vars _ (tLambda na t) :=
  let (vs, iuf') := find_linear iuf (0 :: vars) immutable t in
  ((pop_binder (fst vs), false), iuf');

find_linear iuf vars _ (tApp u v) :=
  let '((vsu, _), iuf') := find_linear iuf vars immutable u in
let '((vsv, _), iuf'') := find_linear iuf' vars immutable v in (* Arguments to arbitrary functions are always immutable *)
  ((seq_compose vsu vsv, false), iuf'');

find_linear iuf vars _ (tConstruct ind n args) :=
  let accum := (fun (acc : ((nat * UF.t) * variables_status)) t =>
    let (iuf, vs) := acc in
    let '((vst, _), iuf') := find_linear iuf vars immutable t in
    (iuf', seq_compose vs vst)) in
  let (iuf', vs) := fold_left accum args (iuf, empty_status) in
  ((vs, false), iuf');

find_linear iuf vars _ (tProj p c) :=
  let '((vsc, _), iuf') := find_linear iuf vars immutable c in
  ((vsc, false), iuf');

find_linear iuf vars _ (tLazy t) :=
  let '((vs, _), iuf') := find_linear iuf vars immutable t in
  (({| read_only_variables := VarsSet.empty;
       linear_variables := VarsSet.empty;
       used_variables := used_variables vs
    |}, false), iuf');
find_linear iuf vars _ (tForce t) :=
  let '((vs, _), iuf') := find_linear iuf vars immutable t in
  (({| read_only_variables := VarsSet.empty;
       linear_variables := VarsSet.empty;
       used_variables := used_variables vs
    |}, false), iuf');

find_linear iuf vars _ (tFix mfix idx) :=
  let accum := (fun (acc : ((nat * UF.t) * variables_status)) d =>
    let (iuf, vs) := acc in
    let '((vst, _), iuf') := find_linear iuf vars immutable (EAst.dbody d) in
    (iuf', undefined_compose vs vst)) in
  let (iuf', vs) := fold_left accum mfix (iuf, empty_status) in
  (({| read_only_variables := VarsSet.empty;
       linear_variables := VarsSet.empty;
       used_variables := used_variables vs
    |}, false), iuf');
find_linear iuf vars _ (tCoFix mfix idx) :=
  let accum := (fun (acc : ((nat * UF.t) * variables_status)) d =>
    let (iuf, vs) := acc in
    let '((vst, _), iuf') := find_linear iuf vars immutable (EAst.dbody d) in
    (iuf', undefined_compose vs vst)) in
  let (iuf', vs) := fold_left accum mfix (iuf, empty_status) in
  (({| read_only_variables := VarsSet.empty;
       linear_variables := VarsSet.empty;
       used_variables := used_variables vs
    |}, false), iuf');

find_linear iuf vars _ (tPrim prim) :=
  match prim.π2 with
  | primIntModel f => ((empty_status, false), iuf)
  | primFloatModel f => ((empty_status, false), iuf)
  | primStringModel f => ((empty_status, false), iuf)
  | primArrayModel a =>
      let '((vsd,_), iuf') := find_linear iuf vars immutable (array_default a) in
      let accum := (fun (acc : ((nat * UF.t) * variables_status)) t =>
        let (iuf, vs) := acc in
        let '((vst, _), iuf') := find_linear iuf vars immutable t in
        (iuf', undefined_compose vs vst)) in
      let (iuf'', vs) := fold_left accum (array_value a) (iuf', empty_status) in
      ((one_of_compose vsd vs, false), iuf'')
  end;
  
find_linear iuf _ _ tBox := ((empty_status, false), iuf);
find_linear iuf _ _ (tVar _) := ((empty_status, false), iuf);
find_linear iuf _ _ (tConst _) := ((empty_status, false), iuf);
.

Definition mk_parray_op (op : ident) : term :=
  tConst (Kernames.MPfile ["PrimArray"; "Array"; "Corelib"], op).

Equations extract_impl (i : nat) (uf : UF.t) (vars : list bool) (t : term) : (term * bool) * nat :=

extract_impl i uf vars (tLetIn na b t) :=
  let is_mut := negb (UF.check uf i 0) in
  let '((b',_), i') := extract_impl (i+1) uf vars b in
  let '((t',mut'), i'') := extract_impl i' uf (is_mut :: vars) t in
  ((tLetIn na b' t', mut'), i'');

extract_impl i _ vars (tRel n) :=
  ((tRel n, nth n vars false), i);

extract_impl i uf vars (tApp u v) :=
  let '((u',_), i') := extract_impl i uf vars u in
  let '((v',_), i'') := extract_impl i' uf vars v in
  ((tApp u' v', false), i'');

extract_impl i uf vars (tConstruct ind n args) :=
  let accum := (fun (acc : (nat * list term)) t =>
    let (i, ts) := acc in
    let '((t',_), i') := extract_impl i uf vars t in
    (i', ts ++ [t'])) in
  let (i', ts) := fold_left accum args (i, []) in
  ((tConstruct ind n ts, false), i');

extract_impl i uf vars (tCase indn c brs) :=
  let is_mut := negb (UF.check uf i 0) in
  let '((c',_), i') := extract_impl (i+1) uf vars c in
  let accum := (fun (acc : (nat * list (list name * term))) br =>
    let '(i, ts) := acc in
    let '((br',_), i') := extract_impl i uf vars (snd br) in
    (i', ts ++ [(fst br, br')])) in
  let '(i'', brs') := fold_left accum brs (i', []) in
  ((tCase indn c' brs', is_mut), i'');

extract_impl i uf vars (tProj p c) :=
  let '((c',_), i') := extract_impl i uf vars c in
  ((tProj p c', false), i');

extract_impl i uf vars (tFix mfix idx) :=
  let accum := (fun (acc : (nat * list (EAst.def term))) d =>
    let (i, ds) := acc in
    let '((db',_), i') := extract_impl i uf vars (EAst.dbody d) in
    let d' := {| EAst.dname := EAst.dname d;
                 EAst.dbody := db';
                 EAst.rarg := EAst.rarg d
              |} in
    (i', ds ++ [d'])) in
  let (i', ds) := fold_left accum mfix (i, []) in
  ((tFix ds idx, false), i');
extract_impl i uf vars (tCoFix mfix idx) :=
  let accum := (fun (acc : (nat * list (EAst.def term))) d =>
    let (i, ds) := acc in
    let '((db',_), i') := extract_impl i uf vars (EAst.dbody d) in
    let d' := {| EAst.dname := EAst.dname d;
                 EAst.dbody := db';
                 EAst.rarg := EAst.rarg d
              |} in
    (i', ds ++ [d'])) in
  let (i', ds) := fold_left accum mfix (i, []) in
  ((tCoFix ds idx, false), i');

extract_impl i uf vars (tPrim prim) :=
  match prim.π2 with
  | primIntModel f => ((tPrim (primInt; primIntModel f), false), i)
  | primFloatModel f => ((tPrim (primFloat; primFloatModel f), false), i)
  | primStringModel f => ((tPrim (primString; primStringModel f), false), i)
  | primArrayModel a =>
      let '((d,_), i') := extract_impl i uf vars (array_default a) in
      let accum := (fun (acc : (nat * list term)) t =>
        let (i, ts) := acc in
        let '((t',_), i') := extract_impl i uf vars t in
        (i', ts ++ [t'])) in
      let (i'', vs) := fold_left accum (array_value a) (i', []) in
      let prim' := primArrayModel {| array_default := d; array_value := vs |} in
      ((tPrim (primArray; prim'), false), i'')
  end;

extract_impl i uf vars (tLazy t) :=
  let '((t', _), i') := extract_impl i uf vars t in
  ((tLazy t', false), i');
extract_impl i uf vars (tForce t) :=
  let '((t', _), i') := extract_impl i uf vars t in
  ((tForce t', false), i');

extract_impl i _ _ (tConst k) := ((tConst k, false), i);
extract_impl i _ _ tBox := ((tBox, false), i);
extract_impl i _ _ (tVar j) := ((tVar j, false), i);
extract_impl i uf vars (tEvar n l) :=
  ((tEvar n (map (fun t => fst (fst (extract_impl i uf vars t))) l), false), i);
extract_impl i uf vars (tLambda na t) :=
  let '((t',_), i') := extract_impl i uf vars t in
  ((tLambda na t', false), i');

extract_impl i uf vars (tAllocate (aArrayNew s b)) :=
  let is_mut := negb (UF.check uf i 0) in
  let '((s',_), i') := extract_impl (i+1) uf vars s in
  let '((b',_), i'') := extract_impl i' uf vars b in
  if is_mut
  then ((tAllocate (aArrayNew s' b'), true), i'')
  else ((tApp (tApp (mk_parray_op "make") s') b', false), i'');
extract_impl i uf vars (tMemoryRead (rArrayGet a ix)) :=
  let '((a',mut), i') := extract_impl i uf vars a in
  let '((ix',_), i'') := extract_impl i' uf vars ix in
  if mut
  then ((tMemoryRead (rArrayGet a' ix'), false), i'')
  else ((tApp (tApp (mk_parray_op "get") a') ix', false), i'');
extract_impl i uf vars (tMemoryRead (rArrayLength a)) :=
  let '((a',mut), i') := extract_impl i uf vars a in
  if mut
  then ((tMemoryRead (rArrayLength a'), false), i')
  else ((tApp (mk_parray_op "length") a', false), i');
extract_impl i uf vars (tMemoryUpdate (uArraySet a ix v)) :=
  let '((a', mut), i') := extract_impl i uf vars a in
  let '((ix', _), i'') := extract_impl i' uf vars ix in
  let '((v', _), i''') := extract_impl i'' uf vars v in
  if mut
  then ((tMemoryUpdate (uArraySet a' ix' v'), true), i''')
  else ((tApp (tApp (tApp (mk_parray_op "set") a') ix') v', false), i''')
.

Definition optimize_arrays (t : EAst.term) : term :=
  let imported := parray_ops (import_term t) in
  let '(_, (_, uf)) := find_linear (1, UF.empty) [] immutable imported in
  let '((r,_),_) := extract_impl 1 uf [] imported in
  r.
