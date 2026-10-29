
From Stdlib.Lists Require Import List.
From MetaRocq.Erasure Require EAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Universes.
From MetaRocq.Erasure Require Import EPrimitive.
From MetaRocq.Common Require Import Primitive.
From Equations Require Import Equations.

Declare Scope erasure.
Local Open Scope erasure.

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
| tArrayNew (na : name) (s b t : term) (* let na := new(s,b) : B array in t *)
| tArrayLength (n : nat)
| tArrayGet (n : nat) (i : term)
| tArraySet (n : nat) (i x : term).

Definition map_def' {term term' : Set} (f : term -> term') (d : EAst.def term): EAst.def term' :=
  {| EAst.dname := d.(EAst.dname); EAst.dbody := f d.(EAst.dbody); EAst.rarg := d.(EAst.rarg) |}.

Fixpoint weaken (t: term): EAst.term := match t with
| tBox => EAst.tBox 
| tRel n => EAst.tRel n
| tVar i => EAst.tVar i 
| tEvar n l => EAst.tEvar n (map weaken l)
| tLambda na t => EAst.tLambda na (weaken t)
| tLetIn na b t => EAst.tLetIn na (weaken b) (weaken t) 
| tApp u v => EAst.tApp (weaken u) (weaken v)
| tConst k => EAst.tConst k
| tConstruct ind n args => EAst.tConstruct ind n (map weaken args)
| tCase indn c brs => EAst.tCase indn (weaken c) (map (fun br => (fst br, weaken (snd br))) brs)
| tProj p c => EAst.tProj p (weaken c)
| tFix mfix idx => EAst.tFix (map (map_def' weaken) mfix) idx
| tCoFix mfix idx => EAst.tCoFix (map (map_def' weaken) mfix) idx
| tPrim prim => EAst.tPrim (map_prim weaken prim)
| tLazy t => EAst.tLazy (weaken t)
| tForce t => EAst.tForce (weaken t)
| tArrayNew na s b t => EAst.tVar "Stdlib.Array.PArray.make"
| tArrayLength n => EAst.tApp (EAst.tVar "Stdlib.Array.PArray.length") (EAst.tRel n)
| tArrayGet n i =>
    EAst.tApp (EAst.tApp (EAst.tVar "Stdlib.Array.PArray.get") (EAst.tRel n)) (weaken i)
| tArraySet n i x =>
    EAst.tApp (EAst.tApp (EAst.tApp (EAst.tVar "Stdlib.Array.PArray.set") (EAst.tRel n))
                         (weaken i))
              (weaken x)
end.

(* Rel is used at most once in a writing position, and is potentially read before that *)
Inductive is_linear_in : nat -> term -> Prop :=
| linearRead (n:nat) (t:term) : is_only_read_in n t -> is_linear_in n t
| linearRel (n r:nat) : n = r -> is_linear_in n (tRel r)
| linearInLet (n:nat) (na : name) (b t : term):
    is_linear_in n b -> is_unused_in (S n) t -> is_linear_in n (tLetIn na b t)
| linearUnderLet (n:nat) (na : name) (b t : term):
    is_only_read_in n b -> is_linear_in (S n) t -> is_linear_in n (tLetIn na b t)
| linearAppFn (n:nat) (u v : term):
    is_linear_in n u -> is_unused_in n v -> is_linear_in n (tApp u v)
| linearAppArg (n:nat) (u v : term):
    is_unused_in n u -> is_linear_in n v -> is_linear_in n (tApp u v)
| linearConstruct (n:nat) (ind:inductive) (c:nat) (args:list term):
    (exists (i : nat), i < length args /\ (is_linear_in n (nth i args tBox)) /\
      (forall (j : nat), (j <> i /\ j < length args) -> is_unused_in n (nth j args tBox))) ->
    is_linear_in n (tConstruct ind c args)
| linearCaseDiscriminee (n:nat) (indn : inductive*nat) (c:term) (brs : list (list name * term)):
    is_linear_in n c ->
    (forall (br : (list name * term)), In br brs -> is_unused_in (n + length (fst br)) (snd br)) ->
    is_linear_in n (tCase indn c brs)
| linearCaseBranches (n:nat) (indn : inductive*nat) (c:term) (brs : list (list name * term)):
    is_unused_in n c ->
    (forall (br : (list name * term)), In br brs -> is_linear_in (n + length (fst br)) (snd br)) ->
    is_linear_in n (tCase indn c brs)
| linearProj (n:nat) (p : projection) (c : term):
    is_linear_in n c -> is_linear_in n (tProj p c)
| linearArrayNew (n : nat) (na : name) (s b t : term):
    is_unused_in n b -> is_linear_in (S n) t -> is_linear_in n (tArrayNew na s b t)
| linearArrayGet (n a : nat) (i : term):
    n <> a -> is_linear_in n i -> is_linear_in n (tArrayGet a i)
| linearArraySet (n a : nat) (i x : term):
    is_only_read_in n i -> is_only_read_in n x -> n = a ->
    is_linear_in n (tArraySet a i x)
| linearArraySetIndex (n a : nat) (i x : term):
    n <> a -> is_linear_in n i -> is_unused_in n x -> is_linear_in n (tArraySet a i x)
| linearArraySetValue (n a : nat) (i x : term):
    n <> a -> is_unused_in n i -> is_linear_in n x -> is_linear_in n (tArraySet a i x)
(* Rel is used only in read position, potentially many times *)
with is_only_read_in : nat -> term -> Prop :=
| readUnused (n:nat) (t:term) : is_unused_in n t -> is_only_read_in n t
| readLetIn (n:nat) (na:name) (b t : term):
    is_only_read_in n b -> is_only_read_in (S n) t -> is_only_read_in n (tLetIn na b t)
| readApp (n:nat) (u v : term):
    is_only_read_in n u -> is_only_read_in n v -> is_only_read_in n (tApp u v)
| readConstruct (n:nat) (ind : inductive) (c:nat) (args:list term):
    (forall (i : nat), i < length args -> is_only_read_in n (nth i args tBox)) ->
    is_only_read_in n (tConstruct ind c args)
| readCase (n:nat) (indn:inductive*nat) (c:term) (brs: list (list name * term)) :
    is_only_read_in n c ->
    (forall (br : (list name * term)), In br brs -> is_only_read_in (n + length (fst br)) (snd br)) ->
    is_only_read_in n (tCase indn c brs)
| readProj (n:nat) (p : projection) (c : term) :
    is_only_read_in n c -> is_only_read_in n (tProj p c)
| readArrayNew (n : nat) (na : name) (s b t : term):
    is_unused_in n b -> is_only_read_in (S n) t -> is_only_read_in n (tArrayNew na s b t)
| readArrayLength (n : nat) : is_only_read_in n (tArrayLength n)
| readArrayGet (n a : nat) (i : term):
    is_only_read_in n i -> is_only_read_in n (tArrayGet a i)
| readArraySet (n a : nat) (i x : term):
    n <> a -> is_only_read_in n i -> is_only_read_in n x -> is_only_read_in n (tArraySet a i x)
(* Rel is unused in the term *)
with is_unused_in : nat -> term -> Prop :=
| unusedBox (n:nat) : is_unused_in n tBox
| unusedRel (n r : nat): n <> r -> is_unused_in n (tRel r)
| unusedVar (n : nat) (i : ident) : is_unused_in n (tVar i)
| unusedLambda (n:nat) (na : name) (t : term):
    is_unused_in (S n) t -> is_unused_in n (tLambda na t)
| unusedLetIn (n:nat) (na:name) (b t : term):
    is_unused_in n b -> is_unused_in (S n) t -> is_unused_in n (tLetIn na b t)
| unusedApp (n:nat) (u v:term):
    is_unused_in n u -> is_unused_in n v -> is_unused_in n (tApp u v)
| unusedConst (n:nat) (k:kername) : is_unused_in n (tConst k)
| unusedConstruct (n:nat) (ind : inductive) (c:nat) (args:list term):
    (forall (i : nat), i < length args -> is_unused_in n (nth i args tBox)) ->
    is_unused_in n (tConstruct ind c args)
| unusedCase (n:nat) (indn:inductive*nat) (c:term) (brs: list (list name * term)) :
    is_unused_in n c ->
    (forall (br : (list name * term)), In br brs -> is_unused_in (n + length (fst br)) (snd br)) ->
    is_unused_in n (tCase indn c brs)
| unusedProj (n:nat) (p : projection) (c : term):
    is_unused_in n c -> is_unused_in n (tProj p c)
| unusedLazy (n:nat) (t:term): is_unused_in n t -> is_unused_in n (tLazy t)
| unusedForce (n:nat) (t:term): is_unused_in n t -> is_unused_in n (tForce t)
| unusedArrayNew (n : nat) (na : name) (s b t : term):
    is_unused_in n b -> is_unused_in (S n) t -> is_unused_in n (tArrayNew na s b t)
| unusedArrayLength (n a : nat): n <> a -> is_unused_in n (tArrayLength a)
| unusedArrayGet (n a : nat) (i : term):
    is_unused_in n i -> n <> a -> is_unused_in n (tArrayGet a i)
| unusedArraySet (n a : nat) (i x : term):
    n <> a -> is_unused_in n i -> is_unused_in n x -> is_unused_in n (tArraySet a i x)
.

(* Evar might use the variable, so we forbid evars under linear binders *)
(* Lambda must not capture array variables, because we do not support marking lambda as linear *)
(* We assume f a b c are evaluated left to right, and that the arguments are fully evaluated before calling f *)
(* Do not assume the matched term in tCase is fully evaluated before any branch executes *)
(* TODO check it is unused in fixpoints/cofixpoints, instead of forbidding them under a let array *)
(* TODO what to do with primitives *)
(* It must be unused in lazy term, because we cannot control when they are going to be evaluated *)

Inductive valid_linear_term : term -> Prop :=
| validLinBox: valid_linear_term tBox
| validLinRel (n : nat): valid_linear_term (tRel n)
| validLinVar (i : ident): valid_linear_term (tVar i)
| validLinEvar (n : nat) (l : list term):
    (forall (t : term), In t l -> valid_linear_term t) -> valid_linear_term (tEvar n l)
| validLinLambda (na : name) (t : term):
    valid_linear_term t -> valid_linear_term (tLambda na t)
| validLinLetIn (na : name) (b t : term):
    valid_linear_term b -> valid_linear_term t -> valid_linear_term (tLetIn na b t)
| validLinApp (u v : term):
    valid_linear_term u -> valid_linear_term v -> valid_linear_term (tApp u v)
| validLinConst (k : kername): valid_linear_term (tConst k)
| validLinConstruct (ind : inductive) (n : nat) (args : list term):
    (forall (t: term), In t args -> valid_linear_term t) ->
    valid_linear_term (tConstruct ind n args)
| validLinCase (indn : inductive * nat) (c : term) (brs : list (list name * term)):
    valid_linear_term c ->
    (forall (br : (list name * term)), In br brs -> valid_linear_term (snd br)) ->
    valid_linear_term (tCase indn c brs)
| validLinProj (p : projection) (c : term):
    valid_linear_term c -> valid_linear_term (tProj p c)
| validLinLazy (t : term):
    valid_linear_term t -> valid_linear_term (tLazy t)
| validLinForce (t : term):
    valid_linear_term t -> valid_linear_term (tForce t)
| validLinArrayNew (na : name) (s b t : term):
    is_linear_in 1 t -> valid_linear_term s -> valid_linear_term b -> valid_linear_term t -> valid_linear_term (tArrayNew na s b t)
| validLinArrayLength (n : nat): valid_linear_term (tArrayLength n)
| validLinArrayGet (n : nat) (i : term):
    valid_linear_term i -> valid_linear_term  (tArrayGet n i)
| validLinArraySet (n : nat) (i x : term):
    valid_linear_term i -> valid_linear_term x -> valid_linear_term (tArraySet n i x)
.

Definition vars_set := list nat.

Fixpoint insert_var (n:nat) (s:vars_set) := match s with
  | nil => [n]
  | m :: s' => match n ?= m with
      | Lt => n :: s
      | Eq => s
      | Gt => m :: insert_var n s'
      end
  end.

Equations? union_vars (s1 s2 : vars_set) : vars_set by wf (length s1 + length s2) lt :=
union_vars [] s2 := s2;
union_vars s1 [] := s1;
union_vars (n :: s1) (m :: s2) := match n ?= m with
  | Lt => n :: union_vars s1 (m :: s2)
  | Eq => n :: union_vars s1 s2
  | Gt => m :: union_vars (n :: s1) s2
  end.
Proof.
- auto with arith.
- auto with arith.
Qed.

Equations? inter_vars (s1 s2 : vars_set) : vars_set by wf (length s1 + length s2) lt :=
inter_vars [] s2 := s2;
inter_vars s1 [] := s1;
inter_vars (n :: s1) (m :: s2) := match n ?= m with
  | Lt => inter_vars s1 (m :: s2)
  | Eq => n :: inter_vars s1 s2
  | Gt => inter_vars (n :: s1) s2
  end.
Proof.
- auto with arith.
- auto with arith.
Qed.

Equations? diff_vars (s1 s2 : vars_set) : vars_set by wf (length s1 + length s2) lt :=
diff_vars [] s2 := s2;
diff_vars s1 [] := s1;
diff_vars (n :: s1) (m :: s2) := match n ?= m with
  | Lt => n :: diff_vars s1 (m :: s2)
  | Eq => diff_vars s1 s2
  | Gt => diff_vars (n :: s1) s2
  end.
Proof.
- auto with arith.
- auto with arith.
Qed.

Fixpoint unions_vars (ss : list vars_set) : vars_set := match ss with
  | [] => []
  | s :: ss' => union_vars s (unions_vars ss')
  end.

(* We always have read_only_variables <= linear_variables <= used_variables *)
Record variables_status :=
  { read_only_variables : vars_set; (* Variables that are only used in read position *)
    linear_variables : vars_set; (* Variables used in correct linear fashion *)
    used_variables : vars_set (* Any used variable *)
  }.

Definition pop_binder_in_rel (n : nat) : list nat :=
  match n with
  | O => []
  | S O => []
  | S m => [m]
  end.

Definition pop_binder (tv : variables_status) : variables_status :=
  {| read_only_variables := flat_map pop_binder_in_rel (read_only_variables tv);
     linear_variables := flat_map pop_binder_in_rel (linear_variables tv);
     used_variables := flat_map pop_binder_in_rel (used_variables tv)
  |}.

Fixpoint pop_binders (n:nat) (tv : variables_status) : variables_status :=
  match n with
  | O => tv
  | S n' => pop_binders n' (pop_binder tv)
  end.

Definition empty_status : variables_status :=
  {| read_only_variables := [];
     linear_variables := [];
     used_variables := []
  |}.

(* Variable usage from the result of two actions executed one after another *)
Definition seq_compose (tv1 tv2 : variables_status) : variables_status :=
  {| read_only_variables := inter_vars (read_only_variables tv1) (read_only_variables tv2);
     linear_variables :=
       union_vars
         (diff_vars (linear_variables tv1) (used_variables tv2))
         (inter_vars (read_only_variables tv1) (linear_variables tv2));
     used_variables := union_vars (used_variables tv1) (used_variables tv2)
  |}.

(* Variable usage from the result of two actions executed in undefined order *)
Definition undefined_compose (tv1 tv2 : variables_status) : variables_status :=
  {| read_only_variables := inter_vars (read_only_variables tv1) (read_only_variables tv2);
     linear_variables :=
       union_vars
         (diff_vars (linear_variables tv1) (used_variables tv2))
         (diff_vars (linear_variables tv2) (used_variables tv1));
     used_variables := union_vars (used_variables tv1) (used_variables tv2)
  |}.

Fixpoint undefined_compose_many (tvs : list variables_status) : variables_status :=
  match tvs with
  | [] => empty_status
  | tv :: tvs' => undefined_compose tv (undefined_compose_many tvs')
  end.

(* Variable usage from the result of two actions, one of which is executed *)
Definition one_of_compose (tv1 tv2 : variables_status) : variables_status :=
  {| read_only_variables := inter_vars (read_only_variables tv1) (read_only_variables tv2);
     linear_variables := inter_vars (linear_variables tv1) (linear_variables tv2);
     used_variables := union_vars (used_variables tv1) (used_variables tv2)
  |}.

Definition one_of_compose_many (tvs : list variables_status) : variables_status :=
  match tvs with
  | [] => empty_status
  | v :: vs => fold_left one_of_compose vs v
  end.

Fixpoint extract_linear (t: EAst.term): term * variables_status := match t with
  | EAst.tBox => (tBox, empty_status)
  | EAst.tRel n => (tRel n, {| read_only_variables := []; linear_variables := [n]; used_variables := [n] |})
  | EAst.tVar i => (tVar i, empty_status)
  | EAst.tEvar n l =>
      let tvs := map extract_linear l in
      (tEvar n (map fst tvs),
      {| read_only_variables := [];
         linear_variables := [];
         used_variables := unions_vars (map (fun tv => used_variables (snd tv)) tvs)
      |})
  | EAst.tLambda na t =>
      let (t', tv) := extract_linear t in (tLambda na t', pop_binder tv)
  | EAst.tLetIn na b t =>
      let (b', bst) := extract_linear b in
      let (t', tst) := extract_linear t in
      (tLetIn na b' t', seq_compose bst (pop_binder tst))
  | EAst.tApp u v =>
      let (u', ust) := extract_linear u in
      let (v', vst) := extract_linear v in
      (tApp u' v', seq_compose ust vst)
  | EAst.tConst k => (tConst k, empty_status)
  | EAst.tConstruct ind n args =>
      let tvs := map extract_linear args in
      let args' := map fst tvs in
      let vars := match map snd tvs with
        | [] => empty_status
        | (v::vs) => fold_left undefined_compose vs v
        end in
      (tConstruct ind n args', vars)
  | EAst.tCase indn c brs =>
      let (c', cst) := extract_linear c in
      let brs' := map (fun nmt => let (t', tst) := extract_linear (snd nmt) in ((fst nmt,t'), pop_binders (length (fst nmt)) tst)) brs in
      (tCase indn c' (map fst brs'), seq_compose cst (one_of_compose_many (map snd brs')))
  | EAst.tProj p c =>
      let (c', cst) := extract_linear c in
      (tProj p c', cst)
  | EAst.tFix mfix idx =>
      let extract_linear_def (d : EAst.def EAst.term) : EAst.def term * variables_status :=
        let (b,bst) := extract_linear (EAst.dbody d) in
        ({| EAst.dname := EAst.dname d;
           EAst.dbody := b;
           EAst.rarg := EAst.rarg d
        |},bst) in
      let mfix' := map extract_linear_def mfix in
      (tFix (map fst mfix') idx,
       {| read_only_variables := [];
          linear_variables := [];
          used_variables := unions_vars (map (fun fx => used_variables (snd fx)) mfix')
       |})
  | EAst.tCoFix mfix idx =>
      let extract_linear_def (d : EAst.def EAst.term) : EAst.def term * variables_status :=
        let (b,bst) := extract_linear (EAst.dbody d) in
        ({| EAst.dname := EAst.dname d;
           EAst.dbody := b;
           EAst.rarg := EAst.rarg d
        |},bst) in
      let mfix' := map extract_linear_def mfix in
      (tCoFix (map fst mfix') idx,
       {| read_only_variables := [];
          linear_variables := [];
          used_variables := unions_vars (map (fun fx => used_variables (snd fx)) mfix')
       |})
  | EAst.tPrim prim =>
    let extract_array_model (a : array_model EAst.term) :=
      let (d,dst) := extract_linear (array_default a) in
      let vals := map extract_linear (array_value a) in
      ({| array_default := d; array_value := map fst vals |},
       one_of_compose dst (undefined_compose_many (map snd vals))) in
    let extract_prim (p : prim_val EAst.term) :=
      match p.π2 return prim_val term * variables_status with
      | primIntModel f =>
          ((primInt; primIntModel f), empty_status)
      | primFloatModel f =>
          ((primFloat; primFloatModel f), empty_status)
      | primStringModel f =>
          ((primString; primStringModel f), empty_status)
      | primArrayModel a =>
          let (a',ast) := extract_array_model a in
          ((primArray; primArrayModel a'), ast)
      end in
    let (prim',primst) := extract_prim prim in
    (tPrim prim', primst)
  | EAst.tLazy t =>
      let (t', tst) := extract_linear t in
      (tLazy t', {| read_only_variables := []; linear_variables := []; used_variables := used_variables tst |})
  | EAst.tForce t =>
      let (t', tst) := extract_linear t in
      (tForce t', tst)
  end.
