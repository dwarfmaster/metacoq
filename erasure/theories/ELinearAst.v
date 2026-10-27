
From Stdlib.Lists Require Import List.
From MetaRocq.Erasure Require EAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Universes.
From MetaRocq.Erasure Require Import EPrimitive.

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
(* We don't assume an order of evaluation for application of function to argument, so the linearity check allows usage on one side only is it isn't read anywhere *)
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
(* | validLinFix (mfix : EAst.mfixpoint term) (idx : nat): *) (* TODO *)
(* | validLinCoFix (mfix : EAst.mfixpoint term) (idx : nat) *) (* TODO *)
(* | validLinPrim (prim : prim_val term) *) (* TODO *)
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
