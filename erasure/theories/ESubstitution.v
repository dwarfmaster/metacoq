(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst PCUICTyping
     PCUICWeakening PCUICSubstitution PCUICWeakeningEnv PCUICElimination.
From MetaCoq.Erasure Require Import ETyping Extract Prelim.


Local Set Keyed Unification.

Module PA := PCUICAst.
Module P := PCUICWcbvEval.
Local Existing Instance config.extraction_checker_flags.

Lemma All2_All_mix_left {A B} {P : A -> Type} {Q : A -> B -> Type}
      {l : list A} {l'}:
  All P l -> All2 Q l l' -> All2 (fun x y => (P x * Q x y)%type) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

(** ** Global Weakening  *)

Lemma Is_type_extends (Σ : global_env_ext) Γ t :
  wf_local Σ Γ ->
  forall (Σ' : global_env), wf Σ' -> extends Σ Σ' -> isErasable Σ Γ t -> isErasable (Σ', Σ.2) Γ t.
Proof.
  intros. destruct X2 as [T []]. destruct Σ as [Σ]. cbn in *.
  exists T. split. change u with (snd (Σ,u)).
  eapply weakening_env; [ | eauto | | ]; eauto using wf_extends; eauto.
  destruct s; eauto.
  destruct s as (u' & ? & ?).
  right. exists u'. split; eauto.
  change u with (snd (Σ,u)).
  eapply weakening_env; [ | eauto | | ]; eauto using wf_extends.
Qed.

Lemma Is_proof_extends (Σ : global_env_ext) Γ t :
  wf_local Σ Γ ->
  forall Σ', wf Σ' -> extends Σ Σ' -> Is_proof Σ Γ t -> Is_proof (Σ',Σ.2) Γ t.
Proof.
  intros. destruct X2 as (? & ? & ? & ? & ?).
  exists x, x0. repeat split.
  eapply weakening_env; [ | eauto | | ]; eauto using wf_extends.
  eapply weakening_env; [ | eauto | | ]; eauto using wf_extends.
  eauto.
Qed.

(* todo move *)
Instance extends_refl : CRelationClasses.Reflexive extends.
Proof. now exists []. Qed.

Lemma Informative_extends:
  forall (Σ : global_env_ext) (ind : inductive)
    (mdecl : PCUICAst.mutual_inductive_body) (idecl : PCUICAst.one_inductive_body),

    PCUICTyping.declared_inductive (fst Σ) mdecl ind idecl ->
    forall (Σ' : global_env) (u0 : Instance.t),
      wf Σ' ->
      extends Σ Σ' ->
      Informative Σ ind -> Informative (Σ', Σ.2) ind.
Proof.
  repeat intros ?.
  assert (extends Σ Σ'0). destruct X0, X2. subst. cbn. exists (x0 ++ x). cbn.
  simpl in e0. now rewrite <- app_assoc.
  edestruct H0; eauto. destruct H3.

  eapply weakening_env_declared_inductive in H; eauto.
  destruct H, H1.
  unfold PCUICTyping.declared_minductive in *.

  eapply extends_lookup in H1; eauto.
  2:{ reflexivity. }
  rewrite H1 in H. inversion H. subst. clear H.
  rewrite H3 in H4. inversion H4. subst. clear H4.
  split. eauto. econstructor. eauto.
Qed.

Lemma erases_extends :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ' -> extends Σ Σ' -> forall t', erases Σ Γ t t' -> erases (Σ', Σ.2) Γ t t')
           (fun Σ Γ wfΓ => wf_local Σ Γ).
Proof.
  apply typing_ind_env; intros; rename_all_hyps; auto.
  all: match goal with [ H : erases _ _ ?a _ |- _ ] => tryif is_var a then idtac else inv H end.
  all: try now (econstructor; eauto).
  all: try now (econstructor; eapply Is_type_extends; eauto).
  - econstructor. all:eauto.
    2:{ eauto. eapply All2_All_left in X3.
        2:{ intros ? ? [[[? ?] ?] ?]. exact e. }
        eapply All2_All_mix_left in X3; eauto.
        eapply All2_impl. exact X3.
        intros. destruct H as [? []].
        split; eauto. }

    eapply Informative_extends; eauto.
  - econstructor. destruct isdecl. 2:eauto.
    eapply Informative_extends; eauto.
  - econstructor.
    eapply All2_All_mix_left in X1; eauto.
    eapply All2_impl. exact X1.
    intros ? ? [[[]] [? []]].
    split; eauto.
  - econstructor.
    eapply All2_All_mix_left in X1; eauto.
    eapply All2_impl. exact X1.
    intros ? ? [[] [? []]].
    split; eauto.
Qed.

(** ** Weakening *)

Lemma Is_type_weakening:
  forall (Σ : global_env_ext) (Γ Γ' Γ'' : PCUICAst.context),
    wf_local Σ (Γ ,,, Γ') ->
    wf Σ ->
    wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
    forall t : PCUICAst.term,
      isErasable Σ (Γ ,,, Γ') t -> isErasable Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (PCUICLiftSubst.lift #|Γ''| #|Γ'| t).
Proof.
  intros. destruct X2 as (T & ? & ?).
  eexists. split. eapply weakening_typing; eauto.
  now apply All_local_env_app in X1.

  destruct s as [? | [u []]].
  - left. clear - i. generalize (#|Γ''|), (#|Γ'|). induction T; cbn in *; intros; try now inv i.
    + now eapply IHT2.
    + now eapply IHT3.
  - right. exists u. split; eauto.
    eapply weakening_typing in t1; eauto.
    now apply All_local_env_app in X1.
Qed.

Require Import MetaCoq.PCUIC.PCUICInversion.
Derive Signature for erases.

Lemma erases_ctx_ext (Σ : global_env_ext) Γ Γ' t t' :
  erases Σ Γ t t' -> Γ = Γ' -> erases Σ Γ' t t'.
Proof.
  intros. now subst.
Qed.

Lemma All_map_inv {A B} (P : B -> Type) (f : A -> B) l : All P (map f l) -> All (compose P f) l.
Proof. induction l; intros Hf; inv Hf; try constructor; eauto. Qed.

Lemma erases_weakening' (Σ : global_env_ext) (Γ Γ' Γ'' : PCUICAst.context) (t T : PCUICAst.term) t' :
    wf Σ ->
    wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
    Σ ;;; Γ ,,, Γ' |- t : T ->
    Σ ;;; Γ ,,, Γ' |- t ⇝ℇ t' ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- (PCUICLiftSubst.lift #|Γ''| #|Γ'| t) ⇝ℇ (ELiftSubst.lift #|Γ''| #|Γ'| t').
Proof.
  intros HΣ HΓ'' * H He.
  generalize_eqs H. intros eqw. rewrite <- eqw in *.
  revert Γ Γ' Γ'' HΓ'' eqw t' He.
  revert Σ HΣ Γ0 t T H .
  apply (typing_ind_env (fun Σ Γ0 t T =>  forall Γ Γ' Γ'',
    wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
    Γ0 = Γ ,,, Γ' ->
    forall t',
    Σ;;; Γ0 |- t ⇝ℇ t' ->
    _)
    (fun Σ Γ wfΓ => wf_local Σ Γ)
    );
    intros Σ wfΣ Γ0; intros; try subst Γ0; auto.
  all: match goal with [ H : erases _ _ ?a _ |- _ ] => tryif is_var a then idtac else inv H end.
  all: try now (cbn; econstructor; eauto).
  all: try now (econstructor; eapply Is_type_weakening; eauto).
  all:cbn.
  - destruct ?; econstructor.
  - econstructor.
    unfold app_context, PCUICAst.snoc in *.
    pose proof (H0 Γ (PCUICAst.vass n t :: Γ') Γ'').
    rewrite lift_context_snoc0, <- plus_n_O in *.
    eapply H1; eauto. cbn. econstructor.
    eauto. cbn. exists s1. eapply weakening_typing with (T := tSort s1); eauto.
    now apply All_local_env_app in X2.
  - econstructor.
    + eapply H0; eauto.
    + pose proof (H1 Γ (PCUICAst.vdef n b b_ty :: Γ') Γ'').
      rewrite lift_context_snoc0, <- plus_n_O in *.
      eapply H2; eauto. cbn. econstructor.
      eauto. cbn. 2: cbn; eapply weakening_typing; eauto.
      eapply weakening_typing in X0; eauto.
      now apply All_local_env_app in X3.
      now apply All_local_env_app in X3.
  - econstructor.
    + eauto.
    + eapply H4; eauto.
    + eapply All2_map.
      eapply All2_All_left in X3.
      2:{ idtac. intros ? ? [[[[? ?] e0] ?] e']. exact e0. }
      eapply All2_impl. eapply All2_All_mix_left.
      eassumption. eassumption. intros.
      destruct H. destruct p0.
      cbn. destruct x, y; cbn in *; subst.
      split; eauto.
  - assert (HT : Σ;;; Γ ,,, Γ' |- PCUICAst.tFix mfix n : (decl.(dtype))).
    econstructor; eauto. eapply All_impl. eassumption. intros.
    destruct X4; cbn in *; firstorder.
    eapply (All_impl X1). firstorder.
    
    eapply weakening_typing in HT; auto.
    2:{ apply All_local_env_app in X2 as [X2 _]. eapply X2. }

    cbn in HT.
    eapply inversion_Fix in HT as (? & ? & ? & ? & ? & ? & ?) ; auto. clear a0 c.


    econstructor.
    eapply All2_map.
    eapply All2_impl. eapply All2_All_mix_left.
    eapply X1. eassumption. simpl.
    intros [] []. simpl. intros [[Hs IH] [<- [<- IH']]].
    repeat split. unfold app_context in *.
    specialize (IH Γ (types ++ Γ') Γ'').
    subst types. rewrite app_length, fix_context_length in IH.
    forward IH.
    { rewrite lift_context_app, <- plus_n_O. unfold app_context.
      eapply All_mfix_wf in a; auto.
      rewrite lift_fix_context in a.
      now rewrite <- !app_assoc. }
    forward IH by now rewrite app_assoc.
    rewrite lift_fix_context.
    rewrite lift_context_app, <- plus_n_O in IH.
    unfold app_context in IH. rewrite <- !app_assoc in IH.
    rewrite (All2_length _ _ X3) in *.
    apply IH. apply IH'.

  - assert (HT : Σ;;; Γ ,,, Γ' |- PCUICAst.tCoFix mfix n : (decl.(dtype))).
    econstructor; eauto. eapply All_impl. eassumption. intros.
    destruct X4; cbn in *; firstorder.
    eapply (All_impl X1). firstorder.
    
    eapply weakening_typing in HT; auto.
    2:{ apply All_local_env_app in X2 as [X2 _]. eapply X2. }

    cbn in HT.
    eapply inversion_CoFix in HT as (? & ? & ? & ? & ? & ? & ?) ; auto. clear a0 c.

    econstructor.
    eapply All2_map.
    eapply All2_impl. eapply All2_All_mix_left.
    eapply X1. eassumption. simpl.
    intros [] []. simpl. intros [[Hs IH] [<- [<- IH']]].
    repeat split. unfold app_context in *.
    specialize (IH Γ (types ++ Γ') Γ'').
    subst types. rewrite app_length, fix_context_length in IH.
    forward IH.
    { rewrite lift_context_app, <- plus_n_O. unfold app_context.
      eapply All_mfix_wf in a; auto.
      rewrite lift_fix_context in a.
      now rewrite <- !app_assoc. }
    forward IH by now rewrite app_assoc.
    rewrite lift_fix_context.
    rewrite lift_context_app, <- plus_n_O in IH.
    unfold app_context in IH. rewrite <- !app_assoc in IH.
    rewrite (All2_length _ _ X3) in *.
    apply IH. apply IH'.
Qed.

Lemma erases_weakening (Σ : global_env_ext) (Γ Γ' : PCUICAst.context) (t T : PCUICAst.term) t' :
  wf Σ ->
  wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t ⇝ℇ t' ->
  Σ ;;; Γ ,,, Γ' |- (PCUICLiftSubst.lift #|Γ'| 0 t) ⇝ℇ (ELiftSubst.lift #|Γ'| 0 t').
Proof.
  intros.
  pose proof (typing_wf_local X1).
  eapply (erases_weakening' Σ Γ [] Γ'); cbn; eauto.
Qed.

Lemma All2_nth_error_None {A B} {P : A -> B -> Type} {l l'} n :
  All2 P l l' ->
  nth_error l n = None ->
  nth_error l' n = None.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. auto.
Qed.

Lemma All2_length {A B} {P : A -> B -> Type} l l' : All2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; auto. Qed.

Derive Signature for subslet.

Lemma is_type_subst (Σ : global_env_ext) Γ Γ' Δ a s :
  wf Σ -> subslet Σ Γ s Γ' ->
  (* Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T -> *)
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  isErasable Σ (Γ ,,, Γ' ,,, Δ) a ->
  isErasable Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a).
Proof.
  intros ? ? ? (T & HT & H).
  exists (PCUICLiftSubst.subst s #|Δ| T). split.
  eapply substitution; eauto.
  destruct H as [ | (u & ? & ?) ].
  - left. generalize (#|Δ|). intros n.
    induction T in n, i |- *; (try now inv i); cbn in *; eauto.
  - right. exists u. split; eauto.
    pose proof (substitution Σ Γ Γ' s Δ).
    eapply X2 in t; eauto.
Qed.

Lemma substlet_typable (Σ : global_env_ext) Γ s Γ' n t :
  subslet Σ Γ s Γ' -> nth_error s n = Some t -> {T & Σ ;;; Γ |- t : T}.
Proof.
  induction n in s, t, Γ, Γ' |- *; intros; cbn in *.
  - destruct s. inv H.
    inv H. depelim X; eauto.
  - destruct s; inv H.
    depelim X. eapply IHn in H1. eauto.  eauto.
    eauto.
Qed.

Lemma erases_eq (Σ : global_env_ext) Γ Γ' t t' s s' :
  erases Σ Γ t t' ->
  Γ = Γ' ->
  t = s ->
  t' = s' ->
  erases Σ Γ' s s'.
Proof.
  now subst.
Qed.

Lemma erases_subst (Σ : global_env_ext) Γ Γ' Δ t s t' s' T :
  wf Σ ->
  subslet Σ Γ s Γ' ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  Σ ;;; Γ ,,, Γ'  ,,, Δ |- t : T ->
  Σ ;;; Γ ,,, Γ'  ,,, Δ |- t ⇝ℇ t' ->
  All2 (erases Σ Γ) s s' ->
  Σ ;;; (Γ ,,, subst_context s 0 Δ) |- (PCUICLiftSubst.subst s #|Δ| t) ⇝ℇ ELiftSubst.subst s' #|Δ| t'.
Proof.
  intros HΣ HΔ Hs Ht He.
  generalize_eqs Ht. intros eqw.
  revert Γ Γ' Δ t' s Hs HΔ He eqw.
  revert Σ HΣ Γ0 t T Ht.
  eapply (typing_ind_env (fun Σ Γ0 t T =>
                            forall (Γ Γ' : PCUICAst.context) Δ t' (s : list PCUICAst.term),
                              wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
                              subslet Σ Γ s Γ' ->
                              Σ;;; Γ ,,, Γ' ,,, Δ |- t ⇝ℇ t' ->
                              Γ0 = Γ ,,, Γ' ,,, Δ ->
                              All2 (erases Σ Γ) s s' ->
                              Σ;;; Γ ,,, subst_context s 0 Δ |- PCUICLiftSubst.subst s #|Δ| t ⇝ℇ ELiftSubst.subst s' #|Δ| t'
         )
         (fun Σ Γ0 _ => wf_local Σ Γ0)
         );
    intros Σ wfΣ Γ0 wfΓ0; intros; simpl in * |-; auto; subst Γ0.
  - inv H0.
    + cbn. destruct ?. destruct ?.
      * eapply All2_nth_error_Some in X2; eauto.
        destruct X2 as (? & ? & ?).
        rewrite e.
        erewrite <- subst_context_length.
        eapply substlet_typable in X1 as []. 2:exact E0.
        eapply erases_weakening; eauto.
      * erewrite All2_length; eauto.
        eapply All2_nth_error_None in X2; eauto.
        rewrite X2. econstructor.
      * econstructor.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H0. econstructor. eapply is_type_subst; eauto.
  - inv H1. econstructor.
    eapply is_type_subst; eauto.
  - inv H1.
    + cbn. econstructor.
      specialize (H0 Γ Γ' (PCUICAst.vass n t :: Δ) t'0 s).
      (* unfold app_context, snoc in *. *)
      rewrite subst_context_snoc0 in *.
      eapply H0; eauto.
      cbn. econstructor. eauto.
      cbn. exists s1. eapply substitution with (T := tSort s1); eauto.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H2.
    + cbn. econstructor.
      eauto.
      specialize (H1 Γ Γ' (PCUICAst.vdef n b b_ty :: Δ) t2' s).
      rewrite subst_context_snoc0 in *.
      eapply H1; eauto.
      cbn. econstructor. eauto.
      cbn.
      eapply substitution in X0; eauto.
      eapply substitution; eauto.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H1.
    + cbn. econstructor.
      eapply H; eauto.
      eapply H0; eauto.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H1.
    + cbn. econstructor.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H0. econstructor.
    eapply is_type_subst; eauto.
  - inv H0.
    + cbn. econstructor.
    + econstructor.
      eapply is_type_subst; eauto.
  - depelim H6.
    + cbn. econstructor.
      * eauto.
      * eapply H4; eauto.
      * eapply All2_map.
        eapply All2_impl_In; eauto.
        intros. destruct H10, x, y. cbn in *. subst. split; eauto.
        eapply All2_All_left in X3.
        2:{ intros ? ? [[[[? ?] e1] ?] ?]. exact e1. }

        eapply In_nth_error in H8 as [].
        eapply nth_error_all in X3; eauto.
        eapply X3; eauto.

  + econstructor.
    eapply is_type_subst; eauto.
  - inv H1.
    + cbn. econstructor.
      * eauto.
      * eauto.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H2.
    + cbn. econstructor.
      eapply All2_map.
      eapply All2_impl_In.
      eassumption.
      intros. destruct H4 as (? & ? & ?).
      repeat split; eauto.
      eapply In_nth_error in H2 as [].
      eapply nth_error_all in X1; eauto.
      destruct X1 as [Hs IH].
      specialize (IH Γ Γ' (Δ ,,, PCUICLiftSubst.fix_context mfix)).
      rewrite app_context_assoc in *.
      eapply IH in e1; eauto.

      eapply erases_eq; eauto.
      * rewrite subst_context_app.
        rewrite <- plus_n_O.
        rewrite app_context_assoc. f_equal.
        now rewrite subst_fix_context.
      * cbn. now rewrite app_context_length, fix_context_length.
      * cbn. now erewrite app_context_length, fix_context_length, All2_length.
      * pose proof (substitution Σ Γ Γ' s (Δ ,,, PCUICLiftSubst.fix_context mfix)).
        rewrite app_context_assoc in *. destruct Hs.
        eapply X1 in t; eauto.
        eapply typing_wf_local.  eassumption.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H2.
    + cbn. econstructor.
      eapply All2_map.
      eapply All2_impl_In.
      eassumption.
      intros. destruct H4 as (? & ? & ?).
      repeat split; eauto.
      eapply In_nth_error in H2 as [].
      eapply nth_error_all in X1; eauto.
      destruct X1.
      specialize (e2 Γ Γ' (Δ ,,, PCUICLiftSubst.fix_context mfix)).
      rewrite app_context_assoc in *.
      eapply e2 in e1; eauto.

      eapply erases_eq; eauto.
      * rewrite subst_context_app.
        rewrite <- plus_n_O.
        rewrite app_context_assoc. f_equal.
        now rewrite subst_fix_context.
      * cbn. now rewrite app_context_length, fix_context_length.
      * cbn. now erewrite app_context_length, fix_context_length, (All2_length _ _ X5).
      * pose proof (substitution Σ Γ Γ' s (Δ ,,, PCUICLiftSubst.fix_context mfix)).
        rewrite app_context_assoc in *.
        eapply X1 in t; eauto.
        eapply typing_wf_local.  eassumption.
    + econstructor.
      eapply is_type_subst; eauto.
  - eapply H; eauto.
Qed.
