Require Import VST.sepcomp.semantics.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Require compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.cfrontend.Clight.

Require Import VST.sepcomp.semantics_generic.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.mem_lemmas.

Require Import VST.sepcomp.lang.
Require Import VST.sepcomp.tactics.
Require Import VST.sepcomp.locations.

Inductive hl_prim_step : expr -> state -> expr -> state -> Prop :=
  | hl_prim_step_base : 
      forall e σ σ' κs e' efs,
        prim_step e σ κs e' σ' efs ->
        hl_prim_step e σ e' σ'
  .

(* store all the function info *)
Parameter global_expr_env : val -> option expr.

Definition hl_initial_core (v: val) (params: list val) : option expr :=
  match global_expr_env v with
  | Some (Rec f x e) => 
      match params with
      | arg_val :: nil =>
          Some (App (Rec f x e) (of_val arg_val))
      | _ => None
      end
  | _ => None
  end.

Definition default_signature : signature := mksignature nil Xvoid cc_default.
Definition hl_at_external (e: expr) : option (external_function * list val) :=
  match (decompose_expr [] e) with
  (* only when func name can be extracted from the binder *)
  | Some (K, ExternalCall (BNamed fname) arg) => 
      match (to_val arg) with
      (* and the parameter has been a value *)
      | Some argv => Some ((EF_external fname default_signature), [argv])
      | _ => None
      end
  | _ => None
  end.

Definition hl_after_external (vret: option val) (e: expr) : option expr :=
  match vret with
  | Some v => 
      match (decompose_expr [] e) with
      | Some (K, ExternalCall (BNamed fname) arg) => 
          match (to_val arg) with
          | Some argv => Some (fill K (of_val v))
          | _ => None
          end
      | _ => None
      end
  | None => None
  end.

Definition hl_halted (e: expr) : option val := to_val e.

Lemma HL_corestep_not_halted :
  forall m q m' q' (i: int), hl_prim_step q m q' m' -> not ((hl_halted q) ≠ None).
Proof.
  intros.
  inv H. inv H0. simpl. inv H2;
  unfold hl_halted;
  destruct to_val eqn:Heq; eauto;
  apply to_val_fill_some in Heq;
  destruct Heq as [veq Heq];
  congruence.
Qed.

Lemma HL_corestep_not_at_external:
  forall m q m' q', 
    hl_prim_step q m q' m' -> hl_at_external q = None.
Proof.
  intros m q m' q' Hstep.
  inversion Hstep as [e σ σ' κs e' efs Hprim]; subst.
  destruct Hprim as [K e1 e2 Hfill_e1 Hfill_e2].
  unfold hl_at_external.
  destruct (decompose_expr [] (fill K e1)) eqn:Heq.
  destruct p as [K' e_ext].
  destruct e_ext eqn:Heq_ext; rewrite Hfill_e1; simpl; rewrite Heq; try reflexivity.

  (* Only the case where e_ext is an external call left *)
  {
    assert (reducible e1 m) as Hredxe1. {
      unfold reducible.
      apply base_prim_step in H.
      eexists _, _, _, _.
      apply H.
    }
    apply (decompose_redo_fill [] K) in Hredxe1.
    rewrite app_nil_r in Hredxe1.
    rewrite Hredxe1 in Heq.


    (* e1 in any base_step cannot be decompose into an external function call *)
    assert (forall σ κ e2 σ' efs fn arg K K',
              base_step e1 σ κ e2 σ' efs -> not (decompose_expr K e1 = Some (K', ExternalCall fn arg))) as Hnot_ext.
    { intros. inversion H0; intro Heq1; discriminate. }
    specialize (Hnot_ext m κs e2 m' efs fname e K K' H).
    rewrite Heq in Hnot_ext.
    congruence.
  }
  {
    subst. simpl. rewrite Heq. reflexivity.
  }
Qed.


Program Definition HL_core_sem:
  @CoreSemantics expr state val :=
  @Build_CoreSemantics _ _ _
    (*deprecated cl_init_mem*)
    (fun _ m c m' v arg => (hl_initial_core v arg = Some c) /\ m' = m)
    (fun c _ => hl_at_external c)
    (fun ret c _ => hl_after_external ret c)
    (* (fun c _ =>  HL_halted c <> None) *)
    (fun c _ =>  not (eq (hl_halted c) None))
    (hl_prim_step)
    (HL_corestep_not_halted)
    (HL_corestep_not_at_external).


Notation uobj_id := nat.

(* how to support pointer to pointer *)
Definition closed (locs : list loc) (m : state) : Prop :=
  forall l l',
    In l locs ->
    m.(heap) !! l = Some $ Some (LitV (LitLoc l')) ->
    In l' locs.

Definition sublist (l1 l2 : list loc) : Prop :=
  forall x, In x l1 -> In x l2.

Search prim_step.
Section specs.

  (* compartmentally pre-allocated heap space for uids *)
  Variable heap_by_uid : uobj_id -> list loc.  
  Variable uid : uobj_id.
  (* fname -> (isCasm func * (pre-cond, post-cond)) *)
  Variable ext_funcs : string -> option (bool * ((state -> Prop) * (state -> Prop))). 

  Definition R_relation (m: state) (m': state) (modified: bool) : Prop :=
    closed (heap_by_uid uid) m' 
    /\ subseteq (dom m.(heap)) (dom m'.(heap))
    /\ (not modified -> forall l, In l (heap_by_uid uid) -> m.(heap) !! l = m'.(heap) !! l).

  Inductive respecting_the_specs (e : expr) (m : state) (Q : state -> Prop) : Prop :=
    | rts_base : 
      forall m', R_relation m m' false ->
      (* internal steps *)
      ((forall (e' : expr) (m'' : state), hl_prim_step e m' e' m'' -> respecting_the_specs e' m'' Q )
        (* halted case *)
        /\ (not (eq (hl_halted e) None) -> Q m')
        (* external call case *)
        /\ (forall fname sig args is_casm (pre_spec : state -> Prop) m'' (post_spec : state -> Prop) vret e',
          (* m_extra satisfied the pre_sped of the external call *)
          hl_at_external e = Some (EF_external fname sig, args)
          -> Some (is_casm, (pre_spec, post_spec) ) = ext_funcs fname
          -> pre_spec m'
          -> R_relation m' m'' is_casm
          -> post_spec m''
          -> hl_after_external (Some vret) e = Some e'
          -> respecting_the_specs e' m Q) 
      ) -> respecting_the_specs e m Q.

End specs.