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

Inductive HL_core : Type :=
  | HL_State : expr -> list ectx_item -> HL_core
  | HL_Callstate : binder -> val -> list ectx_item -> HL_core
  | HL_Returnstate : val -> list ectx_item -> HL_core.


(* Definition HL_core_to_expr (c : HL_core) : expr :=
  match c with
  | HL_State e K => fill K e
  | HL_Callstate f arg K => fill K (ExternalCall f (Val arg))
  | HL_Returnstate v K => fill K (Val v)
  end.
*)

Inductive HL_core_step : HL_core -> state -> HL_core -> state -> Prop :=
  | HL_step_base : 
      (* internal step *)
      forall e K σ σ' κs e' efs,
        base_step e σ κs e' σ' efs ->
        HL_core_step (HL_State e K) σ (HL_State e' K) σ'
  | HL_step_external :
      (* internal step meets external function call *)
      forall fname arg K σ,
        HL_core_step (HL_State (ExternalCall fname (Val arg)) K) σ
                     (HL_Callstate fname arg K) σ
  | HL_step_return :
      forall v K σ,
        HL_core_step (HL_Returnstate v K) σ (HL_State (Val v) K) σ
  .

(* HeapLang val -> CompCert Values.val *)
Definition heaplang_val_to_compcert (v : val) : option Values.val :=
  match v with
  | LitV (LitInt n) => Some (Values.Vint (Int.repr n))
  | _ => None
  end.

(* CompCert Values.val -> HeapLang val *)
Definition compcert_val_to_heaplang (v : Values.val) : option val :=
  match v with
  | Values.Vint i => Some (LitV (LitInt (Int.signed i)))
  | _ => None  
  end.

(* store all the function info *)
Parameter global_expr_env : val -> option expr.

Definition HL_initial_core (v: val) (params: list val) : option HL_core :=
  match global_expr_env v with
  | Some (Rec f x e) => 
      match params with
      | arg_val :: nil =>
          Some (HL_Callstate f arg_val [])
      | _ => None
      end
  | _ => None
  end.

Definition default_signature : signature := mksignature nil Xvoid cc_default.
Definition HL_at_external (c: HL_core) : option (external_function * list val) :=
  match c with
  (* only when func name can be extracted from the binder *)
  | HL_Callstate (BNamed fname) arg K => Some ((EF_external fname default_signature), [arg])
  | _ => None
  end.

Definition hl_after_external (vret: option val) (c: HL_core) : option HL_core :=
  match c with
  | HL_Callstate fname arg K =>
      match vret with
      | Some v => Some (HL_Returnstate v K)
      | None => Some (HL_Returnstate (LitV LitUnit) K)
      end
  | _ => None
  end.

Definition HL_halted (c: HL_core) : option val :=
  match c with
  | HL_State (Val v) [] => Some v
  | _ => None
  end.

Lemma HL_corestep_not_halted :
  forall m q m' q' (i: int), HL_core_step q m q' m' -> not ((HL_halted q) ≠ None).
Proof.
  intros.
  inv H.
  {
    inv H0; simpl; intro; contradiction.
  }
  {
    simpl. intro. contradiction.
  }
  {
    simpl. intro. contradiction.
  }
Qed.

Lemma HL_corestep_not_at_external:
  forall m q m' q', 
          HL_core_step q m q' m' -> HL_at_external q = None.
Proof.
 simpl; intros.
 inv H; try reflexivity; simpl.
Qed.


Program Definition HL_core_sem:
  @CoreSemantics HL_core state val :=
  @Build_CoreSemantics _ _ _
    (*deprecated cl_init_mem*)
    (fun _ m c m' v arg => (HL_initial_core v arg = Some c) /\ m' = m)
    (fun c _ => HL_at_external c)
    (fun ret c _ => hl_after_external ret c)
    (* (fun c _ =>  HL_halted c <> None) *)
    (fun c _ =>  not (eq (HL_halted c) None))
    (HL_core_step)
    (HL_corestep_not_halted)
    (HL_corestep_not_at_external).

