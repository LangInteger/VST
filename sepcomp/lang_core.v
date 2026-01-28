Require Import VST.sepcomp.semantics.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Require compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.cfrontend.Clight.

Require Import VST.sepcomp.semantics.
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
Parameter global_expr_env : Values.val -> option expr.

Definition HL_initial_core (v: Values.val) (params: list Values.val) : option HL_core :=
  match global_expr_env v with
  | Some (Rec f x e) => 
      match params with
      | arg_val :: nil =>
          match compcert_val_to_heaplang arg_val with
          | Some hl_arg_val =>
              Some (HL_Callstate f hl_arg_val [])
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition HL_at_external (c: HL_core) : option (binder * val) :=
  match c with
  | HL_Callstate f arg K => Some (f, arg)
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
  forall m q m' q' (i: int), HL_core_step q m q' m' -> HL_halted q = None.
Proof.
  intros.
  inv H.
  {
    inv H0; simpl; reflexivity.
  }
  {
    simpl. reflexivity.
  }
  {
    simpl. reflexivity.
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
  @CoreSemantics HL_core state :=
  @Build_CoreSemantics _ _
    (*deprecated cl_init_mem*)
    (fun _ m c m' v arg => HL_initial_core v arg = Some c)
    (fun c _ => HL_at_external c)
    (fun ret c _ => hl_after_external ret c)
    (fun c _ =>  not (eq (HL_halted c, None)))
    (HL_core_step)
    (HL_corestep_not_halted)
    (HL_corestep_not_at_external).

