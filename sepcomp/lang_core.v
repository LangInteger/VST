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

Inductive hl_prim_step : expr -> state -> expr -> state -> Prop :=
  | hl_prim_step_base : 
      forall e σ σ' κs e' efs,
        prim_step e σ κs e' σ' efs ->
        hl_prim_step e σ e' σ'
  .

(* store all the function info *)
Parameter global_expr_env : val -> option expr.

Definition HL_initial_core (v: val) (params: list val) : option expr :=
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
Definition HL_at_external (e: expr) : option (external_function * list val) :=
  match (decompose_expr 1000 [] e) with
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
      match (decompose_expr 1000 [] e) with
      | Some (K, ExternalCall (BNamed fname) arg) => 
          match (to_val arg) with
          | Some argv => Some (fill K (of_val v))
          | _ => None
          end
      | _ => None
      end
  | None => None
  end.

Definition HL_halted (e: expr) : option val :=
  match (to_val e) with
  | Some v => Some v
  | _ => None
  end.

Lemma HL_corestep_not_halted :
  forall m q m' q' (i: int), hl_prim_step q m q' m' -> not ((HL_halted q) ≠ None).
Proof.
  intros.
  inv H. inv H0.
Admitted.

Lemma HL_corestep_not_at_external:
  forall m q m' q', 
          hl_prim_step q m q' m' -> HL_at_external q = None.
Proof.
 simpl; intros.
 inv H; try reflexivity; simpl.
Admitted.


Program Definition HL_core_sem:
  @CoreSemantics expr state val :=
  @Build_CoreSemantics _ _ _
    (*deprecated cl_init_mem*)
    (fun _ m c m' v arg => (HL_initial_core v arg = Some c) /\ m' = m)
    (fun c _ => HL_at_external c)
    (fun ret c _ => hl_after_external ret c)
    (* (fun c _ =>  HL_halted c <> None) *)
    (fun c _ =>  not (eq (HL_halted c) None))
    (hl_prim_step)
    (HL_corestep_not_halted)
    (HL_corestep_not_at_external).

Section specs.

  Variable f_names : list string.
  Variable f_specs : string -> mem -> Prop.

  Theorem respecting_the_specs : (forall f, In f f_names, f_specs f) -> 

End specs.