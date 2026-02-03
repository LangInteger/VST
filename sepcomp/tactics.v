From stdpp Require Import fin_maps.
Require Import VST.sepcomp.lang.

Fixpoint decompose_expr(K : list ectx_item) (e : expr)
  : option (list ectx_item * expr) :=
  match e with
  | App e1 (Val v) => decompose_expr ((AppLCtx v) :: K) e1
  | App e1 e2 => decompose_expr ((AppRCtx e1)::K) e2
  | UnOp op e1 => decompose_expr ((UnOpCtx op)::K) e1
  | BinOp op e1 (Val v) => decompose_expr ((BinOpLCtx op v)::K) e1
  | BinOp op e1 e2 => decompose_expr ((BinOpRCtx op e1)::K) e2
  | If e0 e1 e2 => decompose_expr ((IfCtx e1 e2)::K) e0
  | Pair e1 (Val v) => decompose_expr ((PairLCtx v)::K) e1
  | Pair e1 e2 => decompose_expr ((PairRCtx e1)::K) e2
  | Fst e1 => decompose_expr (FstCtx::K) e1
  | Snd e1 => decompose_expr (SndCtx::K) e1
  | InjL e1 => decompose_expr (InjLCtx::K) e1
  | InjR e1 => decompose_expr (InjRCtx::K) e1
  | Case e0 e1 e2 => decompose_expr ((CaseCtx e1 e2)::K) e0
  | AllocN e1 (Val v) => decompose_expr ((AllocNLCtx v)::K) e1
  | AllocN e1 e2 => decompose_expr ((AllocNRCtx e1)::K) e2 
  | Free e1 => decompose_expr (FreeCtx::K) e1
  | Load e1 => decompose_expr (LoadCtx::K) e1
  | Store e1 (Val v) => decompose_expr ((StoreLCtx v)::K) e1
  | Store e1 e2 => decompose_expr ((StoreRCtx e1)::K) e2
  | ExternalCall f arg => decompose_expr ((ExternalCallCtx f)::K) arg
  | _ => Some (K, e)
  end.

Search (_++[]=_).
Search fill.
Search (_++_::_=_++_++_).
Lemma decompose_persist : 
  forall K1 e K2,
    decompose_expr K1 (fill K2 e) = decompose_expr (K1++K2) e.
Proof.
  intros.
  revert K2. revert K1.
  induction e.
  - intros. simpl.
    induction K2.
    + simpl. rewrite app_nil_r. reflexivity.
    + 

Lemma decompose_expr_fill_revised :
  forall K e K' e',
    decompose_expr [] (fill K e) = Some (K', e')
    -> fill K' e' = fill K e.
Proof.
Admitted.


Lemma decompose_expr_fill :
  forall e K e',
    e = fill K e' ->
    decompose_expr [] e = Some (K, e').
Proof.
  intros.
  induction e.
  {
    simpl. 
    assert (to_val (fill K e') = Some v) as Hval. 
    {
      rewrite <- H. simpl. reflexivity.
    }
    apply to_val_fill_some in Hval.
    destruct Hval as [Hval1 Hval2].
    rewrite Hval1.
    rewrite Hval2.
    reflexivity.
  }
Admitted.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  (* Note that the current context is spread into a list of fully-constructed
     items [K], and a list of pairs of values [vs] (prophecy identifier and
     resolution value) that is only non-empty if a [ResolveLCtx] item (maybe
     having several levels) is in the process of being constructed. Note that
     a fully-constructed item is inserted into [K] by calling [add_item], and
     that is only the case when a non-[ResolveLCtx] item is built. When [vs]
     is non-empty, [add_item] also wraps the item under several [ResolveLCtx]
     constructors: one for each pair in [vs]. *)
  let rec go K vs e :=
    match e with
    | _                               => lazymatch vs with [] => tac K e | _ => fail end
    | App ?e (Val ?v)                 => add_item (AppLCtx v) vs K e
    | App ?e1 ?e2                     => add_item (AppRCtx e1) vs K e2
    | UnOp ?op ?e                     => add_item (UnOpCtx op) vs K e
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLCtx op v) vs K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpRCtx op e1) vs K e2
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) vs K e0
    | Pair ?e (Val ?v)                => add_item (PairLCtx v) vs K e
    | Pair ?e1 ?e2                    => add_item (PairRCtx e1) vs K e2
    | Fst ?e                          => add_item FstCtx vs K e
    | Snd ?e                          => add_item SndCtx vs K e
    | InjL ?e                         => add_item InjLCtx vs K e
    | InjR ?e                         => add_item InjRCtx vs K e
    | Case ?e0 ?e1 ?e2                => add_item (CaseCtx e1 e2) vs K e0
    | AllocN ?e (Val ?v)              => add_item (AllocNLCtx v) vs K e
    | AllocN ?e1 ?e2                  => add_item (AllocNRCtx e1) vs K e2
    | Free ?e                         => add_item FreeCtx vs K e
    | Load ?e                         => add_item LoadCtx vs K e
    | Store ?e (Val ?v)               => add_item (StoreLCtx v) vs K e
    | Store ?e1 ?e2                   => add_item (StoreRCtx e1) vs K e2
    end
  with add_item Ki vs K e :=
    lazymatch vs with
    | _               => go (Ki :: K) (@nil (val * val)) e
    end
  in
  go (@nil ectx_item) (@nil (val * val)) e.

(** The tactic [inv_base_step] performs inversion on hypotheses of the shape
[base_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_base_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : base_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.

Create HintDb base_step.
Global Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : base_step.
Global Hint Extern 0 (base_reducible_no_obs _ _) => eexists _, _, _; simpl : base_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (base_step _ _ _ _ _ _) => econstructor : base_step.
Global Hint Extern 0 (base_step (AllocN _ _) _ _ _ _ _) => apply alloc_fresh : base_step.
