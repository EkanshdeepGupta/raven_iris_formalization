From stdpp Require Export binders strings.
From stdpp Require Import countable.
Require Import Eqdep_dec.
From stdpp Require Import gmap list sets coPset.
From stdpp Require Import namespaces.

From iris Require Import options.
From iris.algebra Require Import cmra.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import ghost_map.
From iris.base_logic.lib Require Import invariants.

From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.proofmode Require Import tactics.

From raven_iris.simp_raven_lang Require Export lang lifting ghost_state.
From raven_iris.simp_raven_lang Require Import ghost_state.

From Coq.Program Require Import Wf.

Context `{!simpLangG Σ}.

Definition lvar := string.

Definition proc_name := string.
Global Parameter proc_set : gset proc_name.

Definition pred_name := string.
Global Parameter pred_set : gset pred_name.

Definition inv_name := string.
Global Parameter inv_set : gset inv_name.

(* How to connect Resource Algebras to ucmras, without triggering universe inconsistencies *)
Class ResourceAlgebra (A: Type) := {
  comp : A -> A -> A;
  frame : A -> A -> A;
  fpuValid : A -> A -> bool;
  (* RA Axioms *)
  (* ra_ucmra : ucmra; *)
  (* ra_ucmra_map : A -> ra_ucmra; *)
}.

Global Declare Instance RAEq : forall A: Type, EqDecision (ResourceAlgebra A).
Global Declare Instance RACountable : forall A: Type, Countable (ResourceAlgebra A).

Record RA_Pack := {
  RA_carrier : Type;
  RA_carrier_eqdec :> EqDecision RA_carrier;
  RA_inst :> ResourceAlgebra RA_carrier;
}.

Global Axiom ra_eq_dec :  EqDecision RA_Pack .
(* Global Axiom ra_countable_dec :  Countable RA_Pack . *)

Parameter ResourceAlgebras : list RA_Pack.

Inductive typ :=
| TpInt | TpLoc | TpBool.

(* Definition fld_name := string. *)
Parameter fld_set : gset lang.fld_name.

Record fld := Fld { fld_name_val : fld_name; fld_typ : typ }.

Inductive val :=
| LitBool (b: bool) | LitInt (i: Z) | LitUnit | LitLoc (l: loc).
(* | LitRAElem : forall (r : RA_Pack), RA_carrier r -> val. *)

(* TODO: Figure out how to incorporate RA values *)
Inductive LitRAElem (r : RA_Pack) (x : RA_carrier r): Type. 

Scheme Equality for val.

(* Inductive eq {A : Type} (x : A) : A -> Prop := eq_refl : eq x x. *)


(* Definition val_eq_dec : forall (x y : val), { x = y } + { x <> y }.
Proof.
decide equality.
Defined. *)


Inductive LExpr :=
| LVar (x : lvar)
| LVal (v : val)
| LUnOp (op : un_op) (e : LExpr)
| LBinOp (op : bin_op) (e1 e2 : LExpr)
(* | LIfE  *)
| LIfE (e1 e2 e3 : LExpr)
| LStuck
.

(* TODO: Figure out the right way to do this deep embedding *)

Definition symb_map : Type := lvar -> val.


Fixpoint interp_lexpr (le : LExpr) (mp : symb_map) : option val :=
  match le with
  | LVar x => Some (mp x)
  
  | LVal v => Some v

  | LUnOp op e =>
    match op with
    | NotBoolOp =>
      match interp_lexpr e mp with
      | Some (LitBool b) => Some (LitBool (negb b))
      | _ => None
      end
    | NegOp =>
      match interp_lexpr e mp with
      | Some (LitInt i) => Some (LitInt (-1 * i))
      | _ => None
      end
    end
  
  | LBinOp op e1 e2 =>
    match op with
    | AddOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 + i2))
      | _, _ => None
      end

    | SubOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 - i2))
      | _, _ => None
      end

    | MulOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 * i2))
      | _, _ => None  
      end

    | DivOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 / i2))
      | _, _ => None
      end

    | ModOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 mod i2))
      | _, _ => None
      end

    | EqOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some v1, Some v2 => Some (LitBool (if val_beq v1 v2 then true else false))
      | _, _ => None
      end

    | NeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some v1, Some v2 => Some (LitBool (if val_beq v1 v2 then false else true))
      | _, _ => None
      end

    | LtOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (if Z.ltb i1 i2 then true else false))
      | _, _ => None
      end

    | GtOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (if Z.gtb i1 i2 then true else false))
      | _, _ => None
      end
    
    | LeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (if Z.leb i1 i2 then true else false))
      | _, _ => None
      end
      
    | GeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (if Z.geb i1 i2 then true else false))
      | _, _ => None
      end

    | AndOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitBool b1), Some (LitBool b2) => Some (LitBool (b1 && b2))
      | _, _ => None
      end

    | OrOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitBool b1), Some (LitBool b2) => Some (LitBool (b1 || b2))
      | _, _ => None
      end
    end

  | LIfE e1 e2 e3 =>
    match interp_lexpr e1 mp with
    | Some (LitBool true) => interp_lexpr e2 mp
    | Some (LitBool false) => interp_lexpr e3 mp
    | _ => None
    end 

  | LStuck => None
  end.


(* TODO: Fix this with a proper error state; at present returning True when le is malformed which is not sound. *)
Definition LExpr_holds (le : LExpr) (mp : symb_map) : Prop :=
  match interp_lexpr le mp with
  | Some v => v = LitBool true
  | None => True
  end.

Definition trnsl_val (v: lang.val) : val :=
match v with
| lang.LitBool b => LitBool b
| lang.LitInt i => LitInt i
| lang.LitUnit => LitUnit
| lang.LitLoc l => LitLoc l
end.

Lemma trnsl_val_inj : forall v1 v2, trnsl_val v1 = trnsl_val v2 -> v1 = v2.
Proof.
  destruct v1, v2; simpl; try discriminate; intros H; inversion H; subst; auto.
Qed.

Fixpoint lexpr_subst (expr : LExpr) (subst_map : gmap var LExpr) :=
match expr with
| LVar x => match subst_map !! x with
    | None => LVar x
    | Some e => e
    end
| LVal v => LVal v
| LUnOp op e => LUnOp op (lexpr_subst e subst_map)
| LBinOp op e1 e2 => LBinOp op (lexpr_subst e1 subst_map) (lexpr_subst e2 subst_map)
| LIfE e1 e2 e3 => LIfE (lexpr_subst e1 subst_map) (lexpr_subst e2 subst_map) (lexpr_subst e3 subst_map)
| LStuck => LStuck
end.

Global Instance ra_carrier_eqdec_instance (r : RA_Pack) : EqDecision (RA_carrier r) :=
  RA_carrier_eqdec r.

Global Instance val_eq : EqDecision val.
Proof.
  (* intros x y.
  destruct x; destruct y. *)
  (* solve_decision. *)
  refine (fun x y =>
    match x, y with
    | LitBool b1, LitBool b2 => cast_if (decide (b1 = b2))
    | LitInt i1, LitInt i2 => cast_if (decide (i1 = i2))
    | LitUnit, LitUnit => left eq_refl
    | LitLoc l1, LitLoc l2 => cast_if (decide (l1 = l2))
    (* | LitRAElem r1 a1, LitRAElem r2 a2 =>
        match ra_eq_dec r1 r2 with
        | left Heq =>
            (* r1 = r2, so carriers are same, can cast and decide equality on carrier elements *)
            cast_if (decide (eq_rect r1 (fun r => RA_carrier r) a1 r2 Heq = a2))

        | right _ => right _
        end *)
    | _, _ => right _
    end). 
  all: try by f_equal.
  all: try intros Heq; inversion Heq; auto.
  (* - subst. simpl. by f_equal. *)
  (* - subst. simpl in n. intros Heq. *)
  (* inversion Heq as [H1]. *)
  (* assert (a1 = a2) by (apply (inj_pair2_eq_dec _ ra_eq_dec), H1). *)
  (* done. *)
Qed.

(* TODO: To be proved *)
Global Declare Instance LExpr_Eq : EqDecision LExpr.
Global Declare Instance LExpr_Countable : Countable LExpr.

Global Declare Instance val_countable : Countable val.

Inductive stmt :=
| Seq (s1 s2 : stmt)
(* | Return (e : lang.expr) *)
| IfS (e : lang.expr) (s1 s2 : stmt)
| Assign (v : lang.var) (e : lang.expr)
(* | Free (e : lang.expr) *)
| SkipS
| StuckS (* stuck statement *)
(* | ExprS (e : lang.expr) *)
| Call (v : lang.var) (proc : proc_name) (args : list lang.expr)
| FldWr (v : lang.var) (fld : fld_name) (e2 : lang.expr)
| FldRd (v : lang.var) (e : lang.expr) (fld : fld_name)
| CAS (v : lang.var) (e1 : lang.expr) (fld : fld_name) (e2 : lang.expr) (e3 : lang.expr)
| Alloc (v : lang.var) (fs: list (lang.fld_name * lang.val))
| Spawn (proc : proc_name) (args : list lang.expr)
| UnfoldPred (pred : pred_name) (args : list lang.expr)
| FoldPred (pred : pred_name) (args : list lang.expr)
| InvAccessBlock (inv: inv_name) (args : list lang.expr) (body : stmt)
(* | UnfoldInv (inv: inv_name) (args : list lang.expr)
| FoldInv (inv: inv_name) (args : list lang.expr) *)
| Fpu (e : lang.expr) (fld : fld_name) (RAPack : RA_Pack) (old_val : RA_carrier RAPack) (new_val : RA_carrier RAPack)
.

Inductive assertion :=
| LStack (σ : gmap lang.var lvar)
| LExprA (p: LExpr)
| LPure (p : Prop)
| LOwn (e: LExpr) (fld: fld_name) (chunk: val)
| LGhostOwn (e: LExpr) (fld: fld_name) (RAPack: RA_Pack) (chunk: RA_carrier RAPack)
| LForall (v : var) (body : assertion)
| LExists (v : var) (body : assertion)
| LImpl (cond : LExpr) (body : assertion)
| LInv (inv_name : inv_name) (args : list LExpr)
| LPred (pred_name : pred_name) (args : list LExpr)
| LAnd (assert1 : assertion) (assert2 : assertion)
.

Fixpoint subst (ra: assertion) (mp: gmap var LExpr) : assertion := match ra with
| LStack σ => LStack σ
| LExprA e => LExprA (lexpr_subst e mp)
| LPure p => LPure p
| LOwn e fld chunk => LOwn (lexpr_subst e mp) fld chunk
| LGhostOwn e fld RAPack chunk => LGhostOwn e fld RAPack chunk
| LForall vars body => LForall vars (subst body mp)
| LExists vars body => LExists vars (subst body mp)
| LImpl cond body => LImpl (lexpr_subst cond mp) (subst body mp)
| LInv inv_name args => 
    LInv inv_name (map (fun expr => lexpr_subst expr mp) args)
| LPred pred_name args =>
    LPred pred_name (map (fun expr => lexpr_subst expr mp) args)
| LAnd a1 a2 => LAnd (subst a1 mp) (subst a2 mp)
end.

(* Definition trnsl_r_assertion_assertion (ra: r_assertion) : assertion := 
  subst ra ∅. *)

Record ProcRecord := Proc {
  proc_args: list var;
  proc_precond : assertion;
  proc_postcond : assertion;
  ret_var : var;
  body : stmt;
}.

Global Parameter proc_map : gmap proc_name ProcRecord.
Axiom proc_map_set : dom proc_map = proc_set.

Record InvRecord := Inv {
  inv_args: list var;
  inv_body: assertion;
}.

Global Parameter inv_map : gmap inv_name InvRecord.
Axiom inv_map_set : dom inv_map = inv_set.

Record PredRecord := Pred {
  pred_args: list var;
  pred_body: assertion;
}.

Global Parameter pred_map : gmap pred_name PredRecord.
Axiom pred_map_set : dom pred_map = pred_set.

Inductive expr_well_defined : lang.expr -> Prop :=
| Constr e :
  expr_well_defined e.

Inductive stmt_well_defined : stmt -> Prop := 
| SeqTp s1 s2 :
  stmt_well_defined s1 ->
  stmt_well_defined s2 ->
  stmt_well_defined (Seq s1 s2)
(* | ReturnTp e : 
    expr_well_defined e ->
    stmt_well_defined (Return e) *)
| IfSTp e s1 s2 : 
    expr_well_defined e -> 
    stmt_well_defined s1 ->
    stmt_well_defined s2 -> 
    stmt_well_defined (IfS e s1 s2)
| AssignTp v e: 
    expr_well_defined e ->
    stmt_well_defined (Assign v e)
(* | FreeTp e: 
    expr_well_defined e ->
    stmt_well_defined (Free e) *)
| SkipSTp : stmt_well_defined (SkipS)
| StuckSTp : stmt_well_defined (StuckS)
(* | ExprSTp e: 
    expr_well_defined e -> 
    stmt_well_defined (ExprS e) *)
| CallTp v proc args: 
    proc ∈ proc_set -> 
    (Forall (fun arg => expr_well_defined arg) args) ->
    stmt_well_defined (Call v proc args)
| FldWrTp v fld e2: 
    (fld ∈ fld_set) -> 
    expr_well_defined e2 -> 
    stmt_well_defined (FldWr v fld e2)
| FldRdTp v e fld: 
    fld ∈ fld_set ->
    expr_well_defined e ->
    stmt_well_defined (FldRd v e fld)
| CASTp v e1 fld e2 e3: 
    fld ∈ fld_set ->
    expr_well_defined e1 ->
    expr_well_defined e2 ->
    expr_well_defined e3 ->
    stmt_well_defined (CAS v e1 fld e2 e3)
| AllocTp v fs: 
    Forall (fun fld_v => (fst fld_v) ∈ fld_set) fs ->
    stmt_well_defined (Alloc v fs)
| SpawnTp proc args: 
    proc ∈ proc_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (Spawn proc args)
| UnfoldPredTp pred args : 
    pred ∈ pred_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (UnfoldPred pred args)
| FoldPredTp pred args : 
    pred ∈ pred_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (FoldPred pred args)
| InvAccessBlockTp inv args stmt:
    inv ∈ inv_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined stmt ->
    stmt_well_defined (InvAccessBlock inv args stmt)

(* | UnfoldInvTp inv args : 
    inv ∈ inv_set -> 
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (UnfoldInv inv args)
| FoldInvTp inv args : 
    inv ∈ inv_set ->
    Forall (fun arg => expr_well_defined arg) args ->
    stmt_well_defined (FoldInv inv args) *)
| FpuTp e fld RAPack old_val new_val : 
    fld ∈ fld_set ->
    expr_well_defined e ->
    stmt_well_defined (Fpu e fld RAPack  old_val new_val)
.

Section AtomicAnnotations.
  Parameter inv_namespace_map : inv_name -> namespace.

  Axiom inv_namespace_disjoint : forall inv1 inv2 : inv_name, inv1 ∈ inv_set -> inv2 ∈ inv_set -> (inv_namespace_map inv1) ## (inv_namespace_map inv2).

  Inductive AtomicStep : Type :=
  | Closed
  | Opened (S : list (inv_name * list LExpr))
  | Stepped (S : list (inv_name * list LExpr))
  .

  Definition AtomicAnnotation : Type := (gset inv_name * AtomicStep).

  Definition maskAnnot : Type := gset inv_name.

  (* Definition oneAtomicStep  := match i1, i2 with
  | Closed, Closed => true
  | (Opened s1), (Stepped s2) => bool_decide (s1 = s2)
  | _, _ => false
  end. *)
End AtomicAnnotations.

Section Translation.
  (* Have to include all the resource algebras  *)

    Definition trnsl_lval (v: val) : lang.val :=
    match v with
    | LitBool b => (lang.LitBool b) 
    | LitInt i => (lang.LitInt i)
    | LitUnit => (lang.LitUnit)
    | LitLoc l => (lang.LitLoc (lang.Loc l.(loc_car)))
    (* | LitRAElem _ _ => None *)
    end.

    Global Parameter trnsl_pred : pred_name -> list LExpr -> symb_map -> iProp Σ.
    Global Parameter trnsl_inv : inv_name -> list LExpr -> symb_map -> iProp Σ.


    Definition stack: Type := gmap lang.var lvar.

    Definition symb_stk_to_stk_frm (stk : stack) (mp : symb_map) : stack_frame :=
      StackFrame (fmap (λ v, trnsl_lval (mp v)) stk).

    Fixpoint trnsl_assertion (a : assertion) (stk_id: stack_id) (mp : symb_map): option (iProp Σ) := match a with
    | LStack σ => Some (stack_frame_own stk_id (symb_stk_to_stk_frm σ mp))
    | LExprA l_expr => 
      Some (⌜LExpr_holds l_expr mp⌝%I)
      (* Some (⌜(e = (lang.Val (lang.LitBool true)))⌝) *)
    
    (* ⌜(trnsl_expressions l_expr) = Some (lang.Val (lang.LitBool true))⌝ *)
    | LPure p => Some (⌜ p ⌝%I)
    | LOwn l_expr fld chunk => 
      match trnsl_lval chunk with
      | chunk =>
      Some (∃ l: lang.loc, (
        ⌜LExpr_holds (LBinOp EqOp l_expr (LVal (LitLoc l))) mp⌝ ∗ 
        (l#fld ↦{ 1 } chunk)
        )%I)%I
        (* (heap_maps_to l fld 1 chunk) *)
        end
    (* TODO: Embed RAs properly and redefine this correctly *)
    | LGhostOwn l_expr fld RAPack chunk =>
      None 
    | LForall v body => 
      match trnsl_assertion body stk_id mp with
      | None => None
      | Some body_expr => Some (∀ v':lang.val, body_expr)%I
      end
      (* ∀ v':lang.val, (trnsl_assertion (body)) *)
      (* ∀ vs, (trnsl_assertion body) *)
      (* True *)
    | LExists v body => 
      Some (∃ v': val,
        match trnsl_assertion body stk_id (λ x, if String.eqb x v then v' else mp x) with
        | None => False
        | Some body_expr => body_expr
        end
    )%I
    
    | LImpl cnd body => 
      match (trnsl_assertion body stk_id mp) with
      | None => None
      | Some body_expr => 
      Some (⌜LExpr_holds cnd mp⌝ -∗ body_expr)%I
      end
      (* True *)
    | LInv inv' args => 
      match inv_map !! inv' with
      | Some inv_record => 
        let subst_map := list_to_map (zip inv_record.(inv_args) args) in
        let subst_body := subst inv_record.(inv_body) subst_map in

        Some (inv (inv_namespace_map inv') (trnsl_inv inv' args mp))

        (* False *)
      | None => None
      end
      (* False *)
    | LPred pred args => Some (trnsl_pred pred args mp)
    | LAnd a1 a2 => 
      match (trnsl_assertion a1 stk_id mp), (trnsl_assertion a2 stk_id mp) with
      | None, _ => None
      | _, None => None
      | Some a1, Some a2 => Some (a1 ∗ a2)%I
      end
    end
    .

  Axiom trnsl_pred_validity : forall (pred : pred_name) (args : list LExpr) (stk_id: stack_id) (mp : symb_map), 
    match pred_map !! pred with
    | Some pred_rec => 
      let subst_map := list_to_map (zip pred_rec.(pred_args) args) in

      trnsl_assertion (subst pred_rec.(pred_body) subst_map) stk_id mp = Some (trnsl_pred pred args mp)
    | None => true
    end
  .

  Axiom trnsl_inv_validity : forall (inv : inv_name) (args : list LExpr) (stk_id: stack_id) (mp : symb_map), 
    match inv_map !! inv with
    | Some inv_rec => 
      let subst_map := list_to_map (zip inv_rec.(inv_args) args) in

      trnsl_assertion (subst inv_rec.(inv_body) subst_map) stk_id mp = Some (trnsl_inv inv args mp)
    | None => true
    end
  .

  Definition entails P Q := forall stk_id mp, ∃ P' Q', trnsl_assertion P stk_id mp = Some P' /\ trnsl_assertion Q stk_id mp = Some Q' /\ (P' ⊢  Q')%I.

  Fixpoint trnsl_expr_lExpr (stk: stack) (e: lang.expr) :=
  match e with
  | Var x => match stk !! x with
             | Some v => Some (LVar v)
             | None => None
             end
  | Val v => Some (LVal (trnsl_val v))
  | UnOp op e => 
      match trnsl_expr_lExpr stk e with
      | Some le => Some (LUnOp op le)
      | None => None
      end
  | BinOp op e1 e2 => 
    match (trnsl_expr_lExpr stk e1), (trnsl_expr_lExpr stk e2) with
    | Some le1, Some le2 => Some (LBinOp op le1 le2)
    | _, _ => None
    end

  | IfE e1 e2 e3 =>
    match (trnsl_expr_lExpr stk e1), (trnsl_expr_lExpr stk e2), (trnsl_expr_lExpr stk e3) with
    | Some le1, Some le2, Some le3 => Some (LIfE le1 le2 le3)
    | _, _, _ => None
    end

  | StuckE => Some LStuck
  end.

  Inductive trnsl_stmt_ret :=
  | None'
  | Error
  | Some' (s: lang.stmt).
  
  Fixpoint trnsl_atomic_block (body : stmt) (step_taken : bool) : trnsl_stmt_ret * bool := 
  match body, step_taken with
  | Seq s1 s2, _ =>
    match trnsl_atomic_block s1 step_taken with
    | (None', step_taken') => trnsl_atomic_block s2 step_taken'
    | (Some' s1, step_taken') => 
      match trnsl_atomic_block s2 step_taken' with
      | (None', step_taken'') => (Some' s1, step_taken'')
      | (Some' s2, step_taken'') => (Some' (lang.Seq s1 s2), step_taken'')
      | (Error, _) => (Error, step_taken')
      end
    | (Error, _) => (Error, step_taken)
    end

  | IfS e s1 s2, _ =>
    match trnsl_atomic_block s1 step_taken, trnsl_atomic_block s2 step_taken with
    | (None', step_taken'), (None', step_taken'') => (Some' (lang.SkipS), step_taken' || step_taken'')
    | (None', step_taken'), (Some' s2, step_taken'') => (Some' (lang.IfS e lang.SkipS s2), step_taken' || step_taken'')
    | (Some' s1, step_taken'), (None', step_taken'') => (Some' (lang.IfS e s1 lang.SkipS), step_taken' || step_taken'')
    | (Some' s1, step_taken'), (Some' s2, step_taken'') => (Some' (lang.IfS e s1 s2), step_taken' || step_taken'')
    | (Error, _), _ | _, (Error, _) => (Error, step_taken)
    end

  | Assign v e, false => (Some' (lang.Assign v e), true)
  | Assign v e, true => (Error, true)

  | SkipS, false => (Some' lang.SkipS, false)
  | SkipS, true => (Some' lang.SkipS, true)

  | StuckS, _ => (Some' lang.StuckS, step_taken)
  | Call v proc args, _ => (Error, true)

  | FldWr v fld e2, false => (Some' (lang.FldWr v fld e2), true)
  | FldWr v fld e2, true => (Error, true)

  | FldRd v e fld, false => (Some' (lang.FldRd v e fld), true)
  | FldRd v e fld, true => (Error, true)

  | CAS v e1 fld e2 e3, false => (Some' (lang.CAS v e1 fld e2 e3), true)
  | CAS v e1 fld e2 e3, true => (Error, true)

  | Alloc v fs, false => (Some' (lang.Alloc v fs), true)
  | Alloc v fs, true => (Error, true)

  | Spawn proc args, false => (Some' (lang.Spawn proc args), true)
  | Spawn proc args, true => (Error, true)
  | InvAccessBlock inv args body, _ => trnsl_atomic_block body step_taken
  | _, _ => (None', step_taken)
  end.


  Fixpoint trnsl_stmt (s : stmt) : trnsl_stmt_ret := match s with
  | Seq s1 s2 => 
    match trnsl_stmt s1, trnsl_stmt s2 with
    | None', None' => None'
    | Some' s1, None' => Some' s1
    | None', Some' s2 => Some' s2
    | Some' s1', Some' s2' => Some' (stmt_append s1' s2' )
    | Error, _
    | _, Error => Error
    end

  | IfS e s1 s2 => 
      match (trnsl_stmt s1), (trnsl_stmt s2) with
      | None', None' => None'
      | Some' s1, None' => Some' (lang.IfS e s1 lang.SkipS)
      | None', Some' s2 => Some' (lang.IfS e lang.SkipS s2 )
      | Some' s1, Some' s2 => Some' (lang.IfS e s1 s2) 
      | Error, _ | _, Error => Error
      end

  | Assign v e => Some' (lang.Assign v e)
  | SkipS => Some' (lang.SkipS)
  | StuckS => Some' lang.StuckS
  | Call v proc args => None'
  (* Some (lang.Call v proc args) *)
  | FldWr v fld e2 => Some' (lang.FldWr v fld e2)
  
  | FldRd v e1 fld => Some' (lang.FldRd v e1 fld)
  | CAS v e1 fld e2 e3 => Some' (lang.CAS v e1 fld e2 e3)
  | Alloc v fs => Some' (lang.Alloc v fs)
  | Spawn proc args => None'
  
  | UnfoldPred pred args => None'
  | FoldPred pred args => None'
  | InvAccessBlock inv args body => (trnsl_atomic_block body false).1

  (* | UnfoldInv inv args => None'
  | FoldInv inv args => None' *)
  | Fpu e fld RAPack old_val new_val => None'
  end.

End Translation.


Section RavenLogic.

  Definition fresh_lvar (stk: stack) v := forall v', not (stk !! v' = Some v). 

  Fixpoint field_list_to_assertion lexpr fld_vals  := match fld_vals with
  | [] => LPure true
  | (fld,val) :: fld_vals => LAnd (LOwn lexpr fld (trnsl_val val)) (field_list_to_assertion lexpr fld_vals)
  end.

  Inductive RavenHoareTriple : 
  assertion -> 
      stmt -> maskAnnot ->
  assertion ->  Prop :=

  | VarAssignmentRule stk mask v lv e lexpr :
    trnsl_expr_lExpr stk e = Some lexpr ->
    fresh_lvar stk lv ->
    RavenHoareTriple 
      (LStack stk) 
        (Assign v e) mask 
      (LExists lv 
        (LAnd 
          (LStack (<[v := lv]> stk))
          (LExprA (LBinOp EqOp (LVar lv) lexpr))
        )
      )
    
  
  | HeapReadRule stk mask x e val fld lexpr_e lvar_x  :
    trnsl_expr_lExpr stk e = Some lexpr_e ->
    fresh_lvar stk lvar_x ->
    RavenHoareTriple 
      (LAnd (LStack stk) (LOwn lexpr_e fld val))  
        (FldRd x e fld) mask
      (LExists lvar_x (LAnd 
        (LStack (<[x := lvar_x]> stk)) 
        (LAnd 
          (LOwn lexpr_e fld val) 
          (LExprA (LBinOp EqOp (LVar lvar_x) (LVal val)))
        )
      ))

  | HeapWriteRule stk mask v fld e old_val new_val lv :
    stk !! v = Some lv ->
    trnsl_expr_lExpr stk e = Some (LVal new_val) ->
    RavenHoareTriple
      (LAnd (LStack stk) (LOwn (LVar lv) fld old_val))
        (FldWr v fld e) mask
      (LAnd (LStack stk) (LOwn (LVar lv) fld new_val))
  
    
  | HeapAllocRule stk mask x fld_vals lvar_x :
    fresh_lvar stk lvar_x ->
    RavenHoareTriple
       (LStack stk) 
        (Alloc x fld_vals) mask
      (LExists lvar_x (LAnd (LStack (<[x := lvar_x]> stk)) (field_list_to_assertion (LVar lvar_x) fld_vals)))

  | ProcCallRuleRet stk mask x proc_name args lexprs lvar_x proc_record :
    fresh_lvar stk lvar_x ->
    proc_map !! proc_name = Some proc_record ->
    length args = length proc_record.(proc_args) ->
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    let subst_map := list_to_map (zip proc_record.(proc_args) lexprs) in
    RavenHoareTriple
      (LAnd (LStack stk) (subst proc_record.(proc_precond) subst_map))
        (Call x proc_name args) mask
      (LExists lvar_x (LAnd (LStack (<[x := lvar_x]> stk)) (subst proc_record.(proc_postcond) (<[ proc_record.(ret_var) := LVar lvar_x]> subst_map)))) 

  | SequenceRule mask a1 c1 a2 c2 a3 :
    RavenHoareTriple
      a1 
        c1 mask
      a2
    ->
    RavenHoareTriple
      a2
        c2 mask
      a3
    ->
    RavenHoareTriple
      a1 
        (Seq c1 c2) mask
      a3

  | CondRule stk1 stk2 mask e s1 s2 p q lexpr :
    trnsl_expr_lExpr stk1 e = Some lexpr ->
    RavenHoareTriple
      (LAnd (LStack stk1) (LAnd p (LExprA (lexpr))) )
        s1 mask
      (LAnd (LStack stk2) q)
    ->
    RavenHoareTriple
      (LAnd (LStack stk1) (LAnd p (LExprA (LUnOp NotBoolOp lexpr))))
        s2 mask
      (LAnd (LStack stk2) q)
    ->
    RavenHoareTriple
      (LAnd (LStack stk1) p) 
        (IfS e s1 s2) mask
      (LAnd (LStack stk2) q)

  | InvAccessBlockRule stk mask inv args stmt inv_record p q lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    inv ∈ mask ->
    inv_map !! inv = Some inv_record ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple
      (LAnd (LStack stk) (LAnd (subst inv_record.(inv_body) subst_map) p)) 
        stmt (mask ∖ {[inv]})
      (LAnd (LStack stk) (LAnd (subst inv_record.(inv_body) subst_map) q))  ->
    
    RavenHoareTriple
      (LAnd (LStack stk) (LAnd (LInv inv lexprs) p)) 
        (InvAccessBlock inv args stmt ) mask
      (LAnd (LStack stk) (LAnd (LInv inv lexprs) q))

  (* | InvUnfoldRule stk  mask1 inv args inv_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    match i1, i2 with
      | Closed, Opened s => s = [ (inv, lexprs) ]
      | Opened s1, Opened s2 => s2 = (inv, lexprs) :: s1
      | Stepped s1, Stepped s2 => s2 = (inv, lexprs) :: s1
      | _, _ => False
    end
    ->
    inv ∈ mask1 ->
    inv_map !! inv = Some inv_record ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple
      stk (LInv inv lexprs) (mask1, i1)
        (UnfoldInv inv args) 
      stk (subst inv_record.(inv_body) subst_map) (mask1 ∖ {[inv]}, i2) *)

  (* | InvFoldRule stk  mask1 inv args inv_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    match i1, i2 with
    | Opened s, Closed => s = [ (inv, lexprs) ]
    | Stepped s, Closed => s = [ (inv, lexprs) ]
    | Opened s1, Opened s2 => s1 = (inv, lexprs) :: s2 /\ ¬(s2 = [])
    | Stepped s1, Stepped s2 => s1 = (inv, lexprs) :: s2 /\ ¬(s2 = [])
    | _, _ => False
    end
    ->
    inv ∉ mask1 ->
    inv_map !! inv = Some inv_record ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple
      stk (subst inv_record.(inv_body) subst_map) (mask1, i1)
        (UnfoldInv inv args) 
      stk (LInv inv lexprs) (mask1 ∪ {[inv]}, i2) *)

  | PredUnfoldRule stk mask pred args pred_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    pred_map !! pred = Some pred_record ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple
      (LAnd (LStack stk) (LPred pred lexprs)) 
        (UnfoldPred pred args) mask
      (LAnd (LStack stk) (subst pred_record.(pred_body) subst_map))

  | PredFoldRule stk mask pred args pred_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    pred_map !! pred = Some pred_record ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple
      (LAnd (LStack stk) (subst pred_record.(pred_body) subst_map)) 
        (FoldPred pred args) mask
      (LAnd (LStack stk) (LPred pred lexprs))

  | FPURule stk mask e l_expr fld RAPack old_val new_val :
    trnsl_expr_lExpr stk e = Some l_expr ->
    (RAPack.(RA_inst) ).(fpuValid) old_val new_val = true ->
    RavenHoareTriple
      (LAnd (LStack stk) (LGhostOwn l_expr fld RAPack old_val))
        (Fpu e fld RAPack old_val new_val) mask
        (LAnd (LStack stk) (LGhostOwn l_expr fld RAPack new_val))

  | FrameRule mask s p q r :
    RavenHoareTriple
      p
        s mask
      q
    ->
    RavenHoareTriple
      (LAnd p r)
        s mask
      (LAnd q r)
  
  | WeakeningRule mask p p' q q' c :
    RavenHoareTriple 
      p 
        c mask
      q
    ->
    entails p' p ->
    entails q q' ->

    RavenHoareTriple 
      p'
        c mask
      q'

  | SkipRule stk mask p :
    RavenHoareTriple
      (LAnd (LStack stk) p) 
        SkipS mask
      (LAnd (LStack stk) p)

  | CASSuccRule stk mask v e1 fld e2 e3 lvar_v lexpr1 old_val new_val :
    fresh_lvar stk lvar_v ->
    trnsl_expr_lExpr stk e1 = Some lexpr1 ->
    trnsl_expr_lExpr stk e2 = Some (LVal old_val) ->
    trnsl_expr_lExpr stk e3 = Some (LVal new_val) 
    ->
      RavenHoareTriple
        (LAnd (LStack stk) (LOwn lexpr1 fld old_val))
          (CAS v e1 fld e2 e3) mask
        (LExists lvar_v (LAnd (LStack (<[v := lvar_v]> stk)) (LAnd (LOwn lexpr1 fld new_val) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool true)))))) )

  | CASFailRule stk mask v e1 fld e2 e3 lvar_v lexpr1 old_val old_val2 :
    fresh_lvar stk lvar_v ->
    trnsl_expr_lExpr stk e1 = Some lexpr1 ->
    trnsl_expr_lExpr stk e2 = Some (LVal old_val2)
    ->
      RavenHoareTriple
        (LAnd (LStack stk) (LAnd (LOwn lexpr1 fld old_val) (LExprA (LUnOp NotBoolOp (LBinOp EqOp (LVal old_val) (LVal old_val2))))))
          (CAS v e1 fld e2 e3) mask
        (LExists lvar_v (LAnd (LStack (<[v := lvar_v]> stk)) (LAnd (LOwn lexpr1 fld old_val) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool false)))))))
  .

End RavenLogic.

Section LExpr_embed.
  (* TODO: Figure out the right way to do this deep embedding *)
  Definition EqOp_refl : forall a b mp, LExpr_holds (LBinOp EqOp a b) mp -> LExpr_holds (LBinOp EqOp b a) mp.
  Proof.
    intros.
    unfold LExpr_holds.
    destruct (interp_lexpr (LBinOp EqOp b a) mp) eqn: H0; try done.
  Admitted.
   (* rewrite H0 in H. rewrite H1 in H. rewrite H. reflexivity. *)
  (* Qed. *)



  Definition EqOp_trans : forall a b c mp, LExpr_holds (LBinOp EqOp a b) mp -> LExpr_holds (LBinOp EqOp b c) mp -> LExpr_holds (LBinOp EqOp a c) mp.
  Proof.
    Admitted.

  Definition EqOp_subst : forall var le e mp, LExpr_holds (LBinOp EqOp (LVar var) le) mp -> LExpr_holds e mp -> LExpr_holds (lexpr_subst e (<[ var := le]> ∅)) mp.
  Proof.
    Admitted.

  Definition EqpOp_LVal : forall v1 v2 mp, LExpr_holds (LBinOp EqOp (LVal v1) (LVal v2)) mp -> v1 = v2.
  Proof.
    Admitted.

End LExpr_embed.