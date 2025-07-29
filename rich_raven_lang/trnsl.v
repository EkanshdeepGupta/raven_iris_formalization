From stdpp Require Export binders strings.
From stdpp Require Import countable.
From stdpp Require Export namespaces.
From stdpp Require Import gmap list sets.

From iris Require Import options.
From iris.algebra Require Import cmra.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import ghost_map.
From iris.base_logic.lib Require Import invariants.

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.

From raven_iris.simp_raven_lang Require Import lang lifting ghost_state.
From raven_iris.rich_raven_lang Require Import rrl_lang.


(* Context `{!simpLangG Σ}. *)


Section MainTranslation.
    (* Context `{!simpLangG Σ}. *)
  
    Program Fixpoint trnsl_atomic_annotation (mask: coPset) (a : AtomicAnnotation) {measure match a.2 with | Closed => 0 | Opened s => length s | Stepped s => length s end} : iProp rrl_lang.Σ :=
      match a.2 with
      | Closed => True
      | Opened [] => False
      | Stepped [] => False
      | Opened (inv :: invs) => True ∗ trnsl_atomic_annotation (mask ∪ ↑(inv_namespace_map inv.1)) (a.1, Opened invs)
  
      | Stepped (inv :: invs) => True ∗ trnsl_atomic_annotation (mask ∪ ↑(inv_namespace_map inv.1)) (a.1, Stepped invs)
      end
      .
      Next Obligation.
      intros. simpl; subst filtered_var; rewrite <- Heq_anonymous. simpl; lia.
      Qed.
      Next Obligation.
      intros. simpl; subst filtered_var; rewrite <- Heq_anonymous. simpl; lia.
      Qed.
      Next Obligation.
      intros. simpl. Admitted.
  
  
    Definition inv_set_to_namespace (s : gset inv_name) : coPset :=
      set_fold (λ inv acc, acc ∪ ↑(inv_namespace_map inv)) ∅ s.

      (* Check Σ. *)
  
  
    (* Definition stack_to_stack_frame (stk : stack) : stack_frame := 
    . *)
  
    Definition trnsl_hoare_triple (stk : stack) (stk_frm : stack_frame) (stk_id: stack_id) (p : l_assertion) (a1 : AtomicAnnotation) (cmd : stmt) (stk' : stack) (stk_frm' : stack_frame) (q : l_assertion) (a2 : AtomicAnnotation) : iProp rrl_lang.Σ :=
        match (trnsl_stmt cmd stk), (trnsl_assertions p), (trnsl_assertions q) with
        | Error, _, _ | _, None, _ | _, _, None => True
        | None', Some p', Some q' => 
          (p' ∗ trnsl_atomic_annotation (inv_set_to_namespace a1.1) a1) -∗ |={(inv_set_to_namespace a1.1), (inv_set_to_namespace a2.1) }=> (q' ∗ trnsl_atomic_annotation (inv_set_to_namespace a2.1) a2)
        | Some' s, Some p', Some q' => 
          (* forall (x : Var), trnsl_expressions (stk)-> *)
          {{{ p' ∗ stack_own[ stk_id, stk_frm ] }}}  to_rtstmt stk_id s  {{{ RET lang.LitUnit; q' ∗ stack_own[ stk_id, stk_frm' ] }}}
        end
    .
  
    Theorem rrl_validity stk stk_frm stk_id p a1 cmd stk' stk_frm' q a2 :
      RavenHoareTriple stk p a1 cmd stk' q a2 ->
      ⊢ (trnsl_hoare_triple stk stk_frm stk_id p a1 cmd stk' stk_frm' q a2).
    Proof.
      intros H.
      destruct H as [ | | | | | | | | | | | | | | | | ].
      3: {
        unfold trnsl_hoare_triple.
        destruct (trnsl_stmt (FldWr e1 fld e2) stk) eqn:Ht. 2:{done. }
        - inversion Ht. simpl.
          destruct (trnsl_ravenExpr_lExpr stk e1); try done.
          destruct (trnsl_ravenExpr_lExpr stk e2); try done.
          destruct (trnsl_expressions l); try done.
          destruct (trnsl_expressions l0); try done.
        
        -
          destruct (trnsl_assertions (LOwn lexpr1 fld old_val)) eqn:HOldV; try done.
          destruct (trnsl_assertions (LOwn lexpr1 fld new_val)) eqn:HNewV; try done.
        inversion Ht.
          destruct (trnsl_ravenExpr_lExpr stk e1) eqn:He1; try done.
          destruct (trnsl_ravenExpr_lExpr stk e2) eqn:He2; try done.
          destruct (trnsl_expressions l); try done.
          destruct (trnsl_expressions l0); try done.
          inversion H3; subst. simpl. destruct H3.
  
          (* iApply wp_heap_wr.
          iModIntro.
  
  
  
        destruct (trnsl_val old_val). 2:{ simpl. iIntros "[F _]". iExFalso. iFrame. }
        iIntros  "[Hl HAtm]". 
      } *)
  
  
    Admitted.
    
  
  
  End MainTranslation.