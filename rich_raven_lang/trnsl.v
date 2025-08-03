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
  
    Definition sym_stk_eq_stk_frm (stk : stack) (stk_frm : stack_frame) : Prop :=
      (forall (x : var) (le : LExpr), (stk !! x = Some le) -> (∃ (v : lang.val),  (stk_frm.(locals) !! x = Some v) /\ (LExpr_holds (LBinOp EqOp le (LVal (trnsl_val v)))))) /\
      
      (forall (x : var) (v : lang.val), (stk_frm.(locals) !! x = Some v) -> (∃ (le : LExpr), (stk !! x = Some le) /\ (LExpr_holds (LBinOp EqOp le (LVal (trnsl_val v)))))).

    Lemma sym_stk_eq_stk_frm_func (stk : stack) (stk_frm1 : stack_frame) (stk_frm2 : stack_frame) :
      sym_stk_eq_stk_frm stk stk_frm1 ->
      sym_stk_eq_stk_frm stk stk_frm2 ->
      stk_frm1 = stk_frm2.
    Proof.
      intros H1 H2.
      destruct stk_frm1 as [locals1 ].
      destruct stk_frm2 as [locals2 ].
      f_equal.
      apply map_eq .

      destruct H1 as [H1f H1b].

      intros i.

      destruct (locals1 !! i) eqn: Hstkfrm1i.
      - specialize (H1b i v Hstkfrm1i).
        destruct H1b as [le [Hstki HLexprH]].

        destruct H2 as [H2f H2b].
        specialize (H2f i le Hstki).
        destruct H2f as [v' [Hstkfrm2i HLexprH2]].
        apply EqOp_refl in HLexprH.
        pose proof (EqOp_trans _ _ _ HLexprH HLexprH2) as HE.
        pose proof (EqpOp_LVal _ _ HE) as HE2.
        apply trnsl_val_inj in HE2.
        subst v'.
        simpl in Hstkfrm2i. done.
      
      - destruct (stk !! i) eqn: Hstk1i.
        + specialize (H1f _ _ Hstk1i).
          destruct H1f as [v [Hstkfrm1]].
          simpl in Hstkfrm1.
          rewrite Hstkfrm1 in Hstkfrm1i.
          inversion Hstkfrm1i.

        + destruct (locals2 !! i) eqn: Hstkfrm2i.
          * destruct H2 as [H2f H2b].
            specialize (H2b _ _ Hstkfrm2i).
            destruct H2b as [le' [Hstk2i _]].
            rewrite Hstk1i in Hstk2i.
            inversion Hstk2i.
          * done.
    Qed.


    Definition trnsl_hoare_triple (stk : stack) (stk_frm : stack_frame) (stk_id: stack_id) (p : assertion) (a1 : AtomicAnnotation) (cmd : stmt) (stk' : stack) (stk_frm' : stack_frame) (q : assertion) (a2 : AtomicAnnotation) : iProp rrl_lang.Σ :=
        match (trnsl_stmt cmd stk), (trnsl_assertion p), (trnsl_assertion q) with
        | Error, _, _ | _, None, _ | _, _, None => True
        | None', Some p', Some q' => 
          (p' ∗ trnsl_atomic_annotation (inv_set_to_namespace a1.1) a1) -∗ |={(inv_set_to_namespace a1.1), (inv_set_to_namespace a2.1) }=> (q' ∗ trnsl_atomic_annotation (inv_set_to_namespace a2.1) a2)
        | Some' s, Some p', Some q' => 
          ⌜sym_stk_eq_stk_frm stk stk_frm⌝ -∗
          ⌜sym_stk_eq_stk_frm stk' stk_frm'⌝ -∗
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
        { inversion Ht. } 

        inversion Ht. simpl. 
        destruct (trnsl_lval old_val); destruct (trnsl_lval new_val); simpl; iIntros; try done.
        - iIntros (Φ). iModIntro.
        iIntros "[Hstk1 Hstk2] HΦ".

        iDestruct "Hstk1" as "[%l [%Hlexpr1 Hlfld]]".
        
        iApply (wp_heap_wr stk_id stk_frm _ _ _ l _ _ with "[Hstk2 Hlfld]").


        2: {
          iModIntro. iIntros "[HstkO Hlpt]".
          iApply "HΦ". iFrame.
          iSplitR. { iPureIntro. done. }
          pose proof (sym_stk_eq_stk_frm_func _ _ _ H2 H4). subst stk_frm'. iFrame.
        }
        
        1: {
          iFrame.
          admit.
        }
  
    Admitted.
    
  
  
  End MainTranslation.