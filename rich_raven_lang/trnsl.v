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
  
    Definition sym_stk_eq_stk_frm (stk : stack) (stk_frm : stack_frame) (mp : symb_map): Prop :=
      (forall (x : var) (lv : lvar), (stk !! x = Some lv) -> (∃ (v : lang.val),  (stk_frm.(locals) !! x = Some v) /\ (LExpr_holds (LBinOp EqOp (LVar lv) (LVal (trnsl_val v))) mp))) /\
      
      (forall (x : var) (v : lang.val), (stk_frm.(locals) !! x = Some v) -> (∃ (lv : lvar), (stk !! x = Some lv) /\ (LExpr_holds (LBinOp EqOp (LVar lv) (LVal (trnsl_val v))) mp))).

    Lemma sym_stk_eq_stk_frm_func (stk : stack) (stk_frm1 : stack_frame) (stk_frm2 : stack_frame) (mp : symb_map) :
      sym_stk_eq_stk_frm stk stk_frm1 mp ->
      sym_stk_eq_stk_frm stk stk_frm2  mp->
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
        pose proof (EqOp_trans _ _ _ _ HLexprH HLexprH2) as HE.
        pose proof (EqpOp_LVal _ _ _ HE) as HE2.
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

    Definition symb_stk_to_stk_frm (stk : stack) (mp : symb_map) : stack_frame :=
      StackFrame (fmap (λ v, trnsl_lval (mp v)) stk).

    Lemma trnsl_expr_interp_lexpr_compatibility stk e lv mp : trnsl_expr_lExpr stk e = Some (LVal lv) -> expr_step e (symb_stk_to_stk_frm stk mp) (Val (trnsl_lval lv)).
    Admitted.

    Definition trnsl_hoare_triple (stk : stack) (stk_id: stack_id) (p : assertion) (msk1 : maskAnnot) (cmd : stmt) (stk' : stack) (q : assertion) (msk2 : maskAnnot) (mp : symb_map) : iProp rrl_lang.Σ :=
        match (trnsl_stmt cmd) with 
        | Error => True
        | None' =>
          match (trnsl_assertion p mp), 
                (trnsl_assertion q mp) with
          | None, _ | _, None => True
          | Some p', Some q' =>
            p' ∗ stack_own[ stk_id, symb_stk_to_stk_frm stk mp ] -∗ (q' ∗ stack_own[ stk_id, symb_stk_to_stk_frm stk' mp])
          end
        
        | Some' s =>
          match (trnsl_assertion p mp), 
                (trnsl_assertion q mp) with
          | None, _ | _, None => True
          | Some p', Some q' => 
            {{{ p' ∗ stack_own[ stk_id, symb_stk_to_stk_frm stk mp ] }}}  
              to_rtstmt stk_id s 
            {{{ RET lang.LitUnit; q' ∗ stack_own[ stk_id, symb_stk_to_stk_frm stk' mp] }}}
          end
        end
    .
  
    Theorem rrl_validity stk stk_id p msk1 cmd stk' q msk2 :
      forall mp, RavenHoareTriple stk p msk1 cmd stk' q msk2 ->
      ⊢ (trnsl_hoare_triple stk stk_id p msk1 cmd stk' q msk2 mp).
    Proof.
      intros mp H.
      destruct H as 
      [ | 
      | stk mask v fld e old_val new_val lv Hatm HLexpr1 
      | | | | | | | | | | | | | ].
      3: {
        unfold trnsl_hoare_triple.
        destruct (trnsl_stmt (FldWr v fld e)) eqn:Ht. 2: done.
        { inversion Ht. } 

        inversion Ht. simpl. 
        (* destruct (trnsl_lval old_val); destruct (trnsl_lval new_val); simpl; iIntros; try done. *)
        - iIntros (Φ). iModIntro.
        iIntros "[Hstk1 Hstk2] HΦ".

        iDestruct "Hstk1" as "[%l [%Hlexpr1 Hlfld]]".
        
        iApply (wp_heap_wr stk_id (symb_stk_to_stk_frm stk mp) _ _ _ l _ _ with "[Hstk2 Hlfld]").
        
        {
          iFrame.
          iSplit.
          { iPureIntro. simpl. rewrite lookup_fmap. 
            (* rewrite HLexpr. simpl. apply f_equal.  *)
            rewrite Hatm. simpl. rewrite Hlexpr1. simpl. apply f_equal. 

            destruct l. simpl. done. 
          }

          { iPureIntro. apply trnsl_expr_interp_lexpr_compatibility. done. }
        }

        {
          iModIntro. iIntros "[HstkO Hlpt]".
          iApply "HΦ". iFrame.
          iPureIntro. done.
        }
  
    Admitted.
    
  
  
  End MainTranslation.