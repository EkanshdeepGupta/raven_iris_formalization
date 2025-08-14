From stdpp Require Export binders strings.
From stdpp Require Import countable.
From stdpp Require Export namespaces.
From stdpp Require Import gmap list sets.

From iris Require Import options.
From iris.algebra Require Import cmra.
From iris.bi Require Import derived_laws.
From iris.base_logic Require Import upred.
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

    Definition symb_stk_to_stk_frm (stk : stack) (mp : symb_map) : stack_frame :=
      StackFrame (fmap (λ v, trnsl_lval (mp v)) stk).

    Lemma trnsl_expr_interp_lexpr_compatibility stk e lexpr lv mp : trnsl_expr_lExpr stk e = Some (lexpr) -> interp_lexpr lexpr mp = Some lv -> expr_step e (symb_stk_to_stk_frm stk mp) (Val (trnsl_lval lv)).
    Admitted.

    Definition trnsl_hoare_triple (stk : stack) (stk_id: stack_id) (p : assertion) (msk1 : maskAnnot) (cmd : stmt) (stk' : stack) (q : assertion) (msk2 : maskAnnot) (mp : symb_map) : iProp rrl_lang.Σ :=
        match (trnsl_stmt cmd) with 
        | Error => True
        | None' =>
          match (trnsl_assertion p mp), 
                (trnsl_assertion q mp) with
          | None, _ | _, None => True
          | Some p', Some q' =>
            p' ∗ stack_own[ stk_id, symb_stk_to_stk_frm stk mp ] ={inv_set_to_namespace msk1}=∗ (q' ∗ stack_own[ stk_id, symb_stk_to_stk_frm stk' mp])
          end
        
        | Some' s =>
          match (trnsl_assertion p mp), 
                (trnsl_assertion q mp) with
          | None, _ | _, None => True
          | Some p', Some q' => 
            {{{ p' ∗ stack_own[ stk_id, symb_stk_to_stk_frm stk mp ] }}}  
              to_rtstmt stk_id s @ (inv_set_to_namespace msk1)
            {{{ RET lang.LitUnit; q' ∗ stack_own[ stk_id, symb_stk_to_stk_frm stk' mp] }}}
          end
        end
    .
  
    Theorem rrl_validity stk stk_id p msk1 cmd stk' q msk2 :
      forall mp, ⌜RavenHoareTriple stk p msk1 cmd stk' q msk2⌝
      ⊢ (trnsl_hoare_triple stk stk_id p msk1 cmd stk' q msk2 mp).
    Proof.
      iIntros (mp) "%H". 
      iInduction H as 
      [ | 
      | stk mask v fld e old_val new_val lv Hatm HLexpr1 
      | | | | 
      | stk mask invr args stmt inv_record p q lexprs Hargs Hinv_mask Hinv_record subst Hbody IHHbody
      | | | | | | | | ] "IH".
      3: {
        unfold trnsl_hoare_triple.
        simpl.
        destruct (trnsl_stmt (FldWr v fld e)) eqn:Ht. 2: done.
        { inversion Ht. } 

        inversion Ht. simpl. 
        (* destruct (trnsl_lval old_val); destruct (trnsl_lval new_val); simpl; iIntros; try done. *)
        - iIntros (Φ). iModIntro.
        iIntros "[Hstk1 Hstk2] HΦ".

        iDestruct "Hstk1" as "[%l [%Hlexpr1 Hlfld]]".
        
        iApply (wp_heap_wr stk_id (symb_stk_to_stk_frm stk mp) _ _ _ l _ _ _ with "[Hstk2 Hlfld]").
        
        {
          iFrame.
          iSplit.
          { iPureIntro. simpl. rewrite lookup_fmap. 
            (* rewrite HLexpr. simpl. apply f_equal.  *)
            rewrite Hatm. simpl. unfold LExpr_holds in Hlexpr1. simpl in Hlexpr1. injection Hlexpr1 as Hlv. 
            destruct (val_beq (mp lv) (LitLoc l)) eqn:Hlv'.
            - apply f_equal.
            apply internal_val_dec_bl in Hlv'.
            rewrite Hlv'. simpl. apply f_equal. 

            destruct l. simpl. done.
            - inversion Hlv. 
          } 


          { iPureIntro. apply (trnsl_expr_interp_lexpr_compatibility _ _ (LVal new_val)). { done. } done. }
        }

        {
          iModIntro. iIntros "[HstkO Hlpt]".
          iApply "HΦ". iFrame.
          iPureIntro. done.
        }

      }

      7: {
        unfold trnsl_hoare_triple.

        pose proof (trnsl_inv_validity invr lexprs mp) as Htrnsl_inv_valid.
        rewrite Hinv_record in Htrnsl_inv_valid. simpl in Htrnsl_inv_valid.
        destruct (trnsl_assertion (rrl_lang.subst (inv_body inv_record)
        subst) mp) eqn:HinvBody. 2:{ rewrite HinvBody in Htrnsl_inv_valid. inversion Htrnsl_inv_valid. }

        rewrite HinvBody in Htrnsl_inv_valid. injection Htrnsl_inv_valid as Htrnsl_inv.
        
        destruct (trnsl_stmt (InvAccessBlock invr args stmt)) eqn:Ht. 2: done.

        
        { 
          simpl. rewrite Hinv_record. 
           destruct (trnsl_assertion p mp) eqn:Hp, (trnsl_assertion q mp) eqn:Hq; try done.
           iIntros "[[#H Hu] Hstk]".
           (* unfold trnsl_hoare_triple in IH. *)
           assert (trnsl_stmt stmt = None'). { admit. }
           iEval (rewrite H HinvBody) in "IH".
           (* rewrite Hp Hq in IHHbody. *)

          iInv "H" as "Hinv".
          { 
            (* inv_namespace mask *)
            admit.
          }
          rewrite <- Htrnsl_inv.

          assert (Timeless u). { admit. }
          iDestruct "Hinv" as ">Hinv".
          iCombine "Hinv Hu" as "Hcomb1".
          iCombine "Hcomb1 Hstk" as "Hcomb2".
          (* Unset Printing Notations. *)
          (* iPoseProof IHHbody as "Htriple". *)
          
          iPoseProof ("IH" with "Hcomb2") as "IH2".
          iFrame.
          assert ((inv_set_to_namespace (mask ∖ {[invr]})) = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr). { admit. }
          rewrite H1.
          iDestruct "IH2" as ">IH2".
          iDestruct "IH2" as "[[IHH1 IHH] IHs]".
          iModIntro.
          iFrame "# ∗". done.

          (* pose proof (trnsl_inv_validity invr lexprs mp) as Htrnsl_inv_valid. *)
        }
        
        { 
          assert (trnsl_stmt stmt = Some' s). { admit. }
          simpl.
          iEval (rewrite H HinvBody) in "IH" .
          iEval (rewrite Hinv_record).
          destruct (trnsl_assertion p mp) eqn:Hp, (trnsl_assertion q mp) eqn:Hq; try done.
          iIntros (Φ).
          iModIntro.
          iIntros "[[#HInv Hu] Hstk] HΦ".
          rewrite <- Htrnsl_inv.
          
          assert (Timeless u). { admit. }
          iInv "HInv" as ">HInvBody".
          { 
            (* namespace *) admit.
          }

          {
            (* atomicity *) admit. 
          }

          iCombine "HInvBody" "Hu" as "Hcomb1".
          iCombine "Hcomb1" "Hstk" as "Hcomb2".
          
          assert (inv_set_to_namespace (mask ∖ {[invr]}) = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr). { admit. }
          rewrite H1; destruct H1.

          iApply ("IH" with "Hcomb2").
          iNext.
          iIntros "[[Hu Hu1] Hstk]".
          iModIntro.
          iFrame.
          iApply "HΦ".
          iFrame "# ∗".
        }
      }

      (* 1 : {
        unfold trnsl_hoare_triple. simpl.

        iIntros (Φ).
        iModIntro.
        iIntros "[_ Hstk] HΦ".

        iApply (wp_assign stk_id (symb_stk_to_stk_frm stk mp) v (trnsl_lval (mp v2)) e with "[Hstk]").

        {
          iFrame.
          iPureIntro.
          apply (trnsl_expr_interp_lexpr_compatibility _ _ lexpr). { done. } 

        }
        


      } *)
  
    Admitted.
  
  End MainTranslation.