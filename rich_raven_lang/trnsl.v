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

    (* Definition symb_stk_to_stk_frm (stk : stack) (mp : symb_map) : stack_frame :=
      StackFrame (fmap (λ v, trnsl_lval (mp v)) stk). *)

    Lemma trnsl_expr_interp_lexpr_compatibility stk e lexpr lv mp : 
      trnsl_expr_lExpr stk e = Some (lexpr) -> 
      interp_lexpr lexpr mp = Some lv -> 
      expr_step e (symb_stk_to_stk_frm stk mp) (Val (trnsl_lval lv)).
    Admitted.

    Definition trnsl_hoare_triple (stk_id: stack_id) (p : assertion) (msk : maskAnnot) (cmd : stmt) (q : assertion) (mp : symb_map) : iProp rrl_lang.Σ :=
        match (trnsl_stmt cmd) with 
        | Error => True
        | None' =>
          match (trnsl_assertion p stk_id mp), 
                (trnsl_assertion q stk_id mp) with
          | None, _ | _, None => True
          | Some p', Some q' =>
            p'={inv_set_to_namespace msk}=∗ q'
          end
        
        | Some' s =>
          match (trnsl_assertion p stk_id mp), 
                (trnsl_assertion q stk_id mp) with
          | None, _ | _, None => True
          | Some p', Some q' => 
            {{{ p' }}}  
              to_rtstmt stk_id s @ (inv_set_to_namespace msk)
            {{{ RET lang.LitUnit; q' }}}
          end
        end
    .

    Lemma fresh_var_trnsl_expr_invariant stk lv e lexpr mp v0: 
      fresh_lvar stk lv -> 
      trnsl_expr_lExpr stk e = Some lexpr ->
       interp_lexpr lexpr mp = interp_lexpr lexpr (λ x : lvar, if (x =? lv)%string then v0 else mp x).
    Proof.
      Admitted. 

    Lemma lexpr_holds_interp_compat lexpr v1 mp v:
      LExpr_holds (LBinOp EqOp lexpr (LVal v1)) mp ->
      interp_lexpr lexpr mp = Some v ->
      v = v1.
    Proof.
      intros H1 H2.
      unfold LExpr_holds in H1.
      simpl in H1. rewrite H2 in H1. injection H1 as H1.
      destruct (val_beq v v1) eqn:Hvb.
      - apply internal_val_dec_bl in Hvb. done.
      - inversion H1.
    Qed.



    Lemma val_beq_refl (v : val) : val_beq v v = true.
    Proof.
      Admitted.

    Lemma val_beq_eq (v1 : val) (v2 : val) : val_beq v1 v2 = true -> v1 = v2.
    Proof.
      Admitted.

    Lemma val_beq_neq v1 v2 : val_beq v1 v2 = false -> v1 ≠ v2.
    Proof.
      Admitted.

    Lemma expr_interp_well_defined stk e mp lexpr: 
      trnsl_expr_lExpr stk e = Some lexpr -> 
      interp_lexpr lexpr mp = None -> 
      not (expr_well_defined e).
    Admitted.

    Lemma fresh_mp_rewrite_LExpr_holds stk lv e lexpr mp v0 : 
      fresh_lvar stk lv -> 
      trnsl_expr_lExpr stk e = Some lexpr -> 
      interp_lexpr lexpr mp = Some v0 -> 
      LExpr_holds (LBinOp EqOp (LVar lv) lexpr)
        (λ x : lvar, if (x =? lv)%string then v0 else mp x).
    Proof. intros Hfresh Htrnsl Hinterp.
      set (mp' := (λ x : lvar, if (x =? lv)%string then v0 else mp x)).
      (* assert (interp_lexpr (LVar lv)) *)
      unfold LExpr_holds. simpl. 
      assert (mp' lv = v0). { subst mp'. simpl. rewrite String.eqb_refl. reflexivity. }
      rewrite H.
      rewrite (fresh_var_trnsl_expr_invariant _ _ _ _ _ v0 Hfresh Htrnsl) in Hinterp.
      rewrite Hinterp. 

      assert (val_beq v0 v0 = true) as Hbeq. { apply val_beq_refl. }
      rewrite Hbeq.
      reflexivity.
    Qed.

    Lemma fresh_mp_rewrite_symb_stk_to_stk_frm_compat stk lvar_x x mp val:
      fresh_lvar stk lvar_x ->
        symb_stk_to_stk_frm (<[x:=lvar_x]> stk)
          (λ x0 : lvar, if (x0 =? lvar_x)%string then val else mp x0) =

          {| locals := <[x:=trnsl_lval val]> (locals (symb_stk_to_stk_frm stk mp))|} .
    Proof. intros Hfresh.
      unfold symb_stk_to_stk_frm. apply f_equal.
      apply map_eq.
      intros i.
      destruct (stk !! i) eqn:HstkI.
      - rewrite lookup_fmap. 
        destruct (String.eqb i x) eqn:H_i_x.
        + apply String.eqb_eq in H_i_x. subst i. simpl.
        rewrite lookup_insert. rewrite lookup_insert. simpl. rewrite String.eqb_refl. done.

        + assert (not (i = x)). { apply String.eqb_neq in H_i_x. done. }

        rewrite lookup_insert_ne. 
          2 : { intro Heq; subst i; contradiction. }

        rewrite lookup_insert_ne. 
          2 : { intro Heq; subst i; contradiction. }
        simpl. rewrite HstkI. simpl. rewrite lookup_fmap. rewrite HstkI. simpl. apply f_equal. apply f_equal.
        assert ((l =? lvar_x)%string = false).
          { unfold fresh_lvar in Hfresh.
        specialize (Hfresh i). rewrite HstkI in Hfresh. apply String.eqb_neq. intro H2. subst lvar_x. contradiction. }
        rewrite H0. done.

      - destruct (String.eqb i x) eqn:H_i_x.
        + apply String.eqb_eq in H_i_x. subst i.
        rewrite lookup_fmap. rewrite lookup_insert.
        rewrite lookup_insert. simpl. rewrite String.eqb_refl. done.
        + apply String.eqb_neq in H_i_x.
          simpl.
          rewrite lookup_fmap. rewrite lookup_insert_ne.
          2 : { intro Heq; subst i; contradiction. }
          rewrite lookup_fmap. rewrite HstkI. simpl.
          rewrite lookup_insert_ne.
          2 : { intro Heq; subst i; contradiction. }
          rewrite HstkI. simpl. done.
    Qed.

  
    Theorem rrl_validity stk_id p msk cmd q :
      stmt_well_defined cmd -> 
      forall mp, ⌜RavenHoareTriple p cmd msk q⌝
      ⊢ (trnsl_hoare_triple stk_id p msk cmd q mp).
    Proof.
      iIntros (Hwelldef mp) "%H". 
      iInduction H as 
      [ | 
      | stk mask v fld e old_val new_val lv Hatm HLexpr1 
      | | | | 
      | stk mask invr args stmt inv_record p q lexprs Hargs Hinv_mask Hinv_record subst Hbody IHHbody
      | | | | | | | | ] "IH".
      3: { 
        (* FIELD WRITE *)
        unfold trnsl_hoare_triple.
        simpl.
        destruct (trnsl_stmt (FldWr v fld e)) eqn:Ht. 2: done.
        { inversion Ht. } 

        inversion Ht. simpl. 
        (* destruct (trnsl_lval old_val); destruct (trnsl_lval new_val); simpl; iIntros; try done. *)
        - iIntros (Φ). iModIntro.
        iIntros "[Hstk1 Hstk2] HΦ".

        iDestruct "Hstk2" as "[%l [%Hlexpr1 Hlfld]]".
        
        iApply (wp_heap_wr stk_id (symb_stk_to_stk_frm stk mp) _ _ _ l _ _ _ with "[Hstk1 Hlfld]").
        
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
        (* INV ACCESS BLOCK *)
        unfold trnsl_hoare_triple.

        pose proof (trnsl_inv_validity invr lexprs stk_id mp) as Htrnsl_inv_valid.
        rewrite Hinv_record in Htrnsl_inv_valid. simpl in Htrnsl_inv_valid.
        destruct (trnsl_assertion (rrl_lang.subst (inv_body inv_record)
        subst) stk_id mp) eqn:HinvBody. 2:{ rewrite HinvBody in Htrnsl_inv_valid. inversion Htrnsl_inv_valid. }

        rewrite HinvBody in Htrnsl_inv_valid. injection Htrnsl_inv_valid as Htrnsl_inv.
        
        destruct (trnsl_stmt (InvAccessBlock invr args stmt)) eqn:Ht. 
        2: { done. }

        
        { 
          destruct (trnsl_assertion (LStack stk) stk_id mp) eqn:Hstack.
          2 : { simpl in Hstack. inversion Hstack. }

          simpl. rewrite HinvBody. rewrite Hinv_record.
           destruct (trnsl_assertion p stk_id mp) eqn:Hp, (trnsl_assertion q stk_id mp) eqn:Hq; try done.
           
           iIntros "[Hstk [#H Hu]]".
           (* unfold trnsl_hoare_triple in IH. *)
           assert (trnsl_stmt stmt = None'). { admit. }
           iEval (rewrite H) in "IH".
           (* rewrite Hp Hq in IHHbody. *)

          iInv "H" as "Hinv".
          { 
            (* inv_namespace mask *)
            admit.
          }
          rewrite <- Htrnsl_inv.

          assert (Timeless u). { admit. }
          iDestruct "Hinv" as ">Hinv".
          iCombine "Hstk Hinv Hu" as "Hcomb".
          inversion Hwelldef as [ | | | | | | | | | | | | | inv args' stmt' HInvSet HargsWellDef HBodywelldef | ]; subst stmt' args'.
          (* iCombine "Hcomb1 Hstk" as "Hcomb2". *)
          (* Unset Printing Notations. *)
          (* iPoseProof IHHbody as "Htriple". *)
          
          iPoseProof ("IH" with  "[%] Hcomb") as "IH2". { done. }
          iFrame.
          assert ((inv_set_to_namespace (mask ∖ {[invr]})) = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr) as HInvs. { admit. }
          rewrite HInvs.
          iDestruct "IH2" as ">IH2".
          iDestruct "IH2" as "[IHs [IHH1 IHH] ]".
          iModIntro.
          iFrame "# ∗". done.

          (* pose proof (trnsl_inv_validity invr lexprs mp) as Htrnsl_inv_valid. *)
        }
        
        { 
          assert (trnsl_stmt stmt = Some' s). { admit. }
          simpl.
          iEval (rewrite H HinvBody) in "IH" .
          iEval (rewrite Hinv_record).
          destruct (trnsl_assertion p stk_id mp) eqn:Hp, (trnsl_assertion q stk_id mp) eqn:Hq; try done.
          iIntros (Φ).
          iModIntro.
          iIntros "[Hstk [#HInv Hu]] HΦ".
          rewrite <- Htrnsl_inv.
          
          assert (Timeless u). { admit. }
          iInv "HInv" as ">HInvBody".
          { 
            (* namespace *) admit.
          }

          {
            (* atomicity *) admit. 
          }

          iCombine "Hstk HInvBody Hu" as "Hcomb".
          (* iCombine "Hcomb1"  as "Hcomb2". *)
          
          assert (inv_set_to_namespace (mask ∖ {[invr]}) = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr). { admit. }
          rewrite H1; destruct H1.

          inversion Hwelldef as [ | | | | | | | | | | | | | inv args' stmt' HInvSet HargsWellDef HBodywelldef | ]; subst stmt' args'.
          iApply ("IH" with "[%] Hcomb"). { done. }
          iNext.
          iIntros "[Hstk [Hu Hu1]]".
          iModIntro.
          iFrame.
          iApply "HΦ".
          iFrame "# ∗".
        }
      }

      1 : {
        (* ASSIGN *)
        unfold trnsl_hoare_triple. simpl.

        iIntros (Φ).
        iModIntro.
        iIntros "Hstk HΦ".

        destruct (interp_lexpr lexpr mp) eqn: Hlexpr.

        { iApply (wp_assign stk_id (symb_stk_to_stk_frm stk mp) v (trnsl_lval v0) e with "[Hstk]").

          {
            iFrame.
            iPureIntro.
            apply (trnsl_expr_interp_lexpr_compatibility _ _ lexpr). { done. } 

            done. 
          }
          
          iNext.
          iIntros "Hstk".
          iApply "HΦ".
          iExists (v0).
          iSplitL.
          {
            (* simpl. *)
            (unfold rrl_lang.symb_stk_to_stk_frm). simpl. unfold fresh_lvar in H0.
            assert (<[v:=trnsl_lval v0]> ((λ v1 : lvar, trnsl_lval (mp v1)) <$> stk)
                =
              (λ v1 : lvar, trnsl_lval (if (v1 =? lv)%string then v0 else mp v1)) <$>
                <[v:=lv]> stk).
              {
                apply map_eq.
                intros i.
                destruct (String.eqb i v) eqn:Hi.
                - apply String.eqb_eq in Hi; subst i.
                  simpl. rewrite lookup_insert. rewrite lookup_fmap. rewrite lookup_insert. simpl. rewrite String.eqb_refl. reflexivity.
                - apply String.eqb_neq in Hi.
                  rewrite lookup_insert_ne. 2:{ done. }
                  rewrite lookup_fmap.
                  rewrite lookup_fmap.
                  rewrite lookup_insert_ne; [|done].
                  destruct (stk !! i) as [x|] eqn:HstkI;  simpl; auto.
                  + assert (x ≠ lv). { specialize (H0 i). rewrite HstkI in H0. intros Heq. subst x. contradiction.
                  } simpl.
                  rewrite HstkI. simpl. f_equal. rewrite <- String.eqb_neq in H1. rewrite H1. auto.

                  + rewrite HstkI. simpl. done.
              } rewrite H1. done.

          }
          iPureIntro.

          apply (fresh_mp_rewrite_LExpr_holds stk lv e lexpr mp v0 H0 H Hlexpr).
        }

        pose proof (expr_interp_well_defined stk e mp lexpr H Hlexpr).
        inversion Hwelldef as [ | | | | | | | | | | | | | inv args' stmt' HInvSet HargsWellDef HBodywelldef | ].
        contradiction.
      }

      9 : {
        (* FRAME RULE *)
        iPoseProof ("IH" with  "[%]") as "IH2". { done. }
        iClear "IH".

        unfold trnsl_hoare_triple. simpl.
        destruct (trnsl_stmt s) eqn:Htrnsl; try done.
        { simpl.
          destruct (trnsl_assertion p stk_id mp) eqn:Hp, (trnsl_assertion q stk_id mp) eqn:Hq, (trnsl_assertion r stk_id mp) eqn:Hr; try done. 

          iIntros "[Hu Hu1]".
          iPoseProof ("IH2" with "Hu") as ">IH3". iModIntro; iFrame.

        }

        { destruct (trnsl_assertion p stk_id mp) eqn:Hp, (trnsl_assertion q stk_id mp) eqn:Hq, (trnsl_assertion r stk_id mp) eqn:Hr; try done.  
        
        iIntros (Φ).
        iModIntro. iIntros "[Hu Hu1] HΦ".
        iApply ("IH2" with "Hu").
        iNext. iIntros "Hu0". iApply "HΦ". iFrame.
        }
      }

      1 : {
        (* FIELD READ *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ). iModIntro. iIntros "[Hstk Hl] HΦ".
        iDestruct "Hl" as (l) "[%HLe_h H_l_hp]".

        destruct (interp_lexpr lexpr_e mp) eqn: Hinterp.

        2 : { apply (expr_interp_well_defined _ _ _ _ H) in Hinterp.
          inversion Hwelldef. contradiction.
        }

        pose proof (lexpr_holds_interp_compat _ _ _ _ HLe_h Hinterp) .
          subst v.

        iApply (wp_heap_rd stk_id (rrl_lang.symb_stk_to_stk_frm stk mp) fld e (trnsl_lval val) l x _ 1%Qp with "[Hstk H_l_hp]").

        

        {
          pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H Hinterp).
          iFrame.
          iPureIntro. 
          simpl in H1.
          assert (l = {| loc_car := loc_car l |}).
          { destruct l. simpl. done.  }
          rewrite H2. done. 
        }

        {
          iNext.
          iIntros "[Hstk Hhp]".
          iApply "HΦ".
          iExists val.

          iSplitL "Hstk".
          - pose proof 
          (fresh_mp_rewrite_symb_stk_to_stk_frm_compat stk lvar_x x mp val H0) as HstkOwnDone.
          rewrite HstkOwnDone. iFrame.

          - iSplitL.
            + iExists l. 
            iFrame; iPureIntro.
            pose proof (fresh_var_trnsl_expr_invariant stk lvar_x e _ mp val H0 H).
            unfold LExpr_holds.
            simpl. rewrite <- H1. apply HLe_h.
          
            + iPureIntro. unfold LExpr_holds. simpl. rewrite String.eqb_refl. rewrite val_beq_refl. done.
        }
      }

      1 : {
        (* ALLOC *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ).
        iModIntro.
        iIntros "Hstack HΦ".
        iApply (wp_alloc with "[Hstack]") .
        - iFrame.
        - iNext.
          iIntros "Hpost".
          iDestruct "Hpost" as (l) "[Hstk Hhp]".
          iApply "HΦ".
          iExists (LitLoc l).
          set (mp' := (λ x0 : lvar, if (x0 =? lvar_x)%string then LitLoc l else mp x0)).

          iInduction fld_vals as [ | ] "IH".
          
          + simpl. iFrame. rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done.
          unfold symb_stk_to_stk_frm. simpl. 
          assert (lang.LitLoc l = lang.LitLoc {| loc_car := loc_car l |}) as H0.
          {  destruct l. simpl. done. }
          rewrite <- H0. iFrame.

          + simpl. destruct a as [fld val].
          assert (stmt_well_defined (Alloc x fld_vals)) as Hwell_def'. { admit. }
          destruct (trnsl_assertion (field_list_to_assertion (LVar lvar_x) fld_vals) stk_id mp' ) eqn:Htrfl.
          
            * simpl. rewrite Htrfl.
            iPoseProof ("IH" with "[%]") as "IH2"; try done.
            iClear "IH".
            iDestruct "Hhp" as "[Hhpl Hhpfvs]".
            iPoseProof ("IH2" with "Hstk Hhpfvs") as "[IH3 IH3']". 
            iFrame. iExists l. 
            assert (trnsl_lval (trnsl_val val) = val) as H0. { admit. } 
            rewrite H0. iFrame.
            iPureIntro. 
            unfold LExpr_holds.
            simpl.
            subst mp'. simpl. rewrite String.eqb_refl. rewrite val_beq_refl. done.

            * simpl. rewrite Htrfl. iPoseProof ("IH" with "[%]") as "IH2"; try done. iClear "IH".
            iDestruct "Hhp" as "[Hhpl Hhp2]". 
            iApply ("IH2" with "Hstk Hhp2").  
      }


      4 : {
        (* UNFOLD PRED *)
        unfold trnsl_hoare_triple.
        simpl.
        pose proof (trnsl_pred_validity pred lexprs stk_id mp) as HPredTrnsl. rewrite H0 in HPredTrnsl. unfold subst_map in HPredTrnsl. rewrite HPredTrnsl.
        iIntros. iModIntro.  iFrame.

      }

      4 : {
        (* FOLD PRED *)
        unfold trnsl_hoare_triple.
        simpl.
        pose proof (trnsl_pred_validity pred lexprs stk_id mp) as HPredTrnsl. rewrite H0 in HPredTrnsl. unfold subst_map in HPredTrnsl. rewrite HPredTrnsl.
        iIntros. iModIntro.  iFrame.
      }

      2 : {
        (* SEQ *)
        inversion Hwelldef.
        iPoseProof ("IH" with "[%]") as "IH'"; try done.
        iPoseProof ("IH1" with "[%]") as "IH1'"; try done.
        iClear "IH IH1".

        unfold trnsl_hoare_triple. 
        simpl.
        destruct (trnsl_assertion a2 stk_id mp) eqn:Ha2.
        - destruct (trnsl_stmt c1) eqn:Hc1, (trnsl_stmt c2) eqn:Hc2; try done.
          + destruct (trnsl_assertion a1 stk_id mp) eqn:Ha1, (trnsl_assertion a3 stk_id mp) eqn: Ha3; try done. iIntros "Hu0".
          iPoseProof ("IH'" with "Hu0") as ">IHH".
           iApply "IH1'". iFrame.

          + destruct (trnsl_assertion a1 stk_id mp) eqn:Ha1, (trnsl_assertion a3 stk_id mp) eqn: Ha3; try done. 
            iIntros (Φ). iModIntro. iIntros "Hu0 HΦ".
            iPoseProof ("IH'" with "Hu0") as ">IHH".
            iApply ("IH1'" with "IHH"); iFrame.

          + destruct (trnsl_assertion a1 stk_id mp) eqn:Ha1, (trnsl_assertion a3 stk_id mp) eqn: Ha3; try done. admit.

          + destruct (trnsl_assertion a1 stk_id mp) eqn:Ha1, (trnsl_assertion a3 stk_id mp) eqn: Ha3; try done.
          simpl.
          iApply wp_seq; try done.

        - admit.
           (* Case: trnsl_assertion a2 = None; *)
           (* have to ensure this case cannot arise, perhaps by formalizing type soundness of a2 and mp. *)
      }

      5 : {
        (* SKIP *)
        unfold trnsl_hoare_triple. simpl.
        destruct (trnsl_assertion p stk_id mp); try done.
        (* Unset Printing Notations. *)
        (* iApply (wp_skip (stack_own[ stk_id, symb_stk_to_stk_frm stk mp] ∗ u ) (inv_set_to_namespace mask) (stk_id)). *)
        iIntros (Φ). iModIntro. iIntros "Hp HΦ".
        iApply (wp_skip with "Hp"). iFrame. 
      }

      5: {
        (* CAS SUCC *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ). iModIntro. iIntros "[Hstk He1] HΦ".
        iDestruct "He1" as (l) "[%He1 Hl]".
        assert (interp_lexpr (LVal old_val) mp = Some old_val) as Hinterp_old; try done.
        assert (interp_lexpr (LVal new_val) mp = Some new_val) as Hinterp_new; try done.
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H1 Hinterp_old) as Hexpr_step_e2.
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H2 Hinterp_new) as Hexpr_step_e3.
        unfold LExpr_holds in He1. simpl in He1.
        destruct (interp_lexpr lexpr1 mp) eqn:Hlexpr1.
        2 : { 
            (* Make sure interp_lexpr lexpr1 is not None *)
            admit. 
        }
        
        injection He1 as He1.
        destruct (val_beq v0 (LitLoc l)) eqn:Hv0_l; try done.
        apply val_beq_eq in Hv0_l. rewrite Hv0_l in Hlexpr1.
        
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H0 Hlexpr1) as Hexpr_step_e1.


        iApply (wp_cas_succ v e1 fld e2 e3 stk_id (symb_stk_to_stk_frm stk mp) l (trnsl_lval old_val) (trnsl_lval new_val) with "[Hstk Hl]"); try done.
        
        { assert (trnsl_lval (LitLoc l) = (lang.LitLoc l)).
        - simpl. destruct l. simpl. done.
        - rewrite -> H3 in *. done. }

        { iFrame. }

        iNext. iIntros "[Hstk Hl]".
        iApply "HΦ".
        iExists (LitBool true).
        iSplitL "Hstk".
        - rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done.

        - iSplitL.
        { iExists l.  iSplitR.
        - iPureIntro. apply EqOp_refl. 
          unfold LExpr_holds. simpl. 
          rewrite <- (fresh_var_trnsl_expr_invariant stk lvar_v e1 lexpr1 mp (LitBool true)); try done. rewrite Hlexpr1. 
          assert (internal_loc_beq l l = true) as H_l_l. { admit. } 
          rewrite H_l_l. done.
          
        - iFrame.
          
         }

         iPureIntro.
         unfold LExpr_holds. simpl. rewrite String.eqb_refl. rewrite val_beq_refl. done.

      }

      5 : {
        (* CASS FAIL *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ). iModIntro. iIntros "[Hstk [He1 %Hneq]] HΦ".
        iDestruct "He1" as (l) "[%He1 Hl]".
        assert (interp_lexpr (LVal old_val2) mp = Some old_val2) as Hinterp_old; try done.
        (* assert (interp_lexpr (LVal old_val) mp = Some new_val) as Hinterp_new; try done. *)
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H1 Hinterp_old) as Hexpr_step_e2.
        (* pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H2 Hinterp_new) as Hexpr_step_e3. *)
        unfold LExpr_holds in He1. simpl in He1.
        destruct (interp_lexpr lexpr1 mp) eqn:Hlexpr1.
        2 : { 
            (* Make sure interp_lexpr lexpr1 is not None *)
            admit. 
        }
        
        injection He1 as He1.
        destruct (val_beq v0 (LitLoc l)) eqn:Hv0_l; try done.
        apply val_beq_eq in Hv0_l. rewrite Hv0_l in Hlexpr1.
        
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H0 Hlexpr1) as Hexpr_step_e1.

        iApply (wp_cas_fail v e1 fld e2 e3 stk_id (symb_stk_to_stk_frm stk mp) l (trnsl_lval old_val2) (trnsl_lval old_val) _ with "[Hstk Hl]"); try done.
        
        - assert (trnsl_lval (LitLoc l) = (lang.LitLoc l)) as H2. { simpl. destruct l. simpl. done. }
        { rewrite -> H2 in *. done. }

        - unfold LExpr_holds in Hneq.
          simpl in Hneq. injection Hneq as Hneq.

          assert (val_beq old_val old_val2 = false) as Hbeq.
          { simpl in Hneq.
          move: Hneq. by case (val_beq old_val old_val2). }

          apply val_beq_neq in Hbeq.
          assert (trnsl_lval old_val ≠ trnsl_lval old_val2) as Hneq2.
          { intros Heq. apply Hbeq. apply (trnsl_lval_injective _ _ Heq). }
          done.

        - iFrame.

        - iNext. iIntros "[Hstk Hl]".
          iApply "HΦ".
          iExists (LitBool false).
          iSplitL "Hstk".

          { rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done. }
          
          iSplitL.
          { 
            iExists l. iFrame. iPureIntro. unfold LExpr_holds. simpl. 
            rewrite <- (fresh_var_trnsl_expr_invariant stk lvar_v e1 lexpr1 mp (LitBool false)); try done. rewrite Hlexpr1. rewrite val_beq_refl.
            done.
          }

          { 
            iPureIntro. unfold LExpr_holds; simpl.
            apply f_equal. rewrite String.eqb_refl. rewrite val_beq_refl. done.

          }

      }

      4 : {
        (* WEAKENING *)
        unfold entails in *.
        unfold trnsl_hoare_triple. simpl.
        specialize H0 with stk_id mp.
        destruct H0 as [P' [P [HP' [HP HP_ent_P']]]].
        
        specialize H1 with stk_id mp.
        destruct H1 as [Q [Q' [HQ [HQ' HQ_ent_Q']]]].
        rewrite HP HP' HQ HQ'.

        destruct (trnsl_stmt c) eqn:HtrnslStmt; try done.

        - 
        iPoseProof ("IH" with "[%]") as "IH2"; try done.
        iIntros "HP'".
        iApply HQ_ent_Q'.
        iApply "IH2".
        iApply HP_ent_P'.
        iFrame.

        -
        iPoseProof ("IH" with "[%]") as "IH2"; try done.
        iIntros (Φ). iModIntro. iIntros "HP' HΦ".
        iApply ("IH2" with "[HP']").
          + iApply HP_ent_P'. iFrame.
          + iNext. iIntros "HQ". iApply "HΦ". iApply HQ_ent_Q'. iFrame.
      }

      2 : {
        (* IF *)
        inversion Hwelldef; subst e0 s0 s3.
        iPoseProof ("IH" with "[%]") as "IH'"; try done.
        iPoseProof ("IH1" with "[%]") as "IH1'"; try done.
        iClear "IH IH1".
        unfold trnsl_hoare_triple. simpl.

        destruct (trnsl_stmt s1) eqn:Hs1, (trnsl_stmt s2) eqn:Hs2; try done;

        destruct (trnsl_assertion p stk_id mp) eqn:HP, (trnsl_assertion q stk_id mp) eqn:HQ; try done.

        - iFrame.
        admit.

        - admit.

        - admit.

        - admit.

        

      }





      

    Admitted.
  
  End MainTranslation.