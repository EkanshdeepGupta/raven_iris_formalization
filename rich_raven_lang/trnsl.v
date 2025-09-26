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

Require Import iris.base_logic.lib.later_credits.

Section MainTranslation.
    Definition inv_set_to_namespace (s : gset inv_name) : coPset :=
      set_fold (λ inv acc, acc ∪ ↑(inv_namespace_map inv)) ∅ s.

    (* Definition symb_stk_to_stk_frm (stk : stack) (mp : symb_map) : stack_frame :=
      StackFrame (fmap (λ v, trnsl_lval (mp v)) stk). *)

    Lemma trnsl_expr_interp_lexpr_compatibility stk e lexpr lv mp : 
      trnsl_expr_lExpr stk e = Some (lexpr) -> 
      interp_lexpr lexpr mp = Some lv -> 
      expr_step e (symb_stk_to_stk_frm stk mp) (Val (trnsl_lval lv)).
    Admitted.

    Lemma trnsl_expr_interp_lexpr_compatibility2 stk e lexpr lv mp : 
      trnsl_expr_lExpr stk e = Some (lexpr) -> 
      expr_step e (symb_stk_to_stk_frm stk mp) (Val (trnsl_lval lv)) ->
      interp_lexpr lexpr mp = Some lv.
    Admitted.

    Definition trnsl_hoare_triple Γ (stk_id: stack_id) (p : assertion) (ι1: nat) (msk : maskAnnot) (cmd : stmt) (q : assertion) (ι2: nat) (mp : symb_map) : iProp rrl_lang.Σ :=
        match (trnsl_stmt cmd) with 
        | Error => True
        | None' =>
          match (trnsl_assertion Γ p stk_id mp), 
                (trnsl_assertion Γ q stk_id mp) with
          | None, _ | _, None => True
          | Some p', Some q' =>
            p' ∗ £ ι1 ={inv_set_to_namespace msk}=∗ q' ∗ £ ι2 
          end
        
        | Some' s =>
          match (trnsl_assertion Γ p stk_id mp), 
                (trnsl_assertion Γ q stk_id mp) with
          | None, _ | _, None => True
          | Some p', Some q' => 
            {{{ p' ∗ £ ι1 }}}  
              to_rtstmt stk_id s @ (inv_set_to_namespace msk)
            {{{ RET lang.LitUnit; q' ∗ £ ι2}}}
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

    Axiom proc_specs_valid :
      forall Γ proc proc_record stk_vals, 
      proc ∈ proc_set  ->
      proc_map !! proc = Some proc_record ->

      exists (ret_val: lang.val),
      forall precond postcond stk_id stk_frm mp stmt mask,

      (forall v, v ∈ (proc_args_of proc_record) -> is_Some (stk_frm.(locals) !! v.1)) ->

      Forall2 (λ var val, stk_frm.(locals) !! var = Some val) (proc_args_of proc_record).*1 stk_vals ->

      let subst_map' := list_to_map (zip (proc_args_of proc_record).*1 (map (λ val, LVal (trnsl_val val)) stk_vals)) in

      trnsl_assertion Γ (subst (proc_precond_of proc_record) subst_map') stk_id mp = Some precond ->
      trnsl_assertion Γ (subst (proc_postcond_of proc_record) (<["#ret_val" := LVal (trnsl_val (ret_val))]> subst_map')) stk_id mp = Some postcond ->
      
      ((trnsl_stmt (proc_body_of proc_record) = Some' stmt) \/ (trnsl_stmt (proc_body_of proc_record) = None' /\ stmt = lang.SkipS) ) ->
      (∃ stk_frm'',
      ({{{ stack_own[stk_id, stk_frm] ∗ precond }}} (to_rtstmt stk_id stmt) @ mask {{{ RET lang.LitUnit; stack_own[stk_id, stk_frm''] ∗ ⌜ (locals stk_frm'' !! "#ret_val") = Some ret_val ⌝ ∗ postcond }}})).

    (* Lemma transport_congr {A B : cmra} (H : (cmra_car A) = (cmra_car B)) {x y : A} (Hupd : x ~~> y) :
      transport H x ~~> transport H y.
    Proof.
      unfold transport. revert Hupd.
    (* usually trivial by proper instance or f_equiv *) Admitted. *)

    Theorem rrl_validity Γ ρ σ ι1 ι2 stk_id p msk cmd q :
      stmt_well_defined ρ cmd -> 
      forall mp, (env_typ_well_defined σ mp) ->
       ⌜RavenHoareTriple ρ σ p ι1 cmd msk q ι2⌝
      ⊢  (trnsl_hoare_triple Γ stk_id p ι1 msk cmd q ι2 mp).
    Proof.
      iIntros (Hwelldef mp Henv) "%H". 
      iInduction H as 
      [ | 
      | ρ σ ι stk mask v fld e old_val new_val lv Hatm HLexpr1 
      | | | | 
      | ρ σ ι1 ι2 stk mask invr args stmt inv_record p q lexprs Hargs Hinv_mask Hinv_record Hstk_tp Hcred subst Hbody IHHbody
      | | | | | | | | ] "IH".
      3: { 
        (* FIELD WRITE *)
        unfold trnsl_hoare_triple.
        simpl.
        destruct (trnsl_stmt (FldWr v fld e)) eqn:Ht. 2: done.
        { inversion Ht. } 

        inversion Ht. simpl. 
        - iIntros (Φ). iModIntro.
          iIntros "[[Hstk1 Hstk2] Hcred] HΦ".

          iDestruct "Hstk2" as "[%l [%Hlexpr1 Hlfld]]".
          
          iApply (wp_heap_wr stk_id (symb_stk_to_stk_frm stk mp) _ _ _ l _ _ _ with "[Hstk1 Hlfld]").
        
        {
          iFrame.
          iSplit.
          { iPureIntro. simpl. rewrite lookup_fmap. 
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
          iModIntro. iIntros "[HstkO [Hlpt Hcred']]".
          iApply "HΦ". iCombine "Hcred" "Hcred'" as "Hcred". rewrite Nat.add_1_r. iFrame.
          iPureIntro. done.
        }

      }

      7: {
        (* INV ACCESS BLOCK *)
        unfold trnsl_hoare_triple.

        pose proof (trnsl_inv_validity Γ invr lexprs stk_id mp) as Htrnsl_inv_valid.
        rewrite Hinv_record in Htrnsl_inv_valid. simpl in Htrnsl_inv_valid.
        destruct (trnsl_assertion Γ (rrl_lang.subst (inv_body inv_record)
        subst) stk_id mp) eqn:HinvBody. 2:{ rewrite HinvBody in Htrnsl_inv_valid. inversion Htrnsl_inv_valid. }

        rewrite HinvBody in Htrnsl_inv_valid. injection Htrnsl_inv_valid as Htrnsl_inv.
        
        destruct (trnsl_stmt (InvAccessBlock invr args stmt)) eqn:Ht. 
        2: { done. }

        
        { 
          destruct (trnsl_assertion Γ (LStack stk) stk_id mp) eqn:Hstack.
          2 : { simpl in Hstack. inversion Hstack. }

          simpl. rewrite HinvBody. rewrite Hinv_record.
           destruct (trnsl_assertion Γ p stk_id mp) eqn:Hp, (trnsl_assertion Γ q stk_id mp) eqn:Hq; try done.
           
           iIntros "[[Hstk [#H Hu]] Hcr]".
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

          assert (ι1 = (ι1-1 + 1)) as Hiota. { rewrite Nat.sub_add; [ reflexivity | ]. lia. }
          apply (f_equal lc) in Hiota.
          iEval (rewrite Hiota) in "Hcr".
          iPoseProof ((lc_split (ι1 - 1) 1) with "Hcr") as "[Hcr1 Hcr2]".

          iDestruct (lc_fupd_elim_later with "Hcr2 Hinv") as ">Hinv".

          iCombine "Hstk Hinv Hu" as "Hcomb".
          inversion Hwelldef as [ | | | | | | | | | | | | | inv args' stmt' HInvSet HargsWellDef HBodywelldef | ]; subst stmt' args'.

          
          
          iPoseProof ("IH" with  "[%] [%] [Hcomb Hcr1]") as "IH2"; try iFrame; try done.
          assert ((inv_set_to_namespace (mask ∖ {[invr]})) = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr) as HInvs. { admit. }
          rewrite HInvs.
          iDestruct "IH2" as ">IH2".
          iDestruct "IH2" as "[[IHs [IHH1 IHH] ] Hcr]".
          iModIntro.
          iFrame "# ∗". done.

          (* pose proof (trnsl_inv_validity invr lexprs mp) as Htrnsl_inv_valid. *)
        }
        
        { 
          assert (trnsl_stmt stmt = Some' s). { admit. }
          simpl.
          iEval (rewrite H HinvBody) in "IH" .
          iEval (rewrite Hinv_record).
          destruct (trnsl_assertion Γ p stk_id mp) eqn:Hp, (trnsl_assertion Γ q stk_id mp) eqn:Hq; try done.
          iIntros (Φ).
          iModIntro.
          iIntros "[[Hstk [#HInv Hu]] Hcr] HΦ".
          rewrite <- Htrnsl_inv.

          assert (ι1 = (ι1-1 + 1)) as Hiota. { rewrite Nat.sub_add; [ reflexivity | ]. lia. }
          apply (f_equal lc) in Hiota.
          iEval (rewrite Hiota) in "Hcr".

          iPoseProof ((lc_split (ι1 - 1) 1) with "Hcr") as "[Hcr1 Hcr2]".
          
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
          iApply ("IH" with "[%] [%] [Hcomb Hcr1]"); try iFrame; try done.
          iNext.
          iIntros "[[Hstk [Hu Hu1]] Hcr]".
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
        iIntros "[Hstk Hcr] HΦ".

        destruct (interp_lexpr lexpr mp) eqn: Hlexpr.

        { iApply (wp_assign stk_id (symb_stk_to_stk_frm stk mp) v (trnsl_lval v0) e with "[Hstk]").

          {
            iFrame.
            iPureIntro.
            apply (trnsl_expr_interp_lexpr_compatibility _ _ lexpr). { done. } 
            done. 
          }
          
          iNext.
          iIntros "[Hstk Hcr1]".
          iApply "HΦ".
          iCombine "Hcr" "Hcr1" as "Hcr". rewrite Nat.add_1_r. iFrame.
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
                  rewrite HstkI. simpl. f_equal. rewrite <- String.eqb_neq in H2. rewrite H2. auto.

                  + rewrite HstkI. simpl. done.
              } rewrite H2. done.

          }
          iPureIntro.

          apply (fresh_mp_rewrite_LExpr_holds stk lv e lexpr mp v0 H0 H Hlexpr).
        }

        pose proof (expr_interp_well_defined stk e mp lexpr H Hlexpr).
        inversion Hwelldef.
        contradiction.
      }

      9 : {
        (* FRAME RULE *)
        iPoseProof ("IH" with  "[%]") as "IH2". { done. }
        iClear "IH".

        unfold trnsl_hoare_triple. simpl.
        destruct (trnsl_stmt s) eqn:Htrnsl; try done.
        { simpl.
          destruct (trnsl_assertion Γ p stk_id mp) eqn:Hp, (trnsl_assertion Γ q stk_id mp) eqn:Hq, (trnsl_assertion Γ r stk_id mp) eqn:Hr; try done. 

          iIntros "[[Hu Hu1] Hcr]".
          iPoseProof ("IH2" with "[%] [Hu Hcr]") as ">[IH3 Hcr']"; try iFrame; try done.

        }

        { 
          destruct (trnsl_assertion Γ p stk_id mp) eqn:Hp, 
                   (trnsl_assertion Γ q stk_id mp) eqn:Hq, 
                   (trnsl_assertion Γ r stk_id mp) eqn:Hr; try done.

          iIntros (Φ).
          iModIntro. iIntros "[[Hu Hu1] Hcr] HΦ".
          iApply ("IH2" with "[%] [Hu Hcr]"); try iFrame; try done.
          iNext. iIntros "[Hu0 Hcr']". iApply "HΦ". iFrame.
        }
      }

      1 : {
        (* FIELD READ *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ). iModIntro. iIntros "[[Hstk Hl] Hcr] HΦ".
        iDestruct "Hl" as (l) "[%HLe_h H_l_hp]".

        destruct (interp_lexpr lexpr_e mp) eqn: Hinterp.

        2 : { apply (expr_interp_well_defined _ _ _ _ H) in Hinterp.
          inversion Hwelldef. contradiction.
        }

        pose proof (lexpr_holds_interp_compat _ _ _ _ HLe_h Hinterp). subst v.

        iApply (wp_heap_rd stk_id (rrl_lang.symb_stk_to_stk_frm stk mp) fld e (trnsl_lval val) l x _ 1%Qp with "[Hstk H_l_hp]").

        {
          pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H Hinterp).
          iFrame.
          iPureIntro. 
          simpl in H1.
          assert (l = {| loc_car := loc_car l |}).
          { destruct l. simpl. done.  }
          rewrite H3. done. 
        }

        {
          iNext.
          iIntros "[Hstk [Hhp Hcr']]".
          iApply "HΦ". iCombine "Hcr" "Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame.
          iExists val.

          iSplitL "Hstk".
          - pose proof (fresh_mp_rewrite_symb_stk_to_stk_frm_compat stk lvar_x x mp val H0) as HstkOwnDone.
            rewrite HstkOwnDone. iFrame.

          - iSplitL.
            + iPureIntro.
              pose proof (fresh_var_trnsl_expr_invariant stk lvar_x e _ mp val H0 H).
              unfold LExpr_holds.
              simpl. rewrite <- H2. apply HLe_h.
          
            + iPureIntro. unfold LExpr_holds. simpl. rewrite String.eqb_refl. rewrite val_beq_refl. done.
        }
      }

      1 : {
        (* ALLOC *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ).
        iModIntro.
        iIntros "[Hstack Hcr] HΦ".
        iApply (wp_alloc with "[Hstack]") .
        - iFrame.
        - iNext.
          iIntros "Hpost".
          iDestruct "Hpost" as (l) "[Hstk [Hhp Hcr']]".
          iApply "HΦ". iCombine "Hcr" "Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame.
          iExists (LitLoc l).
          set (mp' := (λ x0 : lvar, if (x0 =? lvar_x)%string then LitLoc l else mp x0)).

          iInduction fld_vals as [ | ] "IH".
          
          + simpl. iFrame. rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done.
          unfold symb_stk_to_stk_frm. simpl. 
          assert (lang.LitLoc l = lang.LitLoc {| loc_car := loc_car l |}) as H1.
          {  destruct l. simpl. done. }
          rewrite <- H1. iFrame.

          + simpl. destruct a as [fld val].
          assert (stmt_well_defined ρ (Alloc x fld_vals)) as Hwell_def'. { admit. }
          destruct (trnsl_assertion Γ (field_list_to_assertion (LVar lvar_x) fld_vals) stk_id mp' ) eqn:Htrfl.
          
            * simpl. rewrite Htrfl.
              iPoseProof ("IH" with "[%]") as "IH2"; try done.
              iClear "IH".
              iDestruct "Hhp" as "[Hhpl Hhpfvs]".
              iPoseProof ("IH2" with "Hstk Hhpfvs") as "[IH3 IH3']". 
              iFrame. iExists l. 
              assert (trnsl_lval (trnsl_val val) = val) as H1. { admit. } 
              rewrite H1. iFrame.
              iPureIntro. 
              unfold LExpr_holds.
              simpl.
              subst mp'. simpl. rewrite String.eqb_refl. rewrite val_beq_refl. done.

            * simpl. rewrite Htrfl. iPoseProof ("IH" with "[%]") as "IH2"; try done.
      }

      4 : {
        (* UNFOLD PRED *)
        unfold trnsl_hoare_triple.
        simpl.
        pose proof (trnsl_pred_validity Γ pred lexprs stk_id mp) as HPredTrnsl. rewrite H0 in HPredTrnsl. unfold subst_map in HPredTrnsl. rewrite HPredTrnsl.
        iIntros. iModIntro.  iFrame.
      }

      4 : {
        (* FOLD PRED *)
        unfold trnsl_hoare_triple.
        simpl.
        pose proof (trnsl_pred_validity Γ pred lexprs stk_id mp) as HPredTrnsl. rewrite H1 in HPredTrnsl. unfold subst_map in HPredTrnsl. rewrite HPredTrnsl.
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
        destruct (trnsl_assertion Γ a2 stk_id mp) eqn:Ha2.
        - destruct (trnsl_stmt c1) eqn:Hc1, (trnsl_stmt c2) eqn:Hc2; try done.
          + destruct (trnsl_assertion Γ a1 stk_id mp) eqn:Ha1, (trnsl_assertion Γ a3 stk_id mp) eqn: Ha3; try done. iIntros "Hu0".
          iPoseProof ("IH'" with "[%] Hu0") as ">IHH"; try done.
           iApply "IH1'"; try done.

          + destruct (trnsl_assertion Γ a1 stk_id mp) eqn:Ha1, (trnsl_assertion Γ a3 stk_id mp) eqn: Ha3; try done. 
            iIntros (Φ). iModIntro. iIntros "Hu0 HΦ".
            iPoseProof ("IH'" with "[%] Hu0") as ">IHH"; try done.
            iApply ("IH1'" with "[%] IHH"); try done.

          + destruct (trnsl_assertion Γ a1 stk_id mp) eqn:Ha1, (trnsl_assertion Γ a3 stk_id mp) eqn: Ha3; try done. admit.

          + destruct (trnsl_assertion Γ a1 stk_id mp) eqn:Ha1, (trnsl_assertion Γ a3 stk_id mp) eqn: Ha3; try done.
          simpl.
          iApply wp_seq.
            { iApply "IH'"; try done. }
            { iApply "IH1'"; try done. }

        - admit.
           (* Case: trnsl_assertion a2 = None; *)
           (* have to ensure this case cannot arise, perhaps by formalizing type soundness of a2 and mp. *)
      }

      5 : {
        (* SKIP *)
        unfold trnsl_hoare_triple. simpl.
        destruct (trnsl_assertion Γ p stk_id mp); try done.
        iIntros (Φ). iModIntro. iIntros "[Hp Hcr] HΦ".
        iApply (wp_skip with "Hp"). 
        iNext. iIntros "[[Hstk Hu] Hcr']". iApply "HΦ". iCombine "Hcr" "Hcr'" as "Hcr". iFrame.
      }

      5: {
        (* CAS SUCC *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ). iModIntro. iIntros "[[Hstk He1] Hcr] HΦ".
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
        - rewrite -> H4 in *. done. }

        { iFrame. }

        iNext. iIntros "[Hstk [Hl Hcr']]".
        iApply "HΦ". iCombine "Hcr" "Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame.
        iExists (LitBool true).
        iSplitL "Hstk".
        - rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done.

        - iSplitL.
        { 
          iPureIntro. apply EqOp_refl. 
          unfold LExpr_holds. simpl. 
          rewrite <- (fresh_var_trnsl_expr_invariant stk lvar_v e1 lexpr1 mp (LitBool true)); try done. rewrite Hlexpr1. 
          assert (internal_loc_beq l l = true) as H_l_l. { admit. } 
          rewrite H_l_l. done.
        }

         iPureIntro.
         unfold LExpr_holds. simpl. rewrite String.eqb_refl. rewrite val_beq_refl. done.
      }

      5 : {
        (* CAS FAIL *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ). iModIntro. iIntros "[[Hstk [He1 %Hneq]] Hcr] HΦ".
        iDestruct "He1" as (l) "[%He1 Hl]".
        assert (interp_lexpr (LVal old_val2) mp = Some old_val2) as Hinterp_old; try done.
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H1 Hinterp_old) as Hexpr_step_e2.
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
        
        - assert (trnsl_lval (LitLoc l) = (lang.LitLoc l)) as H3. { simpl. destruct l. simpl. done. }
        { rewrite -> H3 in *. done. }

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

        - iNext. iIntros "[Hstk [Hl Hcr']]".
          iApply "HΦ".
          iCombine "Hcr" "Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame.
          iExists (LitBool false).
          iSplitL "Hstk".

          { rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done. }
          
          iSplitL.
          { 
            iPureIntro. unfold LExpr_holds. simpl. 
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
        specialize H0 with Γ stk_id mp.
        destruct H0 as [P' [P [HP' [HP HP_ent_P']]]].
        
        specialize H1 with Γ stk_id mp.
        destruct H1 as [Q [Q' [HQ [HQ' HQ_ent_Q']]]].
        rewrite HP HP' HQ HQ'.

        destruct (trnsl_stmt c) eqn:HtrnslStmt; try done.

        - 
        iPoseProof ("IH" with "[%]") as "IH2"; try done.
        iIntros "[HP' Hcr]".
        iPoseProof ("IH2" with "[%] [HP' Hcr]") as "HII"; try iFrame; try done.
        { iApply HP_ent_P'. iFrame. }
        iDestruct  "HII" as ">[HQ Hcr]" . iModIntro. iFrame.
        iApply HQ_ent_Q'.
        iFrame.

        -
        iPoseProof ("IH" with "[%]") as "IH2"; try done.
        iIntros (Φ). iModIntro. iIntros "[HP' Hcr] HΦ".
        iApply ("IH2" with "[%] [HP' Hcr]"); try iFrame; try done.
          + iApply HP_ent_P'. iFrame.
          + iNext. iIntros "[HQ Hcr]". iApply "HΦ". iFrame. iApply HQ_ent_Q'. iFrame.
      }

      2 : {
        (* IF *)
        inversion Hwelldef; subst e0 s0 s3.
        iPoseProof ("IH" with "[%]") as "IH'"; try done.
        iPoseProof ("IH1" with "[%]") as "IH1'"; try done.
        iClear "IH IH1".
        unfold trnsl_hoare_triple. simpl.

        pose proof (lexpr_expr_typ_compat _ _ _ _ _ _ H1 H H0) as Hlexpr_type_inf.
          pose proof (lexpr_typcheck_well_defined _ _ _ _ Henv Hlexpr_type_inf) as Hinterp_lexpr.
          destruct Hinterp_lexpr as [val0 Hinterp_lexpr].
          pose proof (interp_lexpr_typ_compat _ _ _ _ _ Henv Hlexpr_type_inf Hinterp_lexpr) as Hle_typ.
          unfold typeOf in Hle_typ. destruct (trnsl_lval val0) eqn:Hle_val; try done.
          unfold trnsl_lval in Hle_val. destruct (val0) eqn: Hle_val'; try done.

        destruct (trnsl_stmt s1) eqn:Hs1, (trnsl_stmt s2) eqn:Hs2; try done;
        destruct (trnsl_assertion Γ p stk_id mp) eqn:HP, (trnsl_assertion Γ q stk_id mp) eqn:HQ; try done.

        - destruct b0.

          + iIntros "[[Hstk Hu] Hcr]".

          iPoseProof ("IH'" with "[%] [Hstk Hu Hcr]") as "Hpost"; try iFrame; try done.
          { unfold LExpr_holds. rewrite Hinterp_lexpr. done. }

          iDestruct "Hpost" as ">[[Hstk Hu0] Hcr2]".

          assert (ι2 = ι2 `min` ι3 + (ι2 - ι2 `min` ι3)) as Hiota. { lia.  }
          apply (f_equal lc) in Hiota.
          iEval (rewrite Hiota) in "Hcr2".

          iDestruct (lc_split (ι2 `min` ι3) (ι2 - (ι2 `min` ι3)) with "Hcr2") as "[Hcr2 Hcr2']".

          iFrame. iModIntro. done.
          
          + iIntros "[[Hstk Hu] Hcr]".

          iPoseProof ("IH1'" with "[%] [Hstk Hu Hcr]") as "Hpost"; try iFrame; try done.
          { unfold LExpr_holds. simpl.  rewrite Hinterp_lexpr. done. }

          iDestruct "Hpost" as ">[[Hstk Hu0] Hcr2]".

          assert (ι3 = ι2 `min` ι3 + (ι3 - ι2 `min` ι3)) as Hiota. { lia.  }
          apply (f_equal lc) in Hiota.
          iEval (rewrite Hiota) in "Hcr2".

          iDestruct (lc_split (ι2 `min` ι3) (ι3 - (ι2 `min` ι3)) with "Hcr2") as "[Hcr2 Hcr2']".
          iFrame.
          done.

        - iIntros (Φ). iModIntro. iIntros "[[Hstk Hu] Hcr] HΦ".
          destruct b0.
          + iApply (wp_if_t e (RTSkipS stk_id) (to_rtstmt stk_id s) stk_id (symb_stk_to_stk_frm stk1 mp) (u ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ u0 ∗ £ι2) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            *  apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool true) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            iPoseProof ("IH'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. rewrite Hinterp_lexpr. done.  }
            iDestruct "HQ" as ">[[Hstk Hu] Hcr]". iApply (wp_skip (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ u0) with "[Hstk Hu]"); iFrame.
            iNext. iIntros "[[Hstk Hu] Hcr']". iApply "HΦ'". iFrame. 


            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.

            assert (ι2 = ι2 `min` ι3 + (ι2 - ι2 `min` ι3)) as Hiota. { lia.  }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι2 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". iFrame.
          
          + iApply (wp_if_f e (RTSkipS stk_id) (to_rtstmt stk_id s) stk_id (symb_stk_to_stk_frm stk1 mp) (u ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ u0 ∗ £ι3) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            * apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool false) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            iPoseProof ("IH1'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. simpl. rewrite Hinterp_lexpr. done.  }
            iApply "HQ"; iFrame. iNext.
            iIntros "[[Hstk Hu] Hcr]". iApply "HΦ'". iFrame.

            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.

            assert (ι3 = ι2 `min` ι3 + (ι3 - ι2 `min` ι3)) as Hiota. { lia.  }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι3 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". iFrame.

        - iIntros (Φ). iModIntro. iIntros "[[Hstk Hu] Hcr] HΦ".
          destruct b0.
          + iApply (wp_if_t e (to_rtstmt stk_id s) (RTSkipS stk_id) stk_id (symb_stk_to_stk_frm stk1 mp) (u ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ u0 ∗ £ι2) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            *  apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool true) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            iPoseProof ("IH'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. rewrite Hinterp_lexpr. done.  }
            iApply "HQ"; iFrame. iNext. iIntros "[[Hstk Hu] Hcr]". iApply "HΦ'". iFrame.

            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.
            assert (ι2 = ι2 `min` ι3 + (ι2 - ι2 `min` ι3)) as Hiota. { lia.  }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι2 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". iFrame.

          
          + iApply (wp_if_f e (to_rtstmt stk_id s) (RTSkipS stk_id) stk_id (symb_stk_to_stk_frm stk1 mp) (u ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ u0 ∗ £ι3) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            * apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool false) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            iPoseProof ("IH1'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. simpl. rewrite Hinterp_lexpr. done.  }
            iDestruct "HQ" as ">[[Hstk Hu] Hcr]". iApply (wp_skip (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ u0) with "[Hstk Hu]"); iFrame.
            iNext. iIntros "[[Hstk Hu] Hcr']". iApply "HΦ'". iFrame.

            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.
            
            assert (ι3 = ι2 `min` ι3 + (ι3 - ι2 `min` ι3)) as Hiota. { lia.  }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι3 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". iFrame.

        - iIntros (Φ). iModIntro. iIntros "[[Hstk Hu] Hcr] HΦ".
          destruct b0.
          + iApply (wp_if_t e (to_rtstmt stk_id s) (to_rtstmt stk_id s0) stk_id (symb_stk_to_stk_frm stk1 mp) (u ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ u0 ∗ £ι2) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            *  apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool true) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            iPoseProof ("IH'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. rewrite Hinterp_lexpr. done.  }
            iApply "HQ"; iFrame. iNext. iIntros "[[Hstk Hu] Hcr]". iApply "HΦ'". iFrame.

            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.
            assert (ι2 = ι2 `min` ι3 + (ι2 - ι2 `min` ι3)) as Hiota. { lia.  }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι2 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". iFrame.
            
          + iApply (wp_if_f e (to_rtstmt stk_id s) (to_rtstmt stk_id s0) stk_id (symb_stk_to_stk_frm stk1 mp) (u ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ u0 ∗ £ι3) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            * apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool false) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            iPoseProof ("IH1'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. simpl. rewrite Hinterp_lexpr. done.  }
            iApply "HQ"; iFrame. iNext. iIntros "[[Hstk Hu] Hcr]". iApply "HΦ'". iFrame.

            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.

            assert (ι3 = ι2 `min` ι3 + (ι3 - ι2 `min` ι3)) as Hiota. { lia.  }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι3 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". iFrame.

      }
      
      1 : {
        (* CALL *)
        unfold trnsl_hoare_triple. simpl (trnsl_stmt (Call x proc_name args)). case_match; try discriminate.
        pose proof H0 as H0'.
        apply proc_args_unique in H0'.
        pose proof H0 as Hspec_StackFree.
        apply proc_spec_stack_free in Hspec_StackFree.

        destruct (trnsl_assertion Γ (LAnd (LStack stk) (LAnd (LProc proc_name proc_record) (subst (proc_precond_of proc_record) subst_map))) stk_id mp) eqn:HPreCond; try done.

        destruct (trnsl_assertion Γ
          (LExists lvar_x
          (LAnd (LStack (<[x:=lvar_x]> stk))
          (subst (proc_postcond_of proc_record) (<["#ret_var":=LVar lvar_x]> subst_map)))) stk_id mp
        ) eqn:HPostCond; try done.

        inversion Hwelldef; subst ρ0 v proc args0.

        assert (exists arg_vals, Forall2 (fun e v => expr_step e (symb_stk_to_stk_frm stk mp) (Val v)) args arg_vals) as Harg_vals.

        { 
          (* Prove existence of arg_vals *)
          clear Hwelldef H1 H4 H11.
          clear subst_map HPreCond HPostCond.
          revert lexprs H2 H12. 
          induction args as [| a args IH]; intros lexprs H2 H12.
          - simpl in H2. destruct lexprs; [ | discriminate ]. exists nil. constructor.
          - simpl in H2. destruct lexprs as [| l lexprs']; [ discriminate | ].
            (* heads must match and tails must match *)
            simpl in H2. injection H2 as Hhd Htl.
            inversion H12 as [| a' args' Hwd H12']. clear H12; subst.
            (* interp_lexpr either yields a value or None *)
            destruct (interp_lexpr l mp) as [v | ] eqn:He.
            + (* Some v: build the head step and recurse for the tail *)
              specialize (IH lexprs' Htl H12') as [arg_vals' Hforall'].
              exists ((trnsl_lval v) :: arg_vals').
              apply Forall2_cons. split.
              * apply trnsl_expr_interp_lexpr_compatibility with (lexpr:=l); try assumption.
              * exact Hforall'.
            + (* None: contradict well-definedness using expr_interp_well_defined *)
              eapply (expr_interp_well_defined stk a mp l) in Hhd; [ | exact He ].
              congruence.
        }

        destruct Harg_vals as [arg_vals Harg_vals].

        assert (Forall2 (λ expr val, interp_lexpr expr mp = Some (trnsl_val val)) lexprs arg_vals) as Hlexprs_arg_vals.
          {
            clear   Hwelldef H1  H4 H11 H12 subst_map HPreCond HPostCond.
            revert args arg_vals H2 Harg_vals.
            induction lexprs as [| le lexprs IH]; intros args arg_vals H2 Harg_vals.
            - destruct args; [| discriminate]. inversion Harg_vals. constructor.

            - destruct args; [discriminate |]. simpl in H2. injection H2 as Hhd Htl.
              inversion Harg_vals as [ | x0 y l l' HhdExprStep HtlExprStep ]; subst.
              specialize (IH args l' Htl HtlExprStep).
              apply Forall2_cons. split.
              + apply (trnsl_expr_interp_lexpr_compatibility2 stk e); try simpl; try done. rewrite trnsl_lval_trnsl_val_inverse. done.

              + done.
          }

        simpl in *.
        destruct proc_record as [proc_args proc_locals proc_pre proc_post proc_body] eqn:Hproc_record.
        destruct (trnsl_stmt (proc_body)) eqn:Hproc_body, (trnsl_assertion Γ (subst proc_pre subst_map) stk_id mp) eqn:Hproc_pre; try rewrite Hproc_pre in HPreCond;  try discriminate; simpl in HPreCond.
        
        {   
          (* proc_body = Skip *)
        inversion H4; subst s. inversion HPreCond; subst u; clear HPreCond.
        inversion HPostCond as [ HPostCond']; clear HPostCond.
        iIntros (Φ). iModIntro.
        
        iIntros "[[Hstk [Hproc_tbl Hu1]] Hcr] HΦ".

        pose proof (proc_specs_valid Γ proc_name (Proc proc_args proc_locals proc_pre proc_post proc_body) arg_vals ) as [ret_val Hproc]; try done.

        set (subst_map' := @list_to_map var LExpr (gmap var LExpr) _ _ (zip (proc_args).*1 (map (λ val, LVal (trnsl_val val)) arg_vals))).

          destruct (trnsl_assertion Γ (subst proc_pre subst_map') stk_id mp) as [ proc_frame_pre |] eqn: Hproc_frame_pre.
          
          2 : {  
            (* trnsl_assertion (subst proc_pre subst_map') stk_id' mp CANNOT BE None *)
            admit.
          }

          destruct (trnsl_assertion Γ (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp) as [ proc_frame_post |] eqn: Hproc_frame_post.

          2 : {
            (* trnsl_assertion (subst proc_pre subst_map') stk_id' mp CANNOT BE None *)
            admit. 
          }

        iApply (wp_call _ _ _ _ _ _ _ (lang.Proc proc_name proc_args proc_locals _) _ u1 proc_frame_post with "[] [Hstk Hproc_tbl Hu1]"); try iFrame; try done.

          { 
            (* Showing procedure contract holds *)
            iIntros (stk_id' stk_frm') "%HlocalsDef". simpl in *.

            specialize (Hproc proc_frame_pre proc_frame_post stk_id' stk_frm' mp lang.SkipS(inv_set_to_namespace mask)).

            assert ((∀ v : var * typ, v ∈ proc_args_of (Proc proc_args proc_locals proc_pre proc_post proc_body) → is_Some (locals stk_frm' !! v.1))) as HIsSome.

            { 
              intros v Hin. apply elem_of_list_lookup_1 in Hin as [i Hi].
              assert (proc_args.*1 !! i = Some v.1) as Hi'.
              { rewrite list_lookup_fmap. rewrite Hi. done.   } 
              simpl in HlocalsDef.
              eapply (Forall2_lookup_l _ proc_args.*1 arg_vals i v.1 HlocalsDef) in Hi' as [val [Hval Hlookup]]. by eexists.
            }

          pose proof (Hproc HIsSome) as Hproc. simpl in Hproc.

          simpl in HlocalsDef. pose proof (Hproc HlocalsDef) as Hproc.

          rewrite (stack_free_assertion_trnsl Γ (subst proc_pre subst_map') stk_id stk_id' mp) in Hproc_frame_pre. 2 : { apply stack_free_assertion_subst. destruct Hspec_StackFree; done. }

          rewrite (stack_free_assertion_trnsl Γ (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id stk_id' mp) in Hproc_frame_post. 2 : { apply stack_free_assertion_subst. destruct Hspec_StackFree; done. }

          pose proof (Hproc Hproc_frame_pre Hproc_frame_post) as Hproc.

          assert (trnsl_stmt proc_body = Some' lang.SkipS
            ∨ trnsl_stmt proc_body = None' ∧ lang.SkipS = lang.SkipS) as Hproc_body'. { right. split; try done. }
          
          pose proof (Hproc Hproc_body') as Hproc.

          destruct Hproc as [stk_frm'' Hproc].

          iExists stk_frm''.
          
          iIntros (Φ'). iModIntro.
          iIntros "[Hstk Hu1] HΦ".

          iApply (Hproc with "[Hstk Hu1]").

          { 
            rewrite (stack_free_assertion_trnsl Γ (subst proc_pre subst_map') stk_id' stk_id mp) in Hproc_frame_pre. 2 : { apply stack_free_assertion_subst. destruct Hspec_StackFree as [Hpre_stack_free _]. done. }

            iFrame.
            pose proof (trnsl_assertion_w_lexpr_subst Γ proc_pre lexprs proc_args.*1 arg_vals stk_id mp u1 proc_frame_pre Hlexprs_arg_vals Hproc_pre Hproc_frame_pre) as Himpl.
            iApply Himpl. iFrame.
          }

          
          iNext. iExact "HΦ".
          }

          {
            iNext. iIntros "[Hstk [Hq Hcr']]".
            iApply "HΦ". iCombine "Hcr Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame. iExists (trnsl_val ret_val).
          
            destruct (trnsl_assertion Γ (subst proc_post (<["#ret_var":=LVar lvar_x]> subst_map)) stk_id
            (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0)) 
            eqn:Hpost; try done.
            
            iSplitR "Hq". 
            { rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done. rewrite trnsl_lval_trnsl_val_inverse. iFrame. } 
            
            { pose proof (trnsl_assertion_w_lexpr_subst_r Γ proc_post lexprs proc_args.*1 arg_vals lvar_x ret_val stk stk_id mp u proc_frame_post H Hlexprs_arg_vals Hpost Hproc_frame_post) as Himpl. iApply Himpl. iFrame. }
            
            
          }
        }

        {   
          (* proc_body != Skip *)
        inversion H4; subst s. inversion HPreCond; subst u; clear HPreCond.
        inversion HPostCond as [ HPostCond']; clear HPostCond.
        iIntros (Φ). iModIntro.
        
        iIntros "[[Hstk [Hproc_tbl Hu1]] Hcr] HΦ".

        (* pose proof (proc_specs_valid proc_name (Proc proc_args proc_locals proc_pre proc_post proc_body) u1 u0 stk_id' mp lang.SkipS (inv_set_to_namespace mask) stk_frm' arg_vals) as [ret_val Hproc]. *)

        (* destruct HPostCond' as [ret_val HPostCond]. *)

        pose proof (proc_specs_valid Γ proc_name (Proc proc_args proc_locals proc_pre proc_post proc_body) arg_vals ) as [ret_val Hproc]; try done.

        set (subst_map' := @list_to_map var LExpr (gmap var LExpr) _ _ (zip (proc_args).*1 (map (λ val, LVal (trnsl_val val)) arg_vals))).

          destruct (trnsl_assertion Γ (subst proc_pre subst_map') stk_id mp) as [ proc_frame_pre |] eqn: Hproc_frame_pre.
          
          2 : {  
            (* trnsl_assertion (subst proc_pre subst_map') stk_id' mp CANNOT BE None *)
            admit.
          }

          destruct (trnsl_assertion Γ (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp) as [ proc_frame_post |] eqn: Hproc_frame_post.

          2 : {
            (* trnsl_assertion (subst proc_pre subst_map') stk_id' mp CANNOT BE None *)
            admit. 
          }

        iApply (wp_call _ _ _ _ _ _ _ (lang.Proc proc_name proc_args proc_locals _) _ u1 proc_frame_post with "[] [Hstk Hproc_tbl Hu1]"); try iFrame; try done.

          { 
            (* Showing procedure contract holds *)
            iIntros (stk_id' stk_frm') "%HlocalsDef". simpl in *.

            specialize (Hproc proc_frame_pre proc_frame_post stk_id' stk_frm' mp s0 (inv_set_to_namespace mask)).

            assert ((∀ v : var * typ, v ∈ proc_args_of (Proc proc_args proc_locals proc_pre proc_post proc_body) → is_Some (locals stk_frm' !! v.1))) as HIsSome.

            { 
              intros v Hin. apply elem_of_list_lookup_1 in Hin as [i Hi].
              assert (proc_args.*1 !! i = Some v.1) as Hi'.
              { rewrite list_lookup_fmap. rewrite Hi. done.   } 
              simpl in HlocalsDef.
              eapply (Forall2_lookup_l _ proc_args.*1 arg_vals i v.1 HlocalsDef) in Hi' as [val [Hval Hlookup]]. by eexists.
            }

          pose proof (Hproc HIsSome) as Hproc. simpl in Hproc.

          simpl in HlocalsDef. pose proof (Hproc HlocalsDef) as Hproc.

          rewrite (stack_free_assertion_trnsl Γ (subst proc_pre subst_map') stk_id stk_id' mp) in Hproc_frame_pre. 2 : { apply stack_free_assertion_subst. destruct Hspec_StackFree; done. }

          rewrite (stack_free_assertion_trnsl Γ (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id stk_id' mp) in Hproc_frame_post. 2 : { apply stack_free_assertion_subst. destruct Hspec_StackFree; done. }

          pose proof (Hproc Hproc_frame_pre Hproc_frame_post) as Hproc.

          assert (trnsl_stmt proc_body = Some' s0
            ∨ trnsl_stmt proc_body = None' ∧ s0 = lang.SkipS) as Hproc_body'. { left. try done. }
          
          pose proof (Hproc Hproc_body') as Hproc.

          destruct Hproc as [stk_frm'' Hproc].

          iExists stk_frm''.
          
          iIntros (Φ'). iModIntro.
          iIntros "[Hstk Hu1] HΦ".

          iApply (Hproc with "[Hstk Hu1]").

          { 
            rewrite (stack_free_assertion_trnsl Γ (subst proc_pre subst_map') stk_id' stk_id mp) in Hproc_frame_pre. 2 : { apply stack_free_assertion_subst. destruct Hspec_StackFree as [Hpre_stack_free _]. done. }


            iFrame.
            pose proof (trnsl_assertion_w_lexpr_subst Γ proc_pre lexprs proc_args.*1 arg_vals stk_id mp u1 proc_frame_pre Hlexprs_arg_vals Hproc_pre Hproc_frame_pre) as Himpl.
            iApply Himpl. iFrame.
          }

          
          iNext. iExact "HΦ".

          }

          {
            iNext. iIntros "[Hstk [Hq Hcr']]".
            iApply "HΦ". iCombine "Hcr" "Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame. iExists (trnsl_val ret_val).
          
            destruct (trnsl_assertion Γ (subst proc_post (<["#ret_var":=LVar lvar_x]> subst_map)) stk_id
            (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0)) 
            eqn:Hpost; try done.
            
            iSplitR "Hq". 
            { rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done. rewrite trnsl_lval_trnsl_val_inverse. iFrame. } 
            
            { pose proof (trnsl_assertion_w_lexpr_subst_r Γ proc_post lexprs proc_args.*1 arg_vals lvar_x ret_val stk stk_id mp u proc_frame_post H Hlexprs_arg_vals Hpost Hproc_frame_post) as Himpl. iApply Himpl. iFrame. }
          }

        }

      }

      1 : {
        (* FPU *)
        unfold trnsl_hoare_triple; simpl.
        specialize (RAPack_fpuValid Γ RAPack old_val new_val) as HRA_fpu.
        destruct (Γ RAPack) as [i [U [Hdisc [Heq_car [Hindx [Hcomp Hval]]]]]].

        iIntros "[[Hstack Hown] Hcr]".
        iDestruct "Hown" as (l) "[%Heq Hown]".

        iFrame.

        apply (HRA_fpu) in H0.

        iMod (own_update _ 
          (transport (f_equal cmra_car Hindx) ((transport Heq_car old_val))) 
          (transport (f_equal cmra_car Hindx) ((transport Heq_car new_val)))
       with "Hown") as "Hown".

       { apply transport_cmra_update. exact H0.  }

       iModIntro. iExists l. iFrame. iPureIntro. exact Heq.

      }

    Admitted.
  
  End MainTranslation.