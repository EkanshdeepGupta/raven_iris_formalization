From iris.algebra Require Export frac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.prelude Require Import options.

From iris.algebra Require Export auth excl frac numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation par.

Class cinvG Σ := { #[local] cinv_inG :: inG Σ fracR }.

(* Definition cinvΣ : gFunctors := #[GFunctor fracR]. *)

(* Global Instance subG_cinvΣ {Σ} : subG cinvΣ Σ → cinvG Σ. *)
(* Proof. solve_inG. Qed. *)

Section defs.
    Context `{!invGS_gen hlc Σ, !cinvG Σ}.
  
    Definition cinv_own (γ : gname) (p : frac) : iProp Σ := own γ p.
  
    Definition cinv (N : namespace) (γ : gname) (P : iProp Σ) : iProp Σ :=
      inv N (P).
End defs.
  
Global Instance: Params (@cinv) 5 := {}.

Section proofs.

  (* Context `{!invGS_gen hlc Σ, !cinvG Σ}. *)
  Context `{heapGS Σ}.

  (* Global Instance cinv_own_timeless N γ  P : (Timeless P) -> Timeless (cinv N γ P).
  Proof. rewrite /cinv. intros. apply _. Qed. *)

  (* Context (N: namespace). *)
  (* Context {Σ: gFunctors}. *)

  Definition N1 := nroot .@ "1".
  Definition N2 := nroot .@ "2".


  Definition inv2 (x: val) : iProp Σ := inv N2 (∃ l : loc, ⌜x = #l⌝ ∗ l ↦ #1)%I
  ∗ £ 1.

  Definition inv1 (x: val) : iProp Σ := inv N1 (inv2 x) ∗ £ 1.

  Definition inv2' (x: val) : iProp Σ := inv N2 (∃ l : loc, ⌜x = #l⌝ ∗ l ↦ #1)%I.

  Definition inv1' (x: val) : iProp Σ := inv N1 (inv2' x).

  Global  Instance inv2_timeless (x: val) : Timeless (inv2' x).
  Proof.
    unfold Timeless.
    iIntros "#H".
    iAssert (inv2' x) as "H1".
    - admit.
    - 

    unfold bi_except_0.
    iRight. unfold inv2'.
    (* unfold inv.  *)
    rewrite invariants.inv_unseal /invariants.inv_def.
    iModIntro.
    iIntros.
    iApply "H1".
  Abort.
    (* iMod ("H" E) as "H1".

    iMod (inv_acc_timeless _ N2 _) as "H".
    unfold inv.
    unfold invariants.inv_aux.
    Search bi_later inv. 
    Unset Printing Notations.
  Abort. *)


  Lemma nested_inv_later (x: val) :
    {{{ inv1 x }}}
      x <- #1
    {{{RET #(); True }}}.
  Proof.
    iIntros "%Φ [#HInv H] HΦ".
    (* unfold inv1. *)
    iInv "HInv" as "[#HInv2 Hc]".
    iMod (lc_fupd_elim_later with "H HInv2") as "#HInv2'".

    iInv "HInv2'" as ">H".
    iDestruct "H" as "(%l & %xi & Hl)".
    rewrite xi.
    wp_store .
    iModIntro.
    iSplitL "Hl".
    - iNext. iExists l; by iFrame.
    - iModIntro.
    + iFrame "HInv2". iFrame "Hc". iApply "HΦ".
    done.
  Qed.

  Lemma nested_inv_stuck (x: val) :
    {{{ inv1' x }}}
        x <- #1
    {{{RET #(); inv1' x }}}.
  Proof. 
    iIntros "%Φ #HInv HΦ".
    (* unfold inv1. *)
    iInv "HInv" as "#HInv2".
    (* iMod (lc_fupd_elim_later with "H HInv2") as "#HInv2'". *)

    Fail iInv "HInv2" as ">H".
    (* stuck *)
  Abort.

  Lemma nested_inv2 (x: val) :
    {{{ inv1' x }}}
      let v := #1 in
      v+#1;;
      x <- #1
    {{{RET #(); inv1' x }}}.
  Proof.
    iIntros "%Φ #HInv HΦ".
    unfold inv1.
    wp_bind (#1 + #1)%E.
    iInv "HInv" as "#HInv2".
    wp_pure.
    iModIntro.
    iFrame "HInv2".
    wp_pures.
    iInv "HInv2" as ">H".
    iDestruct "H" as "(%l & %H1 & H2)".
    rewrite H1.
    wp_store.
    iModIntro.
    iSplitL "H2".
    - iNext. iExists l; by iFrame.
    - iApply "HΦ". by iFrame.
  Qed.