From New.generatedproof.hashtriemap Require Import hashtriemap.
From New.proof.hashtriemap Require Import prelude.
From New.proof.hashtriemap Require Import model.
From New.proof.hashtriemap Require Import aux.

From New.proof Require Import sync.
From New.proof.sync Require Import atomic.

From Perennial.base_logic.lib Require Import invariants.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.

From Perennial.goose_lang.lib Require Import struct.
From Perennial.goose_lang.lib Require Import atomic.
From Perennial.algebra Require Import auth_map ghost_var.

Section proof.
  Context `{hG: heapGS Σ, !invGS Σ, !ffi_semantics _ _}
    `{!globalsGS Σ} {go_ctx: GoContext}
    `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}.

  #[global] Instance : IsPkgInit hashtriemap := define_is_pkg_init True%I.
  #[global] Instance : GetIsPkgInitWf hashtriemap := build_get_is_pkg_init_wf.

  Lemma wp_newIndirectNode (parent: loc) (γ: ghost_names) (M: gmap w64 w64) :
    {{{ is_pkg_init hashtriemap ∗ hashtriemap_sub γ M }}}
      @! hashtriemap.newIndirectNode #parent
      {{{ (i: loc), RET (#i);
          ∃ (node: loc) (dead: atomic.Bool.t) (children: vec atomic.Value.t (uint.nat (W64 16))),
            i ↦s[hashtriemap.indirect :: "node"] node ∗
              node_is_indirect node i ∗
              i ↦s[hashtriemap.indirect :: "dead"] dead ∗
              i ↦s[hashtriemap.indirect :: "parent"] parent ∗
              i ↦s[hashtriemap.indirect :: "children"] children ∗
              indirect_rep i 0 0 M ∗
              is_indirect γ i 0 0 M }}}.
  Proof. Admitted.

  Lemma own_Uint32_agree u dq dq' v v' :
    own_Uint32 u dq v -∗ own_Uint32 u dq' v' -∗ ⌜v = v'⌝.
  Proof.
    iIntros "H1 H2".
    destruct (own_Uint32_combines_gives with "H1" "H2").
    pose proof (itrm u v v' dq dq' with "H1" "H2") as [Hcomb].
    iDestruct combine_sep_gives as "H".
    { exact Hcomb. }
    iDestruct ("H" with "[$H1 $H2]") as "#Hpers".
    iDestruct "Hpers" as %[_ Heq].
    iPureIntro. exact Heq.
  Qed.

  Lemma wp_HashTrieMap__initSlow (ht: loc) :
    {{{ is_pkg_init hashtriemap ∗ is_pkg_init atomic ∗ is_pkg_init sync ∗
          ∃ γ, hashtriemap_init ht γ }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "initSlow" #()
      {{{ RET #();
          ∃ γ, hashtriemap_init ht γ ∗
                 is_hashtriemap γ ht }}}.
  Proof.
    wp_start as "Hpre".
    iDestruct "Hpre" as (γ) "(#Hinit & #Hmu & Hht_tok)".

    wp_apply wp_with_defer as "%defer defer"; simpl subst.
    wp_auto.

    wp_apply (wp_Mutex__Lock with "[$Hmu]").
    iIntros "(Hown_mutex&Hmu_inv)".
    wp_auto.

    iAssert (hashtriemap_sub γ (∅: gmap w64 w64))%I as "Hsub".
    { rewrite /hashtriemap_sub /ht_map_frag big_sepM_empty. iFrame. }

    wp_apply wp_Uint32__Load.
    iInv "Hinit" as (b) "(>Hinited & >Hinit_tok & #Hstatus_done)" "Hclose".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iNext.
    iFrame.
    iIntros "Hinited".

    iDestruct (persistently_elim with "Hstatus_done") as "#Hstatus_done'".
    iClear "Hstatus_done".
    iRename "Hstatus_done'" into "Hstatus_done".

    destruct b; simpl in *.
    {
      iMod "Hmask".
      iClear "Hmask".
      iMod ("Hclose" with "[Hinit_tok Hinited Hstatus_done]") as "_".
      { iNext; iFrame; iFrame "Hinited Hstatus_done". }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "_".
      wp_auto.

      wp_apply (wp_Mutex__Unlock with "[$Hmu $Hown_mutex $Hmu_inv]").

      wp_finish.
      iExists γ.
      iFrame "Hinit Hmu Hht_tok".
      iExact "Hstatus_done".
    }

    iDestruct "Hmu_inv" as (b) "Hmu_inv".
    destruct b.
    {
      iDestruct (ghost_var_agree with "Hmu_inv Hinit_tok") as %Heq.
      inversion Heq.
    }

    iMod "Hmask".
    iClear "Hmask".
    iMod ("Hclose" with "[Hinit_tok Hinited Hstatus_done]") as "_".
    { iNext; iFrame; iFrame "Hstatus_done Hinited". }
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "_".
    wp_auto.

    wp_apply wp_newIndirectNode.
    { iFrame "Hsub". }
    iIntros (root_node_ptr) "root_node".
    wp_auto.

    iFrame.
    wp_apply wp_Value__Store.

    iInv "Hinit" as (b) "(>Hinited & >Hinit_tok & _)" "Hclose".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hmask".
    iNext.
    iFrame.
    iExists None.

    iDestruct "Hmu_inv" as "(Hinit_tok2 & Hseed & Hroot & Hpre_auth)".
    iDestruct (ghost_var_agree with "Hinit_tok Hinit_tok2") as %Heq.
    subst b.

    iFrame.

    iIntros "Hroot".
    iMod "Hmask".
    iClear "Hmask".
    iMod ("Hclose" with "[Hinit_tok Hinited Hstatus_done]") as "_".
    {
      iNext.
      iFrame.
      iFrame "Hstatus_done Hinited".
    }

    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "_".
    wp_auto.

    iDestruct "Hseed" as (seed) "Hseed".

    wp_apply (wp_store_ty with "Hseed").
    Unshelve.
    2: { eapply into_val_typed_w64. }

    iIntros "Hseed".

    wp_auto.
    wp_apply wp_Uint32__Store.

    iInv "Hinit" as (b) "(>Hinited & >Hinit_tok & _)" "Hclose".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iNext.
    iFrame.
    iIntros "Hinited".
    iMod "Hmask".
    iClear "Hmask".
    destruct b.
    {
      iDestruct (ghost_var_agree with "Hinit_tok Hinit_tok2") as %Heq.
      exfalso. congruence.
    }

    iMod (ghost_var_update_halves true with "Hinit_tok Hinit_tok2") as "(Htok1 & Htok2)".

    iDestruct (hashtriemap_pre_auth_to_auth with "Hpre_auth") as "Hauth".

    iDestruct "root_node" as (node dead children) "(Hnode & Hnode_hdr & Hdead & Hparent & Hchildren & Htrie & Hmu_is_mutex)".

    iAssert (ht_inv ht γ)%I with "[$]" as "Hhtinv".

    iMod (invariants.inv_alloc (nroot.@"hashtriemap") _ (ht_inv ht γ) with "[Hhtinv]") as "#His_map".
    { iNext. iExact "Hhtinv". }

    iMod ("Hclose" with "[Htok1 Hinited His_map]") as "_".
    { iNext. iFrame. iFrame "Hinited". iExact "His_map". }
    iApply fupd_mask_intro.
    {set_solver. }
    iIntros "_".
    wp_auto.

    iAssert (init_mu_inv ht γ)%I with "[Htok2]" as "Hmu_inv_true".
    { simpl. iExists true. iFrame "Htok2". }

    wp_apply (wp_Mutex__Unlock with "[$Hmu $Hown_mutex $Hmu_inv_true]").
    wp_finish.
    iExists γ.
    iFrame.
    iFrame "His_map Hmu Hinit".
  Qed.

  (*precondition: either inited is 0 and we call initSlow, or its 1 and we already have the initialization requirements*)
  Lemma wp_HashTrieMap__initHT (ht: loc) :
    {{{ is_pkg_init hashtriemap ∗ is_pkg_init atomic ∗ is_pkg_init sync ∗
          ∃ γ, hashtriemap_init ht γ }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "initHT" #()
      {{{ RET #();
          ∃ γ, hashtriemap_init ht γ ∗ is_hashtriemap γ ht }}}.
  Proof.
    wp_start as "Hpre".
    iDestruct "Hpre" as (γ) "(#Hinit & #Hmu & Hht_tok)".

    wp_auto.

    wp_apply wp_Uint32__Load.
    iInv "Hinit" as "Hinit2" "Hclose".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iNext.
    iDestruct "Hinit2" as (b) "(Hinited & Hinit_tok & #Hstatus_done)".
    iFrame.
    iIntros "Hinited".
    iMod "Hmask".
    iClear "Hmask".
    iMod ("Hclose" with "[Hinit_tok Hinited Hstatus_done]") as "_".
    { iNext. iFrame. iFrame "Hstatus_done". }
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "_".
    wp_auto.

    wp_if_destruct.
    - wp_apply (wp_HashTrieMap__initSlow with "[Hht_tok]").
      { iFrame. iFrame "Hinit Hmu". }
      iIntros.
      wp_finish.
    - wp_finish.
      iFrame.
      destruct b; simpl.
      + iFrame "Hinit Hmu".
        iExact "Hstatus_done".
      + exfalso. congruence.
  Qed.

  Lemma wp_hashInt (key: w64) (seed: w64) :
    {{{ is_pkg_init hashtriemap }}}
      @! hashtriemap.hashInt #key #seed
      {{{ (a: w64), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__Load (ht: loc) (key: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "Load" #key
      {{{ (a: w64) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__LoadOrStore (ht: loc) (key: w64) (value: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "LoadOrStore" #key #value
      {{{ (a: w64) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__expand (ht: loc) (oldEntry: loc) (newEntry: loc) (newHash: w64) (hashShift: w64) (parent: loc) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "expand" #oldEntry #newEntry #newHash #hashShift #parent
      {{{ (a: loc), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__Store (ht: loc) (key: w64) (old: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "Store" #key #old
      {{{ RET #(); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__Swap (ht: loc) (key: w64) (new: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "Swap" #key #new
      {{{ (a: w64) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__CompareAndSwap (ht: loc) (key: w64) (old: w64) (new: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "CompareAndSwap" #key #old #new
      {{{ (a: bool), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__LoadAndDelete (ht: loc) (key: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "LoadAndDelete" #key
      {{{ (a: w64) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__Delete (ht: loc) (key: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "Delete" #key
      {{{ RET #(); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__CompareAndDelete (ht: loc) (key: w64) (old: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "CompareAndDelete" #key #old
      {{{ (a: bool), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__find (ht: loc) (key: w64) (hash: w64) (checkValue: bool) (value: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "find" #key #hash #checkValue #value
      {{{ (a: loc) (b: w64) (c: loc) (d: loc), RET (#a, #b, #c, #d); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__All (ht: loc) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "All" #()
      {{{ (a: func.t), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__Range (ht: loc) (yield: func.t) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "Range" #yield
      {{{ RET #(); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__iter (ht: loc) (i: loc) (yield: func.t) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "iter" #i #yield
      {{{ (a: bool), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__Clear (ht: loc) :
    {{{ is_pkg_init hashtriemap }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "Clear" #()
      {{{ RET #(); True }}}.
  Proof. Admitted.

  Lemma wp_indirect__empty (i: loc) :
    {{{ is_pkg_init hashtriemap }}}
      i @ (ptrT.id hashtriemap.indirect.id) @ "empty" #()
      {{{ (a: bool), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_newEntryNode (key: w64) (value: w64) :
    {{{ is_pkg_init hashtriemap }}}
      @! hashtriemap.newEntryNode #key #value
      {{{ (a: loc), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_entry__lookup (e: loc) (key: w64) :
    {{{ is_pkg_init hashtriemap }}}
      e @ (ptrT.id hashtriemap.entry.id) @ "lookup" #key
      {{{ (a: w64) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_entry__lookupWithValue (e: loc) (key: w64) (value: w64) (checkValue: bool) :
    {{{ is_pkg_init hashtriemap }}}
      e @ (ptrT.id hashtriemap.entry.id) @ "lookupWithValue" #key #value #checkValue
      {{{ (a: w64) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_entry__swap (head: loc) (key: w64) (new: w64) :
    {{{ is_pkg_init hashtriemap }}}
      head @ (ptrT.id hashtriemap.entry.id) @ "swap" #key #new
      {{{ (a: loc) (b: w64) (c: bool), RET (#a, #b, #c); True }}}.
  Proof. Admitted.

  Lemma wp_entry__compareAndSwap (head: loc) (key: w64) (old: w64) (new: w64) :
    {{{ is_pkg_init hashtriemap }}}
      head @ (ptrT.id hashtriemap.entry.id) @ "compareAndSwap" #key #old #new
      {{{ (a: loc) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_entry__loadAndDelete (head: loc) (key: w64) :
    {{{ is_pkg_init hashtriemap }}}
      head @ (ptrT.id hashtriemap.entry.id) @ "loadAndDelete" #key
      {{{ (a: w64) (b: loc) (c: bool), RET (#a, #b, #c); True }}}.
  Proof. Admitted.

  Lemma wp_entry__compareAndDelete (head: loc) (key: w64) (value: w64) :
    {{{ is_pkg_init hashtriemap }}}
      head @ (ptrT.id hashtriemap.entry.id) @ "compareAndDelete" #key #value
      {{{ (a: loc) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_node__entry (n: loc) :
    {{{ is_pkg_init hashtriemap }}}
      n @ (ptrT.id hashtriemap.node.id) @ "entry" #()
      {{{ (a: loc), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_node__indirect (n: loc) :
    {{{ is_pkg_init hashtriemap }}}
      n @ (ptrT.id hashtriemap.node.id) @ "indirect" #()
      {{{ (a: loc), RET (#a); True }}}.
  Proof. Admitted.

End proof.
