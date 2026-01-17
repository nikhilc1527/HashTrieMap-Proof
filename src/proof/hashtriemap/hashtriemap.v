From New.generatedproof.hashtriemap Require Import hashtriemap.
From New.proof.hashtriemap Require Import prelude.
From New.proof.hashtriemap Require Import model.
From New.proof.hashtriemap Require Import aux.

From New.proof Require Import sync.
From New.proof.sync Require Import atomic.

From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.

From Perennial.goose_lang.lib Require Import atomic.
From Perennial.algebra Require Import auth_map ghost_var.

Open Scope Z_scope.

Section proof.
  Context `{hG: heapGS Σ, !invGS Σ, !ffi_semantics _ _}
    `{(* !mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64),  *)!ghost_varG Σ bool}
    `{!ghost_varG Σ (gmap w64 w64)}
    `{!mapG Σ w64 w64}
    `{!mapG Σ Z (gmap w64 w64)}
           `{!globalsGS Σ} {go_ctx: GoContext}.

  Definition map_get `{!IntoVal V} `{!IntoValTyped V t} (v: option V) : V * bool :=
    (default (default_val V) v, bool_decide (is_Some v)).

  #[global] Instance : IsPkgInit hashtriemap := define_is_pkg_init True%I.
  #[global] Instance : GetIsPkgInitWf hashtriemap := build_get_is_pkg_init_wf.

  Lemma wp_hashInt (key: w64) (seed: w64) :
    {{{ is_pkg_init hashtriemap }}}
      @! hashtriemap.hashInt #key #seed
      {{{ (a: w64), RET (#a); ⌜a = hash_key key⌝ }}}.
  Proof. Admitted.

  Lemma wp_newIndirectNode (γ: ghost_names) (parent: loc) (path: list Z) (hm: hash_map) :
    {{{ is_pkg_init hashtriemap }}}
      @! hashtriemap.newIndirectNode #parent
      {{{ (ind: loc), RET (#ind);
          indirect γ hm ind path }}}.
  Proof.
    wp_start as "Hpre".
    wp_auto.
    rename i_ptr into ind_ptr.
    iRename "i" into "ind".

    wp_apply (wp_slice_make2 (V:=atomic.Value.t)).
    { unfold hashtriemap.nChildren. word. }
    iIntros (children) "(Hchildren & _)".
    wp_auto.
    wp_alloc ind_struct as "ind_struct".
    wp_auto.

    set (children_vs := replicate (sint.nat (W64 hashtriemap.nChildren))
                                  atomic.into_val_typed_Value.(default_val atomic.Value.t)).

    (*
      TODO:
      This invariant feels wrong because i=idx throughout the loop, but then i=idx+1 at the end of the loop
      Either this invariant is actually right or the way goose handles slice range for loops is a bit off
     *)
    iAssert (
        ∃ (vs: list atomic.Value.t) (idx i: w64),
          "Hvs" :: children ↦* vs ∗
          "i" :: i_ptr ↦ i ∗
          "idx" :: idx_ptr ↦ idx ∗
          "%Hi_idx" :: ⌜sint.Z i >= sint.Z idx⌝ ∗
          "%Hi_bound" :: ⌜uint.Z i <= hashtriemap.nChildren⌝ ∗
          "%Hlen" :: ⌜length vs = Z.to_nat hashtriemap.nChildren⌝ ∗
          "%Hprefix" :: ⌜∀ (j: nat), j ≥ 0 → j < uint.Z i →
                                     ∃ av, vs !! j = Some av ∧
                                           av = atomic.Value.mk (interface.mk (ptrT.id hashtriemap.node.id) (# null))⌝ ∗
          "%Hsuffix" :: ⌜∀ (j: nat), j >= uint.Z i → j < length vs → vs !! j = children_vs !! j⌝
      )%I with "[$Hchildren $i $idx]" as "IH".
    {
      iNamed.
      unfold hashtriemap.nChildren.
      iPureIntro.
      simpl.
      split_and!; auto; try word.
      iIntros (j Hj Hj2).
      exfalso.
      word.
    }

    wp_for "IH".

    iDestruct (own_slice_len_keep with "Hvs") as "(Hvs & %Hlen_slice & _)".

    wp_if_destruct.
    2: {
      wp_alloc node as "node".

      iApply struct_fields_split in "ind_struct".
      iNamed "ind_struct".
      iApply struct_fields_split in "node".
      iNamed "node".
      simpl.
      wp_auto.

      iAssert (
          indirect γ hm ind_struct path
        )%I as "Hinv".
      {
        (* TODO: whatever this invariant ends up being, need to prove it here with M=∅ *)
        (* iMod (init_Mutex with "Hmu Hinv") as "Hmu_init". *)
        admit.
      }

      iApply "HΦ".
      iFrame "Hinv".
    }

    wp_pure.
    { split; word. }

    have Hlookup_vs : (vs !! sint.nat i = Some (atomic.into_val_typed_Value.(default_val atomic.Value.t))).
    {
      have Hidx_lt : uint.nat i < length vs.
      { rewrite Hlen. word. }

      have Hsuffix_i : vs !! uint.nat i = children_vs !! uint.nat i.
      { apply Hsuffix; [lia|exact Hidx_lt]. }

      have Hsuit : sint.nat i = uint.nat i.
      { word. }

      rewrite Hsuit.
      rewrite Hsuffix_i.
      rewrite lookup_replicate_2; auto.
      word.
    }

    wp_apply (wp_load_slice_elem with "[$Hvs]"); auto.
    { word. }

    iIntros "Hvs".

    wp_auto.

    wp_pure.
    { split; cbn; word. }

    wp_auto.

    iDestruct ((own_slice_elem_acc) with "[$Hvs]") as "[Helem Hcont]"; eauto.
    { word. }

    iAssert (own_Value (slice.elem_ref_f children atomic.Value i) 1 interface.nil)%I
      with "[Helem]" as "Helem".
    {
      auto.
    }

    wp_apply wp_Value__Store.

    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iNext.
    iFrame "Helem".
    iIntros "Helem".
    iMod "Hmask".
    iClear "Hmask".
    iApply fupd_mask_intro.
    {set_solver. }
    iIntros "_".
    wp_auto.

    iDestruct ("Hcont" with "Helem") as "Hvs".

    wp_for_post.

    iFrame "HΦ parent ind ind_struct".

    iFrame.

    iSplit.
    { word. }

    iSplit.
    { word. }
    iSplit.
    {
      iPureIntro.
      rewrite length_insert.
      exact Hlen.
    }
    iSplit.
    - iPureIntro. intros j Hj_ge Hj_lt.

      have Hj_lte : j ≤ uint.Z i.
      { word. }
      clear Hj_lt.

      apply Z_le_lt_eq_dec in Hj_lte.
      destruct Hj_lte as [Hlt | Heq].

      + (* j < i *)
        specialize (Hprefix j) as Hprefix.
        specialize (Hprefix Hj_ge Hlt).
        destruct Hprefix as (av & Hlookup & Hav).
        exists av.
        split; auto.

        rewrite list_lookup_insert_ne; auto.
        word.
      + (* j = i *)
        exists {| atomic.Value.v' := interface.mk (ptrT.id hashtriemap.node.id) (# null) |}.
        split; auto.
        rewrite list_lookup_insert.
        have Hbool : (sint.nat i = j ∧ (sint.nat i < length vs)%nat)%nat.
        { word. }
        by destruct (decide (sint.nat i = j ∧ (sint.nat i < length vs)%nat)) as [H|H];
        [reflexivity | exfalso; exact (H Hbool)].
    - iPureIntro. intros j Hj_ge Hj_lt.

      have Hj_ge_i1_nat : (j ≥ uint.nat i + 1)%nat.
      { word. }
      have Hj_ge_i_Z : (j >= uint.Z i).
      { word. }
      have Hj_ge_i1_Z : (j >= uint.Z i + 1).
      { word. }
      have Hj_lt_len : (j < length vs).
      { rewrite length_insert in Hj_lt. word. }

      specialize (Hsuffix j) as Hsuffix.
      specialize (Hsuffix Hj_ge_i_Z Hj_lt_len).
      rewrite list_lookup_insert_ne; auto.
      word.
  Admitted.            (* only admitted because of the ind invariant needing proof *)

  Lemma wp_HashTrieMap__initSlow (ht: loc) (γ: ghost_names) (* P {Htimeless: ∀ m, Timeless (P m)} *) :
    {{{ is_pkg_init hashtriemap ∗ is_pkg_init atomic ∗ is_pkg_init sync ∗
        hashtriemap_init ht γ (* P *) }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "initSlow" #()
      {{{ RET #();
          hashtriemap_init ht γ (* P *) ∗ is_hashtriemap γ ht (* P *) }}}.
  Proof.
    wp_start as "Hpre".
    iDestruct "Hpre" as "(#Hinit & #Hmu)".

    wp_apply wp_with_defer as "%defer defer"; simpl subst.
    wp_auto.

    wp_apply (wp_Mutex__Lock with "[$Hmu]").
    iIntros "(Hown_mutex&Hmu_inv)".
    wp_auto.

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
      iFrame "Hinit Hmu".
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

    (* TODO: have lemma to initialize empty_map, and give the ptsto_mut part to newIndirectNode and the auth_map used for constructing ht_inv below *)
    wp_apply (wp_newIndirectNode γ null [] ∅).
    iIntros (root_node_ptr) "root_node".
    wp_auto.

    iFrame.
    wp_apply wp_Value__Store.

    iInv "Hinit" as (b) "(>Hinited & >Hinit_tok & _)" "Hclose".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hmask".
    iNext.
    iFrame.
    iExists interface.nil.

    iDestruct "Hmu_inv" as "(Hinit_tok2 & Hseed & Hroot)".
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

    iAssert (ht_inv ht γ)%I (* with "[$]" *) as "Hhtinv".
    {
      admit.
    }

    iMod (invariants.inv_alloc mapN _ (
            (*                      ∃ m, *)
            (* "HP" :: P m ∗ *)
            "Hinv" :: ht_inv ht γ
                               ) with "[Hhtinv]") as "#His_map".
    { iNext. iFrame "Hhtinv". }

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
    iFrame.
    iFrame "His_map Hmu Hinit".
  Admitted.

  (*precondition: either inited is 0 and we call initSlow, or its 1 and we already have the initialization requirements*)
  Lemma wp_HashTrieMap__initHT (ht: loc) (γ: ghost_names) (* P {Htimeless: ∀ m, Timeless (P m)} *) :
    {{{ is_pkg_init hashtriemap ∗ is_pkg_init atomic ∗ is_pkg_init sync ∗
        hashtriemap_init ht γ (* P *) }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "initHT" #()
      {{{ RET #();
          hashtriemap_init ht γ (* P *) ∗ is_hashtriemap γ ht (* P *) }}}.
  Proof.
    wp_start as "Hpre".
    iDestruct "Hpre" as "(#Hinit & #Hmu)".

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
    - wp_apply (wp_HashTrieMap__initSlow).
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

  (* dont actually need the is_hashtriemap precondition for any of the lemmas because initHT gives it to us *)
  (* Lemma wp_HashTrieMap__Load (ht: loc) (key: w64) (γ: ghost_names) P Q *)
  (*       {Htimeless: ∀ m, Timeless (P m)} : *)
  (*   {{{ is_pkg_init hashtriemap ∗ is_pkg_init atomic ∗ is_pkg_init sync ∗ *)
  (*       hashtriemap_init ht γ P ∗ is_hashtriemap γ ht P ∗ *)
  (*       (∀ m, P m -∗ |==> P m ∗ Q (map_get (m !! key))) *)
  (*   }}} *)
  (*     ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "Load" #key *)
  (*     {{{ (v: w64) (ok: bool), RET (#v, #ok); Q (v, ok) }}}. *)
  (* Proof. *)
  Lemma wp_HashTrieMap__Load (ht: loc) (key: w64) (γ: ghost_names) :
    {{{ is_pkg_init hashtriemap ∗ is_pkg_init atomic ∗ is_pkg_init sync ∗
        hashtriemap_init ht γ ∗ is_hashtriemap γ ht
    }}}
      ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "Load" #key
      {{{ (v: w64) (ok: bool), RET (#v, #ok); True }}}.
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
