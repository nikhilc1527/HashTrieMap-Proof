From iris.bi.lib Require Import atomic.

From New.code.hashtriemap Require Import hashtriemap.
From New.generatedproof.hashtriemap Require Import hashtriemap.

From New.proof Require Import atomic mutex.

From Perennial.algebra Require Import auth_map.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.Helpers Require Import NamedProps.
Import named_props_ascii_notation.
From Perennial.algebra Require Import ghost_var.

From New.proof.hashtriemap Require Import aux.
From New.proof.hashtriemap Require Import paths.
From New.proof.hashtriemap Require Import model.
From New.proof.hashtriemap Require Import hashtriemap_done.

Open Scope Z_scope.

Section proof.
  Context `{hG: heapGS Σ, !ffi_semantics _ _}
    `{!ghost_varG Σ bool}
    `{!ghost_varG Σ (gmap w64 w64)}
    `{!mapG Σ w64 w64}
    `{!mapG Σ Z (gmap w64 w64)}
    `{!globalsGS Σ} {go_ctx: GoContext}.

  #[global] Instance : IsPkgInit hashtriemap := define_is_pkg_init True%I.
  #[global] Instance : GetIsPkgInitWf hashtriemap := build_get_is_pkg_init_wf.

  Definition orphaned_entry e (key: K) (value: V) n : iProp Σ :=
    "#Hnode" ∷ e ↦s[hashtriemap.entry :: "node"]□ n ∗
    "#Hkey" ∷ e ↦s[hashtriemap.entry :: "key"]□ key ∗
    "#Hvalue" ∷ e ↦s[hashtriemap.entry :: "value"]□ value ∗
    "Hoverflow" ∷ struct.field_ref_f hashtriemap.entry "overflow" e ↦ᵥ interface.mk (ptrT.id hashtriemap.entry.id) (# null) ∗
    "#HisEntry" ∷ n ↦s[hashtriemap.node :: "isEntry"]□ true ∗
    "#Hent" ∷ n ↦s[hashtriemap.node :: "ent"]□ e ∗
    "#Hind" ∷ n ↦s[hashtriemap.node :: "ind"]□ null.
  #[global] Transparent orphaned_entry.

  Lemma wp_newEntryNode (key: w64) (value: w64) :
    {{{ is_pkg_init hashtriemap }}}
      @! hashtriemap.newEntryNode #key #value
      {{{ (e: loc) (n: loc), RET (#e); orphaned_entry e key value n }}}.
  Proof.
    wp_start.
    wp_auto.
    wp_alloc e as "eval".
    wp_auto.
    iApply struct_fields_split in "eval".
    iNamed "eval".
    simpl.
    wp_apply wp_Value__Store.
    iApply fupd_mask_intro; first apply empty_subseteq.
    iIntros "Hmask".
    iNext.
    iFrame "Hoverflow".
    iIntros "Hoverflow".
    iMod "Hmask" as "_".
    iModIntro.
    wp_auto.
    wp_alloc n as "n".
    iApply struct_fields_split in "n".
    iNamed "n".
    simpl.
    iPersist "Hkey".
    iPersist "Hvalue".
    iPersist "HisEntry".
    iPersist "Hent".
    iPersist "Hind".
    wp_pure.
    wp_pure.
    wp_load.
    wp_pure.
    wp_store.
    iPersist "Hnode".
    wp_auto.
    iApply "HΦ".
    unfold orphaned_entry.
    iFrame.
    iFrame "#".
  Qed.

  (* if you can provide an updated own_path after one program step, then i give you back an entry *)
  (* Lemma wp_newEntryNode (key: w64) (value: w64) γ path h : *)
  (*   ∀ Φ, *)
  (*   is_pkg_init hashtriemap -∗ *)
  (*   ( *)
  (*     ⌜uint.Z (hash_key key) = h⌝ ∗ *)
  (*     ⌜belongs_to_path path h⌝ ∗ *)
  (*     (|={⊤,∅}=> ∃ rest_map, *)
  (*        own_path γ.(map_name) 1 path (singleton_map_fn h (<[key:=value]> rest_map)) ∗ *)
  (*        (∀ e, entry γ 1 e path ={∅,⊤}=∗ Φ #e)) *)
  (*   ) -∗ *)
  (*   WP @! hashtriemap.newEntryNode #key #value {{ Φ }}. *)
  (* (* Lemma wp_newEntryNode (key: w64) (value: w64) γ path h rest_map : *) *)
  (* (*   {{{ is_pkg_init hashtriemap ∗ *) *)
  (* (*       ⌜uint.Z (hash_key key) = h⌝ ∗ *) *)
  (* (*       ⌜belongs_to_path path h⌝ ∗ *) *)
  (* (*       own_path γ.(map_name) 1 path (singleton_map_fn h (<[key:=value]> rest_map)) *) *)
  (* (*   }}} *) *)
  (* (*     @! hashtriemap.newEntryNode #key #value *) *)
  (* (*     {{{ (e: loc), RET (#e); entry γ 1 e path }}}. *) *)
  (* Proof. *)
  (*   wp_start. *)
  (*   iDestruct "HΦ" as "(Hhash & Hbelongs & Hfupd)". *)
  (*   wp_auto. *)
  (*   wp_alloc e as "eval". *)
  (*   wp_auto. *)
  (*   iDestruct (typed_pointsto_not_null e 1 ({| *)
  (*                hashtriemap.entry.node' := null; *)
  (*                hashtriemap.entry.overflow' := *)
  (*                  {| atomic.Value.v' := interface.nil |}; *)
  (*                hashtriemap.entry.key' := key; *)
  (*                hashtriemap.entry.value' := value *)
  (*              |}) with "[$eval]") as %enotnull. *)
  (*   { vm_compute. auto. } *)
  (*   iApply struct_fields_split in "eval". *)
  (*   simpl. *)
  (*   iNamed "eval". *)
  (*   wp_apply wp_Value__Store. *)
  (*   iApply fupd_mask_intro; first apply empty_subseteq. *)
  (*   iIntros "Hmask". *)
  (*   iNext. *)
  (*   iFrame "Hoverflow". *)
  (*   iIntros "Hoverflow". *)
  (*   iMod "Hmask" as "_". *)
  (*   iModIntro. *)
  (*   wp_auto. *)
  (*   wp_alloc n as "n". *)
  (*   iApply struct_fields_split in "n". *)
  (*   simpl. *)
  (*   iNamed "n". *)
  (*   iPersist "HisEntry". *)
  (*   iPersist "Hent". *)
  (*   iPersist "Hind". *)
  (*   iPersist "Hkey". *)
  (*   iPersist "Hvalue". *)
  (*   (* iDestruct "Hpre" as "[Ha [Hb Hc]]". *) *)
  (*   iApply fupd_wp. *)
  (*   (* wp_bind. *) *)
  (*   (* wp_apply wp_atomic. *) *)
  (*   (* { apply _. } *) *)
  (*   iMod "Hfupd". *)
  (*   iDestruct "Hfupd" as (rest_map) "[Hown_path Hcont]". *)
  (*   (* iNamed "Hfupd". *) *)
  (*   (* iDestruct "Hc" as "" *) *)
  (*   iMod (inv_alloc entryN _ (entry_inv γ 1 (entry γ 1) e path) with "[Hhash Hbelongs Hown_path Hoverflow]") as "Hinv". *)
  (*   { *)
  (*     iNext. *)
  (*     unfold entry_inv. *)
  (*     rewrite decide_False; [|exact enotnull]. *)
  (*     unfold entry_step. *)
  (*     iExists null. *)
  (*     rewrite /named. *)
  (*     iFrame "Hhash Hbelongs". *)
  (*     simpl. *)
  (*     iSplitL "Hown_path". *)
  (*     + iExists value. iExists rest_map. *)
  (*       iFrame "Hown_path". *)
  (*       iFrame "#". *)
  (*     + iFrame. *)
  (*       iNext. *)
  (*       iFrame. *)
  (*   } *)
  (*   iMod ("Hcont" with "[Hinv]") as "HΦ". *)
  (*   { *)
  (*     iApply entry_unfold. *)
  (*     rewrite /entry_F /named. *)
  (*     iFrame "Hinv". *)
  (*   } *)
  (*   iModIntro. *)
  (*   wp_auto. *)
  (*   iApply "HΦ". *)
  (* Qed. *)

  Lemma wp_load_root γ (ht: loc) :
    ∀ (Φ: val → iProp Σ),
    is_pkg_init atomic -∗
    (inv mapN (ht_inv ht γ)) -∗
    (∀ root : loc,
       "#Hroot_indirect" :: indirect γ root [] -∗
       Φ #root)
    -∗
    WP interface.type_assert
      (#
         (method_callv (ptrT.id atomic.Value.id) "Load"
            (#(struct.field_ref_f hashtriemap.HashTrieMap "root" ht)))
         (#()))
      (#(ptrT.id hashtriemap.indirect.id))
      {{ v, Φ v }}.
  Proof.
    intros.
    iIntros "#?".
    iIntros "#His_map".
    iIntros "HΦ".

    wp_apply (wp_Value__Load with "[$]").
    iInv "His_map" as "Hhtinv" "Hclose".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iNext.
    iNamed "Hhtinv".
    iFrame "Hown_root".
    iIntros "Hown_root".
    iMod "Hmask".
    iClear "Hmask".

    unfold ht_inv.
    iMod ("Hclose" with "[$Hauth_map $Huser_map $Hown_root $Hroot_indirect]") as "_"; [iNext; iPureIntro; done|].

    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "_".

    wp_apply wp_interface_type_assert.
    { auto. }
    iApply "HΦ".
    iExact "Hroot_indirect".
  Qed.

  Lemma wp_HashTrieMap__LoadOrStore (ht: loc) (key: K) (value: V) (γ: ghost_names) :
    ∀ (Φ: val → iProp Σ),
    (is_pkg_init hashtriemap ∗ is_pkg_init atomic ∗ is_pkg_init sync) -∗
    ("Hinit" :: hashtriemap_init ht γ ∗
    "Hau" ::
      AU <{ ∃∃ m : gmap K V, own_ht_map γ m }>
      @ ht_au_mask, ∅
                    <{ ∀∀ new_m load_res new_v,
                         ⌜ (new_m, load_res, new_v) = match m !! key with
                                               | Some old_v => (m, true, old_v)
                                               | None => (<[key := value]> m, false, value)
                                               end ⌝ ∗
                         own_ht_map γ new_m, COMM Φ (#new_v, #load_res)%V }>)
                      -∗
                    WP ht @ (ptrT.id hashtriemap.HashTrieMap.id) @ "LoadOrStore" #key #value {{ Φ }}.
  Proof.
    wp_start.
    iNamed "HΦ".

    wp_apply wp_with_defer as "%defer defer"; simpl subst.
    wp_auto.

    wp_apply (wp_HashTrieMap__initHT with "[$]").
    iIntros.
    iNamed.
    iNamed "His_map".
    wp_auto.

    wp_apply wp_hashInt.
    iIntros (hash) "%Hhash".

    wp_auto.
    iPersist "hash".
    iPersist "key".
    iPersist "value".

    iAssert (
        (* ∃ (HIP: bool), *)
        (*   if HIP *)
        (*   then *)
        (*     ∃ nodeptr children_slice next_nibble path cur, *)
        (*       "slot" ∷ slot_ptr ↦ slice.elem_ref_f children_slice atomic.Value next_nibble ∗ *)
        (*       "n" ∷ n_ptr ↦ nodeptr ∗ *)
        (*       "Hcur" ∷ i_ptr ↦ cur ∗ *)
        (*       "Hhash_shift" ∷ hashShift_ptr ↦ w64_word_instance.(word.sub) (W64 (sh path)) (W64 4) *)
        (*   else *)
            ∃ slot n i shift,
              "slot" :: slot_ptr ↦ slot ∗
              "n" :: n_ptr ↦ n ∗
              "i" ∷ i_ptr ↦ i ∗
              "hashShift" ∷ hashShift_ptr ↦ shift
      )%I with "[$slot $n $i $hashShift]" as "Houter_loop_inv".

    wp_for "Houter_loop_inv".

    wp_bind (
        interface.type_assert
          (#
             (method_callv (ptrT.id atomic.Value.id) "Load"
                (#(struct.field_ref_f hashtriemap.HashTrieMap "root" ht)))
             (#()))
          (#(ptrT.id hashtriemap.indirect.id))
          ).

    iApply (wp_load_root with "[# $] [//]").
    iIntros.
    iNamed.
    wp_auto.

    set h := uint.Z (hash_key key).

    iAssert (∃ (path: path) (shift: w64) (cur: loc) (HIP: bool) (sl: loc) (n: loc),
                "slot" ∷ slot_ptr ↦ sl ∗
                "n" ∷ n_ptr ↦ n ∗
                "Hcur" :: i_ptr ↦ cur ∗
                "Hhash_shift" :: hashShift_ptr ↦ shift ∗
                "#Hi_indirect" :: indirect γ cur path ∗
                "%Hshift" :: ⌜shift = sh path⌝ ∗
                "%Hpath_len" :: ⌜length path < 16⌝ ∗
                "%Hkey_path" :: ⌜belongs_to_path path h⌝ ∗
                "haveInsertPoint" :: haveInsertPoint_ptr ↦ HIP ∗ (* HIP actually doesnt matter *)
                "%HIP" :: ⌜shift ≠ 0⌝
            )%I with ("[$Hroot_indirect $hashShift $i $haveInsertPoint $slot $n]") as "Hloop_inv".
    {
      repeat iSplit; eauto; iPureIntro; eauto.
      unfold belongs_to_path, sh, path_to_prefix.
      simpl.
      rewrite Z.shiftr_div_pow2; try word.
    }

    wp_for "Hloop_inv".

    simpl.

    iEval (rewrite indirect_unfold /indirect_F) in "Hi_indirect".
    iNamed "Hi_indirect".

    wp_if_destruct.
    {
      simpl in *.
      exfalso.
      apply HIP0.
      exact e.
    }

    iDestruct (own_slice_len with "Hchildren_slice") as "(%Hlen_children_16 & _)".
    have Hlen_children : uint.Z children_slice.(slice.len_f) = 16.
    { word. }
    clear Hlen_children_16.

    unfold hashtriemap.nChildrenLog2, hashtriemap.nChildrenMask in *.
    wp_pure.
    {
      have Hlen16 : uint.Z children_slice.(slice.len_f) = 16 by word.
      set (x := w64_word_instance.(word.sru) (hash_key key)
                                    (w64_word_instance.(word.sub) (W64 (64 - 4 * length path)) (W64 4))).
      have Hnib_u : 0 ≤ uint.Z (w64_word_instance.(word.and) x (W64 15)) < 16.
      {
        rewrite word.unsigned_and_nowrap.
        change (uint.Z (W64 15)) with 15.
        change 15 with (Z.ones 4).
        rewrite Z.land_ones; word.
      }
      have Hsint :
        sint.Z (w64_word_instance.(word.and) x (W64 15)) =
        uint.Z (w64_word_instance.(word.and) x (W64 15)).
      { word. }
      rewrite Hsint.
      word.
    }

    set next_nibble := (w64_word_instance.(word.and)
                                            (w64_word_instance.(word.sru)
                                                                 (hash_key key)
                                                                 (w64_word_instance.(word.sub)
                                                                                      (W64 (sh path))
                                                                                      (W64 4)))
                                            (W64 15)).

    have Hnib_u : 0 ≤ uint.Z next_nibble < 16.
    {
      unfold next_nibble.
      rewrite word.unsigned_and_nowrap.
      change (uint.Z (W64 15)) with 15.
      split.
      - apply Z.land_nonneg.
        right.
        word.
      - change 15 with (Z.ones 4).
        rewrite Z.land_ones.
        + apply Z_mod_lt.
          word.
        + word.
    }

    have Hlt_nat : (sint.nat next_nibble < length children_vals)%nat by
                     (rewrite Hchildren_len; word).
    destruct (lookup_lt_is_Some_2 children_vals (sint.nat next_nibble) Hlt_nat)
      as [v Hv].

    wp_auto.

    have Hdom : h ∈ path_to_domain path.
    {
      unfold path_to_domain.
      rewrite list_elem_of_filter.
      split.
      - exact Hkey_path.
      - apply full_domain_elem.
    }

    wp_apply wp_Value__Load.
    iInv "His_map" as "Hhtinv" "Hclose_ht".
    iInv "Hind_inv" as "HI" "Hclose_ind".

    unfold own_ht_map.
    iApply fupd_mask_intro.
    { apply empty_subseteq.
    (* set_solver. doesnt work, only when Hdom is defined? *) }
    iIntros "Hmask".
    iNext.

    iEval (unfold childrenP) in "HI".

    iNamed "HI".

    iNamed "Hhtinv".
    iNamed "Hinv".
    iNamedSuffix "Hinv" "2".

    iDestruct (big_sepL_lookup_acc with "Hchildren") as "[Hchild Hchildren_close]".
    { exact Hv. }
    iNamed "Hchild".
    iExists (interface.mk (ptrT.id hashtriemap.node.id) (# nodeptr)).
    replace (W64 (sint.nat next_nibble)) with next_nibble by word.
    iFrame "Hown_child".
    iIntros "Hown_child".

    unfold ht_load_ret.
    iEval (unfold childP) in "Hchild".

    (* unfold own_path. *)

    destruct (decide (nodeptr = null)).
    {
      iMod "Hmask" as "_".

      iDestruct ("Hchildren_close" with "[Hown_child Hchild]") as "Hchildren".
      { iExists nodeptr. iFrame. unfold childP. rewrite decide_True; [iFrame|exact e]. }

      iMod ("Hclose_ind" with "Hchildren") as "_".
      iMod ("Hclose_ht" with "[$Hown_root2 $Hauth_map $Huser_map]") as "_".
      { iFrame "#". done. }
      clear hm user_map Hflat2 Hbuckets2 Hbuckets_rev2.

      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "_".

      wp_apply wp_interface_type_assert.
      { auto. }

      wp_bind.
      replace (bool_decide (nodeptr = null)) with true.
      2: { symmetry. rewrite (bool_decide_eq_true (nodeptr = null)). exact e. }

      wp_auto.
      wp_for_post.

      wp_apply wp_Mutex__Lock.
      { iFrame "#". }

      iIntros "(Hown_mutex & Hx)".
      iNamed "Hx".
      iEval (unfold childrenP) in "Hmu_inv".
      iNamed "Hmu_inv".

      wp_auto.

      wp_apply (wp_Value__Load with "[$]").
      iApply fupd_mask_intro; first apply empty_subseteq.
      iIntros "Hmask".
      iNext.

      iDestruct (big_sepL_lookup_acc with "Hchildren") as "[Hchild Hchildren_close]".
      { exact Hv. }
      iNamed "Hchild".
      iExists (interface.mk (ptrT.id hashtriemap.node.id) (# nodeptr0)).
      replace (W64 (sint.nat next_nibble)) with next_nibble by word.
      iFrame "Hown_child".
      iIntros "Hown_child".

      iMod "Hmask" as "_".
      iModIntro.

      wp_apply wp_interface_type_assert; [auto|].
      wp_if_destruct.
      - wp_apply wp_Bool__Load.
        iApply fupd_mask_intro; first apply empty_subseteq.
        iIntros "Hmask".
        iFrame "Hdead".
        iIntros "Hdead".
        iMod "Hmask" as "_".
        iApply fupd_mask_intro; first set_solver.
        iIntros "_".
        simpl.

        wp_if_destruct.
        {
          iDestruct ("Hchildren_close" with "[$Hchild $Hown_child]") as "Hchildren".
          wp_apply (wp_Mutex__Unlock with "[$Hind_mutex $Hdead $Hchildren $Hown_mutex]").
          wp_for_post.
          iFrame.
        }
        wp_for_post.

        iFrame.
        iEval (unfold childP) in "Hchild".
        iSimpl in "Hchild".

        wp_apply wp_newEntryNode.
        iIntros (e n2) "orphaned".
        unfold orphaned_entry.
        iNamedSuffix "orphaned" "_o".

        wp_auto.
        wp_apply wp_Value__Store.

        iClear "Hroot_indirect".
        iClear "Hroot_indirect2".
        clear rooti.

        iInv "His_map" as (rooti hm user_map) "(>? & >? & >? & Hroot_indirect & >? & >? & >?)" "Hclose_map".
        iInv "Hind_inv" as "Hind" "Hclose_ind_inv".
        iEval (unfold childrenP) in "Hind".
        iNamed.
        iMod (fupd_mask_subseteq ht_au_mask) as "Hau_close_mask".
        { unfold ht_au_mask; apply subseteq_difference_l; set_solver. }

        iDestruct (big_sepL_elem_of_acc with "Hchild") as "[Hptsto Hptsto_close]".
        { exact Hdom. }
        iDestruct (map_valid with "Hauth_map Hptsto") as %Hlookup.
        iDestruct ("Hptsto_close" with "Hptsto") as "Hchild".

        iMod "Hau" as (user_map2) "(Huser_map2 & [_ Hau_close])".

        iDestruct (ghost_var_agree with "Huser_map Huser_map2") as %Heq.
        subst user_map2.
        iMod (ghost_var_update_halves (<[key:=value]> user_map) with "Huser_map Huser_map2") as "[Huser_map Huser_map2]".

        iDestruct (big_sepL_lookup_acc with "Hind") as "[Hchild2 Hchildren_close2]"; [exact Hv|].
        iDestruct "Hchild2" as (nodeptr2) "[>Hown_child2 Hchild2]".
        iNamedSuffix "Hown_child2" "2".
        replace (W64 (sint.nat next_nibble)) with next_nibble by word.
        iDestruct (own_Value_agree with "Hown_child Hown_child2") as %Heq.
        inversion Heq.
        clear Heq.
        apply (inj to_val) in H0.
        subst nodeptr2.
        iEval (unfold childP) in "Hchild2".
        iSimpl in "Hchild2".
        iMod "Hchild2".
        iNamedSuffix "Hchild2" "2".

        iMod (own_path_update_key key value with "Hauth_map [Hchild Hchild2]") as "[Hauth_map Hchild]".
        { exact Hkey_path. }
        { iCombine "Hchild Hchild2" as "Hchild". iExact "Hchild". }

        iNamed.
        iEval (rewrite decide_True) in "Hctx".
        unfold empty_map_fn.
        subst h.
        set h := uint.Z (hash_key key).

        have Hnone : (user_map !! key = None).
        {
          subst user_map.
          unfold empty_map_fn in Hlookup.
          have Hflat : flatten hm !! key = (∅ : gmap K V) !! key.
          { apply (Hbuckets h ∅ key); [exact Hlookup|reflexivity]. }
          rewrite Hflat.
          rewrite lookup_empty.
          done.
        }

        iMod ("Hau_close" with "[$Huser_map2]") as "HΦ".
        {
          rewrite Hnone.
          auto.
        }

        iMod "Hau_close_mask" as "_".
        iApply (fupd_mask_intro); first apply empty_subseteq.
        iIntros "Hmask".
        iNext.
        iNamed.

        change (λ h' : Z, if decide (h' = h) then <[key:=value]> ∅ else ∅)
          with (singleton_map_fn h (<[key:=value]> ∅)).

        iCombine "Hown_child Hown_child2" as "Hown_child".
        iFrame.
        iIntros "[Hown_child Hown_child2]".
        iDestruct (field_pointsto_not_null with "HisEntry_o") as %Hnn.
        { simpl. done. }
        { auto. }
        iDestruct (field_pointsto_not_null with "Hnode_o") as %Hen.
        { simpl. done. }
        { auto. }

        iDestruct "Hpath" as "[Hown_path Hown_path2]".
        iDestruct "Hoverflow_o" as "[Hoverflow Hoverflow2]".

        (* TODO: make entry invariant instance of as_fractional because what is even this *)
        iMod (inv_alloc entryN _ (entry_inv γ (1/2) (entry γ (1/2)) e path) with "[Hoverflow Hown_path]") as "Hinv".
        {
          iNext.
          unfold entry_inv.
          rewrite decide_False; [|exact Hen].
          (* unfold entry_step. *)
          iExists null.
          rewrite /named.
          iFrame.
          iFrame "#".
          simpl.
          iPureIntro; done.
        }
        iMod (inv_alloc entryN _ (entry_inv γ (1/2) (entry γ (1/2)) e path) with "[Hoverflow2 Hown_path2]") as "Hinv2".
        {
          iNext.
          unfold entry_inv.
          rewrite decide_False; [|exact Hen].
          (* unfold entry_step. *)
          iExists null.
          rewrite /named.
          iFrame.
          iFrame "#".
          simpl.
          iPureIntro; done.
        }

        iDestruct ("Hchildren_close2" with "[$Hown_child2 Hinv]") as "Hchildren2".
        {
          rewrite /named.
          unfold childP.
          rewrite decide_False; [|exact Hnn].
          iFrame "#".
          iFrame "#".
          iSplit; [iPureIntro; exact Hen|].
          iApply entry_unfold.
          unfold entry_F.
          iFrame.
        }
        iMod "Hmask" as "_".

        iMod ("Hclose_ind_inv" with "[Hchildren2]") as "_".
        {
          iNext.
          unfold childrenP.
          iFrame "Hchildren2".
        }

        unfold empty_map_fn in Hlookup.
        replace (uint.Z (hash_key key)) with h in * by reflexivity.

        iMod ("Hclose_map" with "[Huser_map Hctx Hown_root Hroot_indirect]") as "_".
        {
          iNext.
          rewrite /named.
          unfold ht_inv.
          iExists rooti.
          iExists (<[h:=<[key:=value]> ∅]> hm).
          rewrite /named.
          iFrame.
          iFrame "#".
          iPureIntro.
          set hm' := <[h := <[key:=value]> ∅]> hm.
          set um' := <[key:=value]> user_map.

          assert (Hum' : (um' = flatten hm')).
          {
            subst um' hm'.
            symmetry.
            subst user_map.
            apply (flatten_update_update hm h key value ∅ ).
            - exact Hlookup.
            - reflexivity.
            - intros.
              eapply Hbuckets_rev.
              + exact H.
              + exact H0.
         }

         split; [exact Hum'|].
          split.
          {
            intros h0 sub k Hhm' Hhash.
            rewrite -Hum'.
            subst um' hm'.
            destruct (decide (h0 = h)) as [->|Hneq].
            - rewrite lookup_insert in Hhm'.
              rewrite decide_True in Hhm'; [|reflexivity].
              inversion Hhm'; subst sub; clear Hhm'.
              destruct (decide (k = key)) as [->|Hk].
              + rewrite lookup_insert. rewrite lookup_insert.
                rewrite decide_True; [|reflexivity].
                rewrite decide_True; [|reflexivity].
                done.
              + rewrite lookup_insert_ne; [|done].
                have Hnone_k : user_map !! k = None.
                { rewrite Hflat.
                  have Hflatk : flatten hm !! k = (∅ : gmap K V) !! k
                                                    by apply (Hbuckets h ∅ k Hlookup Hhash).
                  rewrite Hflatk lookup_empty. done.
                }
                rewrite Hnone_k.
                rewrite lookup_insert_ne; [|done].
                rewrite lookup_empty. done.
            - rewrite lookup_insert_ne in Hhm'; [|done].
              have Hsub : hm !! h0 = Some sub := Hhm'.
              destruct (decide (k = key)) as [->|Hk].
              + exfalso. apply Hneq.
                subst h. rewrite Hhash.
                done.
              + rewrite lookup_insert_ne; [|done].
                rewrite Hflat.
                eapply Hbuckets; eauto.
          }
          {
            intros.
            subst hm'.
            destruct (decide (h0 = h)) as [->|Hneq].
            - rewrite lookup_insert in H.
              rewrite decide_True in H; [|done].
              inversion H; subst sub; clear H.
              destruct (decide (k = key)) as [->|Hk].
              + done.
              + rewrite lookup_insert_ne in H0; [|done].
                rewrite lookup_empty in H0. discriminate.
            - rewrite lookup_insert_ne in H; [|done].
              eapply Hbuckets_rev; eauto.
          }
        }

        iModIntro.

        wp_auto.

        iDestruct ("Hchildren_close" with "[Hown_child Hnode_o Hinv2]") as "Hchildren".
        {
          iFrame.
          unfold childP.
          rewrite decide_False; [|exact Hnn].
          iFrame "#".
          iExists e.
          iSplit; [done|].
          iFrame "#".
          iApply entry_unfold.
          unfold entry_F.
          iFrame "Hinv2".
        }

        wp_apply (wp_Mutex__Unlock with "[$Hind_mutex $Hown_mutex $Hdead $Hchildren]").

        iApply "HΦ".

      - shelve.
    }

    iDestruct "Hchild" as (is_entry) "(#Hnodeis_entry & #Hchild)".
    destruct is_entry.
    {
      iDestruct "Hchild" as (ent) "(%Henotnull & #Hent & #Hind_null & #Hentry)".
      iMod "Hmask" as "_".

      iEval (rewrite entry_unfold /entry_F) in "Hentry".
      iNamed "Hentry".

      iMod (fupd_mask_subseteq ht_au_mask) as "Hclose_au_mask".
      {
        unfold ht_au_mask.
        apply subseteq_difference_l.
        set_solver.
      }

      iDestruct ("Hchildren_close" with "[Hown_child]") as "Hchildren".
      {
        iExists nodeptr. iFrame. unfold childP.
        destruct (decide (nodeptr = null)).
        - exfalso. apply n2. exact e.
        - iExists true. iFrame "#". rewrite entry_unfold /entry_F. iFrame "#". done.
      }

      iMod "Hclose_au_mask" as "_".
      iMod ("Hclose_ind" with "[$Hchildren]") as "_".
      iMod ("Hclose_ht" with "[$Hauth_map $Hown_root2 $Hroot_indirect2 $Huser_map //]") as "_".

      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "_".

      wp_apply wp_interface_type_assert.
      { auto. }
      replace (bool_decide (nodeptr = null)) with false.
      2: { symmetry. rewrite (bool_decide_eq_false (nodeptr = null)). exact n2. }

      wp_auto.

      wp_apply (wp_node__entry with "[# $]").
      wp_apply wp_entry__lookup.
      iFrame "#".
      rewrite /named.
      repeat iSplit; eauto.
      {
        rewrite entry_unfold /entry_F /named.

        iFrame "#".
      }
      iAuIntro.
      rewrite /atomic_acc.
      iMod "Hau" as (m) "[Hown Hclose_au]".
      (* iApply aupd_aacc in "Hau". *)
      iApply fupd_mask_intro; first set_solver.
      iIntros "_".
      iFrame "Hown".
      iSplit; iIntros "Hown".
      {
        iMod ("Hclose_au" with "Hown") as "Hau".
        iApply fupd_mask_intro; first set_solver.
        iIntros "_".
        iFrame.
      }
      destruct (bool_decide (is_Some (m !! key))) eqn:His_some.
      - (* apply bool_decide_eq_true in His_some. *)

        apply bool_decide_eq_true_1 in His_some.
        destruct His_some as [old_v Hv_lookup].

        iDestruct "Hclose_au" as "(_ & Hclose_au)".
        iSpecialize ("Hclose_au" $! m true old_v).

        iMod ("Hclose_au" with "[$Hown]") as "HΦ".
        {
          iPureIntro.
          destruct (m !! key) eqn:Hlookup; simpl.
          - inversion Hv_lookup.
            subst. reflexivity.
          - apply None_ne_Some in Hv_lookup.
            contradiction.
        }

        iApply fupd_mask_intro; first set_solver.
        iIntros "_".
        iFrame.

        wp_auto.
        replace (bool_decide (is_Some (m !! key))) with true.
        2: {
          symmetry. apply bool_decide_eq_true.
          auto.
        }
        wp_auto.
        wp_for_post.
        wp_for_post.
        replace (default (W64 0) (m !! key)) with old_v.
        + iExact "HΦ".
        + rewrite Hv_lookup.
          simpl.
          reflexivity.
      - apply bool_decide_eq_false in His_some.
        iMod ("Hclose_au" with "Hown") as "Hau".
        iApply fupd_mask_intro; first set_solver.
        iIntros "_".
        iFrame.

        wp_auto.
        replace (bool_decide (is_Some (m !! key))) with false by (symmetry; apply bool_decide_eq_false; exact His_some).
        wp_auto.

        wp_for_post.

        clear His_some m.

        shelve.
    }
    iDestruct "Hchild" as (ind) "(%Hnext_path_len & #Hent_null & #Hind & #Hindirect)".

    iDestruct ("Hchildren_close" with "[Hown_child]") as "Hchildren".
    { iExists nodeptr. iFrame. unfold childP.
      destruct (decide (nodeptr = null)).
      - exfalso. congruence.
      - iExists false. iFrame "#".
        iPureIntro. exact Hnext_path_len.
    }

    iMod "Hmask" as "_".
    iMod ("Hclose_ind" with "Hchildren") as "_".
    iMod ("Hclose_ht" with "[$Hauth_map $Hown_root2 $Hroot_indirect2 $Huser_map //]") as "_".

    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "_".

    wp_apply wp_interface_type_assert.
    { auto. }

    replace (bool_decide (nodeptr = null)) with false.
    2: { symmetry. rewrite (bool_decide_eq_false (nodeptr = null)). congruence. }

    wp_auto.
    wp_apply (wp_node__indirect with "[$]").
    wp_for_post.
    iFrame.
    iFrame "#".
    simpl.

    (* iFrame "slot". *)

    set next := Z.of_nat (sint.nat next_nibble).
    set next_path := (path ++ [next]).

    have Hlen : length next_path = (length path + 1)%nat by
                                     rewrite app_length /=.

    have Hz : uint.Z next_nibble = Z.land (h ≫ (sh path - 4)) 15.
    {
      rewrite next_nibble_eq.
      - reflexivity.
      - auto.
    }

    iFrame.
    iPureIntro.

    {
      split_and!; auto.
      - rewrite sh_snoc. unfold sh. word.
      - apply (next_nibble_extend path h next); try done.
        + unfold h.
          pose proof (word.unsigned_range (hash_key key)) as [H0 _].
          exact H0.
        + unfold next.
          rewrite Z2Nat.id; [|word].
          rewrite <- Z2Nat.id with (n:=sint.Z next_nibble) by word.
          word.
      - unfold sh.
        replace (w64_word_instance.(word.sub) (W64 (64 - 4 * length path)) (W64 4)) with (W64 (64 - 4 * length path - 4)) by word.
        have Hlt : (length path < 15)%nat.
        { rewrite app_length /= in Hnext_path_len; lia. }
        have Hpos : (0 < (64 - 4 * length path - 4))%Z.
        { lia. }
        word.
    }

    Unshelve.
    {
      iEval (unfold childP) in "Hchild".
      rewrite decide_False; [|done].
      iDestruct "Hchild" as (is_entry) "[#His_entry Hchild]".
      wp_auto.
      wp_if_destruct.
      {
        wp_apply wp_Bool__Load.
        iApply fupd_mask_intro; first apply empty_subseteq.
        iIntros "Hmask".
        iFrame "Hdead".
        iIntros "Hdead".
        iMod "Hmask" as "_".
        iModIntro.
        wp_auto.
        wp_if_destruct.
        {
          wp_apply (wp_Mutex__Unlock with "[$Hind_mutex $Hown_mutex $Hdead Hchildren_close Hchild Hown_child]").
          {
            iNext.
            iFrame.
            rewrite /named.
            iDestruct ("Hchildren_close" with "[Hchild Hown_child]") as "Hchildren".
            {
              iFrame.
              unfold childP.
              rewrite decide_False; [|done].
              iFrame "#".
              iFrame.
            }
            unfold childrenP.
            iFrame.
          }
          wp_for_post.
          iFrame.
        }
        wp_for_post.
        wp_if_destruct.
        {
          wp_apply wp_newEntryNode.
          iIntros (e n3) "Horphaned_ent".
          wp_auto.
          unfold orphaned_entry.
          iNamed "Horphaned_ent".
          wp_auto.

          wp_apply wp_Value__Store.

          iInv "Hind_inv" as "HI" "Hclose_ind".
          iApply fupd_mask_intro; first apply empty_subseteq.
          iIntros "Hmask".
          iNext.

          iEval (unfold childrenP) in "HI".
          iNamedSuffix "HI" "2".

          iDestruct (big_sepL_lookup_acc with "Hchildren2") as "[Hchild2 Hchildren_close2]".
          { exact Hv. }
          iNamedSuffix "Hchild2" "2".
          replace (W64 (sint.nat next_nibble)) with next_nibble by word.

          iDestruct (own_Value_agree with "Hown_child Hown_child2") as %Hneq.
          inversion Hneq.
          apply (inj to_val) in H0.
          subst nodeptr.

          iCombine "Hown_child Hown_child2" as "Hown_child".

          iFrame "Hown_child".

          iIntros "Hown_child".

          iDestruct "Hown_child" as "[Hown_child Hown_child2]".

          (* iMod (inv_alloc entryN _ (entry_inv γ (1/2) (entry γ (1/2)) e path) with "[Hoverflow Hown_path]") as "Hinv". *)
          (* { *)
          (*   iNext. *)
          (*   unfold entry_inv. *)
          (*   rewrite decide_False; [|exact Hen]. *)
          (*   (* unfold entry_step. *) *)
          (*   iExists null. *)
          (*   rewrite /named. *)
          (*   iFrame. *)
          (*   iFrame "#". *)
          (*   simpl. *)
          (*   iPureIntro; done. *)
          (* } *)

          iDestruct (field_pointsto_not_null with "HisEntry") as %Hnn; [simpl; done|auto|].

          iMod (inv_alloc entryN _ (entry_inv γ (1/2) (entry γ (1/2)) e path) with "[]") as "#Hent_inv2".
          {
            iNext.
            unfold entry_inv.
            rewrite decide_False; [|done].
            iFrame "#".
            admit.
          }

          iDestruct ("Hchildren_close2" with "[Hchild2 Hown_child2]") as "Hchildren2".
          {
            iFrame.
            rewrite /named.
            unfold childP.
            iSimpl in "Hchild2".
            rewrite decide_False; [|exact Hnn].
            iFrame "#".
            iExists e.
            iFrame "#".
            iSplit; [done|].
            rewrite entry_unfold /entry_F /named.
            iFrame "Hent_inv2".
          }

          admit.
        }
        admit.
      }
      admit.
    }

  Admitted.

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

End proof.
