From iris.bi.lib Require Import atomic.
From iris.program_logic Require Import atomic.

From New.code.hashtriemap Require Import hashtriemap.
From New.generatedproof.hashtriemap Require Import hashtriemap.

From New.proof Require Import atomic mutex.

From Perennial.algebra Require Import auth_map.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.Helpers Require Import NamedProps.
Import named_props_ascii_notation.
From New.ghost Require Import ghost_var.

From New.proof.hashtriemap Require Import aux.
From New.proof.hashtriemap Require Import paths.
From New.proof.hashtriemap Require Import model.
From New.proof.hashtriemap Require Import hashtriemap_done.
Import Setoid.

Open Scope Z_scope.

Section proof.
  Context `{hG: heapGS Σ, !ffi_semantics _ _}.
  Context {sem : go.Semantics} {package_sem : hashtriemap.Assumptions}.
  Collection W := sem + package_sem.
  Set Default Proof Using "W".
  Context `{!ghost_varG Σ bool}
    `{!ghost_varG Σ (gmap w64 w64)}
    `{!mapG Σ w64 w64}
    `{!mapG Σ Z (gmap w64 w64)}.

  #[global] Instance : IsPkgInit (iProp Σ) hashtriemap := define_is_pkg_init True%I.
  #[global] Instance : GetIsPkgInitWf (iProp Σ) hashtriemap := build_get_is_pkg_init_wf.

  Definition orphaned_entry e n (key: K) (value: V) : iProp Σ :=
    (* "#Hnode" ∷ e ↦s[hashtriemap.entry :: "node"]□ n ∗ *)
    "#Hkey" ∷ e.[hashtriemap.entry.t, "key"] ↦□ key ∗
    "#Hvalue" ∷ e.[hashtriemap.entry.t, "value"] ↦□ value ∗
    "Hoverflow" ∷ e.[hashtriemap.entry.t, "overflow"] ↦ᵥ interface.mk_ok
                      (go.PointerType hashtriemap.entry) (# null) ∗
    "#HisEntry" ∷ n.[hashtriemap.node.t, "isEntry"] ↦□ true ∗
    "#Hent" ∷ n.[hashtriemap.node.t, "ent"] ↦□ e ∗
    "#Hind" ∷ n.[hashtriemap.node.t, "ind"] ↦□ null.
  #[global] Transparent orphaned_entry.

  Lemma wp_newEntryNode (key: w64) (value: w64) :
    {{{ is_pkg_init hashtriemap }}}
      @! hashtriemap.newEntryNode #key #value
      {{{ (e: loc) (n: loc), RET (#e);
          "orphaned" ∷ orphaned_entry e n key value ∗
          "#Hnode" ∷ e.[hashtriemap.entry.t, "node"] ↦□ n
      }}}.
  Proof.
    wp_start.
    wp_auto.
    wp_alloc e as "eval".
    wp_auto.
    iStructNamed "eval".
    simpl.
    wp_apply wp_Value__Store.
    iApply fupd_mask_intro; first apply empty_subseteq.
    iIntros "Hmask".
    iNext.
    iFrame "overflow".
    iIntros "overflow".
    iMod "Hmask" as "_".
    iModIntro.
    wp_auto.
    wp_alloc n as "n".
    iStructNamed "n".
    simpl.
    iPersist "key".
    iPersist "value".
    iPersist "isEntry".
    iPersist "ent".
    iPersist "ind".
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    iPersist "node".
    wp_auto.
    iApply "HΦ".
    unfold orphaned_entry.
    iFrame.
    iFrame "#".
  Qed.

  (* Lemma wp_HashTrieMap__expand *)
  (*   (ht: loc) (oldEntry newEntry: loc) (newHash hashShift: w64) (parent: loc) *)
  (*   (γ: ghost_names) (path: path) *)
  (*   (old_k new_k: K) (old_v new_v: V) (new_n: loc) (seed: w64) : *)
  (*   ∀ Φ, *)
  (*   (is_pkg_init hashtriemap ∗ *)
  (*    "#His_map" :: is_hashtriemap γ ht ∗ *)
  (*    "#Hparent" :: indirect γ parent path ∗ *)
  (*    "#Hold_entry" :: entry γ (1/2) oldEntry path ∗ *)
  (*    "Hnew_orphan" :: orphaned_entry newEntry new_n new_k new_v ∗ *)
  (*    "#Hnew_node" :: newEntry ↦s[hashtriemap.entry :: "node"]□ new_n ∗ *)
  (*    "%HhashShift" :: ⌜hashShift = W64 (sh path)⌝ ∗ *)
  (*    "%HnewHash" :: ⌜newHash = hash_key new_k⌝ ∗ *)
  (*    "%Hold_belongs" :: ⌜belongs_to_path path (uint.Z (hash_key old_k))⌝ ∗ *)
  (*    "%Hnew_belongs" :: ⌜belongs_to_path path (uint.Z (hash_key new_k))⌝ ∗ *)
  (*    "#Hseed" :: ht ↦s[hashtriemap.HashTrieMap :: "seed"]□ seed ∗ *)
  (*    (* atomic update for abstract map *) *)
  (*    "Hau" :: *)
  (*      AU <{ ∃∃ m : gmap K V, own_ht_map γ m }> *)
  (*      @ ht_au_mask, ∅ *)
  (*                    <{ ∀∀ m', *)
  (*                         ⌜ m' = *)
  (*                         (* collision: just extend overflow *) *)
  (*                         if decide (uint.Z (hash_key old_k) = uint.Z (hash_key new_k)) then *)
  (*                           (* old already in m, new inserted *) *)
  (*                           (<[new_k := new_v]> m) *)
  (*                         else *)
  (*                           (<[new_k := new_v]> m) *)
  (*                             ⌝ ∗ *)
  (*                           own_ht_map γ m', COMM Φ #() }>) *)
  (*   -∗ *)
  (*   WP ht @ (go.PointerType hashtriemap.HashTrieMap.id) @ "expand" *)
  (*     #oldEntry #newEntry #newHash #hashShift #parent *)
  (*     {{ v, Φ v }}. *)
  (* Proof. *)
  (*   intros Φ. *)
  (*   iIntros "[#? Hpre]". *)
  (*   iNamed "Hpre". *)

  (*   wp_method_call; *)
  (*     wp_call; *)
  (*     wp_auto. *)

  (* Admitted. *)

  Tactic Notation "wp_for_join" open_constr(asn) "with" constr(pat) :=
    wp_bind (for: _ ; _ := _)%E;
    iApply (wp_wand _ _ _ asn with pat)%I;
    [ wp_for pat | ].

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
    WP ht @! (go.PointerType hashtriemap.HashTrieMap) @! "LoadOrStore" #key #value {{ Φ }}.
  Proof.
    wp_start.
    iNamed "HΦ".

    wp_apply wp_with_defer as "%defer defer"; simpl subst.
    wp_auto.

    wp_apply (wp_HashTrieMap__initHT with "[$]").
    iIntros.
    iNamed.
    iNamed "His_map".
    iNamed "Hseed".
    wp_auto.

    wp_apply wp_hashInt.
    iIntros (hash) "%Hhash".

    wp_auto.
    iPersist "hash".
    iPersist "key".
    iPersist "value".
    iPersist "ht".

    iAssert (
        ∃ (slot n i: loc) (hashShift: w64),
          "slot" :: slot_ptr ↦ slot ∗
          "n" :: n_ptr ↦ n ∗
          "i" ∷ i_ptr ↦ i ∗
          "hashShift" ∷ hashShift_ptr ↦ hashShift
      )%I with "[$slot $n $i $hashShift]" as "Houter_loop_inv".

    wp_for "Houter_loop_inv".

    wp_bind (TypeAssert _ _).

    iApply (wp_load_root with "[# $]").
    iIntros.
    iNamed.
    wp_auto.

    set h := uint.Z (hash_key key).

    wp_bind.

    iAssert (∃ (path: path) (shift: Z) (cur: loc) (HIP: bool) (sl: loc) (n: loc),
                "slot" ∷ slot_ptr ↦ sl ∗
                "n" ∷ n_ptr ↦ n ∗
                "Hcur" :: i_ptr ↦ cur ∗
                "Hhash_shift" :: hashShift_ptr ↦ W64 shift ∗
                "#Hi_indirect" :: indirect γ cur path ∗
                "%Hshift" :: ⌜shift = sh path⌝ ∗
                "%Hpath_len" :: ⌜length path < 16⌝ ∗
                "%Hkey_path" :: ⌜belongs_to_path path h⌝ ∗
                "haveInsertPoint" :: haveInsertPoint_ptr ↦ HIP ∗ (* HIP actually doesnt matter *)
                "%HIP" :: ⌜shift ≠ 0⌝
            )%I with ("[$Hroot_indirect $slot $n $i $hashShift $haveInsertPoint]") as "Hloop_inv".
    {
      repeat iSplit; eauto; iPureIntro; eauto.
      unfold belongs_to_path, sh, path_to_prefix.
      simpl.
      rewrite Z.shiftr_div_pow2; try word.
    }

    iClear "Hroot_indirect".
    clear root.

    iApply (wp_wand _ _ _
              (λ v,
                 ( ∃ next_nibble children_slice (children_vals: list atomic.Value.t) (nodeptr cur: loc) path next_path (val: atomic.Value.t),
                     "%v" ∷ ⌜v = execute_val⌝ ∗
                     "%next_nibble" ∷ ⌜next_nibble = Z.land (uint.Z (hash_key key) ≫ (sh path - 4)) 15⌝ ∗
                     "%Hnib_u" ∷ ⌜0 ≤ next_nibble < 16⌝ ∗
                     "%Hv" ∷ ⌜children_vals !! Z.to_nat next_nibble = Some val⌝ ∗
                     "%Hdom" ∷ ⌜h ∈ path_to_domain path⌝ ∗
                     "%next_path" ∷ ⌜next_path = path ++ [next_nibble]⌝ ∗
                     "%Hlen" ∷ ⌜length next_path = (length path + 1)%nat⌝ ∗
                     "%Hh" ∷ ⌜h = uint.Z (hash_key key)⌝ ∗
                     "%Hdom_child" ∷ ⌜h ∈ path_to_domain next_path⌝ ∗

                     "Hau" ::
                       (AU <{ ∃∃ m : gmap K V, own_ht_map γ m }>
                          @ ht_au_mask, ∅
                                        <{ ∀∀ new_m load_res new_v,
                                             ⌜ (new_m, load_res, new_v) = match m !! key with
                                                                          | Some old_v => (m, true, old_v)
                                                                          | None => (<[key := value]> m, false, value)
                                                                          end ⌝ ∗
                                             own_ht_map γ new_m, COMM Φ (#new_v, #load_res)%V }>) ∗
                     "#Hchildren_slice" ∷ children_slice ↦*□ children_vals ∗
                     "#Hown_children" ∷ cur.[hashtriemap.indirect.t, "children"] ↦□ children_slice ∗
                     "#Hind_inv" ∷ inv indN
                       (childrenP (indirect γ) γ (1 / 2) children_slice children_vals cur
                          path) ∗
                     "#Hind_mutex" ∷ is_Mutex cur.[hashtriemap.indirect.t, "mu"]
                                                    (∃ dead : bool,
                                                        "Hdead"
                                                          ∷ own_Bool cur.[hashtriemap.indirect.t, "dead"]
                                                                           (DfracOwn 1) dead ∗
                                                        "Hmu_inv"
                                                          ∷ childrenP (indirect γ) γ (1 / 2) children_slice
                                                          children_vals cur path) ∗

                     "slot" ∷ slot_ptr ↦ slice_index_ref atomic.Value.t next_nibble children_slice ∗
                     "hashShift" ∷ hashShift_ptr ↦ w64_word_instance.(word.sub) (W64 (sh path)) (W64 4) ∗
                     "n" ∷ n_ptr ↦ nodeptr ∗
                     "i" ∷ i_ptr ↦ cur ∗
                     "HIP" ∷ haveInsertPoint_ptr ↦ true
                 )
                 ∨
                   (
                     ∃ old_v,
                       "%v" ∷ ⌜v = return_val (# old_v, # true)⌝ ∗
                       "HΦ" ∷ Φ (# old_v, # true)%V
                   )
              )%I
             with "[Hloop_inv Hau]").
    {
      wp_for "Hloop_inv".

      simpl.

      iEval (rewrite indirect_unfold /indirect_F) in "Hi_indirect".
      iNamed "Hi_indirect".

      (* wp_if_destruct. *)
      (* { *)
      (*   unfold sh in e. *)
      (*   word. *)
      (* } *)

      rewrite bool_decide_false.
      2: {
        subst shift.
        unfold sh.
        word.
      }

      rewrite decide_True; [|auto].
      wp_pures.
      wp_auto.

      subst hash.

      iDestruct (own_slice_len with "Hchildren_slice") as %Hlen_children.
      replace ((w64_word_instance.(word.sub) (W64 shift) (W64 4))) with (w64_word_instance.(word.sub) (W64 (sh path)) (W64 4)) by word.

      rewrite next_nibble_eq; [|exact Hpath_len].
      set next_nibble := (Z.land (uint.Z (hash_key key) ≫ (sh path - 4)) 15).
      replace (sint.Z children_slice.(slice.len)) with 16 by word.

      have Hnib_u : 0 ≤ next_nibble < 16.
      {
        subst next_nibble.
        replace 15 with (Z.ones 4) by reflexivity.
        rewrite Z.land_ones; [|word].
        word.
      }
      rewrite decide_True; [|word].

      destruct (lookup_lt_is_Some_2 children_vals (Z.to_nat next_nibble))
        as [v Hv].
      { word. }

      wp_auto.

      have Hdom : h ∈ path_to_domain path by rewrite -in_domain.

      wp_apply wp_Value__Load.
      (* iInv "His_map" as "Hhtinv" "Hclose_ht". *)
      iInv "Hind_inv" as "HI" "Hclose_ind".

      iApply fupd_mask_intro.
      { apply empty_subseteq. }
      iIntros "Hmask".
      iNext.

      iEval (unfold childrenP) in "HI".

      iNamed "HI".

      iDestruct (big_sepL_lookup_acc with "Hchildren") as "[Hchild Hchildren_close]"; [exact Hv|].
      replace (Z.of_nat (Z.to_nat next_nibble)) with next_nibble by word.
      iNamed "Hchild".
      iFrame "Hown_child".
      iIntros "Hown_child".

      set next_path := (path ++ [next_nibble]).

      have Hlen : length next_path = (length path + 1)%nat by
                                       rewrite app_length /=.

      have Hh : h = uint.Z (hash_key key) by reflexivity.
      have Hdom_child : h ∈ path_to_domain next_path.
      {
        have H : belongs_to_path next_path h.
        {
          rewrite /belongs_to_path.
          apply (next_nibble_extend path h next_nibble); try done; word.
        }
        rewrite -in_domain; done.
      }
      destruct (decide (nodeptr = null)).
      {
        iMod "Hmask" as "_".

        iDestruct ("Hchildren_close" with "[$Hown_child $Hchild]") as "Hchildren".

        iMod ("Hclose_ind" with "Hchildren") as "_".

        iModIntro.

        wp_auto; rewrite decide_True; [|reflexivity]; wp_auto.

        rewrite e; simpl.
        wp_auto.

        wp_for_post.
        iLeft.
        iFrame.
        iFrame "#".
        iPureIntro.
        exists next_path, v.
        done.
      }

      iEval (unfold childP; rewrite (decide_False _ _ n1)) in "Hchild".
      iNamed "Hchild".
      destruct is_entry.
      {
        iNamed "Hchild".
        iMod "Hmask" as "_".

        iEval (rewrite entry_unfold /entry_F) in "Hchild_entry".
        iNamed "Hchild_entry".

        iDestruct ("Hchildren_close" with "[Hown_child Hown_path]") as "Hchildren".
        {
          iExists nodeptr. iFrame. unfold childP.
          rewrite (decide_False _ _ n1).
          iExists true.
          iSplit; [iFrame "#"|].
          unfold entry_node.
          iExists ent. iExists map. iExists hash.
          iFrame.
          iFrame "#".
          rewrite entry_unfold /entry_F.
          iFrame "#".
          done.
        }

        iMod ("Hclose_ind" with "[$Hchildren]") as "_".
        iModIntro.

        wp_auto; rewrite decide_True; [|reflexivity]; wp_auto.

        rewrite bool_decide_false; [|exact n1].

        wp_auto.

        wp_apply (wp_node__entry with "[# $]").
        wp_apply wp_entry__lookup.
        iFrame "#".
        rewrite /named.
        repeat iSplit.
        {
          auto.
        }
        {
          rewrite entry_unfold /entry_F.
          iFrame "#".
        }
        2: {
          iPureIntro.
          rewrite in_domain; auto.
        }

        iAuIntro.
        rewrite /atomic_acc.
        iMod "Hau" as (m) "[Hown Hclose_au]".
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
        - apply bool_decide_eq_true_1 in His_some.
          destruct His_some as [old_v Hv_lookup].
          rewrite Hv_lookup.

          iDestruct "Hclose_au" as "[_ Hclose_au]".
          iSpecialize ("Hclose_au" $! m true old_v).

          iMod ("Hclose_au" with "[$Hown]") as "HΦ"; [done|].

          iModIntro.

          unfold ht_load_ret.
          rewrite Hv_lookup.
          wp_auto.
          wp_for_post.
          iApply or_intro_r.
          iExists old_v.
          iFrame.
          done.
        - apply bool_decide_eq_false in His_some.
          iMod ("Hclose_au" with "Hown") as "Hau".
          iApply fupd_mask_intro; first set_solver.
          iIntros "_".
          iFrame.

          wp_auto.
          rewrite -eq_None_not_Some in His_some.
          unfold ht_load_ret.
          rewrite His_some.
          wp_auto.
          wp_for_post.
          iApply or_intro_l.
          iFrame "#".
          iFrame.
          iPureIntro.
          exists next_path, v.
          done.
      }

      iNamed "Hchild".

      iDestruct ("Hchildren_close" with "[Hown_child]") as "Hchildren".
      { iExists nodeptr. iFrame. unfold childP.
        rewrite decide_False; [|done].
        iExists false.
        iFrame "#".
        iPureIntro.
        auto.
      }

      iMod "Hmask" as "_".
      iMod ("Hclose_ind" with "Hchildren") as "_".

      iModIntro.

      wp_auto; rewrite decide_True; [|reflexivity]; wp_auto.

      rewrite bool_decide_false; [|exact n1].

      wp_auto.
      wp_apply (wp_node__indirect with "[$]").
      wp_for_post.
      replace (w64_word_instance.(word.sub)
                                   (W64 (sh path)) (W64 4)) with (W64 (sh path - 4)) by word.
      iFrame.
      iFrame "#".

      iPureIntro.

      {
        split_and!.
        - rewrite sh_snoc.
          reflexivity.
        - auto.
        - rewrite in_domain; [exact Hdom_child|apply Hh].
        - unfold sh.
          word.
      }
    }

    iIntros (v) "[x | x]"; iNamed "x"; subst v; wp_auto.
    2: {
      wp_for_post.
      iApply "HΦ".
    }

    iDestruct (own_slice_len with "Hchildren_slice") as %Hlen_children.

    wp_apply (wp_Mutex__Lock with "[$]").

    iIntros "[Hown_mutex Hx]".
    iNamed "Hx".
    iEval (unfold childrenP) in "Hmu_inv".
    iNamed "Hmu_inv".

    wp_auto.

    wp_apply wp_Value__Load.
    iApply fupd_mask_intro; first apply empty_subseteq.
    iIntros "Hmask".
    iNext.

    iDestruct (big_sepL_lookup_acc with "Hchildren") as "[Hchild Hchildren_close]"; [exact Hv|].
    iNamed "Hchild".
    replace (Z.of_nat (Z.to_nat (next_nibble))) with next_nibble by word.
    iFrame "Hown_child".
    iIntros "Hown_child".

    iMod "Hmask" as "_".
    iModIntro.

    wp_auto; rewrite decide_True; [|reflexivity]; wp_auto.

    (* (n == nil || n.isEntry) && !i.dead.Load() *)
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _
              (λ v,
                 "Hx" ∷ ((⌜v = break_val⌝ ∗
                          ((⌜nodeptr0 = null⌝ ∨
                                          (⌜nodeptr0 ≠ null⌝ ∗ nodeptr0.[hashtriemap.node.t, "isEntry"] ↦□ true))%I
                           ∗ ⌜dead = false⌝)
                         ) ∨
                           (
                             ⌜v = execute_val⌝
                   ))
                 ∗ "Hdead" ∷ own_Bool cur.[hashtriemap.indirect.t, "dead"] (DfracOwn 1) dead ∗
                 "n" ∷ n_ptr ↦ nodeptr0 ∗
                 "i" ∷ i_ptr ↦ cur ∗
                 "Hchild" ∷ childP (indirect γ) γ (1 / 2) nodeptr0 path (path ++ [next_nibble])
              )%I with "[Hdead i n Hchild]"
           ).
    {
      rewrite /named.
      wp_if_destruct.
      - wp_apply wp_Bool__Load.
        iApply fupd_mask_intro; [apply empty_subseteq|].
        iIntros "Hmask".
        iNext.
        iFrame "Hdead".
        iIntros "Hdead".
        iMod "Hmask" as "_".
        iModIntro.
        wp_if_destruct; iFrame; auto.
      - unfold childP.
        rewrite (decide_False _ _ n0).
        iNamed "Hchild".
        wp_auto.
        wp_if_destruct; auto.
        2: {
          iSplit; [auto|].
          unfold indirect_node.
          iNamed "Hchild".
          iFrame "#".
          rewrite /named.
          iFrame.
          auto.
        }
        wp_apply wp_Bool__Load.
        iApply fupd_mask_intro; [apply empty_subseteq|].
        iIntros "Hmask".
        iNext.
        iFrame "Hdead".
        iIntros "Hdead".
        iMod "Hmask" as "_".
        iModIntro.
        wp_if_destruct; iFrame; auto.
        iSplit; auto.
        {
          iLeft.
          auto.
        }
    }

    iIntros (v) "Hx".
    iNamed "Hx".
    wp_auto.
    iDestruct "Hx" as "[[-> [Hcond %a]] | ->]"; wp_auto.
    2: {
      iDestruct ("Hchildren_close" with "[Hchild Hown_child]") as "Hchildren".
      {
        iExists nodeptr0.
        iFrame.
      }
      wp_apply (wp_Mutex__Unlock with "[$Hown_mutex Hdead Hchildren]").
      {
        iFrame "#".
        iNext.
        iFrame.
      }
      wp_for_post.
      iFrame.
    }
    subst dead.
    wp_for_post.

    iDestruct "Hcond" as "[%Hnull | [%Hnotnull #Hisentry]]".
    2: {
      rewrite bool_decide_false; [|auto].
      wp_auto.
      iEval (unfold childP) in "Hchild".
      rewrite (decide_False _ _ Hnotnull).
      iNamed "Hchild".
      iCombine "Hisentry Hnode_is_entry" gives %x; subst is_entry.
      unfold entry_node.
      iNamed "Hchild".
      wp_apply wp_node__entry.
      {
        iSplit; iFrame "#".
      }

      wp_apply wp_entry__lookup.
      iFrame "#".
      rewrite /named.
      repeat iSplit.
      { auto. }
      2: {
        iPureIntro.
        subst.
        rewrite in_domain; auto.
      }

      iAuIntro.
      rewrite /atomic_acc.
      iMod "Hau" as (m) "[Hown Hclose_au]".
      iModIntro.
      iFrame "Hown".
      iSplit; iIntros "Hown".
      {
        iMod ("Hclose_au" with "Hown") as "Hau".
        iModIntro.
        iFrame.
      }
      unfold ht_load_ret.
      destruct (m !! key) eqn:Hv_lookup.
      - iDestruct "Hclose_au" as "[_ Hclose_au]".
        iSpecialize ("Hclose_au" $! m true v).

        iMod ("Hclose_au" with "[$Hown]") as "HΦ".
        {
          iPureIntro.
          reflexivity.
        }

        iModIntro.

        iFrame.

        wp_auto.

        iDestruct ("Hchildren_close" with "[Hown_child Hown_path]") as "Hchildren".
        {
          iExists nodeptr0.
          iFrame.
          unfold childP.
          rewrite (decide_False _ _ Hnotnull).
          iExists true.
          iSplit; [iFrame "#"|].
          unfold entry_node.
          iExists ent, map, hash0.
          iFrame.
          iFrame "#".
          done.
        }
        wp_apply (wp_Mutex__Unlock with "[$Hown_mutex Hdead Hchildren]").
        {
          iFrame "#".
          iNext.
          iFrame.
        }
        wp_end.
      - iMod ("Hclose_au" with "Hown") as "Hau".
        iModIntro.

        iFrame.

        wp_auto.

        wp_apply wp_newEntryNode.
        iIntros (e n2) "Hx".
        iNamed "Hx".

        wp_auto; rewrite (bool_decide_false); [|done]; wp_auto.

        replace ((w64_word_instance.(word.sub) (W64 (sh path)) (W64 4))) with (W64 (sh path - 4)) by word.

        (* TODO: expand *)
        admit.
    }

    rewrite (bool_decide_true); [|done].
    wp_auto.

    wp_apply wp_newEntryNode.
    iIntros (e n2) "Hx".
    iNamed "Hx".

    wp_auto.

    wp_apply wp_Value__Store.

    iInv "His_map" as "[Hroot >Hmap]" "Hclose_map".
    iNamed "Hmap".
    iNamed "Hmap".
    iInv "Hind_inv" as "Hind" "Hclose_ind_inv".
    iEval (unfold childrenP) in "Hind".
    iEval (unfold childP) in "Hind".
    iMod (fupd_mask_subseteq ht_au_mask) as "Hau_close_mask".
    { unfold ht_au_mask; apply subseteq_difference_l; set_solver. }

    iMod "Hau" as (user_map2) "(Huser_map2 & [_ Hau_close])".
    iDestruct (map_state_agree with "Hmap Huser_map2") as %Hx.
    subst user_map2.

    iEval (unfold childP) in "Hchild".
    rewrite (decide_True _ _ Hnull).
    iNamed "Hchild".

    rewrite -next_path0.

    iDestruct (user_map_lookup Hdom_child Hh with "Hmap Hchild") as %Hnone.
    rewrite lookup_empty in Hnone.

    iDestruct (big_sepL_lookup_acc with "Hind") as "[Hchild2 Hchildren_close2]"; [exact Hv|].
    iDestruct "Hchild2" as (nodeptr2) "[>Hown_child2 Hchild2]".
    iNamedSuffix "Hown_child2" "2".
    replace (Z.of_nat (Z.to_nat next_nibble)) with next_nibble by word.
    iCombine "Hown_child Hown_child2" gives %Heq.
    inversion Heq.
    apply (inj _) in H0.
    clear Heq.
    subst nodeptr2.
    iEval (unfold childP) in "Hchild2".
    iSimpl in "Hchild2".
    rewrite (decide_True _ _ Hnull).
    iMod "Hchild2".
    iNamedSuffix "Hchild2" "2".

    replace (path ++ [next_nibble]) with next_path by (apply next_path0).
    iCombine "Hchild Hchild2" as "Hchild".
    iMod (map_state_insert key value Hh Hnone with "[$Hmap $Huser_map2 $Hchild]") as "H".
    {
      rewrite in_domain; auto.
    }
    unfold empty_map_fn.
    subst h.
    set (h := uint.Z (hash_key key)) in *.
    iNamed "H".

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

    iCombine "Hown_child Hown_child2" as "Hown_child".
    iFrame.
    iIntros "[Hown_child Hown_child2]".
    iNamedSuffix "orphaned" "_o".
    have Hnn : n2 ≠ null.
    {
      (* TODO: typed pointsto not null *)
      admit.
    }
    have Hen : e ≠ null.
    {
      (* TODO: typed pointsto not null *)
      admit.
    }

    iDestruct "Hpath" as "[Hown_path Hown_path2]".
    iDestruct "Hoverflow_o" as "[Hoverflow Hoverflow2]".

    iDestruct "Hentry" as "[Hentry1 Hentry2]".

    (* TODO: make entry invariant fractional because what is even this *)
    iMod (inv_alloc entryN _ (entry_inv γ (1/2) (entry γ (1/2)) e next_path) with "[Hoverflow Hentry1]") as "Hinv".
    {
      iNext.
      unfold entry_inv.
      iExists null.
      rewrite /named.
      iFrame.
      iFrame "#".
      simpl.
      iExists _.
      iSplit; auto.
      iSplit; auto.
      {
        iPureIntro.
        rewrite in_domain; auto.
      }
      iIntros "%H".
      contradiction.
    }
    iMod (inv_alloc entryN _ (entry_inv γ (1/2) (entry γ (1/2)) e next_path) with "[Hoverflow2 Hentry2]") as "Hinv2".
    {
      iNext.
      unfold entry_inv.
      iExists null.
      rewrite /named.
      iFrame.
      iFrame "#".
      simpl.
      iExists _.
      iSplit; auto.
      iSplit; auto.
      {
        iPureIntro.
        rewrite in_domain; auto.
      }
      iIntros "%H".
      contradiction.
    }

    unfold childrenP.
    iDestruct ("Hchildren_close2" with "[$Hown_child Hinv Hown_path]") as "Hchildren2".
    {
      rewrite /named.
      rewrite (decide_False _ _ Hnn).
      iExists true.
      iSplit.
      {
        iExact "HisEntry_o".
      }
      unfold entry_node.
      rewrite /named.
      iExists e.
      iExists (<[key:=value]> ∅).
      iExists h.
      unfold singleton_map_fn.
      iFrame.
      iFrame "#".
      iSplit; [iPureIntro; exact Hen|].
      iApply entry_unfold.
      unfold entry_F.
      iFrame.
    }
    iMod "Hmask" as "_".
    iMod ("Hclose_ind_inv" with "Hchildren2") as "_".
    iMod ("Hclose_map" with "[$Hmap $Hroot]") as "_".

    iModIntro.

    wp_auto.

    iDestruct ("Hchildren_close" with "[Hown_child2 Hnode Hinv2 Hown_path2]") as "Hchildren".
    {
      iExists n2.
      iFrame.
      unfold childP.
      rewrite (decide_False _ _ Hnn).
      iExists true.
      iSplit.
      { iExact "HisEntry_o". }
      iExists e.
      unfold singleton_map_fn.
      iExists (<[key:=value]> ∅).
      iExists h.
      iFrame "#".
      iFrame.
      iSplit; [done|].
      iApply entry_unfold.
      unfold entry_F.
      iFrame "Hinv2".
    }

    wp_apply (wp_Mutex__Unlock with "[$Hind_mutex $Hown_mutex $Hdead $Hchildren]").

    wp_end.
  Admitted.

  Lemma wp_HashTrieMap__Store (ht: loc) (key: w64) (old: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "Store" #key #old
      {{{ RET #(); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__Swap (ht: loc) (key: w64) (new: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "Swap" #key #new
      {{{ (a: w64) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__CompareAndSwap (ht: loc) (key: w64) (old: w64) (new: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "CompareAndSwap" #key #old #new
      {{{ (a: bool), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__LoadAndDelete (ht: loc) (key: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "LoadAndDelete" #key
      {{{ (a: w64) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__Delete (ht: loc) (key: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "Delete" #key
      {{{ RET #(); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__CompareAndDelete (ht: loc) (key: w64) (old: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "CompareAndDelete" #key #old
      {{{ (a: bool), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__find (ht: loc) (key: w64) (hash: w64) (checkValue: bool) (value: w64) :
    {{{ is_pkg_init hashtriemap }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "find" #key #hash #checkValue #value
      {{{ (a: loc) (b: w64) (c: loc) (d: loc), RET (#a, #b, #c, #d); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__All (ht: loc) :
    {{{ is_pkg_init hashtriemap }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "All" #()
      {{{ (a: func.t), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__Range (ht: loc) (yield: func.t) :
    {{{ is_pkg_init hashtriemap }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "Range" #yield
      {{{ RET #(); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__iter (ht: loc) (i: loc) (yield: func.t) :
    {{{ is_pkg_init hashtriemap }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "iter" #i #yield
      {{{ (a: bool), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_HashTrieMap__Clear (ht: loc) :
    {{{ is_pkg_init hashtriemap }}}
      ht @! (go.PointerType hashtriemap.HashTrieMap) @! "Clear" #()
      {{{ RET #(); True }}}.
  Proof. Admitted.

  Lemma wp_indirect__empty (i: loc) :
    {{{ is_pkg_init hashtriemap }}}
      i @! (go.PointerType hashtriemap.indirect) @! "empty" #()
      {{{ (a: bool), RET (#a); True }}}.
  Proof. Admitted.

  Lemma wp_entry__lookupWithValue (e: loc) (key: w64) (value: w64) (checkValue: bool) :
    {{{ is_pkg_init hashtriemap }}}
      e @! (go.PointerType hashtriemap.entry) @! "lookupWithValue" #key #value #checkValue
      {{{ (a: w64) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_entry__swap (head: loc) (key: w64) (new: w64) :
    {{{ is_pkg_init hashtriemap }}}
      head @! (go.PointerType hashtriemap.entry) @! "swap" #key #new
      {{{ (a: loc) (b: w64) (c: bool), RET (#a, #b, #c); True }}}.
  Proof. Admitted.

  Lemma wp_entry__compareAndSwap (head: loc) (key: w64) (old: w64) (new: w64) :
    {{{ is_pkg_init hashtriemap }}}
      head @! (go.PointerType hashtriemap.entry) @! "compareAndSwap" #key #old #new
      {{{ (a: loc) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

  Lemma wp_entry__loadAndDelete (head: loc) (key: w64) :
    {{{ is_pkg_init hashtriemap }}}
      head @! (go.PointerType hashtriemap.entry) @! "loadAndDelete" #key
      {{{ (a: w64) (b: loc) (c: bool), RET (#a, #b, #c); True }}}.
  Proof. Admitted.

  Lemma wp_entry__compareAndDelete (head: loc) (key: w64) (value: w64) :
    {{{ is_pkg_init hashtriemap }}}
      head @! (go.PointerType hashtriemap.entry) @! "compareAndDelete" #key #value
      {{{ (a: loc) (b: bool), RET (#a, #b); True }}}.
  Proof. Admitted.

End proof.
