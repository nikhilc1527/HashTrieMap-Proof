From iris.bi.lib Require Import fixpoint_mono.
From iris.bi.lib Require Import fractional.
From New.code.hashtriemap Require Import hashtriemap.
From New.generatedproof.hashtriemap Require Import hashtriemap.
From New.proof Require Import sync.
From New.proof.sync Require Import atomic.
From New.proof.sync_proof Require Import mutex.
From Perennial.algebra Require Import auth_map.
From Perennial.algebra Require Import ghost_var.
From Perennial.Helpers Require Import NamedProps.
Export named_props_ascii_notation.
From Perennial.Helpers.Word Require Import Integers.
From coqutil.Word Require Import Interface.
From iris.algebra Require Import gmap.
From Perennial.base_logic.lib Require Import invariants.
From iris.algebra Require Import dfrac.
From stdpp Require Import gmap list fin_maps.
From Coq Require Import List.
Import ListNotations.
From New.proof.hashtriemap Require Import aux.
Open Scope Z_scope.

Section model.
  Context `{hG: heapGS Σ, !invGS Σ, !ffi_semantics _ _}
           `{!globalsGS Σ, !ghost_varG Σ (gmap w64 w64)} {go_ctx: GoContext}.

  (* pure definitions, mostly hash-related stuff *)

  Parameter hash_key : w64 → w64.

  Definition path_to_prefix := foldl (λ acc x, (Z.shiftl acc hashtriemap.nChildrenLog2) + x) 0.

  (* index is the 4 bits at depth (0-based) of h. *)

  (* Definition hash_index (h: w64) (depth: nat) : nat := *)
  (*   let shift := 64 - 4 * (Z.of_nat (S depth)) in *)
  (*   Z.to_nat (Z.land (Z.shiftr (word.unsigned h) shift) 15). *)

  (* (* prefix is the top 4*depth bits of h (lower bits zeroed). *) *)
  (* Definition hash_prefix (h: w64) (depth: nat) : w64 := *)
  (*   let shift := 64 - 4 * (Z.of_nat depth) in *)
  (*   word.of_Z (Z.shiftl (Z.shiftr (word.unsigned h) shift) shift). *)

  (* (* extend prefix with the next 4-bit child index at depth+1. *) *)
  (* Definition child_prefix (prefix: w64) (depth idx: nat) : w64 := *)
  (*   let shift := 64 - 4 * (Z.of_nat (S depth)) in *)
  (*   word.of_Z (word.unsigned prefix + Z.shiftl (Z.of_nat idx) shift). *)

  Definition same_hash (ks: list w64) : Prop :=
    ∀ k1 k2, k1 ∈ ks → k2 ∈ ks → hash_key k1 = hash_key k2.

  Definition own_hash (path: list Z) (hash: Z) : Prop :=
    Z.shiftr hash (hashtriemap.hashBits - hashtriemap.nChildrenLog2 * Z.of_nat (length path)) = (path_to_prefix path).
  
  (* Ghost state for the hashtriemap. *)

  Record ghost_names := mkNames {
                           map_name : gname;
                           init_name : gname;
                         }.

  (* both of these are designed to be split between an invariant and a mutex, so that reading can be done outside of the critical section and writing can only be done inside *)
  Definition init_tok `{!ghost_varG Σ bool} (γ: ghost_names) (b: bool) : iProp Σ :=
    ghost_var γ.(init_name) (DfracOwn (1/2)) b.
  
  Definition map_tok `{!ghost_varG Σ (gmap w64 w64)} (γ: ghost_names) (m: gmap w64 w64) d : iProp Σ :=
    ghost_var γ.(map_name) d m.

  Definition indirect_par node_inv (γ: ghost_names) d (ind: loc) (path: list Z) : iProp Σ :=
    ∃ (children: list loc),
      (* ownership of the indirect struct’s children field *)
      ind ↦s[hashtriemap.indirect :: "children"] children ∗
      ⌜Z.of_nat (length children) = hashtriemap.nChildren ⌝ ∗
      (* for each child slot, either empty or a node_inv *)
      ([∗ list] i ↦ cloc ∈ children,
         ∃ (nptr: loc),
           own_Value cloc d (interface.mk (ptrT.id hashtriemap.node.id) #nptr) ∗
           (⌜ nptr = null ⌝ ∨ node_inv nptr (path ++ [Z.of_nat i]))).

  Definition entry_recF (γ: ghost_names) d (Φ: loc * gmap w64 w64 → iProp Σ)
    : loc * gmap w64 w64 → iProp Σ :=
    λ '(ent,owned_ghost),
      (if bool_decide (ent = null) then
        ⌜ owned_ghost = ∅ ⌝
      else
        ∃ (k: w64) (v: w64) (overflow: loc) (overflow_loc: loc) (rest: gmap w64 w64),
          ent ↦s[hashtriemap.entry :: "key"] k ∗
          ent ↦s[hashtriemap.entry :: "value"] v ∗
          ent ↦s[hashtriemap.entry :: "overflow"] overflow ∗
          own_Value overflow d (interface.mk (ptrT.id hashtriemap.entry.id) (# overflow_loc)) ∗
          ⌜ owned_ghost = <[k := v]> rest ⌝ ∗
          Φ (overflow_loc, rest))%I.

  Definition entry_rec (γ: ghost_names) (ent: loc) (owned_ghost: gmap w64 w64) d : iProp Σ :=
    bi_least_fixpoint (entry_recF γ d) (ent, owned_ghost).

  Definition entry (γ: ghost_names) (e: loc) (path: list Z) d : iProp Σ :=
    ∃ (owned_ghost: gmap w64 w64),
      map_tok γ owned_ghost d ∗
      entry_rec γ e owned_ghost d.
  
  Definition nodeF (γ: ghost_names) d
                   (Φ: loc * list Z → iProp Σ)
    : loc * list Z → iProp Σ :=
    λ '(n, path),
      (
        ∃ (is_entry: bool),
          n ↦s[hashtriemap.node :: "isEntry"] is_entry ∗
          if is_entry
          then
            let entry_loc := struct.field_ref_f hashtriemap.node "entry" n in
            entry γ entry_loc path d
          else
            let indirect_loc := struct.field_ref_f hashtriemap.node "indirect" n in
            indirect_par (curry Φ) γ d indirect_loc path
      )%I.

  Definition node (γ: ghost_names) d : loc → list Z → iProp Σ :=
    λ n path, bi_least_fixpoint (nodeF γ d) (n, path).

  Definition indirect γ d := indirect_par (node γ d) γ d.

  (* Global invariant tying the trie to the abstract map. *)
  Definition ht_inv `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
                    (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (i: loc),
      own_Value (struct.field_ref_f hashtriemap.HashTrieMap "root" ht) 1
                (interface.mk (ptrT.id hashtriemap.indirect.id) (# i)) ∗
      indirect γ 1 i [].

  (* Public predicate exposed to clients. *)
  Definition mapN         : namespace := nroot .@ "hashtriemap".
  Definition init_statusN : namespace := nroot .@ "hashtriemap.init_status".

  Definition is_hashtriemap `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
                            (γ: ghost_names) (ht: loc) : iProp Σ :=
    inv mapN (ht_inv ht γ).

  Definition init_status_done
               `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64)}
               (γ: ghost_names) (ht: loc) (b: bool) : iProp Σ :=
    (if b then is_hashtriemap γ ht else True%I).

  Definition init_status_inv
               `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
               (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (b: bool),
      own_Uint32 (struct.field_ref_f hashtriemap.HashTrieMap "inited" ht) 1
                 (if b then W32 1 else W32 0) ∗
      init_tok γ b ∗
      □ init_status_done γ ht b.

  Definition init_status
               `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
               (ht: loc) (γ: ghost_names) : iProp Σ :=
    inv init_statusN (init_status_inv ht γ).

  (* Initialization lock invariant for HashTrieMap. *)
  Definition init_mu_inv `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
                         (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (b: bool),
      if b
      then init_tok γ true
      else (init_tok γ false ∗
            (∃ (seed: w64),
               ht ↦s[hashtriemap.HashTrieMap :: "seed"] seed) ∗
            own_Value (struct.field_ref_f hashtriemap.HashTrieMap "root" ht) 1 interface.nil
           )%I.

  Definition init_mu `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
                     (ht: loc) (γ: ghost_names) : iProp Σ :=
    is_Mutex (struct.field_ref_f hashtriemap.HashTrieMap "initMu" ht)
             (init_mu_inv ht γ).

  Definition hashtriemap_init
               `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool}
               (ht: loc) (γ: ghost_names) : iProp Σ :=
    init_status ht γ ∗ init_mu ht γ.

  Lemma hashtriemap_pre_auth_init
          `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool} :
    ⊢ |==> ∃ γ, init_tok γ false ∗ init_tok γ false.
  Proof.
    iMod (ghost_var_alloc (false)) as (init_γ) "[Hinit1 Hinit2]".
    iMod (ghost_var_alloc (∅ : gmap w64 w64)) as (map_γ) "[Huser Hvar]".
    iModIntro.
    iExists (mkNames map_γ init_γ).
    iFrame.
  Qed.

  Lemma hashtriemap_zero_init
      `{!mapG Σ w64 w64, !ghost_varG Σ (gmap w64 w64), !ghost_varG Σ bool(* , !syncG Σ *)}
      (ht: loc) E :
    ht ↦ default_val hashtriemap.HashTrieMap.t ⊢
    |={E}=> ∃ γ, hashtriemap_init ht γ.
  Proof.
    iIntros "Hht".
    iDestruct (struct_fields_split with "Hht") as "Hfields".
    iNamed "Hfields".
    simpl.
    iMod (hashtriemap_pre_auth_init) as (γ) "(Htok1 & Htok2)".

    iApply struct_fields_split in "Hinited".
    iNamed "Hinited".
    iDestruct (Uint32_unfold with "Hv") as "Hinited".
    iClear "H_0".

    iApply struct_fields_split in "Hroot".
    iNamed "Hroot".
    iDestruct (Value_unfold with "Hv") as "Hroot".

    iMod (inv_alloc init_statusN _ (init_status_inv ht γ) with "[Htok1 Hinited]") as "#Hinit".
    {
      iNext.
      iExists false.
      iFrame.
      simpl.
      iModIntro.
      done.
    }

    iAssert (▷ init_mu_inv ht γ)%I with "[Htok2 Hseed Hroot]" as "Hmu_inv".
    {
      iNext.
      iExists false.
      iFrame "Htok2".
      iSplitL "Hseed".
      { iExists (W64 0). iFrame. }
      iFrame "Hroot".
    }

    set (m := struct.field_ref_f hashtriemap.HashTrieMap "initMu" ht).

    iAssert (|={E}=> is_Mutex m (init_mu_inv ht γ))%I with "[HinitMu Hmu_inv]" as "Hmutex".
    {
      iDestruct (init_Mutex (init_mu_inv ht γ) ⊤ m with "[$]") as "Hmu".
      iSpecialize ("Hmu" with "Hmu_inv").
      (* iExact "Hmu". *)
      (* TODO *)
      (* Error: Tactic failure: iExact: "Hmu" : (|={⊤}=> is_Mutex m (init_mu_inv ht γ))%I does not match goal. *)
      (* goal: *)
      (* |={⊤}=> is_Mutex m (init_mu_inv ht γ) *)
      (* ????? *)
      admit.
    }

    iMod "Hmutex".

    iModIntro.
    iExists γ.
    iFrame "Hinit Hmutex".
  Admitted.

End model.
