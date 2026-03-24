From iris.bi.lib Require Import fractional atomic.

From New.code.hashtriemap Require Import hashtriemap.
From New.generatedproof.hashtriemap Require Import hashtriemap.

From New.proof Require Import atomic mutex.

From Perennial.algebra Require Import auth_map.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.Helpers Require Import NamedProps.
Import named_props_ascii_notation.
From New.ghost Require Import ghost_var dghost_var.
From New.ghost Require Import mono_list.
From New.ghost Require Import token.

From New.proof.hashtriemap Require Import aux.
From New.proof.hashtriemap Require Export paths.

From Stdlib Require Import ZArith List.
(* From stdpp Require Import base. *)

Open Scope Z_scope.

Section model.
  (* namespace definitions *)
  Definition mapN         : namespace := nroot .@ "hashtriemap".
  Definition init_statusN : namespace := nroot .@ "init_status".
  Definition indN         : namespace := nroot .@ "indirect".
  Definition entryN       : namespace := nroot .@ "entry".
  Definition bucketN      : namespace := nroot .@ "bucket".
  Definition lookupEscrowN : namespace := nroot .@ "lookup_escrow".
  Definition lookupInterpN : namespace := nroot .@ "lookup_interp".

  Record hash_names := mkHashNames {
                           hh_idxs_name : gname;
                           hh_hist_name : gname;
                           hh_lookup_name : gname;
                         }.

  (* Ghost state for the hashtriemap. *)
  Record ghost_names := mkNames {
                            (* bool *)
                            init_name : gname;
                            (* auth_map w64 (gmap K V) *)
                            map_name : gname;
                            (* auth_map K V *)
                            user_name : gname;
                            (* auth_map Z gname *)
                            buckets_name : gname;
                            (* auth_map (Z * nat) (gmap loc nat) *)
                            idxs_name : gname;
                            histories_name : gname;
                          }.

  (* discount generics *)
  Definition K : Type := w64.
  Definition V : Type := w64.
  #[global] Instance K_inhab : Inhabited K := _.
  #[global] Opaque K V.

  Context `{hG: heapGS Σ, !ffi_semantics _ _}
    {sem: go.Semantics}.

  Context `{!globalsGS Σ, !ghost_varG Σ (gmap w64 w64)}
           `{!ghost_varG Σ bool}
    `{!mapG Σ K V}
    `{!mapG Σ Z (gmap K V)}
    `{!mapG Σ nat (gmap K V)}
    `{!mapG Σ Z gname}
    `{!mapG Σ (Z * nat) (gmap loc nat) }
    `{!mapG Σ Z hash_names}.

  Inductive lookup_status :=
  | LookupPending
  | LookupDone
  | LookupConsumed.

  (* Abstract map state seen by clients. *)
  Definition own_ht_map (γ: ghost_names) (m: gmap K V) : iProp Σ :=
    map_ctx γ.(user_name) (1/2) m.

  Definition ht_load_ret (m: gmap K V) (key: K) : val :=
    (match m !! key with
    | Some v => (#v, #true)
    | None => (#(zero_val V), #false)
    end)%V.

  Definition ht_au_mask : coPset :=
    ⊤ ∖ ↑mapN ∖ ↑indN ∖ ↑entryN ∖ ↑lookupInterpN.

  Record lookup_info := mkLookupInfo {
                            lookup_key : K;
                            lookup_idx : nat;
                            lookup_version : nat;
                            lookup_done_name : gname;
                            lookup_consumed_name : gname;
                          }.

  Context `{!mapG Σ nat lookup_info}.

  Lemma alloc_lookup_help_token {E} (P : iProp Σ) :
    ⊢ |={E}=> ∃ γdone,
        "Htok_to_P" ∷ (token γdone ={↑lookupEscrowN}=∗ ▷ P) ∗
        "HP_to_tok" ∷ (▷ P ={↑lookupEscrowN}=∗ token γdone).
  Proof.
    iMod (token_alloc) as "[%γdone Htok]".
    iMod (token_alloc) as "[%γdone2 Htok2]".
    iMod (inv_alloc lookupEscrowN _ (P ∗ token γdone2 ∨ token γdone)%I with "[$Htok]")
      as "#Hescrow".
    iExists γdone.
    iModIntro.
    iSplitR.
    - iIntros "Ht". iInv "Hescrow" as "[[HP _]| >Hbad]"; first by iFrame.
      iCombine "Ht Hbad" gives %[].
    - iIntros "HP". iInv "Hescrow" as "[[_ >Hbad] | >Htok]".
      + iCombine "Htok2 Hbad" gives %[].
      + iModIntro. iSplitR "Htok"; last by iFrame. iNext. iLeft. iFrame.
  Qed.

  Definition map_current_version (hist : list (gmap K V)) : nat :=
    pred (length hist).

  Parameter hash_key : K → w64.

  Definition hash_map : Type := gmap Z (gmap K V).

  Definition empty_hash_map : hash_map :=
    gset_to_gmap ∅ (list_to_set full_domain).

  Inductive path_ownership :=
  | Empty
  | Singleton (h: Z) (m: gmap K V).

  Context `{!mapG Σ K nat}.

  Definition lookup_status_interp
    (γ : ghost_names) (linfo : lookup_info) (status : lookup_status) γh (idx : gmap K nat) : iProp Σ :=
        match status with
        | LookupPending =>
            (|={⊤∖↑lookupEscrowN,∅}=> ∃ m, own_ht_map γ m ∗
                                          mono_list_idx_own γh.(hh_hist_name) linfo.(lookup_version) m ∗
                                          (own_ht_map γ m ={∅,⊤∖↑lookupEscrowN}=∗
                                           token linfo.(lookup_done_name)))
        | LookupDone =>
            let key := linfo.(lookup_key) in
            token linfo.(lookup_done_name) ∗ ⌜((idx !! key = None) ∨ (∃ (i : nat), idx !! key = Some i ∧ i < linfo.(lookup_idx)))⌝
        | LookupConsumed =>
            token linfo.(lookup_consumed_name)
        end.

  Definition own_hash_history γ h γh : iProp Σ :=
    inv lookupInterpN (
        ∃ (hist : list (gmap K V)) (lookups : gmap nat lookup_info) map (idxs : gmap K nat),
          "Hhash" ∷ h [[γ.(map_name)]]↦{1/2} map ∗
          "#Hhist_name" ∷ ptsto_ro γ.(histories_name) h γh ∗
          "Hown_hist" ∷ mono_list_auth_own γh.(hh_hist_name) 1 hist ∗
          "%Hcur" ∷ ⌜hist !! map_current_version hist = Some map⌝ ∗
          "Hown_lookups" ∷ map_ctx γh.(hh_lookup_name) 1 lookups ∗
          "Hlookups" ∷
            ([∗ map] id ↦ linfo ∈ lookups,
                ⌜linfo.(lookup_version) < length hist⌝ ∗
                ∃ status,
                  ⌜linfo.(lookup_version) < length hist - 1 → status ≠ LookupPending⌝ ∗
                  lookup_status_interp γ linfo status γh idxs
            ) ∗
          "%Hidxs_dom" ∷ ⌜dom idxs = dom map⌝ ∗
          "Hidxs" ∷
            ([∗ map] k ↦ i ∈ idxs,
               ptsto_mut γh.(hh_idxs_name) k 1 i) ∗
          "Hidxs_auth" ∷ map_ctx γh.(hh_idxs_name) (1/2) idxs
      ).

  Definition histories γ : iProp Σ :=
    [∗ list] hash ∈ seqZ 0 (2 ^ 64),
      ∃ γhist,
        hash [[γ.(histories_name)]]↦ro γhist ∗
        own_hash_history γ hash γhist.

  Definition own_domain
    (γ : ghost_names) (q: Qp) (dom : domain) (ownership : path_ownership) : iProp Σ :=
    let γmap := γ.(map_name) in
    let γhists := γ.(histories_name) in
    match ownership with
    | Empty =>
        [∗ list] hash ∈ dom,
          ∃ (map : gmap K V),
            hash [[γmap]]↦{q/2} map
    | Singleton h m =>
        [∗ list] hash ∈ dom,
          if decide (hash = h)
          then
            hash [[γmap]]↦{q/2} m
          else
            ∃ (map : gmap K V),
              hash [[γmap]]↦{q/2} map
    end.

  Definition own_path
    (γ : ghost_names) (q: Qp) (p : path) (ownership : path_ownership) : iProp Σ :=
    own_domain γ q (path_to_domain p) ownership.

  #[global] Instance own_path_fractional γ dom f :
    Fractional (λ q, own_path γ q dom f).
  Proof.
    intros p q.
    rewrite /own_path /own_domain.
    destruct f.
    {
      assert (∀ (n : nat) (hash : Z), Fractional ((λ q0, ∃ map : gmap K V,
                                                    hash [[γ.(map_name)]]↦{q0} map)%I)).
      {
        intros n hash.
        intros a b.
        iSplit.
        - iIntros "[%m x]".
          iDestruct "x" as "[x1 x2]".
          iFrame.
        - iIntros "[[%m1 x] [%m2 y]]".
          iDestruct (ptsto_agree with "x y") as %->.
          iCombine "x y" as "$".
      }
      replace (((p + q) / 2)%Qp) with (((p / 2) + (q / 2))%Qp) by (rewrite Qp.div_add_distr; done).
      iApply (fractional_big_sepL _ _ H).
    }
    {
      assert (∀ (n : nat) (hash : Z), Fractional ((λ q0,
                                                   if decide (hash = h)
                                                   then hash [[γ.(map_name)]]↦{q0} m
                                                   else
                                                     ∃ map : gmap K V,
                                                       hash [[γ.(map_name)]]↦{
                                                           q0} map
                                                )%I)).
      {
        intros n hash.
        intros a b.
        destruct (decide (hash = h)).
        - iSplit.
          + iIntros "[H1 H2]".
            iFrame.
          + iIntros "[a b]".
            iCombine "a b" as "$".
        - iSplit.
          + iIntros "H1".
            iDestruct "H1" as "(%map & H1)".
            iDestruct "H1" as "[H1 H2]".
            iFrame.
          + iIntros "[[%map1 H1] [%map2 H2]]".
            iDestruct (ptsto_agree with "H1 H2") as %->.
            iCombine "H1 H2" as "$".
      }
      replace (((p + q) / 2)%Qp) with (((p / 2) + (q / 2))%Qp) by (rewrite Qp.div_add_distr; done).
      iApply (fractional_big_sepL _ _ H).
    }
  Qed.

  #[global] Instance own_path_as_fractional γ path f q :
    AsFractional (own_path γ q path f) (λ q, own_path γ q path f) q.
  Proof. split; [done|apply _]. Qed.

  #[global] Opaque own_domain.
  #[local] Transparent own_domain.

  #[global] Opaque own_path.
  #[local] Transparent own_path.

  Definition bucket_of_map (m : gmap K V) (h : Z) : gmap K V :=
    map_filter (λ x : K * V, uint.Z (hash_key x.1) = h) _ m.

  (* Definition bucket_snapshot (γ : ghost_names) (ver : nat) (h : Z) (bm : gmap K V) : iProp Σ := *)
  (*   ∃ mver, *)
  (*     mono_list_idx_own γ.(hist_name) ver mver ∗ *)
  (*     ⌜bm = bucket_of_map mver h⌝. *)

  Definition flatten (hm: hash_map) : gmap K V :=
    map_fold (λ (_: Z) (sub: gmap K V) (acc: gmap K V), sub ∪ acc) ∅ hm.

  Definition own_entry (γ: ghost_names) (q: Qp) (k: K) (v: V) : iProp Σ :=
    ptsto_mut γ.(user_name) k q v.

  Definition entry_next (ent next : loc) q := ent.[hashtriemap.entry.t, "overflow"] ↦ᵥ{q}
                           (interface.mk_ok (hashtriemap.entry) (#next)).

  (* entry cannot own the path, then it becomes duplicate ownership between the entries *)
  (* the indirect (node) holding the entry chain needs to own the path, and then the entries *)
  (* own keys that belong to that path *)
  Definition entry_inv
    (γ: ghost_names) (q: Qp)
    (entry: loc -d> Z -d> iProp Σ)
    (e: loc) (h: Z)
    : iProp Σ :=
    ∃ (next: loc) (k: K) (v: V) (γbucket : gname),
      "#Hk" :: e.[hashtriemap.entry.t, "key"]   ↦□ k ∗
      "#Hv" :: e.[hashtriemap.entry.t, "value"] ↦□ v ∗
      "Hown_next" :: entry_next e next (q/2) ∗
      "Hown_entry" ∷ own_entry γ q k v ∗
      "%Hhash" :: ⌜uint.Z (hash_key k) = h⌝ ∗
      "#Hnext_entry" :: (⌜next ≠ null⌝ -∗ ▷ entry next h) ∗
      "Hname" ∷ ptsto_ro γ.(buckets_name) h γbucket ∗
      "Hbucket_frag" ∷ auth_set_frag γbucket e.

  Definition entry_F
    (γ: ghost_names) (q: Qp)
    (entry: loc -d> Z -d> iProp Σ)
    : loc -d> Z -d> iProp Σ :=
    λ e h,
      ("#Hentry_inv" :: inv (entryN .@ e) (entry_inv γ q entry e h))%I.

  #[global] Instance entry_F_contractive γ q : Contractive (entry_F γ q).
  Proof.
    rewrite /entry_F /entry_inv.
    intros n f g Hfg e path.
    (* repeat (f_equiv; try solve_contractive). *)
    do 15 f_equiv.
    solve_contractive.
  Qed.

  Definition entry (γ: ghost_names) (q: Qp) (e: loc) (h: Z) : iProp Σ :=
    fixpoint (entry_F γ q) e h.

  Lemma entry_unfold γ q e path :
    entry γ q e path ⊣⊢ entry_F γ q (entry γ q) e path.
  Proof. apply (fixpoint_unfold (entry_F γ q)). Qed.

  #[global] Instance entry_persistent γ q e path : Persistent (entry γ q e path).
  Proof.
    rewrite entry_unfold /entry_F.
    apply _.
  Qed.

  Definition indirect_node
    (child_indirect: loc -d> path -d> iProp Σ)
    (γ: ghost_names) (q: Qp)
    (nodeptr: loc)
    (path child_path: path) : iProp Σ :=
    ∃ ind,
      "%Hchild_path_len" ∷ ⌜length child_path < 16⌝ ∗
      "%Hchild_not_null" ∷ ⌜ind ≠ null⌝ ∗
      "#Hchild_ind_ptr" ∷ nodeptr.[hashtriemap.node.t, "ind"] ↦□ ind ∗
      "#Hchild_ent_ptr" ∷ nodeptr.[hashtriemap.node.t, "ent"] ↦□ null ∗
      "#Hchild_ind" ∷ ▷ child_indirect ind child_path.

  Definition bucket (γ : ghost_names) (γbucket : gname) (q: Qp) (hash: Z) (sub : gmap K V) (ver : nat) (first_ent : loc) : iProp Σ :=
    ∃ (entries : gset loc) (idxs : gmap loc nat),
      "Hentries_auth" ∷ auth_set_auth γbucket entries ∗
      "#Hidxs" ∷ ptsto_ro γ.(idxs_name) (hash, ver) idxs ∗
      "%Hfirst" ∷ ⌜idxs !! first_ent = Some 0%nat⌝ ∗
      "%Hidxs_dom" ∷ ⌜dom idxs = entries⌝ ∗
      ([∗ set] ent ∈ entries,
         ∃ (next : loc) idx,
           "%Hidx" ∷ ⌜idxs !! ent = Some idx⌝ ∗
           "Hnext" ∷ entry_next ent next (q/2) ∗
           "%Hnext_idx" ∷ ⌜
             if (decide (next ≠ null))
             then (idxs !! next) = Some (S idx)
             else (S idx = size sub)⌝
      ).

  Definition entry_node
    (γ: ghost_names) (q: Qp)
    (nodeptr: loc)
    (path: path) : iProp Σ :=
    ∃ ent map hash γbucket ver,
      "Hown_path" ∷ own_path γ q path (Singleton hash map) ∗
      "%Hchild_not_null" ∷ ⌜ent ≠ null⌝ ∗
      "#Hchild_ent_ptr" ∷ nodeptr.[hashtriemap.node.t, "ent"] ↦□ ent ∗
      "#Hchild_ind_ptr" ∷ nodeptr.[hashtriemap.node.t, "ind"] ↦□ null ∗
      "#Hchild_entry" ∷ entry γ q ent hash ∗
      "%Hbelongs" ∷ ⌜belongs_to_path path hash⌝ ∗
      "#Hnames" ∷ ptsto_ro γ.(buckets_name) hash γbucket ∗
      "Hbucket" ∷ bucket γ γbucket q hash map ver ent.

  (* definition of node *)
  Definition childP
    (child_indirect: loc -d> path -d> iProp Σ)
    (γ: ghost_names) (q: Qp)
    (nodeptr: loc)
    (path child_path: path) : iProp Σ :=
    if (decide (nodeptr = null)) then
      "Hchild" ∷ own_path γ q child_path Empty
    else
      (∃ (is_entry: bool),
          "#Hnode_is_entry" ∷ nodeptr.[hashtriemap.node.t, "isEntry"] ↦□ is_entry ∗
          "Hchild" ∷
            (if is_entry then
               entry_node γ q nodeptr child_path
             else
               indirect_node child_indirect γ q nodeptr path child_path))%I.

  Definition childrenP
    (child_indirect: loc -d> path -d> iProp Σ)
    (γ: ghost_names) (q: Qp) (children_slice: slice.t)
    (children_vals: list atomic.Value.t)
    (ind: loc) (path: path) : iProp Σ :=
    "Hchildren" :: [∗ list] i ↦ val ∈ children_vals,
      ∃ (nodeptr: loc),
        "Hown_child" :: (slice.slice_index_ref atomic.Value.t i children_slice) ↦ᵥ{q}
          (interface.ok (interface.mk (go.PointerType hashtriemap.node) #nodeptr)) ∗
        "Hchild" :: childP child_indirect γ q nodeptr path (path ++ [Z.of_nat i]).

  (* split 50/50 between an invariant and the mutex to allow for lock-free reads *)
  (* we always have read permission on any indirect, but only can write if we acquire the lock *)
  (* the only things ever modified are atomic values (atomic pointers), everything else is □ ownership *)
  Definition indirect_F
    (γ: ghost_names)
    (indirect: loc -d> (list Z) -d> iProp Σ)
    : loc -d> (list Z) -d> iProp Σ :=
    λ ind path,
      (∃ (children_vals: list atomic.Value.t) (children_slice: slice.t),
          "#Hown_children" :: ind.[hashtriemap.indirect.t, "children"] ↦□ children_slice ∗
          "#Hchildren_slice" :: children_slice ↦*□ children_vals ∗
          "%Hchildren_len" :: ⌜length children_vals = 16%nat⌝ ∗
          "#Hind_inv" :: inv (indN) ((childrenP indirect γ (1/2) children_slice children_vals ind path)) ∗
          "#Hind_mutex" :: is_Mutex ind.[hashtriemap.indirect.t, "mu"] (
              (* dont need to split dead between inv and mutex because its only used for modification of the tree *)
              ∃ (dead: bool),
                "Hdead" ∷ own_Bool ind.[hashtriemap.indirect.t, "dead"] (DfracOwn 1) dead ∗
                "Hmu_inv" ∷ ((* ⌜dead = false⌝ -∗ *) childrenP indirect γ (1/2) children_slice children_vals ind path)))%I.

  (* Prove contractiveness *)
  #[global] Instance indirect_F_contractive γ : Contractive (indirect_F γ).
  Proof.
    rewrite /indirect_F.
    intros n f g Hfg ind path.
    unfold childrenP, childP.
    do 24 f_equiv.
    2: do 4 f_equiv.
    all: solve_contractive.
  Qed.

  Definition indirect (γ: ghost_names) (ind: loc) (path: path) : iProp Σ :=
    fixpoint (indirect_F γ) ind path.

  Lemma indirect_unfold γ ind path :
    indirect γ ind path ⊣⊢
    indirect_F γ (indirect γ) ind path.
  Proof. apply (fixpoint_unfold (indirect_F γ)). Qed.

  #[global] Instance indirect_persistent γ ind path : Persistent (indirect γ ind path).
  Proof.
    rewrite indirect_unfold /indirect_F.
    apply _.
  Qed.

  #[global] Instance indirect_node_persistent γ q nodeptr path child_path : Persistent (indirect_node (indirect γ) γ q nodeptr path child_path).
  Proof. apply _. Qed.

  Definition lookup_token
    (γ : ghost_names) (id ver idx : nat) (key : K) : iProp Σ :=
    ∃ (h : Z) γhist γdone (mver : gmap K V) γconsumed,
      "%Hhash" ∷ ⌜h = uint.Z (hash_key key)⌝ ∗
      "#Hhist_name" ∷ ptsto_ro γ.(histories_name) h γhist ∗
      "Hlookup_info" ∷ ptsto_mut γhist.(hh_lookup_name) id (1/2) (mkLookupInfo key idx ver γdone γconsumed) ∗
      "#Hver" ∷ mono_list_idx_own γhist.(hh_hist_name) ver mver ∗
      "Hconsumed_token" ∷ token γconsumed.

  Definition buckets_map (γ: ghost_names) : iProp Σ :=
    (* ∃ buckets, *)
    (*   map_ctx γ.(buckets_name) 1 buckets ∗ *)
      ([∗ list] h ∈ (seqZ 0 (2^64)),
         ∃ (γbucket : gname),
           ptsto_ro γ.(buckets_name) h γbucket).

  (* abstract the state of the entire map, can be fully abstracted away from hashtriemap.v *)
  Definition map_state (γ: ghost_names) (user_map: gmap K V) (hm: hash_map) : iProp Σ :=
    "Hauth_map" :: map_ctx γ.(map_name) 1 hm ∗
    "Huser_map" :: own_ht_map γ user_map ∗
    "%Hflat" :: ⌜user_map = flatten hm⌝ ∗
    (* bucket correctness - if a key exists, then its in the correct bucket *)
    "%Hbuckets" ::     (⌜∀ h sub k,
                         hm !! h = Some sub →
                         uint.Z (hash_key k) = h →
                         flatten hm !! k = sub !! k⌝) ∗
    "%Hbuckets_rev" ∷ (⌜∀ h sub k v,
                         hm !! h = Some sub →
                         sub !! k = Some v →
                         uint.Z (hash_key k) = h⌝).

  (* this is usually only really needed once per function, so it's convenient if its bundled away *)
  Definition own_root
    (γ: ghost_names) (ht: loc) (rooti: loc) : iProp Σ :=
    "Hown_root" ∷ ht.[hashtriemap.HashTrieMap.t, "root"] ↦ᵥ
                       (interface.ok (interface.mk (go.PointerType hashtriemap.indirect) #rooti)) ∗
    "#Hroot_indirect" ∷ indirect γ rooti [].

  Definition ht_inv
    (γ: ghost_names) (ht: loc) : iProp Σ :=
    inv mapN (
        ∃ root user_map hm,
          own_root γ ht root ∗
          map_state γ user_map hm
      ).

  (* Public predicate exposed to clients. *)
  Definition is_hashtriemap
    (γ: ghost_names) (ht: loc) : iProp Σ :=
    ("#Hseed" :: ∃ (seed: w64), ht.[hashtriemap.HashTrieMap.t, "seed"] ↦□ seed) ∗
    "#His_map" :: ht_inv γ ht.

  (* designed to be split between an invariant and a mutex, so that reading can be done outside of the critical section and writing can only be done inside *)
  Definition init_tok `{!ghost_varG Σ bool} (γ: ghost_names) (b: bool) : iProp Σ :=
    ghost_var γ.(init_name) (1/2)%Qp b.

  Definition init_status_done
    (γ: ghost_names) (ht: loc) (b: bool) : iProp Σ :=
    (if b then is_hashtriemap γ ht else True%I).

  Definition init_status_inv
    `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (b: bool),
      own_Uint32 ht.[hashtriemap.HashTrieMap.t, "inited"] 1
        (if b then W32 1 else W32 0) ∗
      init_tok γ b ∗
      □ init_status_done γ ht b.

  Definition init_status
    `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    inv init_statusN (init_status_inv ht γ).

  (* Initialization lock invariant for HashTrieMap. *)
  Definition init_mu_inv `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    ∃ (b: bool),
      if b
      then init_tok γ true
      else (init_tok γ false ∗
            (∃ (seed: w64),
                ht.[hashtriemap.HashTrieMap.t, "seed"] ↦ seed) ∗
            ht.[hashtriemap.HashTrieMap.t, "root"] ↦ᵥ interface.nil
           )%I.

  Definition init_mu `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    is_Mutex ((ht.[hashtriemap.HashTrieMap.t, "initMu"]))
      (init_mu_inv ht γ).

  Definition hashtriemap_init
    `{!ghost_varG Σ bool}
    (ht: loc) (γ: ghost_names) : iProp Σ :=
    "#Hinit" :: init_status ht γ ∗
    "#Hinit_mu" :: init_mu ht γ.

  Lemma hashtriemap_pre_auth_init
    `{!mapG Σ nat lookup_info, !mapG Σ Z gname,
      !mapG Σ (Z * nat) (gmap loc nat), !mapG Σ Z hash_history_names} :
    ⊢ |==> ∃ γ,
      "Hinit_tok1" ∷ init_tok γ false ∗
      "Hinit_tok2" ∷ init_tok γ false.
  Proof.
    iMod (ghost_var_alloc (false)) as (init_γ) "[Hinit1 Hinit2]".
    iMod (ghost_var_alloc (∅ : gmap K V)) as (map_γ) "Hmap".
    iMod (ghost_var_alloc (∅ : gmap K V)) as (user_γ) "[Huser1 Huser2]".
    iMod (map_init (∅ : gmap Z gname)) as (buckets_γ) "Hbuckets".
    iMod (map_init (∅ : gmap (Z * nat) (gmap loc nat))) as (idxs_γ) "Hidxs".
    iMod (map_init (∅ : gmap Z hash_history_names)) as (histories_γ) "Hhistories".

    iMod (token_alloc) as (γ) "_".

    iModIntro.
    iExists (mkNames init_γ map_γ user_γ
               buckets_γ idxs_γ histories_γ).
    iFrame.
  Qed.

  Lemma hashtriemap_zero_init
    `{!mapG Σ nat lookup_info, !mapG Σ Z gname,
      !mapG Σ (Z * nat) (gmap loc nat), !mapG Σ Z hash_history_names}
    {sync_sem : sync.Assumptions} {E}
    (ht: loc) :
    "Hht" ∷ ht ↦ zero_val hashtriemap.HashTrieMap.t ={E}=∗
    ∃ γ, "Hht_init" ∷ hashtriemap_init ht γ.
  Proof.
    iIntros "Hht".
    iDestruct (typed_pointsto_split with "Hht") as "Hfields".
    iNamed "Hfields".
    simpl.
    iMod (hashtriemap_pre_auth_init) as (γ) "(Htok1 & Htok2)".

    iMod (inv_alloc init_statusN _ (init_status_inv ht γ) with "[Htok1 inited]") as "#Hinit".
    {
      iNext.
      iExists false.
      iFrame.
      done.
    }
    set (m := ht.[hashtriemap.HashTrieMap.t, "initMu"]).

    iMod (init_Mutex (init_mu_inv ht γ) E m with "initMu [Htok2 seed root]") as "Hmutex".
    {
      iNext.
      iExists false.
      iFrame.
    }

    iModIntro.
    iExists γ.
    iFrame.
    iFrame "#".
  Qed.

  Lemma own_path_lookup h path γ q m :
    h ∈ path_to_domain path →
    "Hpath" ∷ own_path γ q path (Singleton h m) -∗
    "Hptsto" ∷ ptsto_mut γ.(map_name) h (q/2) m ∗
    "Hclose" ∷ (ptsto_mut γ.(map_name) h (q/2) m -∗ own_path γ q path (Singleton h m)).
  Proof.
    iIntros (Hdom) "Hpath".
    Local Transparent own_path.
    Local Transparent own_domain.
    unfold own_path, own_domain.
    iDestruct (big_sepL_elem_of_acc with "Hpath") as "[Hptsto Hclose]"; [exact Hdom|].
    iSplitL "Hptsto".
    - rewrite decide_True; [done|done].
    - iIntros "Hptsto".
      iApply "Hclose".
      rewrite decide_True; [done|done].
  Qed.

  Lemma buckets_disjoint
    (hm : gmap Z (gmap K V))
    (Hbuckets_rev : ∀ h sub k v,
       hm !! h = Some sub →
       sub !! k = Some v →
       uint.Z (hash_key k) = h) :
    ∀ h1 h2 sub1 sub2,
    hm !! h1 = Some sub1 →
    hm !! h2 = Some sub2 →
    h1 ≠ h2 →
    sub1 ##ₘ sub2.
  Proof.
    intros h1 h2 sub1 sub2 H1 H2 Hneq.
    apply map_disjoint_spec; intros k v1 v2 Hk1 Hk2.
    have Hh1 : uint.Z (hash_key k) = h1 :=
      Hbuckets_rev _ _ _ _ H1 Hk1.
    have Hh2 : uint.Z (hash_key k) = h2 :=
      Hbuckets_rev _ _ _ _ H2 Hk2.
    congruence.
  Qed.

  Lemma flatten_update_update
    hm h k v old :
    hm !! h = Some old →
    uint.Z (hash_key k) = h →
    (∀ h0 sub k v, hm !! h0 = Some sub → sub !! k = Some v → uint.Z (hash_key k) = h0) →
    flatten (<[h:=<[k:=v]> old]> hm) = <[k:=v]> (flatten hm).
  Proof.
    intros Hh Hhash Hbuckets_rev.

    have Hhm_eq : hm = <[h:=old]> (delete h hm).
    {
      apply map_eq; intro h0.
      destruct (decide (h0 = h)) as [->|Hneq].
      - rewrite lookup_insert lookup_delete_eq Hh. rewrite decide_True; reflexivity.
      - rewrite lookup_insert_ne; [|done].
        rewrite lookup_delete_ne; [|done].
        reflexivity.
    }

    rewrite Hhm_eq.
    rewrite insert_insert.

    unfold flatten.
    rewrite map_fold_insert_L; [| |rewrite lookup_delete_eq; reflexivity].
    2: {
      intros.
      rewrite map_union_assoc.
      symmetry.
      rewrite map_union_assoc.
      replace (z2 ∪ z1) with (z1 ∪ z2); [reflexivity|].
      apply map_union_comm.

      have H0' : hm !! j1 = Some z1 by rewrite -Hhm_eq in H0; exact H0.
      have H1' : hm !! j2 = Some z2 by rewrite -Hhm_eq in H1; exact H1.
      eapply buckets_disjoint; eauto.
    }

    rewrite decide_True; [|reflexivity].

    rewrite map_fold_insert_L; [| |rewrite lookup_delete_eq; reflexivity].
    2: {
      intros.
      rewrite map_union_assoc.
      symmetry.
      rewrite map_union_assoc.
      replace (z2 ∪ z1) with (z1 ∪ z2); [reflexivity|].
      apply map_union_comm.

      set (hm'' := <[h:=<[k:=v]> old]> (delete h hm)).
      have Hbuckets_rev' :
        ∀ h0 sub k0 v0,
        hm'' !! h0 = Some sub →
        sub !! k0 = Some v0 →
        uint.Z (hash_key k0) = h0.
      {
        intros h0 sub k0 v0 Hlook Hsub.
        destruct (decide (h0 = h)) as [->|Hneq].
        - rewrite lookup_insert in Hlook.
          rewrite decide_True in Hlook; [|reflexivity].
          inversion Hlook; subst sub.
          destruct (decide (k0 = k)) as [->|Hk].
          + exact Hhash.
          + have Hold : old !! k0 = Some v0 by rewrite lookup_insert_ne in Hsub; [exact Hsub|symmetry; exact Hk].
            have Hh_old : uint.Z (hash_key k0) = h :=
              Hbuckets_rev _ _ _ _ Hh Hold.
            exact Hh_old.
        - rewrite lookup_insert_ne in Hlook; [|symmetry; exact Hneq].
          eapply Hbuckets_rev; eauto.
          apply lookup_delete_Some in Hlook as [_ Hhm].
          exact Hhm.
      }

      have H0' : hm'' !! j1 = Some z1 := H0.
      have H1' : hm'' !! j2 = Some z2 := H1.
      eapply buckets_disjoint; eauto.
    }

    apply map_eq; intro k'.
    destruct (decide (k' = k)) as [->|Hk].
    - rewrite lookup_insert.
      rewrite lookup_union.
      rewrite lookup_insert.
      rewrite decide_True; [|reflexivity].
      rewrite decide_True; [|reflexivity].
      apply union_Some_l.
    - rewrite lookup_insert_ne; [|done].
      rewrite lookup_union.
      rewrite lookup_insert_ne; [|done].
      change (map_fold (λ (_ : Z) (sub acc : gmap K V), sub ∪ acc) ∅ (delete h hm)) with (flatten (delete h hm)).
      rewrite lookup_union.
      reflexivity.
  Qed.

  Lemma own_path_update_key key value γ hm path h old :
    h = uint.Z (hash_key key) →
    let hm' := <[h := <[key:=value]> old]> hm in
    belongs_to_path path h →
    "Hctx" ∷ map_ctx γ.(map_name) 1 hm ∗
    "Hfrag" ∷ h [[γ.(map_name)]]↦{1 / 2} old ∗
    "Hpath" ∷ own_path γ 1 path (Singleton h old) ==∗
    "Hctx" ∷ map_ctx γ.(map_name) 1 hm' ∗
    "Hfrag" ∷ h [[γ.(map_name)]]↦{1 / 2} (<[key:=value]> old) ∗
    "Hpath" ∷ own_path γ 1 path (Singleton h (<[key:=value]> old)).
  Proof.
    intros Hhash hm' Hbelongs.
    iIntros "x"; iNamed "x".
    subst hm'.
    have Hbelongs' : belongs_to_path path (uint.Z (hash_key key)).
    { rewrite <- Hhash. exact Hbelongs. }
    have Hdom0 : uint.Z (hash_key key) ∈ path_to_domain path.
    { apply (path_to_domain_elem _ _); [apply full_domain_elem|exact Hbelongs']. }
    have Hdom : h ∈ path_to_domain path.
    { rewrite Hhash. exact Hdom0. }
    unfold own_path, own_domain.
    set (dom := path_to_domain path) in *.
    have Hnodup : base.NoDup dom by apply dom_no_dup.
    iInduction dom as [|h' dom] "IH".
    { rewrite elem_of_nil in Hdom. done. }
    apply NoDup_ListNoDup in Hnodup.
    apply NoDup_cons_iff in Hnodup as [Hnotin Hnodup].
    simpl.
    iDestruct "Hpath" as "[Hh' Hpath]".
    rewrite elem_of_cons in Hdom.
    destruct Hdom as [-> | Hdom].
    - iClear "IH".
      rewrite decide_True; [|done].
      iCombine "Hfrag Hh'" as "Hh'".
      iMod (map_update h' old (<[key:=value]> old) with "Hctx Hh'") as "[Hctx Hh']".
      iModIntro.
      rewrite decide_True; [|done].
      iDestruct "Hh'" as "[Hh' Hfrag]".
      iFrame.
      iApply (big_sepL_mono with "Hpath").
      iIntros (i y Hy) "Hy".
      destruct (decide (y = h')) as [Heq|Hneq].
      {
        subst y.
        exfalso.
        apply Hnotin.
        apply list_elem_of_lookup_2 in Hy.
        rewrite list_elem_of_In in Hy.
        exact Hy.
      }
      iFrame.
    - rewrite decide_False.
      2: {
        intro Heq.
        subst h'.
        rewrite list_elem_of_In in Hdom.
        exact (Hnotin Hdom).
      }
      subst h.
      apply NoDup_ListNoDup in Hnodup.
      iSpecialize ("IH" $! Hdom Hdom Hnodup with "Hctx Hfrag Hpath").
      iMod "IH" as "x"; iNamed "x".
      iModIntro.
      iFrame.
      rewrite decide_False; [iFrame|].
      intros ->.
      rewrite -list_elem_of_In in Hnotin.
      apply Hnotin.
      exact Hdom.
  Qed.

  Lemma hm_lookup {h path γ m hm q sub} :
    h ∈ path_to_domain path →
    "Hmap_state" ∷ map_state γ m hm -∗
    "Hown_path" ∷ own_path γ q path (Singleton h sub) -∗
    ⌜hm !! h = Some sub⌝.
  Proof.
    iIntros (Hdom) "Hmap_state Hown_path".
    iNamed "Hmap_state".
    iNamed "Hmap_state".
    iDestruct (own_path_lookup h _ _ _ _ Hdom with "Hown_path") as "[Hptsto _]".
    iDestruct (map_valid with "Hauth_map Hptsto") as %Hlookup.
    done.
  Qed.

  Lemma entry_lookup {γ q k v m hm} :
    "Hmap_state" ∷ map_state γ m hm -∗
    "Hentry" ∷ own_entry γ q k v -∗
    ⌜m !! k = Some v⌝.
  Proof.
    iIntros "Hmap_state Hentry".
    iNamed "Hmap_state".
    iNamed "Hmap_state".
    unfold own_entry, own_ht_map.
    iDestruct (map_valid with "Huser_map Hentry") as %Hlookup.
    done.
  Qed.

  Lemma user_map_lookup {h path γ m hm q k sub} :
    h ∈ path_to_domain path →
    h = uint.Z (hash_key k) →
    "Hmap_state" ∷ map_state γ m hm -∗
    "Hown_path" ∷ own_path γ q path (Singleton h sub) -∗
    ⌜m !! k = sub !! k⌝.
  Proof.
    iIntros (Hdom Hh) "Hmap_state Hown_path".
    iDestruct (hm_lookup Hdom with "Hmap_state Hown_path") as %Hhm.
    iNamed "Hmap_state".
    iNamed "Hmap_state".
    rewrite Hflat.
    iPureIntro.
    apply (Hbuckets h sub k); auto.
  Qed.

  Lemma map_state_agree {γ m m2 hm} :
    "Hmap_state" ∷ map_state γ m hm -∗
    "Huser_map2" ∷ own_ht_map γ m2 -∗
    ⌜m = m2⌝.
  Proof.
    iIntros "Hmap_state Huser_map2".
    iNamed "Hmap_state".
    iNamed "Hmap_state".
    iDestruct (map_ctx_agree with "Huser_map Huser_map2") as %Hx.
    done.
  Qed.

  Lemma own_ht_map_agree {γ m m2} :
    "map1" ∷ own_ht_map γ m -∗
    "map2" ∷ own_ht_map γ m2 -∗
    ⌜m = m2⌝.
  Proof.
    iIntros.
    iNamed.
    unfold own_ht_map in *.
    iDestruct (map_ctx_agree with "map1 map2") as %[].
    done.
  Qed.

  Lemma map_state_bucket_of_path {h path γ m hm q sub} :
    h ∈ path_to_domain path →
    "Hmap_state" ∷ map_state γ m hm -∗
    "Hown_path" ∷ own_path γ q path (Singleton h sub) -∗
    ⌜sub = bucket_of_map m h⌝.
  Proof.
    iIntros (Hdom) "Hmap_state Hown_path".
    iDestruct (hm_lookup Hdom with "Hmap_state Hown_path") as %Hhm.
    iNamed "Hmap_state".
    iNamed "Hmap_state".
    iPureIntro.
    have Hhm_sub : hm !! h = Some sub.
    { exact Hhm. }
    apply map_eq; intro k.
    destruct (decide (uint.Z (hash_key k) = h)) as [Hhash|Hhash].
    - destruct (m !! k) as [v|] eqn:Hmk.
      + have Hsub : sub !! k = Some v.
        {
          rewrite <- (Hbuckets h sub k Hhm_sub Hhash).
          rewrite <- Hflat.
          exact Hmk.
        }
        rewrite Hsub.
        symmetry.
        apply map_lookup_filter_Some.
        split; [exact Hmk|exact Hhash].
      + have Hsub : sub !! k = None.
        {
          rewrite <- (Hbuckets h sub k Hhm_sub Hhash).
          rewrite <- Hflat.
          exact Hmk.
        }
        rewrite Hsub.
        symmetry.
        apply map_lookup_filter_None.
        left.
        exact Hmk.
    - rewrite /bucket_of_map.
      destruct (sub !! k) as [v|] eqn:Hsub; last first.
      { symmetry.
        apply map_lookup_filter_None.
        right.
        intros x Hmx Hpred.
        apply Hhash.
        exact Hpred.
      }
      exfalso.
      apply Hhash.
      eapply Hbuckets_rev; eauto using Hhm_sub.
  Qed.

  Lemma own_hash_history_current_eq_from_snapshot
    (γhist : hash_names) hist ver mcur mver :
    ("#Hhist_lb" ∷ mono_list_lb_own γhist.(hh_hist_name) hist ∗
    "#Hidx" ∷ mono_list_idx_own γhist.(hh_hist_name) ver mver ∗
    "%Hcur" ∷ ⌜hist !! map_current_version hist = Some mcur⌝ ∗
    "%Hver_eq" ∷ ⌜map_current_version hist = ver⌝) -∗
    ⌜mcur = mver⌝.
  Proof.
    iIntros "x"; iNamed "x".
    have Hlt : (ver < length hist)%nat.
    {
      rewrite -Hver_eq /map_current_version.
      destruct hist as [|x hist']; first done.
      simpl. lia.
    }
    iDestruct (mono_list_lb_idx_lookup with "Hhist_lb Hidx") as %Hlookup; first exact Hlt.
    iPureIntro.
    rewrite Hver_eq in Hcur.
    congruence.
  Qed.

  Lemma map_state_insert
    {γ path hm user_map user_map2 h old} key value
    (Hhash : h = uint.Z (hash_key key))
    (Hnone : user_map !! key = None)
    (Hbelongs : belongs_to_path path h) :
    let um' := <[key:=value]> user_map in
    let hm' := <[h := <[key:=value]> old]> hm in
    "Hmap" ∷ map_state γ user_map hm ∗
    "Huser_map2" ∷ own_ht_map γ user_map2 ∗
    "Hfrag" ∷ h [[γ.(map_name)]]↦{1 / 2} old ∗
    "Hpath" ∷ own_path γ 1 path (Singleton h old) ==∗
    "Hmap" ∷ map_state γ um' hm' ∗
    "Huser_map2" ∷ own_ht_map γ um' ∗
    "Hfrag" ∷ h [[γ.(map_name)]]↦{1 / 2} (<[key:=value]> old) ∗
    "Hpath" ∷ own_path γ 1 path (Singleton h (<[key:=value]> old)) ∗
    "Hentry" ∷ own_entry γ 1 key value.
  Proof.
    intros um' hm'.
    iIntros "x".
    iNamed "x".
    iNamed "Hmap".
    unfold own_ht_map.
    have Hdom : h ∈ path_to_domain path by rewrite -in_domain.
    iDestruct (own_path_lookup h _ _ _ _ Hdom with "Hpath") as "[Hptsto Hptsto_close]".
    iDestruct (map_valid with "Hauth_map Hptsto") as %Hlookup.
    iDestruct ("Hptsto_close" with "Hptsto") as "Hpath".
    iDestruct (map_ctx_agree with "Huser_map Huser_map2") as %Hagree.
    subst user_map2.
    iCombine "Huser_map Huser_map2" as "Huser_map".
    iMod (map_alloc key value Hnone with "Huser_map") as "[Huser_map Hentry]".
    iDestruct "Huser_map" as "[Huser_map Huser_map2]".
    subst h.
    iMod (own_path_update_key key value with "[$Hauth_map $Hfrag $Hpath]") as "x"; [lia|exact Hbelongs|]; iNamed "x".
    set (h := uint.Z (hash_key key)) in *.
    iNamed.
    assert (Hum' : (um' = flatten hm')).
    {
      subst um' hm'.
      symmetry.
      subst user_map.
      apply (flatten_update_update hm h key value old).
      - exact Hlookup.
      - reflexivity.
      - intros.
        eapply Hbuckets_rev.
        + exact H.
        + exact H0.
    }
    iModIntro.
    unfold map_state.
    iFrame "Huser_map2 Hentry".
    iFrame "Hctx Huser_map".
    iSplitR "Hpath Hfrag"; [|iFrame].
    iFrame.
    iPureIntro.
    split_and!.
    - done.
    - intros h0 sub k Hhm' Hhash0.
      rewrite -Hum'.
      subst um' hm'.
      destruct (decide (h0 = h)) as [->|Hneq].
      + rewrite lookup_insert in Hhm'.
        rewrite decide_True in Hhm'; [|reflexivity].
        inversion Hhm'; subst sub; clear Hhm'.
        destruct (decide (k = key)) as [->|Hk].
        * rewrite lookup_insert. rewrite lookup_insert.
          rewrite decide_True; [|reflexivity].
          rewrite decide_True; [|reflexivity].
          done.
        * rewrite lookup_insert_ne; [|done].
          have Hnone_k : user_map !! k = old !! k.
          {
            rewrite Hflat.
            apply (Hbuckets h); auto.
          }
          rewrite Hnone_k.
          rewrite lookup_insert_ne; [|done].
          done.
      + rewrite lookup_insert_ne in Hhm'; [|done].
        subst h h0.
        rewrite lookup_insert_ne; [|congruence].
        rewrite Hflat.
        eapply Hbuckets; eauto.
    - subst hm'. simpl in *.
      intros.
      destruct (decide (h0 = h)) as [->|Hneq].
      + rewrite lookup_insert in H.
        rewrite decide_True in H; [|done].
        assert (sub = (<[key:=value]> old)) by (inversion H; reflexivity); subst sub.
        destruct (decide (k = key)) as [->|Hk].
        * done.
        * rewrite lookup_insert_ne in H0; [|done].
          apply (Hbuckets_rev h old k v); auto.
      + rewrite lookup_insert_ne in H; [|done].
        eapply Hbuckets_rev; eauto.
  Qed.

  Lemma own_path_frag_agree {γ m h q1 q2 path x} :
    h ∈ path_to_domain path →
    own_path γ q1 path (Singleton h m) -∗ h [[γ.(map_name)]]↦{q2} x -∗ ⌜m = x⌝.
  Proof.
    iIntros "%Hbelong Hmap Hfrag".
    unfold own_path.
    unfold own_domain.
    iDestruct (big_sepL_elem_of_acc with "Hmap") as "[H1 H2]"; [exact Hbelong|].
    iEval (rewrite decide_True) in "H1".
    iDestruct (ptsto_agree with "H1 Hfrag") as %[].
    done.
  Qed.

  Lemma own_path_valid {γ m m2 hm h q path key x} :
    h ∈ path_to_domain path →
    m !! key = x →
    map_state γ m hm -∗
    own_path γ q path (Singleton h m2) -∗
    ⌜m2 !! key = x⌝.
  Proof. Admitted.

  Lemma and_test {γ linfo Φ k} :

  Lemma and_test {γ linfo Φ k} :
    (|={⊤∖↑lookupEscrowN,∅}=> ∃ m, own_ht_map γ m ∗
                                  (own_ht_map γ m ={∅,⊤∖↑lookupEscrowN}=∗ Φ (ht_load_ret m k))) -∗
    ((|={⊤∖↑lookupEscrowN,∅}=> ∃ m, own_ht_map γ m ∗
                                  (own_ht_map γ m ={∅,⊤∖↑lookupEscrowN}=∗ Φ (ht_load_ret m k)))
     ∧ (|={⊤ ∖ ↑lookupEscrowN, ∅}=> token linfo.(lookup_done_name))).
  Proof.
    iIntros "HP".
    iSplit.
    - iFrame.
    - Search big_sepM.
      Search "fupd".
      iMod (fupd_mask_subseteq _) as "Hmask".
      2: iMod "HP" as (m) "(Hmap & Htoken)".
      1: set_solver.
      iMod ("Htoken" with "Hmap") as "Htoken".
      iMod "Hmask" as "_".
      iApply fupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iModIntro.

  Lemma auth_map_delete_big {γ m} m2 :
    m2 ⊆ m →
    map_ctx γ 1 m -∗
    ([∗ map] k↦v ∈ m, ptsto_mut γ k 1 v) ==∗
    (
      map_ctx γ 1 (m ∖ m2) ∗
      ([∗ map] k↦v ∈ (m ∖ m2), ptsto_mut γ k 1 v)
    ).
  Proof.
    iIntros (Hsub) "Hctx Hpts".
    iInduction m2 as [|k v] "IH" using map_ind.
    - replace (m ∖ ∅) with m by (symmetry; apply map_difference_empty).
      iFrame.
      iModIntro.
      done.
    - assert (<[k:=v]> m0 !! k = Some v) as Hlookup.
      {
        rewrite lookup_insert.
        rewrite decide_True; [done|reflexivity].
      }
      pose proof (insert_delete_subseteq m0 m k _ H Hsub) as H1.
      rewrite -delete_difference.
      pose proof (delete_subseteq (<[k:=v]> m0) k) as H2.
      rewrite delete_insert_eq in H2.
      pose proof (delete_id m0 k H) as H3.
      rewrite H3 in H2.
      assert (m0 ⊆ m) as Hsub'.
      { transitivity (<[k:=v]> m0); done. }
      assert (m !! k = Some v) as Hlookup2.
      {
        specialize (Hsub k).
        cbn in Hsub.
        rewrite Hlookup in Hsub.
        cbn in Hsub.
        destruct (m !! k); [subst n; reflexivity|done].
      }
      iMod ("IH" $! Hsub' with "Hctx Hpts") as "[Hctx Hpts]".
      iDestruct (big_sepM_delete _ _ k with "Hpts") as "[Hk Hpts]".
      {
        rewrite lookup_difference_Some.
        done.
      }
      iMod (auth_map.map_delete with "Hk Hctx") as "Hctx".
      iFrame.
      iModIntro.
      done.
  Qed.

  Lemma map_state_version_insert
    {γ path hm user_map user_map2 h old γh idxs} key value
    (Hhash : h = uint.Z (hash_key key))
    (Hnone : user_map !! key = None)
    (Hbelongs : belongs_to_path path h) :
    let new := <[key:=value]> old in
    let um' := <[key:=value]> user_map in
    let hm' := <[h := new]> hm in
    let idxs' := ((<[key:=0%nat]>) ((λ v, (v + 1)%nat) <$> idxs)) in
    "lc" ∷ £ 1 ∗
    "Hmap" ∷ map_state γ user_map hm ∗
    "Huser_map2" ∷ own_ht_map γ user_map2 ∗
    "Hpath" ∷ own_path γ 1 path (Singleton h old) ∗
    "#Hhist" ∷ own_hash_history γ h γh ∗
    "Hidxs_auth2" ∷ map_ctx γh.(hh_idxs_name) (1/2) idxs
    ={⊤}=∗
    "Hmap" ∷ map_state γ um' hm' ∗
    "Huser_map2" ∷ own_ht_map γ um' ∗
    "Hpath" ∷ own_path γ 1 path (Singleton h new) ∗
    "#Hhist" ∷ own_hash_history γ h γh ∗
    "Hentry" ∷ own_entry γ 1 key value ∗
    "Hidxs_auth2" ∷ map_ctx γh.(hh_idxs_name) (1/2) idxs'.
  Proof.
    intros new um' hm' idxs'.
    iIntros "x"; iNamed "x".
    iInv "Hhist" as "H" "Hclose".
    iMod (lc_fupd_elim_later with "lc H") as "H"; iNamed "H".
    assert (h ∈ path_to_domain path) as Hin.
    { rewrite -in_domain; done. }
    iDestruct (own_path_frag_agree Hin with "Hpath Hhash") as %<-.
    iDestruct (mono_list_lb_own_get with "Hown_hist") as "#Hhist_lb".
    iDestruct (mono_list_idx_own_get with "Hhist_lb") as "#Hver"; [exact Hcur|].
    iDestruct (own_path_valid Hin Hnone with "Hmap Hpath") as %Hold_none.
    iMod (map_state_insert key value Hhash Hnone Hbelongs with "[$Hmap $Huser_map2 $Hhash $Hpath]")
      as "x"; iNamed "x".
    iMod (mono_list_auth_own_update (hist ++ [<[key:=value]> old]) with "Hown_hist") as "[Hown_hist #Hlb]".
    { apply prefix_app_r; auto. }

    iDestruct (map_ctx_agree with "Hidxs_auth Hidxs_auth2") as %->.
    iCombine "Hidxs_auth Hidxs_auth2" as "Hidxs_auth".
    iMod (auth_map_delete_big idxs with "Hidxs_auth Hidxs") as "[Hidxs_auth Hidxs]"; [set_solver|].
    replace (idxs ∖ idxs) with (∅ : gmap K nat) by (rewrite map_difference_diag; reflexivity).
    iClear "Hidxs".
    iMod (map_alloc_many idxs' with "Hidxs_auth") as "[Hidxs_auth Hidxs]".
    {
      intros k Hlookup.
      rewrite lookup_empty.
      done.
    }
    replace (idxs' ∪ ∅) with idxs' by (rewrite map_union_empty; reflexivity).
    iDestruct ("Hidxs_auth") as "[Hidxs_auth Hidxs_auth2]".

    assert (idxs !! key = None) as Hidxs_none.
    {
      apply not_elem_of_dom_2 in Hold_none.
      apply not_elem_of_dom.
      rewrite Hidxs_dom.
      exact Hold_none.
    }

    Search "fupd".

    iCombine "Huser_map2 Hlookups" as "Hlookups".

    iMod (big_sepM_mono_fupd (K:=nat)
                             _
            (λ (k: nat) linfo,
              ⌜linfo.(lookup_version) <
                length (hist ++ [<[key:=value]> old])⌝ ∗
              ∃ status : lookup_status,
                ⌜linfo.(lookup_version) < length (hist ++ [<[key:=value]> old]) - 1
                → status ≠ LookupPending⌝ ∗
                lookup_status_interp γ linfo status γh idxs
            )%I
           with "[] [Hlookups]") as "[Huser_map2 Hlookups]".
    2: iFrame.
    {
      iModIntro.
      iIntros (k x lk) "(map & %a & %st & %b & c)".
      unfold lookup_status_interp.
      rewrite length_app.
      rewrite singleton_length.
      replace ((length hist + 1)%nat - 1) with (Z.of_nat (length hist)) by lia.
      replace (Z.of_nat (length hist + 1)%nat) with (length hist + 1) by lia.
      destruct st.
      - iMod (fupd_mask_subseteq _) as "Hmask".
        2: iMod "c" as "(%m & x & [y z])".
        { admit. }
        iDestruct (own_ht_map_agree with "map x") as %->.
        iMod ("z" with "x") as "z".
        iMod "Hmask" as "_".
        iApply fupd_mask_intro; [set_solver|].
        iIntros.
        iFrame.
        iSplit; first (iPureIntro; lia).
        iExists LookupDone.
        iSplitR; first done.
        iFrame.
      - iApply fupd_mask_intro; [set_solver|].
        iIntros.
        iFrame.
        iSplit; first (iPureIntro; lia).
        iExists LookupDone.
        iSplitR; first done.
        iFrame.
      - iApply fupd_mask_intro; [set_solver|].
        iIntros.
        iFrame.
        iSplit; first (iPureIntro; lia).
        iExists LookupConsumed.
        iSplitR; first done.
        iFrame.
    }

    iFrame "Hmap Huser_map2 Hpath Hentry Hhist".
    iDestruct

    iAssert (
        ([∗ map] linfo ∈ lookups,
           |={⊤ ∖ ↑lookupInterpN}=>
           ⌜linfo.(lookup_version) <
             length (hist ++ [<[key:=value]> old])⌝ ∗
           ∃ status : lookup_status,
             ⌜linfo.(lookup_version) < length (hist ++ [<[key:=value]> old]) - 1
             → status ≠ LookupPending⌝ ∗
             lookup_status_interp γ linfo status γh)
      )%I with "[Hlookups]" as "Hlookups".
    {
      iDestruct (big_sepM_mono_with_inv with "Hver Hlookups") as "[_ $]".
      unfold lookup_status_interp.
      iIntros (k x lk) "(#i & %a & %st & %b & c)".
      rewrite length_app.
      rewrite singleton_length.
      replace ((length hist + 1)%nat - 1) with (Z.of_nat (length hist)) by lia.
      replace (Z.of_nat (length hist + 1)%nat) with (length hist + 1) by lia.
      iFrame "i".
      destruct st.
      - iMod (fupd_mask_subseteq _) as "Hmask".
        2: iMod "c" as "(%m & x & [y z])".
        { admit. }
        iMod ("z" with "x") as "z".
        iMod "Hmask" as "_".
        iApply fupd_mask_intro; [set_solver|].
        iIntros.
        iSplit; first (iPureIntro; lia).
        iExists LookupDone.
        iSplitR; first done.
        iFrame.
      - iApply fupd_mask_intro; [set_solver|].
        iIntros.
        iSplit; first (iPureIntro; lia).
        iExists LookupDone.
        iSplitR; first done.
        iFrame.
      - iApply fupd_mask_intro; [set_solver|].
        iIntros.
        iSplit; first (iPureIntro; lia).
        iExists LookupConsumed.
        iSplitR; first done.
        iFrame.
    }
    iMod (big_sepM_fupd with "Hlookups") as "Hlookups".
    iMod ("Hclose" with "[Hown_lookups Hlookups Hfrag Hown_hist]").
    2: done.
    iNext.
    iExists _, lookups, new.
    iFrame.
    iFrame "#".
    iPureIntro.
    unfold map_current_version.
    rewrite length_app.
    rewrite singleton_length.
    replace (Init.Nat.pred (length hist + 1)) with (length hist) by lia.
    rewrite lookup_app_Some.
    right.
    split; [lia|].
    replace (length hist - length hist)%nat with 0%nat by lia.
    rewrite list_lookup_singleton.
    reflexivity.
  Admitted.

  Lemma map_state_register_lookup {γ m hm (* E *) h γhist Φ}
    (key : K) :
    (* (ht_au_mask ⊆ E) → *)
    h = uint.Z (hash_key key) →
    "lc" ∷ £ 1 -∗
    "Hmap" ∷ map_state γ m hm -∗
    "Hhist" ∷ own_hash_history γ h γhist -∗
    "Hpending" ∷ (
        (AU <{ ∃∃ m : gmap K V, own_ht_map γ m }>
           @ ht_au_mask, ∅
                         <{ own_ht_map γ m, COMM Φ (ht_load_ret m key) }>)
      )
    ={⊤}=∗
    ∃ id ver,
      "Hmap" ∷ map_state γ m hm ∗
      "#Hhist_name" ∷ ptsto_ro γ.(histories_name) h γhist ∗
      "Hhist" ∷ own_hash_history γ h γhist ∗
      "Htok" ∷ lookup_token γ id ver key.
  Proof.
    iIntros.
    iNamed.
    iInv "Hhist" as "H" "Hclose".
    iMod (lc_fupd_elim_later with "lc H") as "H"; iNamed "H".
    set (ver := map_current_version hist) in *.
    have Hver_lt : (ver < length hist)%nat.
    {
      rewrite /ver /map_current_version.
      apply Nat.lt_pred_l.
      intros x; apply nil_length_inv in x; subst hist.
      rewrite lookup_nil in Hcur.
      apply None_ne_Some in Hcur.
      done.
    }
    iDestruct (mono_list_lb_own_get with "Hown_hist") as "#Hhist_lb".
    iDestruct (mono_list_idx_own_get with "Hhist_lb") as "#Hver"; first exact Hcur.
    set (id := fresh (dom lookups)).
    have Hid_fresh : lookups !! id = None.
    { apply not_elem_of_dom. apply is_fresh. }
    (* iMod "Hpending". *)
    (* iDestruct "Hpending" as (x) "[Hown_map [_ Hpending_close]]". *)
    iNamed "Hmap".
    (* iDestruct (map_ctx_agree with "Huser_map Hown_map") as %->. *)
    iMod (alloc_lookup_help_token (Φ (ht_load_ret m key))) as "x"; iNamed "x".
    (* iApply fupd_mask_intro. *)

    iMod (token_alloc) as (γconsumed) "consumed_token".

    iMod (map_alloc id (mkLookupInfo ver γdone γconsumed) Hid_fresh with "Hown_lookups")
      as "[Hown_lookups Hlookup_info]".

    iMod ("Hclose" with "[Hhash Hown_hist Hown_lookups Hlookups Hpending HP_to_tok]") as "_".
    {
      iNext.
      iFrame "#".
      iExists hist, (<[id:={|
                              lookup_version := ver;
                              lookup_done_name := γdone;
                              lookup_consumed_name := γconsumed
                            |}]>
                       lookups), map.
      rewrite /named.
      iDestruct (big_sepM_insert with "Hlookups") as "Hlookups".
      iSplitR.
      { iPureIntro; intros. auto. }
      { exact Hid_fresh. }
      simpl.
      iFrame.
      iSplitR; [iPureIntro; lia|].
      iExists LookupPending.
      iSplitR.
      { iPureIntro; intros. rewrite /ver /map_current_version in H0. lia. }
      unfold lookup_status_interp.
      simpl.
      iIntros.
      iMod "Hpending" as (x) "[map [_ cont]]".
      { admit. }
      iApply fupd_mask_intro; [set_solver|].
      iIntros "Hmask".
      iFrame "map".
      iIntros "map".
      iMod "Hmask" as "_".
      iMod ("cont" with "map") as "Hcont".
      iMod (fupd_mask_subseteq _) as "Hmask".
      2: iMod ("HP_to_tok" with "[Hcont]") as "done_tok".
      { admit. }
      - iNext.
        iFrame.

    }

    iMod ("Hclose" with "[]") as "_".

    iMod "Hpending" as (x) "[map [_ cont]]".
    iDestruct (map_ctx_agree with "map Huser_map") as %->.
    iMod ("cont" with "map") as "Hcont".
    iMod (fupd_mask_subseteq _) as "Hmask".
    2: iMod ("HP_to_tok" with "Hcont") as "done_tok".
    1: set_solver.
    iMod "Hmask" as "_".

    set (linfo := {|
                   lookup_key := key;
                   lookup_version := ver;
                   lookup_done_name := γdone;
                   lookup_consumed_name :=
                     γconsumed
                 |}) in *.

    iMod (inv_alloc lookupInterpN _ (
              ∃ (status : lookup_status) (mver : gmap K V),
                    mono_list_idx_own γhist.(hh_hist_name)
                      linfo.(lookup_version) mver ∗
                    ⌜linfo.(lookup_version) < length hist - 1
                     → status ≠ LookupPending⌝ ∗
                    lookup_status_interp γ linfo status mver
            ) with "[done_tok]") as "Hnew_inv".
    {
      iNext.
      iExists LookupPending, m.
      rewrite /ver /map_current_version.
      replace (Z.of_nat (Init.Nat.pred (length hist))) with (length hist - 1) by lia.
      iFrame "#".
      iSplitR; [iPureIntro; intros; subst linfo; simpl in *; subst ver; rewrite /map_current_version in H0; lia|].
      unfold lookup_status_interp.
      simpl.
      iMod "Hpending" as (x) "[map [_ cont]]".
      iApply fupd_mask_intro; [apply empty_subseteq|].
      iIntros "Hmask".
      iFrame.
      iIntros "Hown".
      iSpecialize ("cont" with "Hown").
      iMod "cont".
      iMod (fupd_mask_subseteq _).
      2: {
        iSpecialize ("HP_to_tok" with "[cont]").
        iMod ("HP_to_tok" with "[cont]") as "tok".

      }
      iModIntro.
      iMod "Hpending_close".
      iSpecialize ("HP_to_tok" with "Hpending_close").
      iMod (fupd_mask_subseteq _) as "Hmask2".
      2: {
        iMod "HP_to_tok".
        iFrame.
        iMod "Hmask2" as "_".
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros.
        done.
      }
      set_solver.
    }

    (* iMod ("Hpending_close" with "Hown_map") as "Hpending". *)
    (* iSpecialize ("HP_to_tok" with "Hpending"). *)
    (* iDestruct "Hlookup_info" as "[Hlookup_hist Hlookup_tok]". *)

    iModIntro.
    iFrame.
    iFrame "#".
    iSplitR.
    { iPureIntro; split_and!; done. }

    iSplitL; [|done].
    iSplitR; [done|].
    iApply big_sepM_insert; [exact Hid_fresh|].
    iFrame.
    simpl.
    iSplitR; [iPureIntro; lia|].
    iFrame "Hlookups".

    iMod (inv_alloc lookupInterpN _ (lookup_status_interp γ (mkLookupInfo key ver γdone) LookupPending)
           with "Hpending") as "#Hlookup_inv".
    iModIntro.
    iExists id, ver.
    iFrame "Hmap".
    iFrame "#".
    iFrame.
    iSplitL; last done.
    iSplitR; first done.
    rewrite big_sepM_insert; [|exact Hid_fresh].
    iFrame.
    iExists LookupPending.
    simpl.
    iFrame "#".
    iSplit.
    - iPureIntro. lia.
    - iPureIntro. intros Hlt_old.
      rewrite /ver /map_current_version in Hlt_old.
      lia.
  Qed.

  Lemma lookup_token_status_acc {γ id ver key h γhist sub} :
    h = uint.Z (hash_key key) →
    "Htok" ∷ lookup_token γ id ver key -∗
    "Hhist" ∷ own_hash_history γ γhist h 1 sub -∗
    "Hhist" ∷ own_hash_history γ γhist h 1 sub ∗
    "Htok" ∷ lookup_token γ id ver key ∗
    ∃ info status,
      ⌜info.(lookup_key) = key⌝ ∗
      ⌜info.(lookup_version) = ver⌝ ∗
      "#Hlookup_inv" ∷ inv lookupInterpN (lookup_status_interp γ info status).
  Proof.
    iIntros (Hh) "Htok Hhist".
    iNamed "Htok".
    iNamedSuffix "Htok" "0".
    iNamed "Hhist".
    iNamedSuffix "Hhist" "1".
    rewrite -Hhash0 in Hh.
    assert (h0 = h) as -> by lia.
    iDestruct (ptsto_ro_agree with "Hhist_name0 Hhist_name1") as %->.
    iDestruct (map_valid with "Hown_lookups1 Hlookup_info0") as %Hlookup.
    iDestruct (big_sepM_lookup_acc with "Hlookups1")
      as "[[Hentry #Hr] Hlookups]"; first exact Hlookup.
    iSpecialize ("Hlookups" with "[$Hentry $Hr]").
    iFrame.
    iFrame "#".
    rewrite Hhash0 in Hh.
    iSplit; first done.
    iSplit; first done.
    iDestruct "Hr" as (status) "(%Ha & %Hb & #Hc)".
    iFrame "#".
    iSplit; done.
  Qed.

  #[global] Opaque map_state.

End model.
