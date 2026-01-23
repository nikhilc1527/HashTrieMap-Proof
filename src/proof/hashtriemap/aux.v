(* Things that should be in perennial but arent supported yet *)

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
From iris.base_logic.lib Require Import invariants.
From stdpp Require Import gmap list fin_maps.
From Coq Require Import List.
Import ListNotations.
Open Scope Z_scope.

(* From Perennial.goose_lang.lib Require Export atomic.impl. *)

Section aux.
  Context `{hG: heapGS Σ, !invGS Σ, !ffi_semantics _ _}
    `{!globalsGS Σ} {go_ctx: GoContext}.

  (* Parameter atomic_value_model : atomic.Value.t → option loc → Prop. *)

  (* go std library potential problem: atomic value doesnt have a nocopy embedded in it because it is older than the atomic integer types (that have the nocopy embedded) *)
  Definition own_Value (u : loc) dq (v : interface.t) : iProp Σ :=
    u ↦{dq} atomic.Value.mk v.

  Notation "l ↦ᵥ{ dq } v" := (own_Value l dq v)
    (at level 20, format "l  ↦ᵥ{ dq }  v").

  Lemma Value_unfold l dq (v : interface.t) :
    own_Value l dq v ⊣⊢
    l ↦s[atomic.Value :: "v"]{dq} v.
  Proof.
    iSplit.
    - iIntros "H".
      iApply struct_fields_split in "H". iNamed "H".
      iFrame.
    - iIntros "Hv".
      iApply @struct_fields_combine.
      iFrame "Hv".
  Qed.

  (* Using in place of perennial's, since perennial doesnt have std library proofs for atomic Values yet *)
  Lemma wp_Value__Store u v :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Value u (DfracOwn 1) old ∗ (own_Value u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
    WP u @ (ptrT.id atomic.Value.id) @ "Store" #v {{ Φ }}.
  Proof.
  Admitted.

  Lemma wp_Value__Load u dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v, own_Value u dq v ∗ (own_Value u dq v ={∅,⊤}=∗ Φ #v)) -∗
    WP u @ (ptrT.id atomic.Value.id) @ "Load" #() {{ Φ }}.
  Proof.
  Admitted.

  (* #[global] Instance LoadUint32_Atomic (l:loc) : Atomic StronglyAtomic (atomic.LoadUint32 #l). *)
  (* Proof. apply _. Qed. *)

  (* theres probably already something for this but i couldnt find it *)
  Lemma own_slice_len_keep `{!IntoVal V} `{!IntoValTyped V t} (s: slice.t) dq (vs: list V) :
    s ↦*{dq} vs -∗ s ↦*{dq} vs ∗
                         ⌜length vs = sint.nat s.(slice.len_f) ∧ 0 ≤ sint.Z s.(slice.len_f)⌝.
  Proof.
    iIntros "Hs".
    rewrite own_slice_unseal.
    iDestruct "Hs" as "[Hs %Hlen]".
    iFrame "Hs".
    iPureIntro.
    split; word.
  Qed.
  
End aux.
