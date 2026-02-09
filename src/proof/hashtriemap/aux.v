(* Things that should be in perennial but arent supported yet *)

From iris.bi.lib Require Import fractional.

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
(* From Perennial.goose_lang Require Import struct. *)
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
End aux.

Notation "l ↦ᵥ{ dq } v" := (own_Value l (DfracOwn dq) v)
                             (at level 20, format "l  ↦ᵥ{ dq }  v").

Notation "l ↦ᵥ v" := (own_Value l (DfracOwn 1) v)
                             (at level 20, format "l  ↦ᵥ  v").

Section aux.
  Context `{hG: heapGS Σ, !invGS Σ, !ffi_semantics _ _}
    `{!globalsGS Σ} {go_ctx: GoContext}.

  Implicit Types l : loc.
  Implicit Types u : loc.
  Implicit Types v : interface.t.

  Lemma Value_unfold l dq v :
    l ↦ᵥ{dq} v ⊣⊢
    l ↦s[atomic.Value :: "v"]{DfracOwn dq} v.
  Proof.
    iSplit.
    - iIntros "H".
      iApply struct_fields_split in "H". iNamed "H".
      iFrame.
    - iIntros "Hv".
      iApply @struct_fields_combine.
      iFrame "Hv".
  Qed.

  Lemma own_Value_agree l dq1 dq2 v1 v2 :
    l ↦ᵥ{dq1} v1 -∗
    l ↦ᵥ{dq2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iCombine "H1 H2" gives %[? ?].
    inversion H0.
    done.
  Qed.

  Global Instance own_Uint64_fractional u v : Fractional (λ q, u ↦ᵥ{q} v) := _.
  Global Instance own_Uint64_as_fractional u q v :
    AsFractional (u ↦ᵥ{q} v) (λ q, u↦ᵥ{q} v) q := _.

  (* Using in place of perennial's, since perennial doesnt have std library proofs for atomic Values yet *)
  Lemma wp_Value__Store u v :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, u ↦ᵥ{1} old ∗ (u ↦ᵥ{1} v ={∅,⊤}=∗ Φ #())) -∗
    WP u @ (ptrT.id atomic.Value.id) @ "Store" #v {{ Φ }}.
  Proof.
  Admitted.

  Lemma wp_Value__Load u dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v, u ↦ᵥ{dq} v ∗ (u ↦ᵥ{dq} v ={∅,⊤}=∗ Φ #v)) -∗
    WP u @ (ptrT.id atomic.Value.id) @ "Load" #() {{ Φ }}.
  Proof.
  Admitted.

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
