(* Things that should be in perennial but arent supported yet *)

From iris.bi.lib Require Import fractional.

From New.generatedproof.hashtriemap Require Import hashtriemap.
From New.proof Require Import sync.
From New.proof.sync Require Import atomic.
From New.proof.sync_proof Require Import mutex.
From Perennial.algebra Require Import auth_map.
From New.ghost Require Import ghost_var.
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
  Context `{hG: heapGS Σ, !ffi_semantics _ _}.
  Context {sem: go.Semantics}.

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
  Context `{hG: heapGS Σ, !ffi_semantics _ _}.
  Context {sem : go.Semantics}.

  Implicit Types l : loc.
  Implicit Types u : loc.
  Implicit Types v : interface.t.

  Global Instance own_Value_fractional u v : Fractional (λ q, u ↦ᵥ{q} v).
  Proof. apply fractional_of_dfractional. apply _. Qed.
  Global Instance own_Value_as_fractional u q v :
    AsFractional (u ↦ᵥ{q} v) (λ q, u↦ᵥ{q} v) q := _.

  Global Instance own_Value_combines_gives u v v' dq dq' :
    CombineSepGives (own_Value u dq v) (own_Value u dq' v') (⌜ v = v'⌝).
  Proof.
    unfold CombineSepGives.
    iIntros "?". iDestruct (combine_sep_gives with "[$]") as "H".
    iDestruct "H" as %?. iModIntro. iPureIntro.
    assert (v = v') by congruence.
    done.
  Qed.

  Lemma wp_Value__Load u dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v, u ↦ᵥ{dq} v ∗ (u ↦ᵥ{dq} v ={∅,⊤}=∗ Φ #v)) -∗
    WP u @! (go.PointerType atomic.Value) @! "Load" #() {{ Φ }}.
  Proof.
  Admitted.

  Lemma wp_Value__Store u v :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, u ↦ᵥ{1} old ∗ (u ↦ᵥ{1} v ={∅,⊤}=∗ Φ #())) -∗
    WP u @! (go.PointerType atomic.Value) @! "Store" #v {{ Φ }}.
  Proof.
  Admitted.

End aux.
