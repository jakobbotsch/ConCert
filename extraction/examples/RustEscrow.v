From ConCert.Execution.Examples Require Import Escrow.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From ConCert.Extraction Require Import Printing.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import RustExtract.
From ConCert.Utils Require Import StringExtra.
From Coq Require Import Bool.
From Coq Require Import String.
From MetaCoq.Template Require Import All.
From MetaCoq.Template Require Import Kernames.

Import MonadNotation.

Definition ESCROW_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "escrow"%string;
     concmd_init := @Escrow.init;
     concmd_receive := @Escrow.receive;
     (* Extracting the example as well *)
     concmd_extra := []; |}.

Definition null_remap : remapped_inductive :=
  {| re_ind_name := "()";
     re_ind_ctors := [];
     re_ind_match := None |}.

(* Purely remapped so that they are ignored, can be removed when inlining
   happens on template *)
Definition extra_remap_inds : list (inductive * remapped_inductive) :=
  [ (<! Monads.Monad !>, null_remap) ].

Definition extra_remap_consts : list (kername * string) :=
  [ (<! @RecordSet.SetterFromGetter !>, "") ].

Definition should_inline kn :=
  eq_kername kn <%% @Monads.bind %%>
  || eq_kername kn <%% Monads.Monad_option %%>
  || if String.index 0 "setter_from_getter" (string_of_kername kn) then true else false.

Redirect "examples/rust-extract/Escrow.rs"
MetaCoq Run (concordium_extraction
               ESCROW_MODULE
               (ConcordiumRemap.build_remaps
                  (ConcordiumRemap.remap_arith
                     ++ ConcordiumRemap.remap_blockchain_consts
                     ++ extra_remap_consts)
                  ConcordiumRemap.remap_inline_bool_ops
                  (ConcordiumRemap.remap_std_types
                     ++ ConcordiumRemap.remap_blockchain_inductives
                     ++ extra_remap_inds))
               should_inline).
