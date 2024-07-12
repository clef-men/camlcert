From camlcert Require Import
  prelude.
From camlcert.iris.program_logic Require Export
  ectxi_language.
From camlcert.data_lang Require Export
  semantics.
From camlcert Require Import
  options.

Canonical data_val_O :=
  leibnizO data_val.
Canonical data_expr_O :=
  leibnizO data_expr.
Canonical data_state_O :=
  leibnizO data_state.

Lemma data_ectxi_lang_mixin :
  EctxiLanguageMixin
    data_of_val
    data_to_val
    data_head_step
    data_ectxi.
Proof.
  split.
  - apply data_to_of_val.
  - apply data_of_to_val.
  - apply data_head_step_not_val.
  - apply _.
  - apply data_ectxi_fill_not_val .
  - apply data_ectxi_fill_no_val_inj.
  - apply data_ectxi_fill_head_step_val.
Qed.
Canonical data_ectxi_lang :=
  Build_ectxi_language data_ectxi_lang_mixin.
Canonical data_ectx_lang :=
  ectx_language_of_ectxi_language data_ectxi_lang.
Canonical data_lang :=
  language_of_ectx_language data_ectx_lang.
