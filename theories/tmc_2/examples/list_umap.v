From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  refinement.
From camlcert.data_human_lang Require Export
  compile.
From camlcert.data_human_lang Require Import
  notations.
From camlcert.tmc_2 Require Import
  soundness.
From camlcert Require Import
  options.

Definition list_umap : data_human_program := {[
  "list_umap" :=
    rec: "arg" :=
      let: "fn" := ![𝟙] "arg" in
      let: "xs" := ![𝟚] "arg" in
      match: "xs" with
        NIL =>
          NILₕ
      | CONS "x1", "xs" =>
          match: "xs" with
            NIL =>
              CONSₕ (DataHumanCall "fn" "x1") NILₕ
          | CONS "x2", "xs" =>
              let: "y1" := DataHumanCall "fn" "x1" in
              let: "y2" := DataHumanCall "fn" "x2" in
              CONSₕ "y1" (CONSₕ "y2" ($"list_umap" ("fn", "xs")))
          end
      end
]}%data_human_def.

Definition list_umap_tmc : data_human_program := {[
  "list_umap" :=
    rec: "arg" :=
      let: "fn" := ![𝟙] "arg" in
      let: "xs" := ![𝟚] "arg" in
      match: "xs" with
        NIL =>
          NILₕ
      | CONS "x1", "xs" =>
          match: "xs" with
            NIL =>
              CONSₕ (DataHumanCall "fn" "x1") NILₕ
          | CONS "x2", "xs" =>
              let: "y1" := DataHumanCall "fn" "x1" in
              let: "y2" := DataHumanCall "fn" "x2" in
              let: "dst" := CONSₕ "y1" #ₕ() in
              ( let: "y2" := "y2" in
                let: "dst'" := CONSₕ "y2" #ₕ() in
                "dst" <-[𝟚] "dst'" ;;
                let: "arg" := ("fn", "xs") in
                $"list_umap_dps" ("dst'", 𝟚, "arg")
              ) ;;
              "dst"
          end
      end ;
  "list_umap_dps" :=
    rec: "arg" :=
      let: "dst_idx" := ![𝟙] "arg" in
      let: "idx" := ![𝟚] "dst_idx" in
      let: "dst" := ![𝟙] "dst_idx" in
      let: "arg" := ![𝟚] "arg" in
      let: "fn" := ![𝟙] "arg" in
      let: "xs" := ![𝟚] "arg" in
      match: "xs" with
        NIL =>
          "dst" <-["idx"] NILₕ
      | CONS "x1", "xs" =>
          match: "xs" with
            NIL =>
              "dst" <-["idx"] CONSₕ (DataHumanCall "fn" "x1") NILₕ
          | CONS "x2", "xs" =>
              let: "y1" := DataHumanCall "fn" "x1" in
              let: "y2" := DataHumanCall "fn" "x2" in
              let: "y1" := "y1" in
              let: "y2" := "y2" in
              let: "dst'" := CONSₕ "y2" #ₕ() in
              "dst" <-["idx"] CONSₕ "y1" "dst'" ;;
              let: "arg" := ("fn", "xs") in
              $"list_umap_dps" ("dst'", 𝟚, "arg")
          end
      end
]}%data_human_def.

Lemma list_umap_tmc_sound :
  data_program_refinement
    (data_human_program_compile list_umap)
    (data_human_program_compile list_umap_tmc).
Proof.
  rewrite /list_umap /list_umap_tmc. apply tmc_sound.
  - split.
    + apply data_human_program_compile_well_formed.
      rewrite /data_human_program_well_formed map_Forall_singleton //.
    + apply data_human_program_compile_scoped.
  - rewrite /data_human_program_compile map_fmap_singleton fmap_insert map_fmap_singleton /=.
    exists {["list_umap" := "list_umap_dps"]}; try set_solver.
    + intros * (<- & <-)%lookup_singleton_Some.
      rewrite lookup_insert.
      eexists. split; last done. repeat econstructor; done.
    + intros * (<- & <-)%lookup_singleton_Some (_ & <-)%lookup_singleton_Some.
      eexists. split; last done. repeat econstructor; done.
Qed.
