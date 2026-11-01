
From Stdlib.Array Require Import PArray.
From Stdlib Require Import Numbers.Cyclic.Int63.Uint63.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Transform.
From MetaRocq.Template Require Import Loader.
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.Erasure Require ELinearAst.

Import Common.Transform.Transform.

(* Framework *)
Program Definition erase_to_ast
    (p : Ast.Env.program) : ELinearAst.term :=
  let erased :=
    run_erase_program default_erasure_config ([], p) _ in
  ELinearAst.optimize_arrays erased.2.

Next Obligation.
  split.
  - auto.
  - split.
    + apply assume_that_we_only_erase_on_welltyped_programs.
    + cbv [PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn].
      pose proof @PCUICSN.normalization.
      split; typeclasses eauto.
Qed.

(* Basic linear test *)
MetaRocq Quote Recursively Definition basic_linear :=
  (let arr0 := make 3%int63 0 in
  let arr1 := arr0.[0 <- 2].[1 <- 3].[2 <- 5] in
  let x1 := arr1.[1] in
  let x2 := arr1.[2] in
  x1 + x2).
Definition basic_linear_ext := Eval vm_compute in erase_to_ast basic_linear.
Print basic_linear_ext.
(* OK: it indeed compiles all the operations as linear ones *)

(* No variables *)
MetaRocq Quote Recursively Definition no_variables :=
  (let x := (make 3%int63 0).[0 <- 2].[0] in x).
Definition no_variables_ext := Eval vm_compute in erase_to_ast no_variables.
Print no_variables_ext.
(* OK: the array operations are indeed compiled as mutable arrays *)

(* Not linear *)
MetaRocq Quote Recursively Definition not_linear :=
  (let arr := make 3%int63 0 in
   let arr' := arr.[2 <- 5].[1 <- 6] in
   let arr1 := arr'.[0 <- 2] in
   let arr2 := arr'.[0 <- 1] in
   arr1.[0] + arr2.[0]).
Definition not_linear_ext := Eval vm_compute in erase_to_ast not_linear.
Print not_linear_ext.
(* OK: everything is compiled as immutable arrays *)

(* Case linear *)
MetaRocq Quote Recursively Definition case_linear :=
  (let arr := (make 3%int63 0).[0 <- 5] in
   let arr' := if true then arr.[2 <- 6] else arr.[1 <- 5] in
   arr'.[0]).
Definition case_linear_ext := Eval vm_compute in erase_to_ast case_linear.
Print case_linear_ext.
(* OK: Everything compiled to mutable array *)

(* No variables case *)
MetaRocq Quote Recursively Definition no_variables_case :=
  (let x := (if true then make 3%int63 0 else make 5%int63 1).[0] in x).
Definition no_variables_case_ext := Eval vm_compute in erase_to_ast no_variables_case.
Print no_variables_case_ext.
(* OK: compiled to mutable arrays *)

(* Function cut *)
MetaRocq Quote Recursively Definition function_cut :=
  (let f := fun x => x in
   let arr := make 3%int63 0 in
   (f arr).[0]).
Definition function_cut_ext := Eval vm_compute in erase_to_ast function_cut.
Print function_cut_ext.
(* OK: compiled to immutable array, functions arguments and results are always
   assumed to be immutable arrays. *)

(* No variables immutable *)
MetaRocq Quote Recursively Definition no_variables_immutable :=
  (let f := fun x => make x 0 in
   let x := (if true then f 3%int63 else make 5%int63 1).[0] in x).
Definition no_variables_immutable_ext :=
  Eval vm_compute in erase_to_ast no_variables_immutable.
Print no_variables_immutable_ext.
(* OK: Everything compiled to immutable arrays *)

(* Misc usage *)
MetaRocq Quote Recursively Definition misc_usage :=
  (let arr := make 3%int63 0 in
   let arr' := match arr.[0] with
   | O => arr.[0 <- 3]
   | S _ => make 3%int63 3
   end in
   arr'.[0]).
Definition misc_usage_ext := Eval vm_compute in erase_to_ast misc_usage.
Print misc_usage_ext.
(* OK: everything compiled to mutable arrays *)

