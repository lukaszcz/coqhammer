From Hammer Require Import Hammer.









Require Export Notations.
Require Export Logic.
Require Export Logic_Type.
Require Export Datatypes.
Require Export Specif.
Require Coq.Init.Nat.
Require Export Peano.
Require Export Coq.Init.Wf.
Require Export Coq.Init.Tactics.
Require Export Coq.Init.Tauto.

Declare ML Module "cc_plugin".
Declare ML Module "ground_plugin".

Add Search Blacklist "_subproof" "_subterm" "Private_".
