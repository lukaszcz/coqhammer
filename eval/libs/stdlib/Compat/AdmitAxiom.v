From Hammer Require Import Hammer.











Axiom proof_admitted : False.
Ltac admit := clear; abstract case proof_admitted.
