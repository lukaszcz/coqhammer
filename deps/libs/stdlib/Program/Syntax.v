From Hammer Require Import Hammer.












Notation " () " := Datatypes.unit : type_scope.
Notation " () " := tt.



Arguments Some {A} _.
Arguments None {A}.

Arguments pair {A B} _ _.
Arguments fst {A B} _.
Arguments snd {A B} _.

Arguments nil {A}.
Arguments cons {A} _ _.

Require List.
Export List.ListNotations.

Require Import Bvector.
