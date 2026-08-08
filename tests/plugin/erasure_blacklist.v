From Hammer Require Import Hammer.

Inductive blkt_box : Set :=
| BlktHidden : nat -> blkt_box
| BlktVisible : blkt_box.

Definition blkt_id (x : blkt_box) : blkt_box := x.

(* Drop the ConstructRef from the search results while the IndRef passes:
   Defhash then holds blkt_box's IndType (listing BlktHidden) without the
   constructor's entry.  Translation must degrade (classify -> CRegular,
   injection/discrim/inversion skipped), not abort. *)
Add Search Blacklist "BlktHidden".
Hammer_transl "blkt_id".
Remove Search Blacklist "BlktHidden".
