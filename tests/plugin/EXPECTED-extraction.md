# Extraction test expected profile

This records the current (pre extraction-refactor) end-to-end `hammer` profile for
the extraction test files. Goals listed as passing are left as
`Proof. hammer. Qed.` and must keep passing in later phases. Goals listed as
failing are wrapped as `Fail hammer.` / `Abort.` until the relevant translator work
makes them pass. `extraction_matches.v` temporarily pins `Hammer Predictions` to 16
around `extraction_g_deep` through `extraction_tmirror_node`, and pins
`Hammer ATPLimit` to 0 around `extraction_rsize_nil`, to keep the current profile
reproducible with the pre-refactor translator.

## `extraction_matches.v`

### Passing now

- `extraction_myadd_succ`: `forall n m, myadd (S n) m = S (myadd n m)`
- `extraction_match_goal`: `forall n (m : nat), (match n with 0 => m | S _ => m end) = m`
- `extraction_k_true`: `k true = 1`
- `extraction_k_cases`: `forall b, k b = 0 \/ k b = 1`
- `extraction_g_one`: `g 1 = 1`
- `extraction_tsize_node`: `forall l x r, tsize (N l x r) = S (myadd (tsize l) (tsize r))`
- `extraction_tmirror_node`: two-step `tmirror` equation on `N l x r`
- `extraction_tmirror_injective`: `forall t u, tmirror t = tmirror u -> t = u`
- `extraction_list_map_cons`: stdlib `List.map` cons equation
- `extraction_nat_eqb_refl`: `Nat.eqb 5 5 = true`

### Expected failures now

- `extraction_myadd_ground`: `myadd 2 2 = 4`
- `extraction_mypred_succ`: `forall n, mypred (S n) = n`
- `extraction_mypred_nonzero`: `forall n, n <> 0 -> S (mypred n) = n`
- `extraction_g_deep`: `forall x, g (S (S x)) = x` (checked with `Set Hammer Predictions 16` to keep the expected failure deterministic)
- `extraction_is_zero_zero`: `is_zero 0`
- `extraction_is_zero_succ`: `forall n, ~ is_zero (S n)`
- `extraction_hd_d_cons`: `forall (d x : nat) l, hd_d d (cons x l) = x`
- `extraction_even_ss`: `forall n, even (S (S n)) = even n`
- `extraction_rsize_nil`: `rsize (Rose nil) = 1` (checked with `Set Hammer ATPLimit 0` to keep the expected failure deterministic)

## `extraction_deptypes.v`

### Passing now

- `no_junk`: `2 + 2 = 4` (after the `Program Fixpoint idiv` definition)
- `extraction_h_two_specs`: two instantiated `h` specs imply `a = c`
- `extraction_safe_pred_proof_irrel`: `safe_pred (S n)` result independent of proof argument
- `extraction_posnat_payload`: `forall p : posnat, 0 < pval p`
- `extraction_vhead_cons`: vector-head equation on `Vector.cons`

### Expected failures now

- `extraction_h_proj`: `forall x y z p, proj1_sig (h x y z p) = z`
- `extraction_h_spec`: `forall x y z p, x = proj1_sig (h x y z p)`
- `extraction_safe_pred_spec`: `forall n p, S (proj1_sig (safe_pred n p)) = n`
- `extraction_tr_refl`: transport erasure goal, expected only at ATP level until Phase 5 reconstruction support
- `extraction_beq_correct`: `forall n m, beq n m = true <-> n = m`
- `extraction_between_low`: `forall n, n <= proj1_sig (sig_of_sig2 (between n))`
- `extraction_tag_fst`: `forall n, fst (tag n) = n`
- `extraction_refinement_hyp`: refinement expansion in hypothesis position
- `extraction_h_exists`: positive-polarity expansion under `exists`
- `extraction_idiv_small`: Phase-4 `Program Fixpoint` WF unfolding equation
- `extraction_idiv2_small`: Phase-4 bare `Fix lt_wf` WF unfolding equation
- `extraction_idiv3_small`: Phase-4 `Fix_F` WF detection-coverage guardrail; pre-Phase-4 it must remain wrapped
- `canary`: `False` with the full file environment and `Set Hammer ATPLimit 5` (the `Fail hammer` must keep succeeding)
