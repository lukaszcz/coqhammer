# Extraction test expected profile

This records the current (pre extraction-refactor) end-to-end `hammer` profile for
`tests/plugin/extraction_matches.v`. Goals listed as passing are left as
`Proof. hammer. Qed.` and must keep passing in later phases. Goals listed as
failing are wrapped as `Fail hammer.` / `Abort.` until the relevant translator work
makes them pass. The file temporarily pins `Hammer Predictions` to 16 around
`extraction_g_deep` through `extraction_tmirror_node` to keep the current profile
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
- `extraction_rsize_nil`: `rsize (Rose nil) = 1`
