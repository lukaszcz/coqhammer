# Extraction test expected profile

This records the current extraction-refactor profile for the extraction
TDD files. Items marked **enforced now** are compiled or checked by
`make -C tests/plugin test-extraction`. Items marked **staged** remain wrapped in
`Fail`/disabled assertion blocks until the listed phase task makes them pass.

## matches

### Enforced now

Passing end-to-end `hammer` goals in `extraction_matches.v`:

- `extraction_myadd_ground`: `myadd 2 2 = 4`
- `extraction_myadd_succ`: `forall n m, myadd (S n) m = S (myadd n m)`
- `extraction_mypred_succ`: `forall n, mypred (S n) = n`
- `extraction_mypred_nonzero`: `forall n, n <> 0 -> S (mypred n) = n`
- `extraction_match_goal`: `forall n (m : nat), (match n with 0 => m | S _ => m end) = m`
- `extraction_k_true`: `k true = 1`
- `extraction_k_cases`: `forall b, k b = 0 \/ k b = 1`
- `extraction_g_deep`: `forall x, g (S (S x)) = x`
- `extraction_g_one`: `g 1 = 1`
- `extraction_is_zero_zero`: `is_zero 0`
- `extraction_is_zero_succ`: `forall n, ~ is_zero (S n)`
- `extraction_hd_d_cons`: `forall (d x : nat) l, hd_d d (cons x l) = x`
- `extraction_even_ss`: `forall n, even (S (S n)) = even n`
- `extraction_tsize_node`: node equation for `tsize`
- `extraction_tmirror_node`: two-step `tmirror` equation on `N l x r`
- `extraction_tmirror_injective`: injectivity via the proved `tmirror_invol` premise
- `extraction_list_map_cons`: stdlib `List.map` cons equation
- `extraction_nat_eqb_refl`: `Nat.eqb 5 5 = true`
- `extraction_rsize_nil`: nested-inductive/nested-fix fallback ground equation

Phase 1 / TASK_10 landed: all §4.1 match/fix goals are unwrapped and enforced.

## deptypes

### Enforced now

Passing end-to-end `hammer` goals in `extraction_deptypes.v`:

- `no_junk`: `2 + 2 = 4` after the `Program Fixpoint idiv` definition
- `extraction_h_two_specs`: two instantiated `h` specs imply `a = c`
- `extraction_safe_pred_proof_irrel`: `safe_pred (S n)` result independent of proof argument
- `extraction_posnat_payload`: `forall p : posnat, 0 < pval p`
- `extraction_vhead_cons`: vector-head equation on `Vector.cons`
- `extraction_tr_refl`: transport reflexivity is ATP-provable from the
  `Hammer_dump` problem `transport-tr-refl.p` and enforced by
  `check-consistency.sh`; the lemma remains wrapped end-to-end until the Phase 5
  reconstruction variants graduate the UIP/transport case
- `canary`: `False` with the full file environment and `Set Hammer ATPLimit 5`
  remains wrapped as `Fail hammer` and that failure is enforced by compilation

Phase 2 / TASK_12 landed: singleton/transport erasure is enforced at the
translation layer, `safe_pred` proof-irrelevance remains end-to-end green, and
transport is pinned ATP-level while reconstruction work is deferred to Phase 5.

### Staged per phase

Expected failures now, wrapped with `Fail hammer.` / `Abort.`:

- Phase 3 / TASK_15: `extraction_h_proj`, `extraction_h_spec`,
  `extraction_safe_pred_spec`, `extraction_beq_correct`,
  `extraction_between_low`, `extraction_tag_fst`, `extraction_refinement_hyp`,
  `extraction_h_exists`
- Phase 4 / TASK_17: `extraction_idiv_small`, `extraction_idiv2_small`,
  `extraction_idiv3_small`

## transl

### Enforced now

`extraction_transl.v` is compiled with output redirected to
`extraction_transl.out`; `check-extraction-transl.sh` enforces line-based
structural assertions that hold with the current translator:

- No `Hammer_transl` lookup failures.
- No untranslated `Init.Logic` connective constants (`and`, `or`, `not`, `iff`,
  `ex`, `all`) in the output. Proof constants such as `eq_refl`/`False_rect` are
  still part of the baseline profile and are pinned where relevant.
- Corpus constants: Phase-1 split-equation checks for variable and compound
  scrutinees (`myadd`, `g`, `k`, `safe_pred`, `pval`, `beq`) plus mutual-fix
  equations for `even`/`odd`; baseline definition/type-shape checks for `h`,
  `tag`, and `idiv`; `idiv` is specifically checked not to expose an
  unconditional recursive `le_lt_dec`/`Nat.sub` unfolding equation before
  Phase 4.
- Stdlib regression constants: Phase-1 split-equation checks for `Nat.add`,
  `List.app`, and `Streams.hd`; structural checks for
  `List.Forall`, `eq_ind_r`, `proj1`, `Acc_rect`, `Nat.eq_dec`, `sumbool`, `sig`,
  `prod`, `Vector.hd`, a `Streams` coinductive destructor, and the
  `Equivalence_Reflexive` typeclass method projection.  Phase 2 additionally
  enforces a transport-erased `$_def_` equation for `eq_ind_r`.

### Staged per phase

Disabled, clearly labeled assertion blocks live in
`check-extraction-transl.sh` and are enabled by the phase acceptance tasks:

- Phase 3 / TASK_15: refinement unboxing/specification shapes for `h`,
  `safe_pred`, `pval`, `tag`, `beq`, `sig`/`sumbool`.
- Phase 4 / TASK_17: premised WF-recursion equations for `idiv`, `idiv2`, and
  `idiv3`, with explicit absence of unconditional WF unfolding equations.
