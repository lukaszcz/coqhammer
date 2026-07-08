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
- `extraction_match_goal`: `forall n (m : nat), (match n with 0 => m | S _ => m end) = m`
- `extraction_k_true`: `k true = 1`
- `extraction_k_cases`: `forall b, k b = 0 \/ k b = 1`
- `extraction_g_deep`: `forall x, g (S (S x)) = x`
- `extraction_g_one`: `g 1 = 1`
- `extraction_tsize_node`: node equation for `tsize`
- `extraction_tmirror_node`: two-step `tmirror` equation on `N l x r`
- `extraction_tmirror_injective`: injectivity via the proved `tmirror_invol` premise
- `extraction_list_map_cons`: stdlib `List.map` cons equation
- `extraction_nat_eqb_refl`: `Nat.eqb 5 5 = true`

### Staged per phase

Expected failures now, wrapped with `Fail hammer.` / `Abort.`:

- Phase 1 / TASK_10: `extraction_mypred_succ`,
  `extraction_mypred_nonzero`, `extraction_is_zero_zero`,
  `extraction_is_zero_succ`, `extraction_hd_d_cons`, `extraction_even_ss`
- Fallback-profile fixture: `extraction_rsize_nil` remains expected-failing until
  a later task explicitly changes the nested-inductive/nested-fix fallback story

## deptypes

### Enforced now

Passing end-to-end `hammer` goals in `extraction_deptypes.v`:

- `no_junk`: `2 + 2 = 4` after the `Program Fixpoint idiv` definition
- `extraction_h_two_specs`: two instantiated `h` specs imply `a = c`
- `extraction_safe_pred_proof_irrel`: `safe_pred (S n)` result independent of proof argument
- `extraction_posnat_payload`: `forall p : posnat, 0 < pval p`
- `extraction_vhead_cons`: vector-head equation on `Vector.cons`
- `canary`: `False` with the full file environment and `Set Hammer ATPLimit 5`
  remains wrapped as `Fail hammer` and that failure is enforced by compilation

### Staged per phase

Expected failures now, wrapped with `Fail hammer.` / `Abort.`:

- Phase 2 / TASK_12: `extraction_tr_refl` (ATP-level first; end-to-end after Phase 5)
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
- Corpus constants: Phase-1a split-equation checks for variable-scrutinee
  `myadd`, `g`, `safe_pred`, and `pval`; baseline definition/type-shape checks
  for `k`, `h`, `beq`, `tag`, and `idiv`; `idiv` is specifically
  checked not to expose an unconditional recursive `le_lt_dec`/`Nat.sub`
  unfolding equation before Phase 4.
- Stdlib regression constants: Phase-1a split-equation checks for `Nat.add`,
  `List.app`, and `Streams.hd`; structural checks for
  `List.Forall`, `eq_ind_r`, `proj1`, `Acc_rect`, `Nat.eq_dec`, `sumbool`, `sig`,
  `prod`, `Vector.hd`, a `Streams` coinductive destructor, and the
  `Equivalence_Reflexive` typeclass method projection.

### Staged per phase

Disabled, clearly labeled assertion blocks live in
`check-extraction-transl.sh` and are enabled by the phase acceptance tasks:

- Phase 1 / TASK_10: remaining unit split-equation shapes for `k` and any
  structural-recursive constants not covered by TASK_08's variable-scrutinee
  checks.
- Phase 2 / TASK_12: Prop-singleton elimination shapes for `h`, `safe_pred`,
  transport/`eq_ind_r`, and WF guardrails.
- Phase 3 / TASK_15: refinement unboxing/specification shapes for `h`,
  `safe_pred`, `pval`, `tag`, `beq`, `sig`/`sumbool`.
- Phase 4 / TASK_17: premised WF-recursion equations for `idiv`, `idiv2`, and
  `idiv3`, with explicit absence of unconditional WF unfolding equations.
