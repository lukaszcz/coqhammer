# Extraction test expected profile

This records the current extraction-refactor profile for the extraction TDD
files after suite promotion. All listed items are enforced by `make tests`
(`make -C tests/plugin all`), with `make -C tests/plugin test-extraction` kept as
an alias. Any remaining deviations are called out explicitly below.

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

All match/fix goals in this section are unwrapped and enforced in the normal plugin test suite.

## deptypes

### Enforced now

Passing end-to-end `hammer` goals in `extraction_deptypes.v`:

- `no_junk`: `2 + 2 = 4` after the `Program Fixpoint idiv` definition
- `extraction_h_two_specs`: two instantiated `h` specs imply `a = c`
- `extraction_safe_pred_proof_irrel`: `safe_pred (S n)` result independent of proof argument
- `extraction_posnat_payload`: `forall p : posnat, 0 < pval p`
- `extraction_h_proj`: `forall x y z p, proj1_sig (h x y z p) = z`
- `extraction_h_spec`: `forall x y z p, x = proj1_sig (h x y z p)`
- `extraction_safe_pred_spec`: `forall n p, S (proj1_sig (safe_pred n p)) = n`
- `extraction_between_low`: `forall n, n <= proj1_sig (sig_of_sig2 (between n))`
- `extraction_tag_fst`: `forall n, fst (tag n) = n`
- `extraction_refinement_hyp`: `forall s : {u : nat | 0 < u}, 1 <= proj1_sig s`
- `extraction_h_exists`: `forall x y z p, exists u, proj1_sig (h x y z p) = u /\ x = u`
- `extraction_vhead_cons`: vector-head equation on `Vector.cons`
- `extraction_beq_correct`: `forall n m, beq n m = true <-> n = m` using the
  `Nat.eq_dec`/`sumbool`-driven definition and helper lemmas for reconstruction
- `extraction_tr_refl`: transport reflexivity passes end-to-end with `hammer`,
  with the `Hammer_dump` problem `transport-tr-refl.p` still enforced by
  `check-consistency.sh` to pin the ATP-level translation quality independently
- `extraction_idiv_small`: Program `Fix_sub` division small-argument equation,
  using the proved `idiv_small_unfold` reconstruction helper while the
  translation-shape gates enforce the premised unfolding axiom
- `extraction_idiv2_small`: bare `Fix lt_wf` division small-argument equation,
  using the proved `idiv2_small_unfold` reconstruction helper while the
  translation-shape gates enforce the premised unfolding axiom
- `extraction_idiv3_small`: direct `Fix_F` packaging of the same equation, using
  the proved `idiv3_small_unfold` reconstruction helper while the translation
  gates enforce the premised unfolding axiom
- `canary`: `False` with the full file environment and `Set Hammer ATPLimit 5`
  remains wrapped as `Fail hammer` and that failure is enforced by compilation

The bare `Fix`/`Fix_F`, Program `Fix_sub`, and transport/UIP fixtures are
unwrapped and enforced.  The transport ATP dump assertion remains as an
independent translation-quality gate.

### Documented deviations

No dependent-types extraction goals remain wrapped. The `canary`
lemma is intentionally a negative consistency check (`Fail hammer`) and is
enforced by compilation.

## transl

### Enforced now

`extraction_transl.v` is compiled with output redirected to
`extraction_transl.out`; `check-extraction-transl.sh` enforces line-based
structural assertions that hold with the current translator:

- No `Hammer_transl` lookup failures.
- No untranslated `Init.Logic` connective constants (`and`, `or`, `not`, `iff`,
  `ex`, `all`) in the output. Proof constants such as `eq_refl`/`False_rect` are
  still part of the baseline profile and are pinned where relevant.
- Corpus constants: split-equation checks for variable and compound scrutinees
  (`myadd`, `g`, `k`, `safe_pred`, `pval`, `beq`) plus mutual-fix equations for
  `even`/`odd`; unboxing checks for `h`, `safe_pred`, `pval`, `between`, `tag`,
  and `proj1_sig`; specification checks for inline `sig`/`sig2`/record/prod
  payloads, enum result guards, `Nat.eq_dec` sumbool payloads, and pruned
  Prop-premise arity; shallow-output gates over the covered corpus; premised WF
  equations for Program `idiv`, bare `Fix` `idiv2`, and direct `Fix_F` `idiv3`;
  all three are checked to carry the converted `b <> 0` premise on link and case
  equations, with corpus-wide guards against unpremised WF unfolding equations.
- Stdlib regression constants: split-equation checks for `Nat.add`, `List.app`,
  and `Streams.hd`; structural checks for `List.Forall`, `eq_ind_r`, `proj1`,
  `proj1_sig`, `Acc_rect`, `Nat.eq_dec`, `sumbool`, `sig`, `prod`, `Vector.hd`, a
  `Streams` coinductive destructor, and the `Equivalence_Reflexive` typeclass
  method projection.  The profile additionally enforces a transport-erased
  `$_def_` equation for `eq_ind_r` and pins declaration-level subset
  injectivity/inversion as present with the optional skip constant off by default.

### Documented deviations

No disabled translation assertion blocks remain. The transport ATP-dump layer
remains as an independent translation-quality gate in addition to the end-to-end
`hammer` goal.
