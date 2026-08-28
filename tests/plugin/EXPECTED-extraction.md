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
- `extraction_dsize_leaf` / `extraction_dsize_node`: split equations of a match
  whose scrutinee is declared at the type-level function `dres dred n`, merely
  convertible to the matched family `dtree n`
- `extraction_dheight_succ`: the same shape with the declared type's arity equal
  to the matched family's telescope, only permuted, so a declared-type reading
  yields a well-formed but wrong index guard instead of an error
- `canary`: `False` with the full file environment and `Set Hammer ATPLimit 5`
  remains wrapped as `Fail hammer` and that failure is enforced by compilation

The bare `Fix`/`Fix_F`, Program `Fix_sub`, and transport/UIP fixtures are
unwrapped and enforced.  The transport ATP dump assertion remains as an
independent translation-quality gate.  The two type-level-function scrutinee
fixtures are additionally dumped as `consistency-dsize.p` and
`consistency-dheight.p` and ATP-checked by `check-consistency.sh`, since a
misread index guard is soundness-relevant rather than merely lossy.

The consistency suite also retains five indexed-family canary groups in the
existing dump names enumerated by `check-consistency.sh`:

- `consistency-prop-or-match.p` / `consistency-false-case-prop.p`: negative and
  positive `reflect` expansions, including the `true` result index;
- `consistency-dsize.p` / `consistency-dheight.p`: vector and `Fin.t 0`
  hypotheses whose constructor indices rigidly clash;
- `consistency-eq-rect.p`: the F*-#1542-shaped equality match under
  `true = false`, together with erased transports across `nat`, `bool`, and
  `string` in one problem;
- `consistency-h.p`: an indexed subset at zero whose expanded carrier payload
  is the refutable proposition `k < 0`;
- `consistency-indexed-poly-subset.p`: a parameter-dependent indexed subset
  whose equal carrier payload is constructed at two distinct indices.

Each group keeps its relevant definition/typing formulas as axioms, so replacing
the conjecture by `$false` checks the emitted theory rather than merely deleting
the exercised shape.

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
- Forded indexed split equations: `dsize` and `dheight` have unconditional
  equations for both constructors, with no legacy `=> @` index premise and no
  reference to the `dres`/`dswap` type-level functions in their definition
  lines. `dstack_size` likewise has unconditional leaf/node equations even
  though its scrutinee is declared through a type-level fixpoint the
  head-normalizer does not unfold. For nested matching at `dtree 0`, the link
  applies the outer case symbol directly to the inner option case; rigid clash
  pruning keeps the leaf equation and omits the impossible node equation.
- Indexed-family fixtures from `extraction_indexed.v`: declaration inversion
  axioms for `breflect`, `tagged`, `okp`, and `vec` are checked by parsing their
  fresh binders and correlating those exact identifiers across typing guards,
  constructor parameters and payloads, and residual index equations. `untag`
  fords the constructor's solved index to the occurrence index without a
  premise, so its equation binds that index once; `ibval` erases the
  `IBounded` package to its carrier and expands the `k < n` payload in its type
  axiom, and `ibidx` -- whose body reads the solved index instead of the carrier
  -- equates its result with the scrutinee's index rather than with a fresh
  binder that would occur on the right-hand side alone; `indexed_poly_value`
  likewise fords its constructor index; `fromok`, `fromisT`, `fromtrue`, `cast`,
  and the JMeq match collapse to unconditional equations. Their asserted typing/inversion axioms retain the
  relevant Prop premises and index equalities. In particular, `cast`'s helper
  correlates its exact source/target binders through the equality premise and
  source-payload/target-result typing, and reuses its exact outer function binder
  in both self-typing and the result application. The user `vhead`
  emits only its live `vcons` equation, and `dheight2` emits only its live
  `dbox_succ` equation; neither equation has a legacy index premise. Default
  indexed-subset declaration skipping is pinned by requiring the ordinary
  `$_typeof_extraction_indexed.ibounded` axiom while forbidding
  `$_inj_extraction_indexed.IBounded` and `$_inversion_extraction_indexed.ibounded`.
  `ibpart`, an under-applied `IBounded`, is eta-expanded and collapsed to the
  lambda `f x = x`, and its typing axiom instantiates the `k < n` payload at the
  literal occurrence index on both sides of the implication -- the index formal
  the classification substitutes for the forded argument is free here, so
  leaving it in the residual field types aborted the translation.
- Indexed guard expansion: `introT` and `$_typeof_Nat.eqb_spec` each contain
  `ReflectT` and `ReflectF` alternatives with the positive/negative proposition
  payload and `= true`/`= false` residual index equations. For `Nat.eqb_spec`,
  the exact generated proposition helpers are checked to define equality and
  the exact shared boolean helper is checked against the full `Nat.eqb` O/S
  truth table. Their old nominal `$HasType ... reflect` leaves are forbidden.
- Stdlib regression constants: split-equation checks for `Nat.add`, `List.app`,
  and `Streams.hd`; structural checks for `List.Forall`, `eq_rect`, `eq_ind_r`,
  `proj1`, `proj1_sig`, `Acc_rect`, `Nat.eq_dec`, `Nat.eqb_spec`, `sumbool`,
  `introT`, `sig`, `prod`, `Vector.hd`, a `Streams` coinductive destructor, and
  the `Equivalence_Reflexive` typeclass method projection. The generic
  singleton path emits the unconditional `eq_rect(A,x,P,f,y) = f` equation;
  `eq_ind` and `eq_ind_r` contribute only their
  formulas, with no synthetic `$Proof = $Proof` definition. `Acc_rect` carries
  exactly one `Acc` premise. Declaration-level subset injectivity/inversion
  remains present for parameter-dependent `sig`.

### Documented deviations

No disabled translation assertion blocks remain. The transport ATP-dump layer
remains as an independent translation-quality gate in addition to the end-to-end
`hammer` goal. Standard transports now use the generic definition path; no
synthetic transport-definition axiom or definitional `$Proof = $Proof` equality
remains.
