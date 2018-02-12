#
# ATP evaluation
#
# See README for details.
#

# input files
FFILES=$(shell find i/f/ -type f | sort -R)

# timeout (in seconds)
TIM=30

all: e-par0 e-par1 e-par2 e-par3 \
  e-14 e-18 e-19 \
  vam-18 vam-26 vam-30 vam-40 \
  z3-32 z3-40 z3-40q z3-432 z3-442 \
  spass-35 p9-09.11a ipr-09 ipr-10 ipr-14 ipr-14sat metis-23 \
  para-3 para-4 \
  cvc4-1.3 cvc4-1.5pre \
  leancop-21 leancop-22 \
  leancop-pl.cut.conj leancop-pl.cut leancop-pl.nocut \
  leancop-ml.cut.conj leancop-ml.cut leancop-ml.nocut \
  meson-infer \
  yic-1 cvc-3 alte

e-par0: $(patsubst i/f/%,o/e-par0/%,$(FFILES))
o/e-par0/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) runepar2.pl $(TIM) 0 "$<" 2 1 1 default | grep "file[(]'\|# SZS" > "$@"

e-par1: $(patsubst i/f/%,o/e-par1/%,$(FFILES))
o/e-par1/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) runepar2.pl $(TIM) 0 "$<" 2 1 1 m10u2_184 | grep "file[(]'\|# SZS" > "$@"

e-par2: $(patsubst i/f/%,o/e-par2/%,$(FFILES))
o/e-par2/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) runepar2.pl $(TIM) 0 "$<" 2 1 1 f6_40_128  | grep "file[(]'\|# SZS"> "$@"

e-par3: $(patsubst i/f/%,o/e-par3/%,$(FFILES))
o/e-par3/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) runepar2.pl $(TIM) 0 "$<" 2 1 1 new_mzt_small  | grep "file[(]'\|# SZS"> "$@"

e-14: $(patsubst i/f/%,o/e-14/%,$(FFILES))
o/e-14/%: i/f/%
	@mkdir -p `dirname "$@"`
	@eproof14 -s --cpu-limit=$(TIM) -R -xAuto -tAuto --tstp-format "$<"  | grep "file[(]'\|# SZS" > "$@"

e-18: $(patsubst i/f/%,o/e-18/%,$(FFILES))
o/e-18/%: i/f/%
	@mkdir -p `dirname "$@"`
	@eprover18 -s --cpu-limit=$(TIM) --auto-schedule -R --print-statistics -p --tstp-format "$<"  | grep "file[(]'\|# SZS" > "$@"

e-19: $(patsubst i/f/%,o/e-19/%,$(FFILES))
o/e-19/%: i/f/%
	@mkdir -p `dirname "$@"`
	@eprover19 -s --cpu-limit=$(TIM) --auto-schedule -R --print-statistics -p --tstp-format "$<"  | grep "file[(]'\|# SZS" > "$@"

vam-18: $(patsubst i/f/%,o/vam-18/%,$(FFILES))
o/vam-18/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) vampire_1.8 --mode casc -t $(TIM) --proof tptp --output_axiom_names on "$<" | grep "file[(]'\|% SZS" > "$@"

vam-26: $(patsubst i/f/%,o/vam-26/%,$(FFILES))
o/vam-26/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) vampire_2.6 --mode casc -t $(TIM) --proof tptp --output_axiom_names on "$<" | grep "file[(]'\|% SZS" > "$@"

vam-30: $(patsubst i/f/%,o/vam-30/%,$(FFILES))
o/vam-30/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) vampire_3.0 --mode casc -t $(TIM) --proof tptp --output_axiom_names on "$<" | grep "file[(]'\|% SZS" > "$@"

vam-40: $(patsubst i/f/%,o/vam-40/%,$(FFILES))
o/vam-40/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) vampire_4.0ltb --mode casc -t $(TIM) --proof tptp --output_axiom_names on "$<" | grep "file[(]'\|% SZS" > "$@"

# Andrei says: try to also use "casc_sat"

z3-40: $(patsubst i/f/%,o/z3-40/%,$(FFILES))
o/z3-40/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) z3-4.0 -tptp DISPLAY_UNSAT_CORE=true -T:$(TIM) "$<" > "$@"

z3-432: $(patsubst i/f/%,o/z3-432/%,$(FFILES))
o/z3-432/%: i/f/%
	@mkdir -p `dirname "$@"`
	@LD_LIBRARY_PATH=~/lib64-432 timeout $(TIM) z3_tptp-4.32 -c -t:$(TIM) "$<" > "$@"

z3-442: $(patsubst i/f/%,o/z3-442/%,$(FFILES))
o/z3-442/%: i/f/%
	@mkdir -p `dirname "$@"`
	@LD_LIBRARY_PATH=~/lib64-442 timeout $(TIM) z3_tptp-4.42 -c -t:$(TIM) "$<" > "$@"

z3-32: $(patsubst i/f/%,o/z3-32/%,$(FFILES))
o/z3-32/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) z3-3.2 -tptp DISPLAY_UNSAT_CORE=true -T:$(TIM) "$<" > "$@"

z3-40q: $(patsubst i/f/%,o/z3-40q/%,$(FFILES))
o/z3-40q/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) z3-4.0 -tptp DISPLAY_UNSAT_CORE=true  ELIM_QUANTIFIERS=true PULL_NESTED_QUANTIFIERS=true -T:$(TIM) "$<" > "$@"

spass-35: $(patsubst i/f/%,o/spass-35/%,$(FFILES))
o/spass-35/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) SPASS -TPTP -PGiven=0 -PProblem=0 -DocProof -TimeLimit=$(TIM) "$<" | grep "SPASS beiseite\|Formulae used in the proof" > "$@"

p9-09.11a: $(patsubst i/f/%,o/p9-09.11a/%,$(FFILES))
o/p9-09.11a/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) run-prover9 "$<" | grep "THEOREM PROVED" > "$@"

ipr-09: $(patsubst i/f/%,o/ipr-09/%,$(FFILES))
o/ipr-09/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) iproveropt09 --clausifier /home/ami/cek/bin/vclausify_rel --tptp_safe_out true "$<" | grep "SZS status\|file" > "$@"

ipr-10: $(patsubst i/f/%,o/ipr-10/%,$(FFILES))
o/ipr-10/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) iproveropt10 --clausifier /home/ami/cek/bin/vclausify_rel --tptp_safe_out true "$<" | grep "SZS status\|file" > "$@"

ipr-14: $(patsubst i/f/%,o/ipr-14/%,$(FFILES))
o/ipr-14/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) iproveropt14 --clausifier /home/ami/cek/bin/vclausify_rel --tptp_safe_out true "$<" | grep "SZS status\|file" > "$@"

ipr-14sat: $(patsubst i/f/%,o/ipr-14sat/%,$(FFILES))
o/ipr-14sat/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) iproveropt14 --schedule sat --clausifier /home/ami/cek/bin/vclausify_rel --time_out_real $(TIM) --tptp_safe_out true "$<" | grep "SZS status\|file" > "$@"

para-3: $(patsubst i/f/%,o/para-3/%,$(FFILES))
o/para-3/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) paradox3 --tstp --no-progress --verbose 0 --time $(TIM) "$<" 2>&1 > "$@"

para-4: $(patsubst i/f/%,o/para-4/%,$(FFILES))
o/para-4/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) paradox4 --tstp --no-progress --verbose 0 --time $(TIM) "$<" 2>&1 > "$@"

metis-23: $(patsubst i/f/%,o/metis-23/%,$(FFILES))
o/metis-23/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) metis --show proof --time-limit $(TIM) "$<" | grep "SZS status\|^fof" | grep -v "fof[(]normalize" > "$@"

cvc4-1.3: $(patsubst i/f/%,o/cvc4-1.3/%,$(FFILES))
o/cvc4-1.3/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) run-cvc4-13 $(TIM) "$<" > "$@"

cvc4-1.5pre: $(patsubst i/f/%,o/cvc4-1.5pre/%,$(FFILES))
o/cvc4-1.5pre/%: i/f/%
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) cvc4-2016-01-29 -L tptp --dump-unsat-cores "$<" > "$@"

meson-infer: o/meson-infer $(patsubst i/f/%,o/meson-infer/%,$(FFILES))
o/meson-infer:
	@mkdir -p "$@"
o/meson-infer/%: i/f/%
	@timeout $(TIM) meson-infer "$<" &> "$@"

leancop-ml.cut.conj: o/leancop-ml.cut.conj $(patsubst i/f/%,o/leancop-ml.cut.conj/%,$(FFILES))
o/leancop-ml.cut.conj:
	@mkdir -p "$@"
o/leancop-ml.cut.conj/%: i/f/%
	@timeout $(TIM) mlleancop-cut-conj "$<" &> "$@"

leancop-ml.cut: o/leancop-ml.cut $(patsubst i/f/%,o/leancop-ml.cut/%,$(FFILES))
o/leancop-ml.cut:
	@mkdir -p "$@"
o/leancop-ml.cut/%: i/f/%
	@timeout $(TIM) mlleancop-cut "$<" &> "$@"

leancop-ml.nocut: o/leancop-ml.nocut $(patsubst i/f/%,o/leancop-ml.nocut/%,$(FFILES))
o/leancop-ml.nocut:
	@mkdir -p "$@"
o/leancop-ml.nocut/%: i/f/%
	@timeout $(TIM) mlleancop-nocut "$<" &> "$@"

leancop-21: o/leancop-21 $(patsubst i/f/%,o/leancop-21/%,$(FFILES))
o/leancop-21:
	@mkdir -p "$@"
o/leancop-21/%: i/f/%
	@timeout $(TIM) leancop21.sh "$<" $(TIM) > "$@"

leancop-22: o/leancop-22 $(patsubst i/f/%,o/leancop-22/%,$(FFILES))
o/leancop-22:
	@mkdir -p "$@"
o/leancop-22/%: i/f/%
	@timeout $(TIM) leancop22.sh "$<" $(TIM) > "$@"

leancop-pl.nocut: o/leancop-pl.nocut $(patsubst i/f/%,o/leancop-pl.nocut/%,$(FFILES))
o/leancop-pl.nocut:
	@mkdir -p "$@"
o/leancop-pl.nocut/%: i/f/%
	@timeout $(TIM) leancop-nc.sh "$<" $(TIM) > "$@"

leancop-pl.cut: o/leancop-pl.cut $(patsubst i/f/%,o/leancop-pl.cut/%,$(FFILES))
o/leancop-pl.cut:
	@mkdir -p "$@"
o/leancop-pl.cut/%: i/f/%
	@timeout $(TIM) leancop-cut.sh "$<" $(TIM) > "$@"

leancop-pl.cut.conj: o/leancop-pl.cut.conj $(patsubst i/f/%,o/leancop-pl.cut.conj/%,$(FFILES))
o/leancop-pl.cut.conj:
	@mkdir -p "$@"
o/leancop-pl.cut.conj/%: i/f/%
	@timeout $(TIM) leancop-cut-conj.sh "$<" $(TIM) > "$@"

why: $(patsubst i/f/%,i/w/%.why,$(FFILES))
i/w/%.why: i/f/%
	@mkdir -p `dirname "$@"`
	@grep -v conjecture "$<" | sort | uniq > /tmp/$(shell basename "$<")
	@grep conjecture "$<" >> /tmp/$(shell basename "$<")
	@sed -i "s/(\([0-9]\)/(renamed\1/g;s/, \([0-9]\)/, renamed\1/g;s/=\([0-9]\)/=renamed\1/g" /tmp/$(shell basename "$<")
	@why3 -F tptp /tmp/$(shell basename "$<") &> "$@"
	@sed -i "s/[(][*] use tptp.Univ [*][)]/type iType/g" "$@"
	@rm /tmp/$(shell basename "$<")

yic-1: $(patsubst i/f/%,o/yic-1/%,$(FFILES))
o/yic-1/%: i/w/%.why
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) why3 -P yices -m 10000 -t $(TIM) "$<" > "$@"

alte: $(patsubst i/f/%,o/alte/%,$(FFILES))
o/alte/%: i/w/%.why
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) why3 -P alt-ergo -m 10000 -t $(TIM) "$<" > "$@"

cvc-3: $(patsubst i/f/%,o/cvc-3/%,$(FFILES))
o/cvc-3/%: i/w/%.why
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) why3 -P cvc3 -m 10000 -t $(TIM) "$<" > "$@"

ilean-12: $(patsubst i/f/%,o/ilean-12/%,$(FFILES))
o/ilean-12/%: i/l/%.leancop
	@mkdir -p `dirname "$@"`
	@timeout $(TIM) ileancop12.sh "$<" $(TIM) > "$@"

