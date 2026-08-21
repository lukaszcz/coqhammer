#
# ATP evaluation
#
# See README for details.
#

# input files
FFILES=$(shell find i/f/ -type f -name "*.p" | sort -R)

# timeout (in seconds)
TIM=30

# Grace period (in seconds) for the external htimeout backstop.  Each prover is
# given TIM as its own deadline; killing it at exactly TIM races with the status
# line it writes on expiry, which loses the result and leaves an empty output.
# Only the backstop for a wedged process moves; no prover's search budget grows.
KILLTIM=$$(($(TIM) + 5))

all: eprover vampire z3 cvc4

eprover: $(patsubst i/f/%,o/eprover/%,$(FFILES))
o/eprover/%: i/f/%
	@mkdir -p `dirname "$@"`
	@eprover -s --cpu-limit=$(TIM) --auto-schedule -R --print-statistics -p --tstp-format "$<"  | grep "file[(]'\|# SZS" > "$@"

vampire: $(patsubst i/f/%,o/vampire/%,$(FFILES))
o/vampire/%: i/f/%
	@mkdir -p `dirname "$@"`
	@htimeout $(KILLTIM) vampire --mode casc -t $(TIM) --proof tptp --output_axiom_names on "$<" | grep "file[(]'\|% SZS" > "$@"

z3: $(patsubst i/f/%,o/z3/%,$(FFILES))
o/z3/%: i/f/%
	@mkdir -p `dirname "$@"`
	@htimeout $(KILLTIM) z3_tptp -c -t:$(TIM) "-file:$<" > "$@"

cvc4: $(patsubst i/f/%,o/cvc4/%,$(FFILES))
o/cvc4/%: i/f/%
	@mkdir -p `dirname "$@"`
	@htimeout $(KILLTIM) cvc4 --tlimit $$(($(TIM) * 1000)) --dump-unsat-cores-full "$<" > "$@"
