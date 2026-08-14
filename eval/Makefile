# input files
FFILES=$(shell find problems/ -name "*.v" | sort -R)
OFILES=$(patsubst problems/%.v,problems/%.vo,$(FFILES))
# Conditional, so that the -coqlib flag `evaluate.sh library` exports for the
# `_installs/current` prefix survives: a plain `COQFLAGS=` would override the
# environment and silently evaluate against the active switch instead.
COQFLAGS ?=
COQC=rocq c $(COQFLAGS) $(shell find problems/ -name "*.conf" -exec cat {} + | tr "\n" " ")
COMPILE_SUPERVISOR ?= tools/rocq-compile-supervisor.sh
COMPILE_TIMEOUT ?= 600
COMPILE_TIMEOUT_GRACE ?= 10
COMPILE_PHASE ?= compile
SUPERVISED_COQC=$(COMPILE_SUPERVISOR) --timeout "$(COMPILE_TIMEOUT)" \
	--grace "$(COMPILE_TIMEOUT_GRACE)" --phase "$(COMPILE_PHASE)"

all:
	@echo "See README on how to invoke make."

test-prepare-corpus:
	python3 tests/test_insert_committed_preamble.py

test-grid-engine:
	bash tests/test_grid_engine.sh

test-compile-supervisor:
	bash tests/test_compile_supervisor.sh

test-atp-makefile:
	bash tests/test_atp_makefile.sh

test-premise-grid-spec:
	bash tests/test_premise_grid_spec.sh

test-confirmation-option-probe:
	bash tests/test_confirmation_option_probe.sh

test-premise-summarizer:
	python3 tests/test_summarize_premise_screening.py

test: test-prepare-corpus test-grid-engine test-compile-supervisor \
      test-atp-makefile test-premise-grid-spec test-confirmation-option-probe \
      test-premise-summarizer

init: $(OFILES)
problems/%.vo: problems/%.v
	@mkdir -p logs/init
	$(SUPERVISED_COQC) --source "$<" -- $(COQC) "$<" \
		> logs/init/`basename "$@" .vo`.log 2>&1

check: $(patsubst problems/%.v,logs/check/%.log,$(FFILES))
logs/check/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
	$(SUPERVISED_COQC) --source "$<" -- $(COQC) "$<" > "$@" 2>&1

atp: $(patsubst problems/%.v,logs/atp/%.log,$(FFILES))
logs/atp/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
	$(SUPERVISED_COQC) --source "$<" -- $(COQC) "$<" > "$@" 2>&1

reconstr: $(patsubst problems/%.v,logs/reconstr/%.log,$(FFILES))
logs/reconstr/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
	$(SUPERVISED_COQC) --source "$<" -- $(COQC) "$<" > "$@" 2>&1

prove: $(patsubst problems/%.v,logs/prove/%.log,$(FFILES))
logs/prove/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
	$(SUPERVISED_COQC) --source "$<" -- $(COQC) "$<" > "$@" 2>&1

clean-vo:
	rm -f $(OFILES)

clean: clean-vo
	rm -rf logs coqhammer.opt check.log gen_atp.log
	$(MAKE) -C tools clean

clean-problems: clean-vo
	rm -f $(patsubst problems/%.v,problems/.%.aux,$(FFILES))
	rm -f $(patsubst problems/%.v,problems/%.v.bak,$(FFILES))
	rm -f $(patsubst problems/%.v,problems/%.glob,$(FFILES))

.PHONY: clean clean-vo clean-problems test test-prepare-corpus test-grid-engine \
        test-compile-supervisor test-atp-makefile test-premise-grid-spec \
        test-confirmation-option-probe \
        test-premise-summarizer \
        check atp reconstr init all
