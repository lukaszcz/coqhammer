# input files
FFILES=$(shell find problems/ -name "*.v" | sort -R)

all:
	@echo "See README on how to invoke make."

init: $(patsubst problems/%.v,logs/init/%.log,$(FFILES))
logs/init/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
	coqc "$<" > "$@" 2>&1

check: $(patsubst problems/%.v,logs/check/%.log,$(FFILES))
logs/check/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
	@echo "check" > coqhammer.opt
	coqc "$<" > "$@" 2>&1

atp: $(patsubst problems/%.v,logs/atp/%.log,$(FFILES))
logs/atp/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
	@echo "gen-atp" > coqhammer.opt
	coqc "$<" > "$@" 2>&1

reconstr: $(patsubst problems/%.v,logs/reconstr/%.log,$(FFILES))
logs/reconstr/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
	./run-reconstr.sh "$<" "$@"

clean:
	rm -rf logs coqhammer.opt
