# input files
FFILES=$(shell find problems/ -name "*.v" | sort -R)

init: $(patsubst problems/%.v,logs/init/%.log,$(FFILES))
logs/init/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
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
