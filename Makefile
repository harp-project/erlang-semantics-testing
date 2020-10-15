
ERLC=erlc

all: cst_to_ast.beam


cst_to_ast.beam: converter/cst_to_ast.erl
	$(ERLC) converter/cst_to_ast.erl

.PHONY: clean check

check: all
	echo 2 | ./script.sh

clean:
	rm -f -- cst_to_ast.beam

