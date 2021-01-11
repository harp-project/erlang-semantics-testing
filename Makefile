
ERLC=erlc
KOMPILE=kompile

COR_TESTS=$(shell find tests -name "*.erl")

all: cst_to_ast.beam exec.beam execute_erl.beam execute_coq.beam execute_k.beam misc.beam

compile_k: erlang-semantics/erl_env/erl.k
	$(KOMPILE) erlang-semantics/erl_env/erl.k

cst_to_ast.beam: converter/cst_to_ast.erl
	$(ERLC) converter/cst_to_ast.erl

exec.beam: exec.erl
	$(ERLC) exec.erl

execute_erl.beam: execute_erl.erl
	$(ERLC) execute_erl.erl

execute_coq.beam: execute_coq.erl
	$(ERLC) execute_coq.erl

execute_k.beam: execute_k.erl
	$(ERLC) execute_k.erl

misc.beam: misc.erl
	$(ERLC) misc.erl

.PHONY: clean check

check: all
	./scripts.erl $(COR_TESTS)

check-all:
	@echo "TODO: implement"
	exit 1

clean:
	rm -f -- cst_to_ast.beam
	rm -f -- exec.beam
	rm -f -- execute_erl.beam
	rm -f -- execute_coq.beam
	rm -f -- execute_k.beam
	rm -f -- misc.beam
