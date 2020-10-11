
ERLC=erlc

COR_TESTS=tests/andalso1.erl tests/andalso2.erl tests/andalso3.erl tests/andalso4.erl tests/case_guard2.erl tests/case_guard3.erl tests/case_guard4.erl tests/case_guard5.erl tests/case_guard6.erl tests/case_guard7.erl tests/case_guard8.erl tests/case_guard9.erl tests/fun_shadow.erl tests/fun_var_scope.erl tests/listcomp1.erl tests/listcomp2.erl tests/listcomp3.erl tests/listcomp4.erl tests/list_comparison1.erl tests/list_comparison2.erl tests/list_comparison3.erl tests/list_pattern_match2.erl tests/list_substract2.erl tests/listcomp_shadow1.erl tests/term_comparison.erl

all: cst_to_ast.beam exec.beam execute_erl.beam execute_coq.beam execute_k.beam


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

