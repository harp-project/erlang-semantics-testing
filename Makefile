
ERLC=erlc
KOMPILE=kompile

COR_TESTS=tests/andalso1.erl tests/andalso2.erl tests/andalso3.erl tests/andalso4.erl tests/begin_end1.erl tests/begin_end2.erl tests/begin_end.erl tests/case1.erl tests/case_guard1.erl tests/case_guard2.erl tests/case_guard3.erl tests/case_guard4.erl tests/case_guard5.erl tests/case_guard6.erl tests/case_guard7.erl tests/case_guard8.erl tests/case_guard9.erl tests/count.erl tests/element.erl tests/fib.erl tests/fun1.erl tests/fun2.erl tests/fun_shadow.erl tests/fun_var_scope.erl tests/gcd.erl tests/higherorder.erl tests/if1.erl tests/if2.erl tests/if3.erl tests/if4.erl tests/if5.erl tests/implicit_fun1.erl tests/implicit_fun2.erl tests/implicit_fun3.erl tests/listcomp1.erl tests/listcomp2.erl tests/listcomp3.erl tests/listcomp4.erl tests/list_comparison1.erl tests/list_comparison2.erl tests/list_comparison3.erl tests/listcomp.erl tests/listcomp_shadow1.erl tests/listcomp_shadow2.erl tests/listconcat.erl tests/list_length.erl tests/list_pattern_match2.erl tests/list_pattern_match3.erl tests/list_pattern_match.erl tests/list_substract1.erl tests/list_substract2.erl tests/listsum.erl tests/list_tl.erl tests/m.erl tests/recfun2.erl tests/recfun3.erl tests/recfun.erl tests/setelement.erl tests/sum.erl tests/term_comparison.erl tests/tuple_size.erl tests/atom.erl tests/tuple.erl tests/list.erl tests/map.erl tests/test.erl tests/checks.erl tests/fa_ex.erl tests/not_ex.erl tests/or_ex.erl tests/and_ex.erl tests/orelse_ex.erl tests/andalso_ex.erl tests/app_ex.erl tests/list_to_tuple.erl tests/tuple_to_list.erl tests/or1.erl tests/diff_ex.erl tests/div_ex.erl tests/rem_ex.erl tests/cmp.erl tests/badarity.erl tests/clos_ex.erl tests/apply_ex.erl tests/param_ex.erl

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
