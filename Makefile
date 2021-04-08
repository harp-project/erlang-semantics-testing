
ERLC=erlc
GHC=ghc
COQC=coqc 
SED=sed
KOMPILE=kompile

COR_TESTS=$(shell find tests -name "*.erl")
GIT_PREFIX=erllvm-bench/src/small/
BENCH_PREFIX=bench/
GIT_TESTS=decode.erl fib.erl huff.erl length.erl length_c.erl length_u.erl mean_nnc.erl nrev.erl qsort.erl smith.erl tak.erl zip_nnc.erl

all: cst_to_ast.beam exec.beam execute_erl.beam execute_coq.beam execute_ghc.beam execute_k.beam misc.beam BigStepSemantics.o BigStepSemanticsTraced.o setup_tests

setup_tests:
	bash setup_tests.sh $(addprefix $(GIT_PREFIX), $(GIT_TESTS))

compile_k: erlang-semantics/erl_env/erl.k
	$(KOMPILE) erlang-semantics/erl_env/erl.k

pretty_print_coq.beam: converter/pretty_print_coq.erl
	$(ERLC) converter/pretty_print_coq.erl

pretty_print_ghc.beam: converter/pretty_print_ghc.erl
	$(ERLC) converter/pretty_print_ghc.erl

cst_to_ast.beam: converter/cst_to_ast.erl pretty_print_coq.beam pretty_print_ghc.beam
	$(ERLC) converter/cst_to_ast.erl

exec.beam: exec.erl
	$(ERLC) exec.erl

execute_erl.beam: execute_erl.erl
	$(ERLC) execute_erl.erl

execute_coq.beam: execute_coq.erl
	$(ERLC) execute_coq.erl

execute_k.beam: execute_k.erl
	$(ERLC) execute_k.erl

execute_ghc.beam: execute_ghc.erl
	$(ERLC) execute_ghc.erl

BigStepSemantics.o: BigStepSemantics.hs
	$(GHC) -dynamic BigStepSemantics.hs

BigStepSemanticsTraced.o: BigStepSemanticsTraced.hs
	$(GHC) -dynamic BigStepSemanticsTraced.hs

BigStepSemantics.hs: ExtractBigStepSemantics.v
	$(COQC) -R Core-Erlang-Formalization/src 'Core_Erlang' ExtractBigStepSemantics.v
	$(SED) -i "s/import qualified Prelude/import qualified Prelude\nimport qualified Data.Char\nimport qualified Data.Bits\n/g" BigStepSemantics.hs

BigStepSemanticsTraced.hs: ExtractBigStepSemanticsTraced.v
	$(COQC) -R Core-Erlang-Formalization/src 'Core_Erlang' ExtractBigStepSemanticsTraced.v
	$(SED) -i "s/import qualified Prelude/import qualified Prelude\nimport qualified Data.Char\nimport qualified Data.Bits\n/g" BigStepSemanticsTraced.hs

misc.beam: misc.erl
	$(ERLC) misc.erl

.PHONY: clean check

check: all
	./scripts.erl $(COR_TESTS)

check-bench:
	./scripts.erl $(addprefix $(BENCH_PREFIX), $(GIT_TESTS))

clean:
	rm -f -- *.beam
	rm -f -- BigStepSemantics.hs
	rm -f -- BigStepSemantics.hi
	rm -f -- BigStepSemantics.o
	rm -f -- ExtractBigStepSemantics.glob
	rm -f -- ExtractBigStepSemantics.vo
	rm -f -- ExtractBigStepSemantics.vok
	rm -f -- ExtractBigStepSemantics.vos
	rm -f -- BigStepSemanticsTraced.hs
	rm -f -- BigStepSemanticsTraced.hi
	rm -f -- BigStepSemanticsTraced.o
	rm -f -- ExtractBigStepSemanticsTraced.glob
	rm -f -- ExtractBigStepSemanticsTraced.vo
	rm -f -- ExtractBigStepSemanticsTraced.vok
	rm -f -- ExtractBigStepSemanticsTraced.vos
	rm -f -- Program1
	rm -f -- Program1.hs
	rm -f -- Program1.hi
	rm -f -- Program1.o
	rm -f -- Main.hi
	rm -f -- Main.o
	rm -f -- *.P
