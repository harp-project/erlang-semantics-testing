#!/bin/bash

# ==============================================================================

KDIR=""
COQDIR=Core-Erlang-Formalization/src
#COQDIR=/mnt/c/Users/petib/Desktop/Core-Erlang-Formalization/src
# COQDIR=""
# Use functional semantics or traditional (true -> functional, false -> traditional)
FUNCTIONAL=true

export result=(0 0 0 0 0 0)

# ==============================================================================

ALL_TESTS=( tests/*.erl )
COR_TESTS=( 
            tests/andalso1.erl \
            tests/andalso2.erl \
            tests/andalso3.erl \
            tests/andalso4.erl \
            tests/case_guard2.erl \
            tests/case_guard3.erl \
            tests/case_guard4.erl \
            tests/case_guard5.erl \
            tests/case_guard6.erl \
            tests/case_guard7.erl \
            tests/case_guard8.erl \
            tests/case_guard9.erl \
            tests/fun_shadow.erl \
            tests/fun_var_scope.erl \
            tests/listcomp1.erl \
            tests/listcomp2.erl \
            tests/listcomp3.erl \
            tests/listcomp4.erl \
            tests/list_comparison1.erl \
            tests/list_comparison2.erl \
            tests/list_comparison3.erl \
            tests/list_pattern_match2.erl \
            tests/list_substract2.erl \
            tests/listcomp_shadow1.erl \
            tests/term_comparison.erl
          )

# ==============================================================================

hline() { echo "------------------------------------------------------------"; }
hdline() { echo "============================================================"; }

generate_random_program()
{
	local num=$1
  echo "### Generating a random program..."
  echo "-module(module$num)." > "module$num.erl"
  echo "-export([main/0])." >> "module$num.erl"
  erl -pa eqc-2.01.0/ebin -pa generator/ebin -noshell -eval "random:seed(erlang:now()), io:format('~p', [egg_tester:y()])" -eval 'init:stop()' | head -n -4 >> "module$num.erl"
  # cat "module$num.erl"
}

use_test_case()
{
	hdline
    echo "### Using test case $1..."
    echo ""
    cat $1 >> module1.erl
}

execute_k()
{
    if [ "$KDIR" = "" ]; then
		echo "### (I'm skipping the K execution step.)"
    else
        echo "### Executing the K framework..."
        krun -d $KDIR --config-var Exp="module1:main(.Exps)" module1.erl > kfw_result
        echo "### Extracting the result..."
        RESULT_KFW=$(xpath -q -e '/cfg/k/text()' "kfw_result" | tr -d '[:space:]')
        echo "### The result is: ${RESULT_KFW}"
    fi
}

execute_coq()
{
	local num=$1
    if [ "$COQDIR" = "" ]; then
        echo "### (I'm skipping the Coq execution step.)"
    else
        echo "### Transforming Erl CST to CERL Coq-AST..."
        # here you can give whether functional (true) or traditional (false) semantics should be used (second param of from_erl)
        erl -pa converter -noshell -eval "io:format(cst_to_ast:from_erl(module$num, $FUNCTIONAL))" -eval 'init:stop()' > "tmp$num.v"
        if ! [ $? -eq 0 ]; then
            echo -e "### The \e[44mCoq\e[m converter has \e[41mFAILED\e[m"
            return 1
        fi
        echo "### Executing Coq..."
        coqc -Q $COQDIR "" "tmp$num.v" > "coqresult$num.res" 2> "coqerror$num.res"
		
		# Distinction of failures
		
		grep 'Error: Tactic failure: Tactic timeout!.' "coqerror$num.res" > "coqtimeouterror$num.res"
		grep 'Error:' "coqerror$num.res" > "coqrealerror$num.res"
		
		# timeout errors
		
		if [ -s "coqtimeouterror$num.res" ]; then
			echo -e "### \e[41mERROR!\e[m Coq tactic timeout!!"
			return 1
		else
		
			# other errors
			
			if [ -s "coqrealerror$num.res" ]; then
				echo -e "### \e[41mERROR!\e[m Coq execution failed!!"
				return 2
			else
		
				echo "### Extracting the result..."
				# The string notation "str" shouldn't be disposed after introducting strings to the formalisation
				# RESULT_COQ=$(cat "coqresult$num.res" | tail -n +2 | tr -d '[:space:]' | sed 's/.*--e->\(.*\)/\L\1/' | sed -e 's/inl//g' | sed -e 's/`//g' | sed -e 's/@//g' | sed -e 's/==>/=>/g' | sed -e 's/\"//g' | sed -e 's/'\''//g')
        if [ $FUNCTIONAL == "true" ] ; then
          RESULT_COQ=$(cat "coqresult$num.res")
          RESULT_COQ=${RESULT_COQ#*Some }
          RESULT_COQ=${RESULT_COQ::-14}
          RESULT_COQ=$(sed -e 's/`//g' <<< $RESULT_COQ | sed -e 's/@//g' | sed -e 's/==>/=>/g' | sed -e 's/\"//g' | sed -e 's/'\''//g')
        else
          RESULT_COQ=$(cat "coqresult$num.res" | tail -n +2 | tr -d '[:space:]' | sed 's/.*--e->\(.*\)/\L\1/' | sed -e 's/inl//g' | sed -e 's/`//g' | sed -e 's/@//g' | sed -e 's/==>/=>/g' | sed -e 's/\"//g' | sed -e 's/'\''//g' | sed -e 's/%//g')
        fi
				echo "### The result is: ${RESULT_COQ}"
				return 0
			fi
		fi
		
	fi
}

timestamp() {
 echo ""
 #  date +"%T"
}

execute_erl()
{
	local num=$1
  echo "### Compiling the Erlang code..."
  erlc -W0 "module$num.erl"
  echo "### Executing the Erlang code..."
  erl -noshell -eval "io:format('~p', [module$num:main()])" -eval 'init:stop()' > "erlresult$num.res" 2> "erlerror$num.res"
	grep 'Crash dump is being written to: erl_crash.dump...done\|no such file or directory' "erlerror$num.res" > "erltrueerror$num.res"
	RESULT_ERL=$(cat "erlresult$num.res")
	echo "### The Erlang result is: ${RESULT_ERL}"

}

compare_k_to_erl()
{
    if ! [ "$RESULT_KFW" = "" ]; then
        RESULT_FST=$(erl -noshell -eval "io:format('~p',[${RESULT_KFW}==${RESULT_ERL}])" -eval 'init:stop()')
        if [ "$RESULT_FST" = "true" ]; then
            echo -e "### The \e[44mK framework\e[m result is \e[42mCORRECT\e[m"
            return 0
        else
            echo -e "### The \e[44mK framework\e[m result is \e[42mCORRECT\e[m"
            return 1
      fi
    else
        echo "### (No K result to compare.)"
    fi
}

compare_coq_to_erl()
{
    if ! [ "$RESULT_COQ" = "" ]; then
        RESULT_SND=$(erl -noshell -eval "io:format('~p',[${RESULT_COQ}==${RESULT_ERL}])" -eval 'init:stop()')
        if [ "$RESULT_SND" = "true" ]; then
            echo -e "### The \e[44mCoq\e[m result is \e[42mCORRECT\e[m"
            return 0
        else
            echo -e "### The \e[44mCoq\e[m result is \e[41mINCORRECT\e[m"
            return 1
        fi
    else
        echo "### (No Coq result to compare.)"
    fi
}

cleanup()
{
  rm -f module*.erl
  rm -f tmp*.*
	rm -f .tmp*
  rm -f *_result
	rm -f *_error
  rm -f *.beam
  rm -f erl_crash.dump
	rm -f *.res
}

execute_and_check()
{
	local num=$1
	echo "### Test case started:"
	timestamp
    hline && execute_erl "$num" hline
    hline
	if [ -s "erltrueerror$num.res" ]; then
		echo -e "### Erlang compilation \e[41mFAILED\e[m!"
		echo "### Test case finished:"
		timestamp
		return 5
	else
		if execute_k; then
			if ! [ "$RESULT_KFW" = "" ] && ! compare_k_to_erl; then
				echo "### Test case finished:"
				timestamp
				return 2
			fi
		else
			echo "### Test case finished:"
			timestamp
			return 1
		fi
		hline
		if execute_coq "$num"; then
			if ! [ "$RESULT_COQ" = "" ] && ! compare_coq_to_erl; then
				echo "### Test case finished:"
				timestamp
				return 4
			fi
		else
			echo "### Test case finished:"
			timestamp
			return 3
		fi
		echo "### Test case finished:"
		timestamp
		return 0
	fi
}

compile_converter()
{
	echo "### Compiling the translator..."
  erlc converter/cst_to_ast.erl > /dev/null
}

test_all()
{
  n=${#ALL_TESTS[@]}
  echo "Number of all test cases: $n"
  compile_converter
  result=(0 0 0 0 0 0)
  for f in "${ALL_TESTS[@]}"; do
    use_test_case $f
    execute_and_check 1
    R=$?
    if [ $R -eq 0 ]; then ((result[0]++)); fi
    if [ $R -eq 1 ]; then ((result[1]++)); fi
    if [ $R -eq 2 ]; then ((result[2]++)); fi
    if [ $R -eq 3 ]; then ((result[3]++)); fi
    if [ $R -eq 4 ]; then ((result[4]++)); fi
    if [ $R -eq 5 ]; then ((result[5]++)); fi
  done
  echo ""
  echo "@@@ STATISTICS on $n cases"
  echo " - SUCCESSFUL     : ${result[0]}"
  echo " - K ERROR        : ${result[1]}"
  echo " - K INCORRECT    : ${result[2]}"
  echo " - COQ ERROR      : ${result[3]}"
  echo " - COQ INCORRECT  : ${result[4]}"
  echo " - ERLANG FAILED  : ${result[5]}"
  echo ""
}

test_corrects()
{   
  n=${#COR_TESTS[@]}
  c=0
  echo "Number of test cases marked as correct: $n"
	compile_converter
  for f in "${COR_TESTS[@]}"; do
  use_test_case $f
  if execute_and_check 1; then ((c++)); fi
  done
  echo "STATISTICS: $c/$n"
}

function foo()
{
	local num=$1
	generate_random_program "$num"
	execute_and_check "$num"
	local R=$?
	if [ $R -eq 0 ]; then ((result[0]++)); fi
	if [ $R -eq 1 ]; then ((result[1]++)); fi
	if [ $R -eq 2 ]; then ((result[2]++)); fi
	if [ $R -eq 3 ]; then ((result[3]++)); fi
	if [ $R -eq 4 ]; then ((result[4]++)); fi
	if [ $R -eq 5 ]; then ((result[5]++)); fi
	# echo "ALMAFAAAAAAAAAAAA: ${result[3]}"
}

test_random()
{
	echo "### How many tests do you want to run?"
	read num
	if [[ ! $num =~ ^[0-9]+$ ]] ; then
		echo "### $num is not a number!"
		exit
	fi
	compile_converter
	# result=(0 0 0 0 0 0)
	local limit=$(( $num/8 ))
	for (( d=0; d<limit; d++ )) ; do
		for (( c=1; c<=8; c++ )) ; do
			foo "$((d*8+c))" &
		done
		wait
	done
	for (( d=1; d<=$num%8; d++ )) ; do
		foo "$(( num/8*8+d ))" &
	done
	wait
	echo ""
    echo "@@@ STATISTICS on $num cases"
    echo " - SUCCESSFUL     : ${result[0]}"
    echo " - K ERROR        : ${result[1]}"
    echo " - K INCORRECT    : ${result[2]}"
    echo " - COQ ERROR      : ${result[3]}"
    echo " - COQ INCORRECT  : ${result[4]}"
	echo " - ERLANG FAILED  : ${result[5]}"
    echo ""
}

test_single()
{
	echo "### Which file should I test?"
	read testcase
	use_test_case $testcase
	compile_converter
	execute_and_check 1
}

startup()
{
	echo "### Which tests should I run?"
	echo "### 1: All predefined tests"
	echo "### 2: Predefined tests which are marked correct"
	echo "### 3: Random tests"
	echo "### 4: Single test file"
	read inp
	if [ "$inp" == "1" ] ; then
		test_all
	else
		if [ "$inp" == "2" ] ; then
			test_corrects
		else
			if [ "$inp" == "3" ]; then
				test_random
			else
				if [ "$inp" == "4" ]; then
					test_single
				else
					echo "### Invalid input"
				fi
			fi
		fi
	fi
}

startup
echo "### Cleaning up..."
cleanup

