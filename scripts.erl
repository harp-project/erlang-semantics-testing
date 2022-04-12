#!/usr/bin/env escript
%%! -i -pa converter -pa generator/ebin -pa eqc-2.01.0/ebin

-module(scripts).
-compile([export_all]).

% -include_lib("eqc/include/eqc.hrl"). % This does not work on Windows Subsystem for Linux
-include("./eqc-2.01.0/include/eqc.hrl").

%% ---------------------------------------------------------------------
%% OPTIONS

-define(REPORT_DIRECTORY, "./reports/").
-define(SHRINKING, false).
-define(TRACING, false).
-define(GHC_EXPORT, false).
-define(GEN_REC_LIMIT, 2).
-define(GEN_SIZE, 2).
-define(GEN_REC_WEIGHT, 1).

%% ---------------------------------------------------------------------

mktmpdir() ->
    TimeInSeconds = erlang:system_time(second),
    %Date = calendar:system_time_to_rfc3339(TimeInSeconds),
    DirPath = io_lib:format("~ssemantic-tester-~p/", [?REPORT_DIRECTORY, TimeInSeconds]),
    filelib:ensure_dir(DirPath),
    io:format("Report Directory created: ~s~n", [DirPath]),
    DirPath.

report(ReportDirectory, Result, Success) ->
    misc:write_to_file(ReportDirectory ++ "result.out", io_lib:format("Result:~n~p~nVerdict: ~p~n", [Result, Success]), write),
    case Success of
       false -> io:format("~n Test failed~n", [misc:remove_directory(ReportDirectory)]),
                io:format("X");
       true  -> io:format(".")
    end.

compare_results(ErlResults, CoqResults) ->
    % in the future, we can parallelize the funcitonality, thus the results should be compared in an ordered way
    OrderedErlResults = lists:sort(fun({ModName1, _}, {ModName2, _}) -> ModName1 < ModName2 end, ErlResults), 
    OrderedCoqResults = lists:sort(fun({ModName1, _}, {ModName2, _}) -> ModName1 < ModName2 end, CoqResults),
    List = lists:zip(OrderedErlResults, OrderedCoqResults),
    lists:foldr(fun({{_, ErlResult}, {_, {CoqResult}}}, Acc)       -> (ErlResult == CoqResult) and Acc; % non-traced Coq
                   ({{_, ErlResult}, {_, {CoqResult, _, _}}}, Acc) -> (ErlResult == CoqResult) and Acc; % traced Coq
                   (_,                 _)                          -> io:format("Illegal result format!~n") end, 
                true, List).

check_cases(FilePaths, ReportDirectory) ->
  % Compile Erlang
  execute_erl:compile(FilePaths, ReportDirectory),
  % Compile Coq or Haskell
  CoqResults =
      case ?GHC_EXPORT of
          true  -> io:format("GHC Export is not supported yet~n");
          false -> execute_coq:execute(FilePaths, ReportDirectory, ?TRACING)
      end,
  % Execute Erlang
  ErlangResults = execute_erl:execute(FilePaths),
  io:format("~n~nErlang execution result: ~p~n~n", [ErlangResults]),
  io:format("~n~nCoq execution result: ~p~n~n", [CoqResults]),
  Success = compare_results(ErlangResults, CoqResults),
  report(ReportDirectory, {ErlangResults, CoqResults}, Success),
  if 
      ?TRACING -> io:format("Tracing is not supported yet~n");
                  % execute_coq:update_coverage(element(2,Result)),
                  %execute_k:update_coverage(element(3,Result));
      true     -> ok % do nothing
    end,
  Success
  .

%% ---------------------------------------------------------------------

unit_test(Tests) when is_list(Tests) ->
    ReportDirectory = mktmpdir(),
    [check_cases([Test], ReportDirectory) || Test <- Tests].

%% ---------------------------------------------------------------------

is_compilable(T) ->
    S = [erl_syntax:revert(T2) || T2 <- erl_syntax:form_list_elements(eval(T))],
    C = compile:forms(S, [strong_validation, return_errors, nowarn_unused_vars]),
    element(1, C) /= ok andalso io:format("~nGenerated file cannot be compiled :(~n~p~n", [C]),
    element(1, C) == ok.

prettyprint_generated_module(T, ReportDirectory) ->
    ModuleNamePattern = io_lib:format("test~p_module\\1", [get(test_id)]),
    RawProgramText = erl_prettypr:format(eqc_symbolic:eval(T)),
    ProgramText = re:replace(RawProgramText, "module([0-9]+)", ModuleNamePattern, [global, {return, list}]),
    {match,[{Pos,Len}]} = re:run(ProgramText, "test[0-9]+_module[0-9]+", [{capture, first}]),
    ModuleName = string:substr(ProgramText, Pos+1, Len),
    FilePath = ReportDirectory ++ ModuleName ++ ".erl",
    misc:write_to_file(FilePath, ProgramText),
    FilePath.

random_test(NumTests) ->
    ReportDirectory = mktmpdir(),
    put(test_id, 0),
    ModCnt = 3,
    random:seed(erlang:monotonic_time(), erlang:unique_integer(), erlang:time_offset()), % random combination of the suggested functions instead of now()
    G = resize(?GEN_SIZE, gen_erlang:gen_modules(ModCnt, ?GEN_REC_LIMIT, ?GEN_REC_WEIGHT)),
    G2 = ?LET(M, G, proplists:get_value(value, M)),
    G3 = ?SUCHTHAT(Ts, G2,
                   lists:all(fun(T) -> is_compilable(T) end, Ts)),
    P = ?FORALL(Ts, if ?SHRINKING -> G3; true -> noshrink(G3) end,
          %?WHENFAIL(io:format("~n~s~n", [erl_prettypr:format(eqc_symbolic:eval(T))]),
            begin
                TestPath = ReportDirectory ++ integer_to_list(get(test_id)) ++ "/",
                filelib:ensure_dir(TestPath),
                FilePaths = [prettyprint_generated_module(T, TestPath) || T <- Ts],
                Success = check_cases(FilePaths, TestPath),
                io:format("Success : ~p~n~n", [Success]),
                % TODO compile all files in FilePaths, execute some functions and compare the results
                put(test_id, get(test_id)+1),
                true
            end
          %)
        ),
    [eqc:quickcheck(eqc:numtests(NumTests, P))],
    nosummary.

%% ---------------------------------------------------------------------

summary(help) ->
    io:format("wrong number of arguments~n");
summary(nosummary) ->
    nosummary;
summary(Results) ->
    Cnt = length(Results),
    OK = length([X || X <- Results, X == true]),
    io:format("~nAll ~p Passed ~p Failed ~p~n", [Cnt, OK, Cnt-OK]).

parser_main_arguments(Args) when is_list(Args), length(Args) > 0 ->
    case Args of
        ["random", N] -> {runRandTests, list_to_integer(N)};
        _             -> {runUnitTests, Args}
    end;
parser_main_arguments(_) ->
    help.

setup() ->
    execute_coq:setup(),
    execute_erl:setup(),
    execute_k:setup().

report() ->
    if ?TRACING -> execute_coq:report(),
                   execute_erl:report(),
                   execute_k:report();
       true     -> io:format("~nCoverage data is not measured!~n")
    end.

main(Args) ->
    setup(),
    Results = case parser_main_arguments(Args) of
        {runRandTests, NoT} -> random_test(NoT);
        {runUnitTests, LoT} -> unit_test(LoT);
        _                   -> help
    end,
    summary(Results),
    report().
