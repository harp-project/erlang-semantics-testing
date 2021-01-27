#!/usr/bin/env escript
%%! -i -pa converter -pa generator/ebin -pa eqc-2.01.0/ebin

-module(scripts).
-compile([export_all]).

% -include_lib("eqc/include/eqc.hrl"). % This does not work on Windows Subsystem for Linux
-include("./eqc-2.01.0/include/eqc.hrl").

%% ---------------------------------------------------------------------
%% OPTIONS

-define(REPORT_DIRECTORY, "./reports/").
-define(SHRINKING, true).
-define(TRACING, false).
-define(GHC_EXPORT, false).
-define(GEN_REC_LIMIT, 20).
-define(GEN_SIZE, 20).

%% ---------------------------------------------------------------------

mktmpdir() ->
    TimeInSeconds = erlang:system_time(second),
    %Date = calendar:system_time_to_rfc3339(TimeInSeconds),
    DirPath = io_lib:format("~ssemantic-tester-~p/", [?REPORT_DIRECTORY, TimeInSeconds]),
    filelib:ensure_dir(DirPath),
    io:format("Report Directory created: ~s~n", [DirPath]),
    DirPath.

report(Test, ReportDirectory, Result, Success) ->
    misc:write_to_file(ReportDirectory ++ Test ++ ".result", io_lib:format("Result:~n~p~nVerdict: ~p~n", [Result, Success]), write),
    case Success of
       false -> io:format("~n ~s failed~n", [Test]),
                io:format("X");
       true  -> io:format(".")
    end.

compare_results({ErlResult, CoqResult, KResult}) ->
    case ErlResult of
        {ok, ErlVal} -> begin
                            case CoqResult of
                                {ok, CoqVal, _, _} -> CoqVal == ErlVal;
                                {ok, CoqVal}       -> CoqVal == ErlVal;
                                _                  -> false
                            end and
                            case KResult of
                                {ok, KVal, _} -> KVal == ErlVal;
                                {_ , KVal}    -> KVal == ErlVal orelse
                                                 case is_list(KVal) of
                                                    % In case of parsing ambiguity (potential internal bug in K 3.6):
                                                     true  -> lists:prefix("Illegal K result format: ~nidentity crisis:", KVal);
                                                     false -> false
                                                 end;
                                _             -> false
                            end
                        end;
        _            -> false
    end;
compare_results(_) -> io:format("Illegal result format!~n"), false.

-spec test_case(string(), string()) -> boolean().
test_case(Test, ReportDirectory) ->
    BaseName = misc:remove_extension(Test),
    ModuleName = misc:remove_directory(BaseName),
    spawn(execute_erl, execute, [BaseName, ModuleName, ReportDirectory, ?TRACING, self()]),
    case ?GHC_EXPORT of
        false -> spawn(execute_ghc, execute, [BaseName, ModuleName, ReportDirectory, ?TRACING, self()]);
        true  -> spawn(execute_coq, execute, [BaseName, ModuleName, ReportDirectory, ?TRACING, self()])
    end,
    spawn(execute_k  , execute, [BaseName, ModuleName, ReportDirectory, ?TRACING, self()]),
    Result = {
    receive
        {ErlResult, erl_res} -> ErlResult
    end,
    receive
        {CoqResult, coq_res}    -> CoqResult
    end,
    receive
        {KResult, k_res}        -> KResult
    end},
    % Result = {
    %     execute_erl:execute(BaseName, ModuleName, ReportDirectory),
    %     execute_coq:execute(BaseName, ModuleName, ReportDirectory, ?TRACING),
    %     execute_k:execute(BaseName, ModuleName, ReportDirectory, ?TRACING)
    % },
    Success = compare_results(Result),
    report(ModuleName, ReportDirectory, Result, Success),
    if 
      ?TRACING -> execute_coq:update_coverage(element(2,Result)),
                  execute_k:update_coverage(element(3,Result));
      true     -> ok % do nothing
    end,
    Success.

%% ---------------------------------------------------------------------

unit_test(Tests) when is_list(Tests) ->
    ReportDirectory = mktmpdir(),
    [test_case(Test, ReportDirectory) || Test <- Tests].

%% ---------------------------------------------------------------------

-define(ModuleNamePlaceHolder, "modulenameplaceholder").

is_compilable(T) ->
    S = [erl_syntax:revert(T2) || T2 <- erl_syntax:form_list_elements(eval(T))],
    C = compile:forms(S, [strong_validation, return_errors, nowarn_unused_vars]),
    element(1, C) /= ok andalso io:format("~nGenerated file cannot be compiled :(~n~p~n", [C]),
    element(1, C) == ok.

random_test(NumTests) ->
    ReportDirectory = mktmpdir(),
    put(test_id, 0),
    random:seed(erlang:monotonic_time(), erlang:unique_integer(), erlang:time_offset()), % random combination of the suggested functions instead of now()
    G = resize(?GEN_SIZE, erlgen:module(?ModuleNamePlaceHolder, ?GEN_REC_LIMIT)),
    G2 = ?LET(M, G, case lists:keysearch(value, 1, M) of
                        {value, {_, Value}} -> Value;
                        false -> []
                    end),
    G3 = ?SUCHTHAT(T, G2, is_compilable(T)),
    P = ?FORALL(T, if ?SHRINKING -> G3; true -> noshrink(G3) end,
          %?WHENFAIL(io:format("~n~s~n", [erl_prettypr:format(eqc_symbolic:eval(T))]),
            begin
                TestId = get(test_id),
                ModuleName = io_lib:format("module~p", [TestId]),
                put(test_id, TestId+1),
                RawProgramText = erl_prettypr:format(eqc_symbolic:eval(T)),
                ProgramText = re:replace(RawProgramText, ?ModuleNamePlaceHolder, ModuleName, [global, {return, list}]),
                FilePath = ReportDirectory ++ ModuleName ++ ".erl",
                misc:write_to_file(FilePath, ProgramText, write),
                test_case(FilePath, ReportDirectory)
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
