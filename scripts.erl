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
       false -> io:format("~n ~s failed ~p~n", [Test, Result]),
                io:format("X");
       true  -> io:format(".")
    end.

compare_results([{Ok, Head} | Tail]) ->
    lists:all(fun(Elem) ->
                 case Elem of
                   {Ok, {Result, _, _}} -> Result == Head;
                   {Ok, Result}         -> Result == Head;
                   _                    -> io:format("Illegal result format!~n"), 
                                           false
                 end
                   end, Tail);
compare_results(_) -> io:format("Illegal result format!~n"), false.

-spec test_case(string(), string()) -> bool().
test_case(Test, ReportDirectory) ->
    Basename = misc:remove_extension(Test),
    ModuleName = misc:remove_directory(Basename),
    Result = [
        execute_erl:execute(Basename, ModuleName, ReportDirectory),
        execute_coq:execute(Basename, ModuleName, ReportDirectory)
        % execute_k:execute(Basename, ModuleName, ReportDirectory)
    ],
    Success = compare_results(Result),
    report(ModuleName, ReportDirectory, Result, Success),
    execute_coq:update_coverage(Result),
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
    element(1, C) /= ok andalso io:format("\nnem fordul:(\n"),
    element(1, C) == ok.

random_test(NumTests) ->
    ReportDirectory = mktmpdir(),
    put(test_id, 0),
    random:seed(erlang:now()),
    G = resize(20, erlgen:module(?ModuleNamePlaceHolder, 20)),
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
    io:format("All ~p Passed ~p Failed ~p~n", [Cnt, OK, Cnt-OK]).

parser_main_arguments(Args) when is_list(Args), length(Args) > 0 ->
    case Args of
        ["random", N] -> {runRandTests, list_to_integer(N)};
        _             -> {runUnitTests, Args}
    end;
parser_main_arguments(_) ->
    help.

main(Args) ->
    execute_coq:setup(),
    Results = case parser_main_arguments(Args) of
        {runRandTests, NoT} -> random_test(NoT);
        {runUnitTests, LoT} -> unit_test(LoT);
        _                   -> help
    end,
    summary(Results),
    execute_coq:report().
