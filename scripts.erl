#!/usr/bin/env escript

%%! -pa converter
%%! -pa eqc-2.01.0/ebin
%%! -pa generator/ebin
%%

-module(scripts).

-compile([export_all]).

-define(REPORT_DIRECTORY, "./reports/").

remove_extension(Filename) ->
    hd(string:split(Filename, ".", trailing)).

remove_directory(Path) ->
    case string:find(Path, "/", trailing) of
        nomatch -> Path;
        Matching -> string:substr(Matching, 2)
    end.

mktmpdir() ->
    TimeInSeconds = erlang:system_time(second),
    %Date = calendar:system_time_to_rfc3339(TimeInSeconds),
    DirPath = io_lib:format("~ssemantic-tester-~p/", [?REPORT_DIRECTORY, TimeInSeconds]),
    filelib:ensure_dir(DirPath),
    io:format("Report Directory created: ~s~n", [DirPath]),
    DirPath.

report(Test, ReportDirectory, Result) ->
    Success = is_homogene(Result),
    write_to_file(ReportDirectory ++ Test ++ ".result", io_lib:format("Result:~n~p~nVerdict: ~p~n", [Result, Success])),
    case Success of
       false -> io:format("~n ~s failed ~p~n", [Test, Result]),
                io:format("X");
       true  -> io:format(".")
    end.

is_homogene(List) ->
    [Head | Tail] = List,
    lists:all(fun(Elem) -> Elem == Head end, Tail).

execute_and_compare_result(Test, ReportDirectory) ->
    Basename = remove_extension(Test),
    ModuleName = remove_directory(Basename),
    Result = [
        execute_erl:execute(Basename, ModuleName, ReportDirectory),
        %execute_k:execute(Basename, ModuleName, ReportDirectory),
        execute_coq:execute(Basename, ModuleName, ReportDirectory)
    ],
    report(ModuleName, ReportDirectory, Result),
    is_homogene(Result).

write_to_file(Filename, Content) ->
    case file:open(Filename, [write]) of
        {ok, Fd} ->
            file:write(Fd, Content),
            file:close(Fd);
        {Status, Msg} ->
            io:format("Error opening file ~s: ~s", [Status, Msg])
    end.

generator_remove_junk(Input) ->
    hd(string:split(Input, "----------", trailing)).

generate_and_save_random_test(Id, ReportDirectory) ->
    random:seed(erlang:now()),
    ModuleName = io_lib:format("module~p", [Id]),
    Basename = ModuleName ++ ".erl",
    Filename = ReportDirectory ++ Basename,
    % TODO: egg_tester:y() should return with a string instead of printing it
    %       write_to_file(Filename, io_lib:format('-module(module~p).~n-export([main/0]).~n~p', [Id, egg_tester:y()])),
    case
        exec:shell_exec(
            io_lib:format("erl -pa eqc-2.01.0/ebin -pa generator/ebin -noshell -eval \"random:seed(erlang:now()), io:format('~~p', [erl_2020_gen:sample(module~p, ~p)])\" -eval 'init:stop()'",
                          [Id, 10])
        )
    of
        {0, Output} ->
            write_to_file(
                Filename,
                generator_remove_junk(Output)
            );
        {_, Output} ->
            io:format("Cannot generate code ~p~n", [Output])
    end,
    %NOTE: this is kinda dirty, but some generated erlang code either won't compile or
    %      crashes durring execution due to ill formed code.
    case execute_erl:execute(Filename, ModuleName, ReportDirectory) of
       {error, _} -> generate_and_save_random_test(Id, ReportDirectory);
       _          -> Filename
    end.

count_if(Pred, Lists) ->
    length(lists:filter(Pred, Lists)).

count(Elem, Lists) ->
    count_if(fun(X) -> Elem == X end, Lists).

run_multiple_test(Tests) when is_list(Tests) ->
    ReportDirectory = mktmpdir(),
    lists:map(fun(Test) -> execute_and_compare_result(Test, ReportDirectory) end, Tests).

generate_and_multiple_test(NumberOfTests) when is_number(NumberOfTests) ->
    ReportDirectory = mktmpdir(),
    lists:map(
        fun(Id) ->
            Test = generate_and_save_random_test(Id, ReportDirectory),
            Result = execute_and_compare_result(Test, ReportDirectory),
            Result
        end,
        lists:seq(1, NumberOfTests)
    ).

parser_main_arguments([]) ->
    help;
parser_main_arguments(Args) when is_list(Args) ->
    case hd(Args) of
        "random" -> {runRandomTests, list_to_integer(lists:nth(2, Args))};
        _ -> {runTests, Args}
    end;
parser_main_arguments(_) ->
    help.

report_result(help) ->
    io:format("wrong number of arguments~n");
report_result(Results) ->
    io:format("All ~p Passed ~p Failed ~p~n", [
        length(Results),
        count(true, Results),
        length(Results) - count(true, Results)
    ]).

main(Args) ->
    case parser_main_arguments(Args) of
        {runRandomTests, NoT} -> Results = generate_and_multiple_test(NoT);
        {runTests, Tests} -> Results = run_multiple_test(Tests);
        help -> Results = help;
        true -> Results = help
    end,
    report_result(Results).
