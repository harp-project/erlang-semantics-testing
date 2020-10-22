#!/usr/bin/env escript

%%! -pa converter
%%! -pa eqc-2.01.0/ebin
%%! -pa generator/ebin
%%

-module(scripts).

-compile([export_all]).

remove_extension(Filename) ->
    hd(string:split(Filename, ".", trailing)).

remove_directory(Path) ->
    case string:find(Path, "/", trailing) of
        nomatch -> Path;
        Matching -> string:substr(Matching, 2)
    end.

execute_and_compare_result(Test) ->
    Basename = remove_extension(Test),
    ModuleName = remove_directory(Basename),
    Result = [
        execute_erl:execute(Basename, ModuleName),
        execute_coq:execute(Basename, ModuleName),
        execute_k:execute(Basename, ModuleName)
    ],
    [Head | Tail] = Result,
    io:format("."), %print about progress
    lists:all(fun(Elem) -> Elem == Head end, Tail).

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

generate_and_save_random_test(Id) ->
    random:seed(erlang:now()),
    Filename = io_lib:format("module~p.erl", [Id]),
    % TODO: egg_tester:y() should return with a string instead of printing it
    %       write_to_file(Filename, io_lib:format('-module(module~p).~n-export([main/0]).~n~p', [Id, egg_tester:y()])),
    case
        exec:shell_exec(
            "erl -pa eqc-2.01.0/ebin -pa generator/ebin -noshell -eval \"random:seed(erlang:now()), io:format('~p', [egg_tester:y()])\" -eval 'init:stop()'"
        )
    of
        {0, Output} ->
            write_to_file(
                Filename,
                io_lib:format('-module(module~p).~n-export([main/0]).~n~s', [
                    Id,
                    generator_remove_junk(Output)
                ])
            );
        {_, Output} ->
            io:format("Cannot generate code ~p~n", [Output])
    end,
    Filename.

count_if(Pred, Lists) ->
    length(lists:filter(Pred, Lists)).

count(Elem, Lists) ->
    count_if(fun(X) -> Elem == X end, Lists).

run_multiple_test(Tests) when is_list(Tests) ->
    lists:map(fun(Test) -> execute_and_compare_result(Test) end, Tests).

generate_and_multiple_test(NumberOfTests) when is_number(NumberOfTests) ->
    lists:map(
        fun(Id) ->
            Test = generate_and_save_random_test(Id),
            Result = execute_and_compare_result(Test),
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
