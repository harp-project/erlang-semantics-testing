-module(misc).
-compile(export_all).

remove_extension(Filename) ->
    hd(string:split(Filename, ".", trailing)).

remove_directory(Path) ->
    case string:find(Path, "/", trailing) of
        nomatch -> Path;
        Matching -> string:substr(Matching, 2)
    end.

write_to_file(Filename, Content) ->
    write_to_file(Filename, Content, [write, directory]).

write_to_file(Filename, Content, Modes) ->
    case file:open(Filename, Modes) of
        {ok, Fd} ->
            file:write(Fd, Content),
            file:close(Fd);
        {Status, Msg} ->
            io:format("Error opening file ~s: ~s", [Status, Msg])
    end.

parse(Expression) ->
    {ok, Tokens, _} = erl_scan:string(Expression++"."),
    {ok, Parsed} = erl_parse:parse_exprs(Tokens),
    {value, Result, _} = erl_eval:exprs(Parsed, []),
    Result.

report_coverage_to_csv(Map, Filename) ->
  StatLine = maps:fold(fun(_, V, Acc) -> integer_to_list(V) ++ ";" ++ Acc end, "\n", Map), % "~n" does not work here, only "\n"
  case filelib:is_regular(Filename) of
    %% No header needed
    true  -> misc:write_to_file(Filename, StatLine, append);
    
    %% header needed
    false ->
      begin
        HeaderLine = maps:fold(fun(K, _, Acc) -> if is_atom(K) -> atom_to_list(K);
                                                    true -> K
                                                 end ++ ";" ++ Acc end, "\n", Map),
        misc:write_to_file(Filename, HeaderLine ++ StatLine, [append])
      end
  end
.

%% FILL UP INITIAL MAP WITH KEY-0 PAIRS
init_stat_map(List) ->
  lists:foldr(fun(Elem, Acc) -> maps:put(Elem, 0, Acc) end, #{}, List).

hline() ->
    io:format("------------------------------------------------------------------------~n").

update_map(K, V, Acc) ->
    case maps:is_key(K, Acc) of
       true  -> maps:update_with(K, fun(X) -> X + V end, Acc);
       false -> Acc
    end.

process_trace(Trace, Loc) ->
  ReportMap = get(Loc),
  UpdatedReportMap = maps:fold(fun(K, V, Acc) ->
                                      update_map(K, V, Acc)
                                 end, ReportMap, Trace),
  put(Loc, UpdatedReportMap).
