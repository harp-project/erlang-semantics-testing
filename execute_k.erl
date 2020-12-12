-module(execute_k).

-export([execute/3]).

-define(KDIR, "erlang-semantics/erl_env").

execute(BaseName, ModuleName, ReportDirectory) ->
    
    %% krun --config-var Exp="module:main(.Exps)" module.erl
    case
        exec:shell_exec(
            io_lib:format("krun -d ~s --config-var Exp=\"~s:main(.Exps)\" ~s", [
               ?KDIR,
               ModuleName,
               BaseName ++ ".erl"
           ])
        )
    of
        {_, Output} ->
            FileName = ReportDirectory ++ ModuleName ++ ".kresult",
		    write_to_file(FileName, Output),
            get_k_result_from_string(Output);
        _ ->
            io:format("Error running krun~n"),
            -1
    end.

write_to_file(Filename, Content) ->
    case file:open(Filename, [write]) of
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

%% Returns {ok, Exp} if the k result was parseable, otherwise {error, errormsg}
get_k_result_from_string(Output) ->
  case string:split(Output, "<k>", leading) of
    [_ | [Tail]] -> case string:split(Tail, "</k>", leading) of
                       [Head | _] -> 
                             begin
                               ToParse = lists:flatten(string:replace(Head, ".Exps", "")),
							   {ok, parse(ToParse)}
                             end;
                       _          -> {error, "Illegal K result format: ~n" ++ Output}
                    end;
    _            -> {error, "Illegal K result format: ~n" ++ Output}
  end
.


%% WARNING: xmerl cannot parse every k framework result!!
get_k_result_from_xml(FileName) ->
   XMLResult = xmerl_scan:file(FileName),
   try
   %% get the XML result cell:
     case element(9 ,element(1, XMLResult)) of
        [_, KCell | _] ->
		  [KTuple] = element(9, KCell),
		  ToParse = element(5, KTuple),
		  {ok, parse(ToParse)};
        _ -> 
           {error, "Illegal K result format!"}
     end
   catch
       _ -> {error, "Illegal K result format!"}
   end
.
