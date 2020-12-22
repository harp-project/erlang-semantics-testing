-module(execute_k).

-export([execute/4, setup/0, report/0, update_coverage/1]).

-define(KDIR, "erlang-semantics/erl_env").
-define(TRACED_KDIR, "erlang-semantics/erl_env_traced").
-define(K_FILENAME, "./reports/k_coverage.csv").
-define(K_RULE_LOC, k_rule_coverage_map).

execute(BaseName, ModuleName, ReportDirectory, Tracing) ->
    
    %% krun --config-var Exp="module:main(.Exps)" module.erl
    KDir = if Tracing -> ?TRACED_KDIR;
              true    -> ?KDIR
           end,
    case
        exec:shell_exec(
            io_lib:format("krun -d ~s --config-var Exp=\"~s:main(.Exps)\" ~s", [
               KDir,
               ModuleName,
               BaseName ++ ".erl"
           ])
        )
    of
        {_, Output} ->
            FileName = ReportDirectory ++ ModuleName ++ ".kresult",
		        misc:write_to_file(FileName, Output),
            {St, Res} = get_k_result_from_string(Output),
            if Tracing -> {St, {Res, get_k_trace(Output)}};
               true    -> {St, Res}
            end;
        _ ->
            io:format("Error running krun~n"),
            -1
    end.


get_k_result_from_string(Output) ->
  try 
    case string:split(Output, "<k>", leading) of
      [_ | [Tail]] -> case string:split(Tail, "</k>", leading) of
                         [Head | _] -> 
                               begin
                                  ToParse = lists:flatten(string:replace(Head, ".Exps", "")),
			  				                  {ok, misc:parse(ToParse)}
                               end;
                         _          -> {error, "Illegal K result format: ~n" ++ Output}
                      end;
      _              -> {error, "Illegal K result format: ~n" ++ Output}
    end
  catch
    _:_ -> {error, "Illegal K result format: ~n" ++ Output}
  end
.


%% ---------------------------------------------------------------------
%% Erlang Semnatics Coverage Measurement


get_k_trace(Output) ->
  try
    case string:split(Output, "<trace>", leading) of
      [_ | [Tail]] -> case string:split(Tail, "</trace>", leading) of
                        [Head | _] -> 
                              begin
                                ToParse = "#{" ++ re:replace(
                                                    re:replace(string:trim(Head), "[\n]", ",", [global, {return, list}]),
                                                    "[|][-][>]",
                                                    "=>",
                                                    [global, {return, list}]) ++ "}",
                                misc:parse(ToParse)
                              end;
                        _          -> #{}
                      end;
      _              -> #{}
    end
    catch
    _:_ -> io:format("~n~nK coverage:~nasdasdasdasdasdasdn~n"), #{}
    end
.

semantic_rules() -> ["lookup_var", "lookup_fun", "restore_env", "restore_all", "count", "parseVar", "fv", "fvs", "module", "fundefs", "modules", "export", "import", 
                     "module_init", "module_attr_init", "attr_init", "fundefs_init", "is_atom", "is_boolean", "is_integer", "is_number", "hd", "tl", "element", "setelement", 
                     "tuple_size", "list_to_tuple", "tuple_to_list", "length", "matches_and_restore", "matches_fun_and_restore", "matches", "matches_guard", "matches_guard_heat", 
                     "matches_guard_cool", "matches_fun", "mult", "div", "div_ex", "rem", "rem_ex", "plus", "minus", "lt", "le", "lt_list", "ge", "gt", "or", "or_ex", "eq", "neq", 
                     "and", "and_ex", "andalso", "orelse", "not", "app", "diff", "listcomp", "implicit_call", "recursive_call", "anon_call", "anon_call_var", "mfa_call", "fa_import_call", 
                     "fa_local_call", "if", "case", "match", "begin_end"].

setup() ->
  %% Initialize with the Coq coverage map, where all rules were used 0 times:
    put(?K_RULE_LOC, misc:init_stat_map(semantic_rules())).

%% CAUTION: Uses the fact, that the Coq result is the second one in the list
%% returns #{...}
update_coverage(Result) ->
  case Result of
    %% [Erlresult, {Ok, {Coqresult, CoqTrace}} | Rest]
    {_ ,{_, RuleTrace}} -> misc:process_trace(RuleTrace, ?K_RULE_LOC);
    _                   -> #{}
  end.

report() ->
  %% Rule coverage map:
    RuleCoverage = get(?K_RULE_LOC),
  
  %% used rule percent
    UsedRulesNr = maps:size(maps:filter(fun(_, V) -> V > 0 end, RuleCoverage)),
    Semantics_rules = semantic_rules(),
    misc:hline(),
    io:format("K coverage data:~n"),
    io:format("Rule coverage: ~p %~n", [(UsedRulesNr / length(Semantics_rules)) * 100]),
    misc:report_coverage_to_csv(RuleCoverage, ?K_FILENAME),
    misc:hline()
  .

%% ---------------------------------------------------------------------

%% WARNING: xmerl cannot parse every k framework result!!
get_k_result_from_xml(FileName) ->
   XMLResult = xmerl_scan:file(FileName),
   try
   %% get the XML result cell:
     case element(9 ,element(1, XMLResult)) of
        [_, KCell | _] ->
		  [KTuple] = element(9, KCell),
		  ToParse = element(5, KTuple),
		  {ok, misc:parse(ToParse)};
        _ -> 
           {error, "Illegal K result format!"}
     end
   catch
       _:_ -> {error, "Illegal K result format!"}
   end
.
