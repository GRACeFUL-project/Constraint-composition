%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Time-series constraints in MiniZinc 
%
% author: Ekaterina Arafailova, Mines Nantes
% email: ekaterina.arafailova@mines-nantes.fr
%
% last revision: July 2016
% version: 1.0 
%
% This Source Code Form is subject to the terms of the Mozilla Public
% License, v. 2.0. If a copy of the MPL was not distributed with this
% file, You can obtain one at http://mozilla.org/MPL/2.0/.
%
% Instructions: 
%
% 1. predicate time-series constraints:
% predicate time_series_constraints(string: predicate, string: feature, string: pattern, array[int] of var int: x)
% 'predicate' is one of  {"all_equal", "decreasing", "increasing"}
% 'feature' is one of {"max", "min", "range", "surface", "width"}
% 'pattern' is one of {"bump_on_decreasing_sequence", "decreasing", "decreasing_sequence", "decreasing_terrace",
%                  "dip_on_increasing_sequence", "gorge", "increasing", "increasing_sequence", "increasing_terrace",
%                  "peak", "plain", "plateau", "proper_plain", "proper_plateau", "steady", "steady_sequence",
%                  "strictly_decreasing_sequence", "strictly_increasing_sequence", "summit", "valley", "zigzag"}
% Note: some combinations of aggregator, feature, pattern do not exist
% 'x' is an already declared array of time-series variables with finite domains, 
% returns true if 'predicate' is true.
% Example: predicate = "all_equal", feature = "max", pattern = "peak" 
% the predicate returns true if all peaks in an input time series have the same maximum
%
% 2. functional time-series constraints:
% predicate time_series_constraints(string: aggregator, string: feature, 
%                                   string: pattern, array[int] of var int: x, var int: result)
% 'aggregator' is one of {"max", "min", "sum"}
% 'feature' is one of {"max", "min", "one", "range", "surface", "width"}
% 'pattern' is one of {"bump_on_decreasing_sequence", "decreasing", "decreasing_sequence", "decreasing_terrace",
%                  "dip_on_increasing_sequence", "gorge", "increasing", "increasing_sequence", "increasing_terrace",
%                  "peak", "plain", "plateau", "proper_plain", "proper_plateau", "steady", "steady_sequence",
%                  "strictly_decreasing_sequence", "strictly_increasing_sequence", "summit", "valley", "zigzag"}
% Note: some combinations of aggregator, feature, pattern do not exist
% 'x' is an already declared array of time-series variables with finite domains, 
% constrains 'result' to be the value computed from a time-series.
% Example: predicate = "sum", feature = "one", pattern = "peak" 
% then result = the number of peaks in an input time series
%
% function var:int time_series_constraints(string: aggregator, string: feature, 
%                                          string: pattern, array[int] of var int: x)
% 'feature' is one of {"max", "min", "one", "range", "surface", "width"}
% 'pattern' is one of {"bump_on_decreasing_sequence", "decreasing", "decreasing_sequence", "decreasing_terrace",
%                  "dip_on_increasing_sequence", "gorge", "increasing", "increasing_sequence", "increasing_terrace",
%                  "peak", "plain", "plateau", "proper_plain", "proper_plateau", "steady", "steady_sequence",
%                  "strictly_decreasing_sequence", "strictly_increasing_sequence", "summit", "valley", "zigzag"}
% Note: some combinations of aggregator, feature, pattern do not exist
% 'x' is an already declared array of time-series variables with finite domains, 
% returns the value computed from a time-series. 
% Example: predicate = "sum", feature = "one", pattern = "peak" 
% returns the number of peaks in an input time series
% 
% 3. footprint time-series constraints:
% predicate time_series_constraints(string: pattern, array[int] of var int: x, array[int] of var int: p)
% 'pattern' is one of {"bump_on_decreasing_sequence", "decreasing", "decreasing_sequence", "decreasing_terrace",
%                  "dip_on_increasing_sequence", "gorge", "increasing", "increasing_sequence", "increasing_terrace",
%                  "peak", "plain", "plateau", "proper_plain", "proper_plateau", "steady", "steady_sequence",
%                  "strictly_decreasing_sequence", "strictly_increasing_sequence", "summit", "valley", "zigzag"}
% 'x' is an already declared array of time-series variables with finite domains, 
% 'p' is footprint of time series in x. 
% constrains 'p' to be the footprint of a time series in 'x'.
% Example: predicate = "sum", feature = "one", pattern = "peak", x = [1,2,1,0,3,4,4,2,1] 
% then p = [0,1,1,0,2,2,2,2,0]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

function var int: time_series_constraint(string: aggregator,
                                            string: feature, 
                                             string: pattern, 
                              array[int] of var int: x) ::promise_total =
      let {var int: result} in
          result;

predicate time_series_constraint_predicate(string: predicate_name,
                                           string: feature,
                                           string: pattern,
                            array[int] of var int: x) = 
let { var int: result = 0} in
  time_series_constraint(predicate_name, feature, pattern, x, result);

predicate time_series_constraint_footprint(string: pattern,
                            array[int] of var int: x,
                            array[int] of var int: p) = 
let { var int: result = 0} in
  good_pattern(pattern)      /\
  impose_time_series_constraint1("footprint", "footprint", pattern, x, p, result);


predicate time_series_constraint(string: aggregator,
                                 string: feature, 
                                 string: pattern, 
                  array[int] of var int: x,
                                var int: result) =
  let {
        int: time_series_length = length(x),
        array[1..1] of var 0..0: P, %not used for function and predicate constraints, only footprint
  } in
  good_pattern(pattern)      /\
  assert(feature = "height"  \/
         feature = "max"     \/
         feature = "min"     \/
         feature = "one"     \/
         feature = "range"   \/
         feature = "surf"    \/
         feature = "width"   \/
         feature = "footprint",
         "Sorry, the feature " ++show(feature)++ " currently does not exist",
  
  assert(aggregator = "max"        \/
         aggregator = "min"        \/
         aggregator = "sum"        \/
         aggregator = "all_equal"  \/
         aggregator = "decreasing" \/
         aggregator = "increasing" \/
         aggregator = "footprint",
         "Sorry, the aggregator " ++show(aggregator)++ " currently does not exist",

  assert(aggregator = "max"         /\ feature != "one"       \/
         aggregator = "min"         /\ feature != "one"       \/
         aggregator = "all_equal"   /\ feature != "one"       \/
         aggregator = "decreasing"  /\ feature != "one"       \/
         aggregator = "increasing"  /\ feature != "one"       \/
         aggregator = "footprint"   /\ feature != "footprint" \/
         aggregator = "sum",
         "The 'one' feature can be only in combination with the 'sum' aggregator",

  assert(feature = "max"  /\  pattern != "decreasing_terrace"
                          /\  pattern != "gorge"
                          /\  pattern != "increasing_terrace"
                          /\  pattern != "plain" 
                          /\  pattern != "plateau" 
                          /\  pattern != "proper_plain" 
                          /\  pattern != "proper_plateau" 
                          /\  pattern != "steady" 
                          /\  pattern != "steady_sequence" 
                          /\  pattern != "valley" \/
        feature != "max",
        "The 'max' feature cannot be in combination with the '"++show(pattern)++"' pattern.",

  assert(feature = "min"  /\ pattern != "peak"
                          /\ pattern != "summit" \/
        feature != "min",
        "The 'min' feature cannot be in combination with the '"++show(pattern)++"' pattern.",
  
  assert(feature = "height"  /\ (pattern = "decreasing_terrace" 
                             \/  pattern = "increasing_terrace"
                             \/  pattern = "plain" 
                             \/  pattern = "plateau" 
                             \/  pattern = "proper_plain" 
                             \/  pattern = "proper_plateau" 
                             \/  pattern = "steady"
                             \/  pattern = "steady_sequence") \/
        feature != "height",
        "The 'height' feature cannot be in combination with the '"++show(pattern)++"' pattern.",
  
  assert(feature = "range"   /\ (pattern  = "decreasing" 
                             \/  pattern = "decreasing_sequence"
                             \/  pattern = "increasing" 
                             \/  pattern = "increasing_sequence" 
                             \/  pattern = "strictly_decreasing_sequence" 
                             \/  pattern = "strictly_increasing_sequence") \/ 
        feature != "range",
        "The 'range' feature cannot be in combination with the '"++show(pattern)++"' pattern.",
  
  assert(feature = "width"  /\  pattern != "bump_on_decreasing_sequence" 
                            /\  pattern != "decreasing"
                            /\  pattern != "dip_on_increasing_sequence" 
                            /\  pattern != "increasing" 
                            /\  pattern != "steady" \/
        feature != "width",
        "The 'width' feature cannot be in combination with the '"++show(pattern)++"' pattern.",
         
  impose_time_series_constraint1(aggregator, feature, pattern, x, P, result)))))))));

predicate good_pattern(string: pattern) =
   assert(pattern= "bump_on_decreasing_sequence"  \/
        pattern = "decreasing"                   \/
        pattern = "decreasing_sequence"          \/
        pattern = "decreasing_terrace"           \/
        pattern = "dip_on_increasing_sequence"   \/
        pattern = "gorge"                        \/
        pattern = "increasing"                   \/
        pattern = "increasing_sequence"          \/
        pattern = "increasing_terrace"           \/
        pattern = "inflexion"                    \/
        pattern = "peak"                         \/
        pattern = "plain"                        \/
        pattern = "plateau"                      \/
        pattern = "proper_plain"                 \/
        pattern = "proper_plateau"               \/
        pattern = "steady"                       \/
        pattern = "steady_sequence"              \/
        pattern = "strictly_decreasing_sequence" \/
        pattern = "strictly_increasing_sequence" \/
        pattern = "summit"                       \/
        pattern = "valley"                       \/
        pattern = "zigzag",
        "Sorry, the pattern " ++show(pattern)++ " currently does not exist");
  
        
  

predicate impose_time_series_constraint1(string: aggregator,
                                         string: feature, 
                                         string: pattern, 
                          array[int] of var int: x,
                          array[int] of var int: P,
                                        var int: result) =
  let{
       % common parameters 
        int: not_in    = not_in(), 
        int: not_in_r  = not_in_r(), 
        int: not_in_a  = not_in_a(),
        int: maybe_b   = maybe_b(),
        int: found     = found(), 
        int: found_end = found_end(), 
        int: maybe_a   = maybe_a(),
        int: in_p      = in_p(),
  
        int: smaller = smaller(), 
        int: equal   = equal(), 
        int: greater = greater(),
  
        int: nb_transition_params = 4,
        
       % transducers
       %bump_on_decreasing_sequence
        int:after_bump_on_decreasing_sequence = 1,
        int:s_bump_on_decreasing_sequence = 1,
        int:r_bump_on_decreasing_sequence = 2,
        int:t_bump_on_decreasing_sequence = 3,
        int:u_bump_on_decreasing_sequence = 4,
        int:v_bump_on_decreasing_sequence = 5,
        int:initial_state_bump_on_decreasing_sequence = s_bump_on_decreasing_sequence,
        int:nb_of_states_bump_on_decreasing_sequence = 5,
        array[1..nb_of_states_bump_on_decreasing_sequence*3,1..nb_transition_params]
              of int:  Transitions_bump_on_decreasing_sequence = 
                  [|  s_bump_on_decreasing_sequence, smaller, s_bump_on_decreasing_sequence, not_in, 
                   | s_bump_on_decreasing_sequence, equal, s_bump_on_decreasing_sequence, not_in, 
                   | s_bump_on_decreasing_sequence, greater, r_bump_on_decreasing_sequence, not_in, 
                   | r_bump_on_decreasing_sequence, smaller, s_bump_on_decreasing_sequence, not_in, 
                   | r_bump_on_decreasing_sequence, equal, s_bump_on_decreasing_sequence, not_in, 
                   | r_bump_on_decreasing_sequence, greater, t_bump_on_decreasing_sequence, not_in, 
                   | t_bump_on_decreasing_sequence, greater, t_bump_on_decreasing_sequence, not_in, 
                   | t_bump_on_decreasing_sequence, equal, s_bump_on_decreasing_sequence, not_in, 
                   | t_bump_on_decreasing_sequence, smaller, u_bump_on_decreasing_sequence, maybe_b, 
                   | u_bump_on_decreasing_sequence, smaller, s_bump_on_decreasing_sequence, not_in_r, 
                   | u_bump_on_decreasing_sequence, equal, s_bump_on_decreasing_sequence, not_in_r, 
                   | u_bump_on_decreasing_sequence, greater, v_bump_on_decreasing_sequence, maybe_b, 
                   | v_bump_on_decreasing_sequence, smaller, s_bump_on_decreasing_sequence, not_in_r, 
                   | v_bump_on_decreasing_sequence, equal, s_bump_on_decreasing_sequence, not_in_r, 
                   | v_bump_on_decreasing_sequence, greater, t_bump_on_decreasing_sequence, found_end, 
                  |],
         
        %decreasing
        int:after_decreasing = 0,
        int:s_decreasing = 1,
        int:initial_state_decreasing = s_decreasing,
        int:nb_of_states_decreasing = 1,
        array[1..nb_of_states_decreasing*3,1..nb_transition_params]
             of int: Transitions_decreasing = 
                                 [| s_decreasing, greater, s_decreasing, found_end, 
                                  | s_decreasing, smaller, s_decreasing, not_in, 
                                  | s_decreasing, equal, s_decreasing, not_in, 
                                  |],
         
        %decreasing_sequence
        int:after_decreasing_sequence = 0,
        int:s_decreasing_sequence = 1,
        int:t_decreasing_sequence = 2,
        int:initial_state_decreasing_sequence = s_decreasing_sequence,
        int:nb_of_states_decreasing_sequence = 2,
        array[1..nb_of_states_decreasing_sequence*3,1..nb_transition_params] 
              of int: Transitions_decreasing_sequence = 
                                          [| s_decreasing_sequence, greater, t_decreasing_sequence, found, 
                                           | s_decreasing_sequence, smaller, s_decreasing_sequence, not_in, 
                                           | s_decreasing_sequence, equal, s_decreasing_sequence, not_in, 
                                           | t_decreasing_sequence, greater, t_decreasing_sequence, in_p, 
                                           | t_decreasing_sequence, equal, t_decreasing_sequence, maybe_a, 
                                           | t_decreasing_sequence, smaller, s_decreasing_sequence, not_in_a, 
                                           |],
         
        %decreasing_terrace
        int:after_decreasing_terrace = 1,
        int:s_decreasing_terrace = 1,
        int:r_decreasing_terrace = 2,
        int:t_decreasing_terrace = 3,
        int:initial_state_decreasing_terrace = s_decreasing_terrace,
        int:nb_of_states_decreasing_terrace = 3,
        array[1..nb_of_states_decreasing_terrace*3,1..nb_transition_params] 
            of int: Transitions_decreasing_terrace = 
                                         [| s_decreasing_terrace, greater, r_decreasing_terrace, not_in, 
                                          | s_decreasing_terrace, smaller, s_decreasing_terrace, not_in, 
                                          | s_decreasing_terrace, equal, s_decreasing_terrace, not_in, 
                                          | r_decreasing_terrace, greater, r_decreasing_terrace, not_in, 
                                          | r_decreasing_terrace, equal, t_decreasing_terrace, maybe_b, 
                                          | r_decreasing_terrace, smaller, s_decreasing_terrace, not_in, 
                                          | t_decreasing_terrace, greater, r_decreasing_terrace, found_end, 
                                          | t_decreasing_terrace, equal, t_decreasing_terrace, maybe_b, 
                                          | t_decreasing_terrace, smaller, s_decreasing_terrace, not_in_r, 
                                          |],
         
        %dip_on_increasing_sequence
        int:after_dip_on_increasing_sequence = 1,
        int:s_dip_on_increasing_sequence = 1,
        int:r_dip_on_increasing_sequence = 2,
        int:t_dip_on_increasing_sequence = 3,
        int:u_dip_on_increasing_sequence = 4,
        int:v_dip_on_increasing_sequence = 5,
        int:initial_state_dip_on_increasing_sequence = s_dip_on_increasing_sequence,
        int:nb_of_states_dip_on_increasing_sequence = 5,
        array[1..nb_of_states_dip_on_increasing_sequence*3,1..nb_transition_params] of 
              int: Transitions_dip_on_increasing_sequence= 
                          [| s_dip_on_increasing_sequence, greater, s_dip_on_increasing_sequence, not_in, 
                           | s_dip_on_increasing_sequence, equal, s_dip_on_increasing_sequence, not_in, 
                           | s_dip_on_increasing_sequence, smaller, r_dip_on_increasing_sequence, not_in, 
                           | r_dip_on_increasing_sequence, greater, s_dip_on_increasing_sequence, not_in, 
                           | r_dip_on_increasing_sequence, equal, s_dip_on_increasing_sequence, not_in, 
                           | r_dip_on_increasing_sequence, smaller, t_dip_on_increasing_sequence, not_in, 
                           | t_dip_on_increasing_sequence, smaller, t_dip_on_increasing_sequence, not_in, 
                           | t_dip_on_increasing_sequence, equal, s_dip_on_increasing_sequence, not_in, 
                           | t_dip_on_increasing_sequence, greater, u_dip_on_increasing_sequence, maybe_b, 
                           | u_dip_on_increasing_sequence, greater, s_dip_on_increasing_sequence, not_in_r, 
                           | u_dip_on_increasing_sequence, equal, s_dip_on_increasing_sequence, not_in_r, 
                           | u_dip_on_increasing_sequence, smaller, v_dip_on_increasing_sequence, maybe_b, 
                           | v_dip_on_increasing_sequence, greater, s_dip_on_increasing_sequence, not_in_r, 
                           | v_dip_on_increasing_sequence, equal, s_dip_on_increasing_sequence, not_in_r, 
                           | v_dip_on_increasing_sequence, smaller, t_dip_on_increasing_sequence, found_end, 
                           |],
         
        %gorge
        int:after_gorge = 1,
        int:s_gorge = 1,
        int:r_gorge = 2,
        int:t_gorge = 3,
        int:u_gorge = 4,
        int:initial_state_gorge = s_gorge,
        int:nb_of_states_gorge = 4,
        array[1..nb_of_states_gorge*3,1..nb_transition_params] of int:Transitions_gorge =  
                            [| s_gorge, smaller, s_gorge, not_in, 
                             | s_gorge, equal, s_gorge, not_in, 
                             | s_gorge, greater, r_gorge, not_in, 
                             | r_gorge, greater, r_gorge, maybe_b, 
                             | r_gorge, smaller, t_gorge, found, 
                             | r_gorge, equal, u_gorge, maybe_b, 
                             | t_gorge, equal, t_gorge, maybe_a, 
                             | t_gorge, smaller, t_gorge, in_p, 
                             | t_gorge, greater, r_gorge, not_in_a, 
                             | u_gorge, equal, u_gorge, maybe_b, 
                             | u_gorge, greater, r_gorge, maybe_b, 
                             | u_gorge, smaller, s_gorge, not_in_r, 
                             |],
         
        %increasing
        int:after_increasing = 0,
        int:s_increasing = 1,
        int:initial_state_increasing = s_increasing,
        int:nb_of_states_increasing = 1,
        array[1..nb_of_states_increasing*3,1..nb_transition_params] of int:Transitions_increasing = 
                                 [| s_increasing, greater, s_increasing, not_in, 
                                  | s_increasing, equal, s_increasing, not_in, 
                                  | s_increasing, smaller, s_increasing, found_end, 
                                  |],
         
        %increasing_sequence
        int:after_increasing_sequence = 0,
        int:s_increasing_sequence = 1,
        int:t_increasing_sequence = 2,
        int:initial_state_increasing_sequence = s_increasing_sequence,
        int:nb_of_states_increasing_sequence = 2,
        array[1..nb_of_states_increasing_sequence*3,1..nb_transition_params] of int:Transitions_increasing_sequence =
                                          [| s_increasing_sequence, greater, s_increasing_sequence, not_in, 
                                           | s_increasing_sequence, equal, s_increasing_sequence, not_in, 
                                           | s_increasing_sequence, smaller, t_increasing_sequence, found, 
                                           | t_increasing_sequence, greater, s_increasing_sequence, not_in_a, 
                                           | t_increasing_sequence, equal, t_increasing_sequence, maybe_a, 
                                           | t_increasing_sequence, smaller, t_increasing_sequence, in_p, 
                                           |],
         
        %increasing_terrace
        int:after_increasing_terrace = 1,
        int:s_increasing_terrace = 1,
        int:r_increasing_terrace = 2,
        int:t_increasing_terrace = 3,
        int:initial_state_increasing_terrace = s_increasing_terrace,
        int:nb_of_states_increasing_terrace = 3,
        array[1..nb_of_states_increasing_terrace*3,1..nb_transition_params] of int:Transitions_increasing_terrace =
                                         [| s_increasing_terrace, greater, s_increasing_terrace, not_in, 
                                          | s_increasing_terrace, equal, s_increasing_terrace, not_in, 
                                          | s_increasing_terrace, smaller, r_increasing_terrace, not_in, 
                                          | r_increasing_terrace, greater, s_increasing_terrace, not_in, 
                                          | r_increasing_terrace, equal, t_increasing_terrace, maybe_b, 
                                          | r_increasing_terrace, smaller, r_increasing_terrace, not_in, 
                                          | t_increasing_terrace, greater, s_increasing_terrace, not_in_r, 
                                          | t_increasing_terrace, equal, t_increasing_terrace, maybe_b, 
                                          | t_increasing_terrace, smaller, r_increasing_terrace, found_end, 
                                          |],
         
        %inflexion
        int:after_inflexion = 1,
        int:s_inflexion = 1,
        int:r_inflexion = 2,
        int:t_inflexion = 3,
        int:initial_state_inflexion = s_inflexion,
        int:nb_of_states_inflexion = 3,
        array[1..nb_of_states_inflexion*3,1..nb_transition_params] of int: Transitions_inflexion =  
                                [| s_inflexion, greater, t_inflexion, not_in, 
                                 | s_inflexion, equal, s_inflexion, not_in, 
                                 | s_inflexion, smaller, r_inflexion, not_in, 
                                 | r_inflexion, greater, t_inflexion, found_end, 
                                 | r_inflexion, smaller, r_inflexion, maybe_b, 
                                 | r_inflexion, equal, r_inflexion, maybe_b, 
                                 | t_inflexion, greater, t_inflexion, maybe_b, 
                                 | t_inflexion, equal, t_inflexion, maybe_b, 
                                 | t_inflexion, smaller, r_inflexion, found_end, 
                                 |],
         
        %peak
        int:after_peak = 1,
        int:s_peak = 1,
        int:r_peak = 2,
        int:t_peak = 3,
        int:initial_state_peak = s_peak,
        int:nb_of_states_peak = 3,
        array[1..nb_of_states_peak*3,1..nb_transition_params] of int:Transitions_peak = 
                           [| s_peak, greater, s_peak, not_in, 
                            | s_peak, equal, s_peak, not_in, 
                            | s_peak, smaller, r_peak, not_in, 
                            | r_peak, greater, t_peak, found, 
                            | r_peak, smaller, r_peak, maybe_b, 
                            | r_peak, equal, r_peak, maybe_b, 
                            | t_peak, greater, t_peak, in_p, 
                            | t_peak, equal, t_peak, maybe_a, 
                            | t_peak, smaller, r_peak, not_in_a, 
                            |],
         
        %plain
        int:after_plain = 1,
        int:s_plain = 1,
        int:r_plain = 2,
        int:t_plain = 3,
        int:initial_state_plain = s_plain,
        int:nb_of_states_plain = 3,
        array[1..nb_of_states_plain*3,1..nb_transition_params] of int:Transitions_plain = 
                            [| s_plain, smaller, s_plain, not_in, 
                             | s_plain, equal, s_plain, not_in, 
                             | s_plain, greater, r_plain, not_in, 
                             | r_plain, greater, r_plain, not_in, 
                             | r_plain, equal, t_plain, maybe_b, 
                             | r_plain, smaller, s_plain, found_end, 
                             | t_plain, greater, r_plain, not_in_r, 
                             | t_plain, equal, t_plain, maybe_b, 
                             | t_plain, smaller, s_plain, found_end, 
                             |],
         
        %plateau
        int:after_plateau = 1,
        int:s_plateau = 1,
        int:r_plateau = 2,
        int:t_plateau = 3,
        int:initial_state_plateau = s_plateau,
        int:nb_of_states_plateau = 3,
        array[1..nb_of_states_plateau*3,1..nb_transition_params] of int:Transitions_plateau =  
                              [| s_plateau, greater, s_plateau, not_in, 
                               | s_plateau, equal, s_plateau, not_in, 
                               | s_plateau, smaller, r_plateau, not_in, 
                               | r_plateau, smaller, r_plateau, not_in, 
                               | r_plateau, equal, t_plateau, maybe_b, 
                               | r_plateau, greater, s_plateau, found_end, 
                               | t_plateau, smaller, r_plateau, not_in_r, 
                               | t_plateau, equal, t_plateau, maybe_b, 
                               | t_plateau, greater, s_plateau, found_end, 
                               |],
         
        %proper_plain
        int:after_proper_plain = 1,
        int:s_proper_plain = 1,
        int:r_proper_plain = 2,
        int:t_proper_plain = 3,
        int:initial_state_proper_plain = s_proper_plain,
        int:nb_of_states_proper_plain = 3,
        array[1..nb_of_states_proper_plain*3,1..nb_transition_params] of int:Transitions_proper_plain =  
                                   [| s_proper_plain, greater, r_proper_plain, not_in, 
                                    | s_proper_plain, smaller, s_proper_plain, not_in, 
                                    | s_proper_plain, equal, s_proper_plain, not_in, 
                                    | r_proper_plain, greater, r_proper_plain, not_in, 
                                    | r_proper_plain, equal, t_proper_plain, maybe_b, 
                                    | r_proper_plain, smaller, s_proper_plain, not_in, 
                                    | t_proper_plain, greater, r_proper_plain, not_in_r, 
                                    | t_proper_plain, equal, t_proper_plain, maybe_b, 
                                    | t_proper_plain, smaller, s_proper_plain, found_end, 
                                    |],
         
        %proper_plateau
        int:after_proper_plateau = 1,
        int:s_proper_plateau = 1,
        int:r_proper_plateau = 2,
        int:t_proper_plateau = 3,
        int:initial_state_proper_plateau = s_proper_plateau,
        int:nb_of_states_proper_plateau = 3,
        array[1..nb_of_states_proper_plateau*3,1..nb_transition_params] of int:Transitions_proper_plateau = 
                                     [| s_proper_plateau, greater, s_proper_plateau, not_in, 
                                      | s_proper_plateau, equal, s_proper_plateau, not_in, 
                                      | s_proper_plateau, smaller, r_proper_plateau, not_in, 
                                      | r_proper_plateau, greater, s_proper_plateau, not_in, 
                                      | r_proper_plateau, equal, t_proper_plateau, maybe_b, 
                                      | r_proper_plateau, smaller, r_proper_plateau, not_in, 
                                      | t_proper_plateau, greater, s_proper_plateau, found_end, 
                                      | t_proper_plateau, equal, t_proper_plateau, maybe_b, 
                                      | t_proper_plateau, smaller, r_proper_plateau, not_in_r, 
                                      |],
         
        %steady
        int:after_steady = 0,
        int:s_steady = 1,
        int:initial_state_steady = s_steady,
        int:nb_of_states_steady = 1,
        array[1..nb_of_states_steady*3,1..nb_transition_params] of int:Transitions_steady = 
                             [| s_steady, smaller, s_steady, not_in, 
                              | s_steady, greater, s_steady, not_in, 
                              | s_steady, equal, s_steady, found_end, 
                              |],
         
        %steady_sequence
        int:after_steady_sequence = 0,
        int:s_steady_sequence = 1,
        int:t_steady_sequence = 2,
        int:initial_state_steady_sequence = s_steady_sequence,
        int:nb_of_states_steady_sequence = 2,
        array[1..nb_of_states_steady_sequence*3,1..nb_transition_params] of int:Transitions_steady_sequence =  
                                      [| s_steady_sequence, smaller, s_steady_sequence, not_in, 
                                       | s_steady_sequence, greater, s_steady_sequence, not_in, 
                                       | s_steady_sequence, equal, t_steady_sequence, found, 
                                       | t_steady_sequence, smaller, s_steady_sequence, not_in_a, 
                                       | t_steady_sequence, greater, s_steady_sequence, not_in_a, 
                                       | t_steady_sequence, equal, t_steady_sequence, in_p, 
                                       |],
         
        %strictly_decreasing_sequence
        int:after_strictly_decreasing_sequence = 0,
        int:s_strictly_decreasing_sequence = 1,
        int:t_strictly_decreasing_sequence = 2,
        int:initial_state_strictly_decreasing_sequence = s_strictly_decreasing_sequence,
        int:nb_of_states_strictly_decreasing_sequence = 2,
        array[1..nb_of_states_strictly_decreasing_sequence*3,1..nb_transition_params] of 
              int: Transitions_strictly_decreasing_sequence =
                      [| s_strictly_decreasing_sequence, greater, t_strictly_decreasing_sequence, found, 
                       | s_strictly_decreasing_sequence, smaller, s_strictly_decreasing_sequence, not_in, 
                       | s_strictly_decreasing_sequence, equal, s_strictly_decreasing_sequence, not_in, 
                       | t_strictly_decreasing_sequence, greater, t_strictly_decreasing_sequence, in_p, 
                       | t_strictly_decreasing_sequence, smaller, s_strictly_decreasing_sequence, not_in_a, 
                       | t_strictly_decreasing_sequence, equal, s_strictly_decreasing_sequence, not_in_a, 
                       |],
         
        %strictly_increasing_sequence
        int:after_strictly_increasing_sequence = 0,
        int:s_strictly_increasing_sequence = 1,
        int:t_strictly_increasing_sequence = 2,
        int:initial_state_strictly_increasing_sequence = s_strictly_increasing_sequence,
        int:nb_of_states_strictly_increasing_sequence = 2,
        array[1..nb_of_states_strictly_increasing_sequence*3,1..nb_transition_params] of 
                  int: Transitions_strictly_increasing_sequence = 
                 [| s_strictly_increasing_sequence, greater, s_strictly_increasing_sequence, not_in, 
                  | s_strictly_increasing_sequence, equal, s_strictly_increasing_sequence, not_in, 
                  | s_strictly_increasing_sequence, smaller, t_strictly_increasing_sequence, found, 
                  | t_strictly_increasing_sequence, greater, s_strictly_increasing_sequence, not_in_a, 
                  | t_strictly_increasing_sequence, equal, s_strictly_increasing_sequence, not_in_a, 
                  | t_strictly_increasing_sequence, smaller, t_strictly_increasing_sequence, in_p, 
                  |],
         
        %summit
        int:after_summit = 1,
        int:s_summit = 1,
        int:r_summit = 2,
        int:t_summit = 3,
        int:u_summit = 4,
        int:initial_state_summit = s_summit,
        int:nb_of_states_summit = 4,
        array[1..nb_of_states_summit*3,1..nb_transition_params] of int:Transitions_summit =  
                             [| s_summit, greater, s_summit, not_in, 
                              | s_summit, equal, s_summit, not_in, 
                              | s_summit, smaller, r_summit, not_in, 
                              | r_summit, smaller, r_summit, maybe_b, 
                              | r_summit, greater, t_summit, found, 
                              | r_summit, equal, u_summit, maybe_b, 
                              | t_summit, equal, t_summit, maybe_a, 
                              | t_summit, greater, t_summit, in_p, 
                              | t_summit, smaller, r_summit, not_in_a, 
                              | u_summit, equal, u_summit, maybe_b, 
                              | u_summit, smaller, r_summit, maybe_b, 
                              | u_summit, greater, s_summit, not_in_r, 
                              |],
         
        %valley
        int:after_valley = 1,
        int:s_valley = 1,
        int:r_valley = 2,
        int:t_valley = 3,
        int:initial_state_valley = s_valley,
        int:nb_of_states_valley = 3,
        array[1..nb_of_states_valley*3,1..nb_transition_params] of int:Transitions_valley = 
                             [| s_valley, greater, r_valley, not_in, 
                              | s_valley, smaller, s_valley, not_in, 
                              | s_valley, equal, s_valley, not_in, 
                              | r_valley, greater, r_valley, maybe_b, 
                              | r_valley, equal, r_valley, maybe_b, 
                              | r_valley, smaller, t_valley, found, 
                              | t_valley, greater, r_valley, not_in_a, 
                              | t_valley, equal, t_valley, maybe_a, 
                              | t_valley, smaller, t_valley, in_p, 
                              |],
         
        %zigzag
        int:after_zigzag = 1,
        int:s_zigzag = 1,
        int:a_zigzag = 2,
        int:b_zigzag = 3,
        int:c_zigzag = 4,
        int:d_zigzag = 5,
        int:e_zigzag = 6,
        int:f_zigzag = 7,
        int:g_zigzag = 8,
        int:h_zigzag = 9,
        int:initial_state_zigzag = s_zigzag,
        int:nb_of_states_zigzag = 9,
        array[1..nb_of_states_zigzag*3,1..nb_transition_params] of int:Transitions_zigzag = 
                             [| s_zigzag, greater, e_zigzag, not_in, 
                              | s_zigzag, equal, s_zigzag, not_in, 
                              | s_zigzag, smaller, a_zigzag, not_in, 
                              | a_zigzag, greater, b_zigzag, maybe_b, 
                              | a_zigzag, equal, s_zigzag, not_in, 
                              | a_zigzag, smaller, a_zigzag, not_in, 
                              | b_zigzag, greater, e_zigzag, not_in_r, 
                              | b_zigzag, equal, s_zigzag, not_in_r, 
                              | b_zigzag, smaller, c_zigzag, found, 
                              | c_zigzag, greater, d_zigzag, in_p, 
                              | c_zigzag, equal, s_zigzag, not_in_a, 
                              | c_zigzag, smaller, a_zigzag, not_in_a, 
                              | d_zigzag, greater, e_zigzag, not_in_a, 
                              | d_zigzag, equal, s_zigzag, not_in_a, 
                              | d_zigzag, smaller, c_zigzag, in_p, 
                              | e_zigzag, greater, e_zigzag, not_in, 
                              | e_zigzag, equal, s_zigzag, not_in, 
                              | e_zigzag, smaller, f_zigzag, maybe_b, 
                              | f_zigzag, greater, g_zigzag, found, 
                              | f_zigzag, equal, s_zigzag, not_in_r, 
                              | f_zigzag, smaller, a_zigzag, not_in_r, 
                              | g_zigzag, greater, e_zigzag, not_in_a, 
                              | g_zigzag, equal, s_zigzag, not_in_a, 
                              | g_zigzag, smaller, h_zigzag, in_p, 
                              | h_zigzag, greater, g_zigzag, in_p, 
                              | h_zigzag, equal, s_zigzag, not_in_a, 
                              | h_zigzag, smaller, a_zigzag, not_in_a, 
                              |]
        
    } in 
      if pattern = "bump_on_decreasing_sequence" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_bump_on_decreasing_sequence,
                                    initial_state_bump_on_decreasing_sequence,
                                    Transitions_bump_on_decreasing_sequence,
                                    after_bump_on_decreasing_sequence,
                                    aggregator,
                                    feature) 
     elseif pattern = "decreasing" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_decreasing,
                                    initial_state_decreasing,
                                    Transitions_decreasing,
                                    after_decreasing,
                                    aggregator,
                                    feature)  
    elseif pattern = "decreasing_sequence" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_decreasing_sequence,
                                    initial_state_decreasing_sequence,
                                    Transitions_decreasing_sequence,
                                    after_decreasing_sequence,
                                    aggregator,
                                    feature) 
    elseif pattern = "decreasing_terrace" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_decreasing_terrace,
                                    initial_state_decreasing_terrace,
                                    Transitions_decreasing_terrace,
                                    after_decreasing_terrace,
                                    aggregator,
                                    feature)   
    elseif pattern = "dip_on_increasing_sequence" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_dip_on_increasing_sequence,
                                    initial_state_dip_on_increasing_sequence,
                                    Transitions_dip_on_increasing_sequence,
                                    after_dip_on_increasing_sequence,
                                    aggregator,
                                    feature)   
    elseif pattern = "gorge" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_gorge,
                                    initial_state_gorge,
                                    Transitions_gorge,
                                    after_gorge,
                                    aggregator,
                                    feature) 
    elseif pattern = "increasing" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_increasing,
                                    initial_state_increasing,
                                    Transitions_increasing,
                                    after_increasing,
                                    aggregator,
                                    feature) 
    elseif pattern = "increasing_sequence" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_increasing_sequence,
                                    initial_state_increasing_sequence,
                                    Transitions_increasing_sequence,
                                    after_increasing_sequence,
                                    aggregator,
                                    feature)  
    elseif pattern = "increasing_terrace" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_increasing_terrace,
                                    initial_state_increasing_terrace,
                                    Transitions_increasing_terrace,
                                    after_increasing_terrace,
                                    aggregator,
                                    feature)  
     elseif pattern = "inflexion" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_inflexion,
                                    initial_state_inflexion,
                                    Transitions_inflexion,
                                    after_inflexion,
                                    aggregator,
                                    feature)  
     elseif pattern = "peak" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_peak,
                                    initial_state_peak,
                                    Transitions_peak,
                                    after_peak,
                                    aggregator,
                                    feature) 
     elseif pattern = "plain" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_plain,
                                    initial_state_plain,
                                    Transitions_plain,
                                    after_plain,
                                    aggregator,
                                    feature)  
    elseif pattern = "plateau" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_plateau,
                                    initial_state_plateau,
                                    Transitions_plateau,
                                    after_plateau,
                                    aggregator,
                                    feature)  
     elseif pattern = "proper_plain" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_proper_plain,
                                    initial_state_proper_plain,
                                    Transitions_proper_plain,
                                    after_proper_plain,
                                    aggregator,
                                    feature)  
    elseif pattern = "proper_plateau" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_proper_plateau,
                                    initial_state_proper_plateau,
                                    Transitions_proper_plateau,
                                    after_proper_plateau,
                                    aggregator,
                                    feature)  
    elseif pattern = "steady" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_steady,
                                    initial_state_steady,
                                    Transitions_steady,
                                    after_steady,
                                    aggregator,
                                    feature)  
    elseif pattern = "steady_sequence" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_steady_sequence,
                                    initial_state_steady_sequence,
                                    Transitions_steady_sequence,
                                    after_steady_sequence,
                                    aggregator,
                                    feature)  
    elseif pattern = "strictly_decreasing_sequence" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_strictly_decreasing_sequence,
                                    initial_state_strictly_decreasing_sequence,
                                    Transitions_strictly_decreasing_sequence,
                                    after_strictly_decreasing_sequence,
                                    aggregator,
                                    feature)  
    elseif pattern = "strictly_increasing_sequence" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_strictly_increasing_sequence,
                                    initial_state_strictly_increasing_sequence,
                                    Transitions_strictly_increasing_sequence,
                                    after_strictly_increasing_sequence,
                                    aggregator,
                                    feature) 
    elseif pattern = "summit" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_summit,
                                    initial_state_summit,
                                    Transitions_summit,
                                    after_summit,
                                    aggregator,
                                    feature)  
     elseif pattern = "valley" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_valley,
                                    initial_state_valley,
                                    Transitions_valley,
                                    after_valley,
                                    aggregator,
                                    feature)  
    elseif pattern = "zigzag" then 
      impose_time_series_constraint(x,
                                    P,
                                    result,
                                    nb_of_states_zigzag,
                                    initial_state_zigzag,
                                    Transitions_zigzag,
                                    after_zigzag,
                                    aggregator,
                                    feature)  
    else false endif; 

predicate impose_time_series_constraint(array[int] of var int: X,
                                        array[int] of var int: P,
                                                      var int: result, 
                                                          int: nb_of_states,
                                                          int: initial_state,
                                        array[int,int] of int: Transitions,
                                                          int: after,
                                                       string: aggregator,
                                                       string: feature) =
   let{ 
      %length of time series
      int: time_series_length = length(X),
   
      %infinities 
      int: plus_infinity          =  ub_array(X) + 1,
      int: minus_infinity         =  lb_array(X) - 1,
      int: plus_infinity_range    =  max(0,max(ub_array(X), ub_array(X) - lb_array(X))) + 1,
      int: minus_infinity_range   =  min(0,lb_array(X)) - 1,
      int: plus_infinity_range_s  =  max(0,max(ub_array(X), ub_array(X) - lb_array(X)))*time_series_length + 1,
      int: minus_infinity_range_s =  min(0,min(lb_array(X), lb_array(X) - ub_array(X)))*time_series_length - 1,
      int: plus_infinity_s        =  2*(max(0,plus_infinity*time_series_length) + 1),
      int: minus_infinity_s       =  2*(min(0,minus_infinity*time_series_length)- 1),

      %input and output alphabet power
      int: nb_of_input_letters      = 3, 
      int: nb_of_output_letters     = 8, 

      %transition parameters  
      int: current_state            = 1,
      int: input_symbol             = 2,
      int: next_state               = 3,
      int: output_symbol            = 4,
 
      %used ranges   
      set of int: TimeSeriesRange   = 1..time_series_length,
      set of int: SignatureRange    = 1..time_series_length - 1,
      set of int: TransitionsRange  = 1..nb_of_states*nb_of_input_letters,
      
      %signature variables
      int: smaller              = smaller(),
      int: equal                = equal(),
      int: greater              = greater(),
      array[SignatureRange] of var 1..nb_of_input_letters: S,
    
      %state variables
      array[TimeSeriesRange] of var 1..nb_of_states: Q,
    
      %semantic variables
      array[SignatureRange] of var 1..nb_of_output_letters: Sem
     
    } in

      Q[1] = initial_state /\

     %impose signature constraints
      forall(i in SignatureRange) (
             (X[i] < X[i+1]) /\ (S[i] = smaller)  \/ 
             (X[i] = X[i+1]) /\ (S[i] = equal)    \/  
             (X[i] > X[i+1]) /\ (S[i] = greater)) /\
      forall(i in SignatureRange, j in TransitionsRange) (
              (Q[i]  != Transitions[j,current_state] \/ S[i]  != Transitions[j,input_symbol])  \/
               Q[i+1] = Transitions[j,next_state]    /\ Sem[i] = Transitions[j,output_symbol])  /\
      
     %encode accumulator updates 
     if aggregator = "max" /\ feature = "max" then 
                    impose_accumulator_updates(aggregator, feature, after, Sem, X, 
                                              result, minus_infinity, minus_infinity, plus_infinity, minus_infinity)
     elseif aggregator = "max" /\ (feature = "min" \/ feature = "height") then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X,
                                              result, minus_infinity, plus_infinity, plus_infinity, minus_infinity)
     elseif aggregator = "max" /\ feature = "max" then 
                    impose_accumulator_updates(aggregator, feature, after, Sem, X,
                                               result, minus_infinity, minus_infinity, plus_infinity, minus_infinity)
     elseif aggregator = "max" /\ feature = "surf"then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X,
                                               result, minus_infinity_s, 0, plus_infinity_s, minus_infinity_s)
     elseif aggregator = "max" /\ feature = "width" then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X,
                                               result, 0, 0, time_series_length + 1, 0)
     elseif aggregator = "min" /\ feature = "max" then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X, 
                                              result, plus_infinity, minus_infinity, plus_infinity, minus_infinity)
     elseif aggregator = "min" /\ (feature = "min" \/ feature = "height") then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X,
                                               result, plus_infinity, plus_infinity, plus_infinity, minus_infinity)
     elseif aggregator = "min" /\ feature = "surf" then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X, 
                                               result, plus_infinity_s, 0, plus_infinity_s, minus_infinity_s)
     elseif aggregator = "min" /\ feature = "width" then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X,
                                               result, time_series_length + 1, 0, time_series_length + 1, 0)
     elseif aggregator = "sum" /\ feature = "max" then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X, 
                                               result, 0, minus_infinity, plus_infinity_s, minus_infinity_s)
     elseif aggregator = "sum" /\ (feature = "min" \/ feature = "height") then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X,
                                               result, 0, plus_infinity, plus_infinity_s, minus_infinity_s)
     elseif aggregator = "sum" /\ feature = "one" then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X, 
                                               result, 0, 0, time_series_length, 0)
     elseif aggregator = "sum" /\ feature = "surf" then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X,
                                               result, 0, 0, plus_infinity_s, minus_infinity_s)
     elseif aggregator = "sum" /\ feature = "width" then
                    impose_accumulator_updates(aggregator, feature, after, Sem, X, 
                                              result, 0, 0, time_series_length*2, 0)
     elseif aggregator = "max" /\ feature = "range" then
                    impose_accumulator_updates_range(aggregator, Sem, X, 
                                                     result, 0, plus_infinity_range, minus_infinity_range)
     elseif aggregator = "min" /\ feature = "range" then
                    impose_accumulator_updates_range(aggregator, Sem, X, 
                                                     result, plus_infinity_range, plus_infinity_range, minus_infinity_range)
     elseif aggregator = "sum" /\ feature = "range" then
                    impose_accumulator_updates_range(aggregator, Sem, X, 
                                                    result, 0, plus_infinity_range_s, minus_infinity_range_s)
     elseif aggregator = "all_equal" /\ feature = "max" then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X, 
                                                      plus_infinity, minus_infinity, plus_infinity, minus_infinity)
     elseif aggregator = "all_equal" /\ (feature = "min" \/ feature = "height") then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X,
                                                      plus_infinity, plus_infinity, plus_infinity, minus_infinity)
     elseif aggregator = "all_equal" /\ feature = "surf" then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X, 
                                                     plus_infinity, 0, plus_infinity_s, minus_infinity_s)
     elseif aggregator = "all_equal" /\ feature = "width" then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X,
                                                    time_series_length + 1, 0, time_series_length + 1, 0)
     elseif aggregator = "all_equal" /\ feature = "range" then
                    impose_accumulator_updates_predicate_range(aggregator, Sem, X, 
                                                                plus_infinity_range, minus_infinity_range)
     elseif aggregator = "decreasing" /\ feature = "max" then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X, 
                                                   plus_infinity, minus_infinity, plus_infinity, minus_infinity)
     elseif aggregator = "decreasing" /\ (feature = "min" \/ feature = "height") then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X,
                                                    plus_infinity, plus_infinity, plus_infinity, minus_infinity)
     elseif aggregator = "decreasing" /\ feature = "surf" then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X, 
                                                    plus_infinity, 0, plus_infinity_s, minus_infinity_s)
     elseif aggregator = "decreasing" /\ feature = "width" then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X,
                                                    time_series_length + 1, 0, time_series_length + 1, 0)
     elseif aggregator = "decreasing" /\ feature = "range" then
                    impose_accumulator_updates_predicate_range(aggregator, Sem, X, 
                                                            plus_infinity_range, minus_infinity_range)
     elseif aggregator = "increasing" /\ feature = "max" then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X, 
                                                   plus_infinity, minus_infinity, plus_infinity, minus_infinity)
     elseif aggregator = "increasing" /\ (feature = "min" \/ feature = "height") then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X,
                                                   plus_infinity, plus_infinity, plus_infinity, minus_infinity)
     elseif aggregator = "increasing" /\ feature = "surf" then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X, 
                                                   plus_infinity, 0, plus_infinity_s, minus_infinity_s)
     elseif aggregator = "increasing" /\ feature = "width" then
                    impose_accumulator_updates_predicate(aggregator, feature, after, Sem, X,
                                                  time_series_length + 1, 0, time_series_length + 1, 0)
     elseif aggregator = "increasing" /\ feature = "range" then
                    impose_accumulator_updates_predicate_range(aggregator, Sem, X,
                                                   plus_infinity_range, minus_infinity_range)
     elseif aggregator = "footprint"                       then
                   impose_accumulator_updates_footprint(Sem, P, time_series_length)
     else false endif ;

%pseudo macros
function int: smaller() = 1; 
function int: equal()   = 2; 
function int: greater() = 3;

function int: not_in()    = 1; 
function int: not_in_r()  = 2; 
function int: not_in_a()  = 3; 
function int: maybe_b()   = 4;
function int: found()     = 5; 
function int: found_end() = 6; 
function int: maybe_a()   = 7;
function int: in_p()      = 8;

%accumulator updates
predicate impose_accumulator_updates(string: aggregator, 
                                     string: feature, 
                                        int: after, 
                      array[int] of var int: Sem, 
                      array[int] of var int: X, 
                                    var int: result,
                                        int: default_g, 
                                        int: neutral,
                                        int: plus_infinity,
                                        int: minus_infinity) =
  let{
       int: not_in    = not_in(), 
       int: not_in_r  = not_in_r(), 
       int: not_in_a  = not_in_a(),
       int: maybe_b   = maybe_b(),
       int: found     = found(), 
       int: found_end = found_end(), 
       int: maybe_a   = maybe_a(),
       int: in_p      = in_p(),
      
      int: time_series_length     = length(X),
      set of int: TimeSeriesRange = 1..time_series_length,
      set of int: SignatureRange  = 1..time_series_length-1,

      %accumulator variables
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: C, %% domains ?
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: D, %% domains ?
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: R, %% domains ?
      
      %variables necessary for encoding accumulator updates      
      array[SignatureRange] of var minus_infinity..plus_infinity: Delta,
      array[SignatureRange] of var minus_infinity..plus_infinity: DeltaPrime,
      array[SignatureRange] of var minus_infinity..plus_infinity: FeatureTmpVars,
      array[SignatureRange] of var minus_infinity..plus_infinity: AggrTmpVars
      
  } in
    % accumulator initialisation 
    C[1] = default_g /\
    D[1] = neutral   /\
    R[1] = default_g /\

    % accumulator update
    forall(j in SignatureRange) (
  
          delta(feature,X[j], Delta[j]) /\ delta_prime(feature, after, X[j], X[j+1], DeltaPrime[j]) /\

          (Sem[j] != not_in    \/   C[j+1] = C[j]                     /\ 
                                    D[j+1] = D[j]                     /\ 
                                    R[j+1] = R[j]                     /\
                                    FeatureTmpVars[j] = plus_infinity /\
                                    AggrTmpVars[j] = plus_infinity)   /\

          (Sem[j] != not_in_r  \/   C[j+1] = C[j]                     /\ 
                                    D[j+1] = neutral                  /\ 
                                    R[j+1] = R[j]                     /\
                                    FeatureTmpVars[j] = plus_infinity /\
                                    AggrTmpVars[j] = plus_infinity)   /\

          (Sem[j] != not_in_a  \/   C[j+1] = default_g                         /\
                                    D[j+1] = neutral                           /\ 
                                    aggregate(aggregator, R[j+1], R[j], C[j])  /\
                                    FeatureTmpVars[j] = plus_infinity          /\
                                    AggrTmpVars[j] = plus_infinity)            /\

          (Sem[j] != maybe_b   \/   C[j+1] = C[j]                                     /\     
                                    compute_feature(feature, D[j+1], D[j], Delta[j])  /\
                                    R[j+1] = R[j]                                     /\
                                    FeatureTmpVars[j] = plus_infinity                 /\
                                    AggrTmpVars[j] = plus_infinity)                   /\

          (Sem[j] != maybe_a   \/   C[j+1] = C[j]                                         /\     
                                    compute_feature(feature, D[j+1], D[j], DeltaPrime[j]) /\
                                    R[j+1] = R[j]                                         /\
                                    FeatureTmpVars[j] = plus_infinity                     /\
                                    AggrTmpVars[j] = plus_infinity)                       /\

          (Sem[j] != found     \/   compute_feature2(after,feature, C[j+1],D[j],Delta[j], 
                                                     DeltaPrime[j],FeatureTmpVars[j])     /\
                                    D[j+1] = neutral                                      /\
                                    R[j+1] = R[j]                                         /\
                                    AggrTmpVars[j] = plus_infinity)                       /\

          (Sem[j] != in_p      \/  compute_feature2(0,feature, C[j+1],C[j],D[j], 
                                                    DeltaPrime[j],FeatureTmpVars[j])      /\
                                   D[j+1] = neutral                                       /\
                                   R[j+1] = R[j]                                          /\
                                   AggrTmpVars[j] = plus_infinity)                        /\

          (Sem[j] != found_end \/  C[j+1] = C[j]                                                  /\     
                                   D[j+1] = neutral                                               /\
                                   aggregate2(after, feature, aggregator, R[j+1], R[j], D[j], Delta[j],
                                               DeltaPrime[j],FeatureTmpVars[j], AggrTmpVars[j]))) /\
     
     % action on return
     aggregate(aggregator, result, R[time_series_length], C[time_series_length]);

%accumulator updates when feature being range
predicate impose_accumulator_updates_range(string: aggregator, 
                            array[int] of var int: Sem, 
                            array[int] of var int: X, 
                                          var int: result,
                                              int: default_g,
                                              int: plus_infinity,
                                              int: minus_infinity) =
  let{
       int: not_in    = not_in(), 
       int: not_in_r  = not_in_r(), 
       int: not_in_a  = not_in_a(),
       int: maybe_b   = maybe_b(),
       int: found     = found(), 
       int: found_end = found_end(), 
       int: maybe_a   = maybe_a(),
       int: in_p      = in_p(),
      
      int: time_series_length     = length(X),    
      set of int: TimeSeriesRange = 1..time_series_length,
      set of int: SignatureRange  = 1..time_series_length-1,

      %accumulator variables
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: C, %% domains ?
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: H, %% domains ?
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: R, %% domains ?
      
      %variables necessary for encoding accumulator updates       
      array[SignatureRange] of var minus_infinity..plus_infinity: AggrTempVars
      
  } in
    % accumulator initialisation 
    C[1] = default_g /\
    H[1] = X[1]      /\
    R[1] = default_g /\

    % accumulator update
    forall(j in SignatureRange)(
          (Sem[j] != not_in    \/   C[j+1] = C[j]                     /\ 
                                    H[j+1] = X[j+1]                   /\ 
                                    R[j+1] = R[j]                     /\
                                    AggrTempVars[j] = plus_infinity)  /\
               
          (Sem[j] != not_in_r  \/   C[j+1] = C[j]                     /\ 
                                    H[j+1] = X[j+1]                   /\ 
                                    R[j+1] = R[j]                     /\
                                    AggrTempVars[j] = plus_infinity)  /\
              
          (Sem[j] != not_in_a  \/   C[j+1] = default_g                          /\ 
                                    H[j+1] = X[j+1]                             /\ 
                                    aggregate(aggregator, R[j+1], R[j], C[j])   /\
                                    AggrTempVars[j] = plus_infinity)            /\
              
          (Sem[j] != maybe_b   \/  C[j+1] = C[j]                     /\     
                                   H[j+1] = H[j]                     /\
                                   R[j+1] = R[j]                     /\
                                   AggrTempVars[j] = plus_infinity)  /\
            
          (Sem[j] != maybe_a   \/  C[j+1] = C[j]                     /\     
                                   H[j+1] = H[j]                     /\
                                   R[j+1] = R[j]                     /\
                                   AggrTempVars[j] = plus_infinity)  /\
            
          (Sem[j] != found_end \/  C[j+1] = C[j]                                         /\  
                                   H[j+1] = X[j+1]                                       /\
                                   AggrTempVars[j] = abs(H[j] - X[j+1])                  /\
                                   aggregate(aggregator, R[j+1], R[j], AggrTempVars[j])) /\
            
          (Sem[j] != in_p      \/  C[j+1] = abs(H[j] - X[j+1])       /\   
                                   H[j+1] = H[j]                     /\
                                   R[j+1] = R[j]                     /\
                                   AggrTempVars[j] = plus_infinity)  /\
            
          (Sem[j] != found     \/  C[j+1] = abs(H[j] - X[j+1])       /\   
                                   H[j+1] = H[j]                     /\
                                   R[j+1] = R[j]                     /\
                                   AggrTempVars[j] = plus_infinity)) /\
     
     % action on return
     aggregate(aggregator, result, R[time_series_length], C[time_series_length]);

%accumulator updates
predicate impose_accumulator_updates_predicate(string: predicate_name, 
                                               string: feature, 
                                                  int: after, 
                                array[int] of var int: Sem, 
                                array[int] of var int: X, 
                                                  int: default_theta, 
                                                  int: neutral,
                                                  int: plus_infinity,
                                                  int: minus_infinity) =
  let{
       int: not_in    = not_in(), 
       int: not_in_r  = not_in_r(), 
       int: not_in_a  = not_in_a(),
       int: maybe_b   = maybe_b(),
       int: found     = found(), 
       int: found_end = found_end(), 
       int: maybe_a   = maybe_a(),
       int: in_p      = in_p(),
      
      int: time_series_length     = length(X),
      set of int: TimeSeriesRange = 1..time_series_length,
      set of int: SignatureRange  = 1..time_series_length-1,

      %accumulator variables
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: C, %% domains ?
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: D, %% domains ?
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: F, %% domains ?
      array[TimeSeriesRange] of var bool: R, 
      
      %variables necessary for encoding accumulator updates      
      array[SignatureRange] of var minus_infinity..plus_infinity: Delta,
      array[SignatureRange] of var minus_infinity..plus_infinity: DeltaPrime,
      array[SignatureRange] of var minus_infinity..plus_infinity: FeatureTmpVars,
      
  } in
    % accumulator initialisation 
    C[1] = default_theta /\
    D[1] = neutral   /\
    %F[1] = default_theta   /\
    R[1] = true /\

    % accumulator update
    forall(j in SignatureRange) (
  
          delta(feature,X[j], Delta[j]) /\ delta_prime(feature, after, X[j], X[j+1], DeltaPrime[j]) /\

          (Sem[j] != not_in    \/   C[j+1] = C[j]                       /\ 
                                    D[j+1] = D[j]                       /\
                                    F[j+1] = F[j]                       /\  
                                    R[j+1] = R[j]                       /\
                                    FeatureTmpVars[j] = plus_infinity)  /\

          (Sem[j] != not_in_r  \/   C[j+1] = C[j]                       /\ 
                                    D[j+1] = neutral                    /\ 
                                    F[j+1] = F[j]                       /\ 
                                    R[j+1] = R[j]                       /\
                                    FeatureTmpVars[j] = plus_infinity)  /\

          (Sem[j] != not_in_a  \/   C[j+1] = C[j]                                           /\
                                    D[j+1] = neutral                                        /\ 
                                    F[j+1] = C[j]                                           /\ 
                                    (R[j+1] = (R[j] /\ theta(predicate_name, F[j],C[j])))   /\
                                    FeatureTmpVars[j] = plus_infinity)                      /\

          (Sem[j] != maybe_b   \/   C[j+1] = C[j]                                     /\     
                                    compute_feature(feature, D[j+1], D[j], Delta[j])  /\
                                    F[j+1] = F[j]                                     /\
                                    R[j+1] = R[j]                                     /\
                                    FeatureTmpVars[j] = plus_infinity)                /\ 

          (Sem[j] != maybe_a   \/   C[j+1] = C[j]                                         /\     
                                    compute_feature(feature, D[j+1], D[j], DeltaPrime[j]) /\
                                    F[j+1] = F[j]                                         /\
                                    R[j+1] = R[j]                                         /\
                                    FeatureTmpVars[j] = plus_infinity)                    /\

          (Sem[j] != found     \/   compute_feature2(after,feature, C[j+1],D[j],Delta[j], 
                                                     DeltaPrime[j],FeatureTmpVars[j])     /\
                                    D[j+1] = neutral                                      /\
                                    F[j+1] = F[j]                                         /\
                                    R[j+1] = R[j])                                        /\

          (Sem[j] != in_p      \/  compute_feature2(0,feature, C[j+1],C[j],D[j], 
                                                    DeltaPrime[j],FeatureTmpVars[j]) /\
                                   D[j+1] = neutral                                  /\
                                   F[j+1] = F[j]                                     /\
                                   R[j+1] = R[j])                                    /\

          (Sem[j] != found_end \/  compute_feature2(after,feature, C[j+1],D[j],Delta[j],
                                                     DeltaPrime[j],FeatureTmpVars[j])          /\     
                                   D[j+1] = neutral                                            /\
                                   F[j+1] = C[j+1]                                             /\
                                   (R[j+1] = (R[j]  /\ theta(predicate_name, F[j], C[j+1]))))) /\ 
     % action on return
     R[time_series_length] /\ theta(predicate_name, F[time_series_length], C[time_series_length]);

predicate impose_accumulator_updates_footprint(array[int] of var int: Sem, 
                                               array[int] of var int: P, 
                                                                 int: time_series_length) =
  let{
       int: not_in    = not_in(), 
       int: not_in_r  = not_in_r(), 
       int: not_in_a  = not_in_a(),
       int: maybe_b   = maybe_b(),
       int: found     = found(), 
       int: found_end = found_end(), 
       int: maybe_a   = maybe_a(),
       int: in_p      = in_p(),
      
       set of int: TimeSeriesRange = 1..time_series_length,
       set of int: SignatureRange  = 1..time_series_length-1,

      %accumulator variables
       array[TimeSeriesRange] of var 0..time_series_length: C, %% domains ? 
  } in
  
  % accumulator initialisation 
    C[1] = 0 /\
    P[time_series_length] = 0 /\
  
    
    % accumulator update
    forall(j in SignatureRange) (

          ((Sem[j] != not_in)    \/  (P[j] = 0)) /\
  
          (((Sem[j] != not_in)   \/  (P[j] != 0))        \/ (C[j+1] = C[j]))   /\
          
          ((Sem[j] != not_in)    \/  (P[j] = 0))  /\
                                  
          (((Sem[j] != not_in_r) \/  (P[j] != 0))        \/ (C[j+1] = C[j]))   /\ 

          ((Sem[j] != not_in_r)  \/  (P[j] = 0)) /\
          
          (((Sem[j] != not_in_a) \/  (P[j] != 0))        \/ (C[j+1] = C[j]))   /\ 

          ((Sem[j] != not_in_a)  \/  (P[j] = 0)) /\
 
          (((Sem[j] != maybe_b)  \/  (P[j] != P[j+1]))   \/ (C[j+1] = C[j]))   /\ 

          ((Sem[j] != maybe_b)   \/  (P[j] = P[j+1]))  /\
                          
          (((Sem[j] != maybe_a)  \/  (P[j] != P[j+1]))   \/ (C[j+1] = C[j]))   /\ 

          ((Sem[j] != maybe_a)   \/  (P[j] = P[j+1]))  /\

          (((Sem[j] != found)    \/  (P[j] != C[j] + 1)) \/ (C[j+1] = C[j]+1)) /\ 

          ((Sem[j] != found)     \/  (P[j] = C[j] + 1)) /\

          (((Sem[j] != found_end)\/  (P[j] != C[j] + 1)) \/ (C[j+1] = C[j]+1)) /\ 

          ((Sem[j] != found_end) \/  (P[j] = C[j] + 1)) /\

          (((Sem[j] != in_p)     \/  (P[j] != C[j]))     \/ (C[j+1] = C[j]))  /\
  
          ((Sem[j] != in_p)      \/  (P[j] = C[j])));

predicate impose_accumulator_updates_predicate_range(string: predicate_name, 
                                      array[int] of var int: Sem, 
                                      array[int] of var int: X, 
                                                        int: plus_infinity,
                                                        int: minus_infinity) =
  let{
       int: not_in    = not_in(), 
       int: not_in_r  = not_in_r(), 
       int: not_in_a  = not_in_a(),
       int: maybe_b   = maybe_b(),
       int: found     = found(), 
       int: found_end = found_end(), 
       int: maybe_a   = maybe_a(),
       int: in_p      = in_p(),
      
      int: time_series_length     = length(X),    
      set of int: TimeSeriesRange = 1..time_series_length,
      set of int: SignatureRange  = 1..time_series_length-1,

      %accumulator variables
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: C, %% domains ?
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: F, %% domains ?
      array[TimeSeriesRange] of var minus_infinity..plus_infinity: H, %% domains ?
      array[TimeSeriesRange] of var bool: R, %% domains ?
            
  } in
    % accumulator initialisation 
    C[1] = 0         /\
    H[1] = X[1]      /\
    R[1] = true      /\

    % accumulator update
    forall(j in SignatureRange)(
          (Sem[j] != not_in    \/   C[j+1] = C[j]   /\ 
                                    F[j+1] = F[j]   /\
                                    H[j+1] = X[j+1] /\ 
                                    R[j+1] = R[j])  /\
               
          (Sem[j] != not_in_r  \/   C[j+1] = C[j]   /\ 
                                    F[j+1] = F[j]   /\
                                    H[j+1] = X[j+1] /\ 
                                    R[j+1] = R[j])  /\
              
          (Sem[j] != not_in_a  \/   C[j+1] = C[j]                         /\ 
                                    F[j+1] = abs(H[j] - X[j])             /\
                                    H[j+1] = X[j+1]                       /\ 
                                    R[j+1] = (R[j] /\ theta(predicate_name, F[j], C[j]))) /\
              
          (Sem[j] != maybe_b   \/  C[j+1] = C[j]  /\ 
                                   F[j+1] = F[j]  /\    
                                   H[j+1] = H[j]  /\
                                   R[j+1] = R[j]) /\
            
          (Sem[j] != maybe_a   \/  C[j+1] = C[j]  /\   
                                   F[j+1] = F[j]  /\  
                                   H[j+1] = H[j]  /\
                                   R[j+1] = R[j]) /\
            
          (Sem[j] != found_end \/   C[j+1] = abs(H[j] - X[j+1])              /\ 
                                    F[j+1] = abs(H[j] - X[j+1])              /\
                                    H[j+1] = X[j+1]                        /\ 
                                    R[j+1] = (R[j] /\ theta(predicate_name, F[j], F[j+1])))/\
            
          (Sem[j] != in_p      \/  C[j+1] = abs(H[j] - X[j+1]) /\  
                                   F[j+1] = F[j]               /\ 
                                   H[j+1] = H[j]               /\
                                   R[j+1] = R[j])              /\
            
          (Sem[j] != found     \/  C[j+1] = abs(H[j] - X[j+1]) /\  
                                   F[j+1] = F[j]               /\ 
                                   H[j+1] = H[j]               /\
                                   R[j+1] = R[j]))             /\
     
     % action on return
     R[time_series_length] /\ theta(predicate_name, F[time_series_length], C[time_series_length]);

predicate theta(string: predicate_name, 
               var int: var1, 
               var int: var2) =
  if predicate_name = "all_equal" 
    then var1 = var2
  elseif predicate_name = "increasing" 
    then var1 <= var2
  elseif predicate_name = "decreasing" 
    then var1 >= var2
  else false endif;
  
predicate delta(string: feature, 
               var int: x,
               var int: delta) =
  if feature = "max" then delta = x
  elseif 
     feature = "min" then delta = x
  elseif
    feature = "surf" then delta = x
  elseif
    feature = "one"  then delta = 1
  elseif
    feature = "width"then delta = 1
  else false endif;

predicate delta_prime(string: feature, 
                         int: after,
                     var int: x, 
                     var int: x_next,
                     var int: delta_prime) =
  if after = 1 then delta(feature, x, delta_prime)
  elseif
     feature = "max"     then delta_prime = x_next
  elseif
     feature = "min"     then delta_prime = x_next
  elseif
     feature = "surf"    then delta_prime = x_next
  elseif
     feature = "one"     then delta_prime = 1
  elseif
     feature = "width"   then delta_prime = 1
  else false endif;

predicate aggregate(string: aggregator, 
                   var int: result, 
                   var int: var1,
                   var int: var2) =
  if aggregator = "max" then result = max(var1, var2)
  elseif
     aggregator = "min" then result = min(var1, var2)
  elseif
     aggregator = "sum" then result = var1 + var2
  else false endif;

predicate compute_feature(string: feature, 
                         var int: result, 
                         var int: var1,
                         var int: var2) =
  if feature = "max"     then result = max(var1, var2)
  elseif
     feature = "min"     then result = min(var1, var2)
  elseif
     feature = "surf" then result = var1 + var2
  elseif
     feature = "one"     then result = 1
  elseif
     feature = "width"   then result = var1 + var2
  else false endif;

predicate compute_feature2(int: after, 
                        string: feature, 
                       var int: result, 
                       var int: var1,
                       var int: var2, 
                       var int: var3,
                       var int: temp_var) =
  if after = 1 then compute_feature(feature, result, var1, var2) /\ temp_var = ub(temp_var)
  else
    compute_feature(feature, temp_var, var1, var2) /\ 
    compute_feature(feature, result, temp_var, var3) 
  endif;

predicate aggregate2(int: after, 
                  string: feature, 
                  string: aggregator, 
                 var int: result, 
                 var int: var1, 
                 var int: var2, 
                 var int: var3,
                 var int: var4,
                 var int: temp_var_feat,
                 var int: temp_var_aggr) =
  compute_feature2(after, feature, temp_var_aggr, var2, var3, var4, temp_var_feat) /\
  aggregate(aggregator, result, temp_var_aggr, var1);

