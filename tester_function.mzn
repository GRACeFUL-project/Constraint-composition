include "time_series_constraints.mzn";

string: feature;
string: aggregator;
string: pattern;

int: domain_ub ;
int: domain_lb ;
int: time_series_length ;

set of int: Domains = domain_lb..domain_ub;
array[1..time_series_length] of var Domains: x;
var int: result;

constraint time_series_constraint(aggregator, feature, pattern, x, result);

solve :: int_search(x, input_order, indomain_min, complete)
      satisfy;

output["Time series = ", show(x), ", constraint = ", show(aggregator), 
      "_", show(feature), "_", show(pattern), ", result = ", show(result)];

