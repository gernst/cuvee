type Trace<a>;
function earlier<a>(x: a, xs: Trace<a>): bool;
function last<a>(xs: Trace<a>): a;