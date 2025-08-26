type Trace<a>;

function current<a>(xs: Trace<a>): a;

function counter(stop: int): Trace<int>;
function range(start: int, step: int, stop: int): Trace<int>;

function selects<a,b>(init: [a]b, keys: Trace<a>): Trace<b>;
function stores<a,b>(init: [a]b, keys: Trace<a>, values: Trace<b>): Trace<[a]b>;

function holds<a>(xs: Trace<a>): bool;
function sums<a>(array: [a]int, keys: Trace<a>): Trace<int>;