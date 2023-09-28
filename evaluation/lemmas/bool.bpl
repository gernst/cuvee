function not_(p: bool): bool;
axiom not_(false) == true;
axiom not_(true) == false;

function and_(p: bool, q: bool): bool;
axiom forall q: bool ::
    and_(false, q) == false;
axiom forall q: bool ::
    and_(true, q) == q;

function or_(p: bool, q: bool): bool;
axiom forall q: bool ::
    or_(false, q) == q;
axiom forall q: bool ::
    or_(true, q) == true;

function ite_(p: bool, q: bool, t: bool): bool;
axiom forall q: bool, r: bool ::
    ite_(false, q, r) == r;
axiom forall q: bool, r: bool ::
    ite_(true, q, r) == q;
