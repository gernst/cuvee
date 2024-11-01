var counter: int;

procedure incremen(amount: int)
    modifies counter;
    ensures counter == old(counter) + amount;
{
    counter := counter + amount;
}