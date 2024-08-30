var counter: int;

procedure count()
    modifies counter;
    requires counter >= 0;
    ensures last(false) && always(counter >= 0);
{
    while(true)
        trace    always counter >= 0;
    {
        counter := counter + 1;
    }
}