///////////////////////////////////////////////////////////////////////////
// Basic counter
///////////////////////////////////////////////////////////////////////////

class Counter
{
    var incs: int;
    var decs: int;


    ghost var Value : int;

    predicate Valid()
        reads this
    {
        Value == incs - decs
    }

    constructor ()
        ensures Valid()
        ensures Value == 0
    {
        incs, decs, Value := 0, 0, 0;
    }

    method getValue() returns (x: int)
        requires Valid()
        ensures x == Value
    {
        x := incs - decs;
    }

    method inc()
        modifies this
        requires Valid()
        ensures Valid()
        ensures Value == old(Value) + 1
    {
        incs, Value := incs + 1, Value + 1;
    }

    method dec()
        modifies this
        requires Valid()
        ensures Valid()
        ensures Value == old(Value) - 1
    {
        decs, Value := decs + 1, Value - 1;
    }

    method Main()
    {
        var c := new Counter();
        c.inc(); 
        c.inc();
        c.dec();
        c.inc();
        var x := c.getValue();
        assert x == 2;
        assert c.Valid();
    }
}
