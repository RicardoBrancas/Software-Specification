class TreeNode 
{
    var data: int
    var left: TreeNode?
    var right: TreeNode?


    predicate Valid()
    {
        // TODO
        true
    }

    constructor (x: int)
    {
        data := x;
        left := null;
        right := null;
    }

    method Insert(x: int)
    {
        if x == data { return; }
        if x < data {
            if left == null {
                left := new TreeNode(x);
            } else {
                left.Insert(x);
            }
        } else {
            if right == null {
                right := new TreeNode(x);
            } else {
                right.Insert(x);
            }
        }
    }

    method Find(x: int) returns (present: bool)
    {
        // TODO
    }


    method Main()
    {
        var t1 := new TreeNode(1);
        var t2 := new TreeNode(2);
        t1.Insert(2);
        assert t1.Valid();
        t2.Insert(3);
        assert t1.Valid();
        var b := t1.Find(2);
        assert b;
    }

}