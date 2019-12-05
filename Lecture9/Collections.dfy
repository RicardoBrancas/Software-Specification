method Main() {
    // Sets
    var st1: set<nat> := {};
    
    st1 := st1 + {1,2,3};
    assert 1 in st1;
    
    st1 := st1 - {1};
    assert 1 !in st1;
    assert st1 == {2, 3};

    assert st1 <= {2,3,4};
    assert st1 !! {1,4};


    // Sequences
    var sq1: seq<nat> := [];

    sq1 := sq1 + [1,2,3];
    assert sq1[1] == 2;
    sq1 := sq1[1..];
    assert sq1 == [2,3];
    sq1 := sq1[..1];
    assert sq1 == [2];

    // Maps
    var m1: map<string,nat> := map[];

    m1 := m1["k1" := 1];
    assert m1["k1"] == 1;

    m1 := m1["k2" := 2];
    assert "k2" in m1;
    
    assert "k1" in m1;
    m1 := map k | k in m1 && k != "k1" :: m1[k];
    assert "k1" !in m1;


}