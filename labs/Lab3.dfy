//////////////////////////////////////////////////////////
// Lab 3: Exercises
//////////////////////////////////////////////////////////

// This file defines functions that manipulate lists.
// The goal of this lab is to practice proving simple 
// inductive properties of recursive functions.

//////////////////////////////////////////////////////////
// Exercise 1. Read the code provided and test it by 
// experimenting with it. You can add code to the Main 
// method. Feel free to add comments with your notes.
//////////////////////////////////////////////////////////

datatype List<T> = Nil | Cons (head: T, tail: List)

predicate non_empty<T>(l: List<T>) {
    l != Nil
}

function method length<T>(l: List<T>): nat
decreases l
{
    match l 
        case Nil => 0
        case Cons(h,t) => 1 + length(t)
}

function method head<T>(l: List<T>): T
requires non_empty(l)
{
    match l 
        case Cons(h,t) => h
}

function nth<T>(n: nat, l: List<T>): T 
    requires non_empty(l)
    requires n < length(l)
    decreases n
{
    if n==0 then head(l) else nth(n-1, l)
}

function method elem<T(==)>(value: T, l: List<T>): bool
decreases l
{
    match l
        case Nil        => false
        case Cons(h, t) => if value == h then true else elem(value, t)
}

function method append<T>(l1: List<T>, l2: List<T>): List<T>
decreases l1
{
    match l1
        case Nil => l2
        case Cons(h, t) => Cons(h, append(t, l2))
}

method Main()
{
    var l1 := Cons(1, Cons(2, Cons(3, Nil)));
    print "Length of list is ", length(l1), "\n";

    var l2 := Cons(true, Cons(false, Cons(false, Nil)));
    print "Length of list is ", length(l2), "\n";

}

//////////////////////////////////////////////////////////
// Exercise 2. Write a lemma that shows that append is associative:
//
//  append(append(l1, l2), l3) == append(l1, append(l2, l3))
//
// for all l1, l2 and l3
//////////////////////////////////////////////////////////

lemma append_assoc (l1: List, l2: List, l3: List)
    ensures append(append(l1, l2), l3) == append(l1, append(l2, l3))
{}

//////////////////////////////////////////////////////////
// Exercise 3. Write a lemma that shows that Nil is the 
// neutral element of append:
//
//  append(l1, Nil) == l1
//  append(Nil, l1) == l1
//
// for all l1
//////////////////////////////////////////////////////////

lemma nil_neutral (l: List)
    ensures append(l, Nil) == l
    ensures append(Nil, l) == l
{}

//////////////////////////////////////////////////////////
// Exercise 4. Define a function reverse that reverses
// a list
//////////////////////////////////////////////////////////

function reverse(l: List): List
{
    match l
        case Nil => Nil
        case Cons(h, T) => append(reverse(T), Cons (h, Nil))
}

//////////////////////////////////////////////////////////
// Exercise 5. Show that 
//
// reverse(append(l1, l2)) == append(reverse(l2), reverse(l1))
//
// for all l1 and l2.
//
// Note: Dafny won't be able to do this automatically. 
// You will need to write an inductive proof. It might
// help writing it on paper first.
//////////////////////////////////////////////////////////

lemma rev_app(l1: List, l2: List)
    ensures reverse(append(l1, l2)) == append(reverse(l2), reverse(l1))
{
    match l1
        case Nil =>
            calc == {
                reverse(append(l1, l2));
                reverse(append(Nil, l2));
                reverse(l2);
                == {nil_neutral(reverse(l2));}
                append(reverse(l2), Nil);
                append(reverse(l2), reverse(l1));
            }

        case Cons(h, T) =>
            calc == {
                reverse(append(l1, l2));
                reverse(append(Cons(h, T), l2));
                reverse(Cons(h, append(T, l2)));
                append(reverse(append(T, l2)), Cons(h, Nil));
                append(append(reverse(l2), reverse(T)), Cons(h, Nil));
                == {append_assoc(reverse(l2), reverse(T), Cons(h, Nil)); }
                append(reverse(l2), append(reverse(T), Cons(h, Nil)));
                append(reverse(l2), reverse(l1));
            }
}

//////////////////////////////////////////////////////////
// Exercise 6. Use the previous lemma to show that 
// reversing a list twice is the same as not changing it:
//
// reverse(reverse(l)) == l
//
// for all l
//////////////////////////////////////////////////////////

lemma rev_rev (l: List)
    ensures reverse(reverse(l)) == l
{
    match l
        case Nil =>
            calc == {
                reverse(reverse(l));
                reverse(reverse(Nil));
                reverse(Nil);
                Nil;
            }
        case Cons(h, T) =>
            calc == {
                reverse(reverse(Cons(h, T)));
                reverse(append(reverse(T), Cons(h, Nil)));
                == { rev_app(reverse(T), Cons(h, Nil)); }
                append(reverse(Cons(h, Nil)), reverse(reverse(T)));
                append(Cons(h, Nil), T);
                Cons(h, T);
            }
}



//////////////////////////////////////////////////////////
// Exercise 7. Define a function
//
// function del<T>(value: T, l: List<T>): List<T>
//
// such that the properties hold:
//
// 1. forall v,l :: !elem(v, l) ==> del(v, l) == l
// 2. forall v,l :: !elem(v, del(v, l))
// 3. forall v,l1,l2 :: del(v, append(l1,l2)) == 
//                      append(del(v,l1), del(v,l2))
//
// Write the function body and express the three properties
// as lemmas.
//////////////////////////////////////////////////////////

function del<T>(value: T, l: List<T>): List<T> {
    match l
        case Nil => Nil
        case Cons(h, T) => if h == value then del(value, T) else Cons(h, del(value, T))
}

lemma del_nothing<T>(v: T, l: List<T>)
    ensures !elem(v, l) ==> del(v, l) == l
{}

lemma del_deletes<T>(v: T, l: List<T>)
    ensures !elem(v, del(v, l))
{}

lemma del_recurse<T>(v: T, l1: List<T>, l2: List<T>)
    ensures del(v, append(l1,l2)) == append(del(v,l1), del(v,l2))
{}

//////////////////////////////////////////////////////////
// Exercise 8. Define a similar function to the above
//
// function del1<T>(value: T, l: List<T>): List<T>
//
// such that the properties hold:
//
// 1. forall v,l :: !elem(v, l) ==> del1(v, l) == l
// 2. forall v,l :: elem(v, l) ==> length(l) == 1 + length(del1(v, l))
// 3. forall v,l1,l2 :: elem(v, l) ==>
//                      append(del1(v, l1), l2) == del1(v, append(l1,l2))
//
// Write the function body and express the three properties
// as lemmas.
//////////////////////////////////////////////////////////

function del1<T>(value: T, l: List<T>): List<T> {
    match l
        case Nil => Nil
        case Cons(h, T) => if h == value then T else Cons(h, del1(value, T))
}

lemma del1_nothing<T>(v: T, l: List<T>)
    ensures !elem(v, l) ==> del1(v, l) == l
{}

lemma del1_deletes<T>(v: T, l: List<T>)
    ensures elem(v, l) ==> length(l) == 1 + length(del1(v, l))
{}

lemma del2_recurse<T>(v: T, l1: List<T>, l2: List<T>)
    ensures elem(v, l1) ==> append(del1(v, l1), l2) == del1(v, append(l1,l2))
{}

//////////////////////////////////////////////////////////
// Exercise 9. Define a function 'count' that given a
// value v and a List l, returns a natural number that
// satisfies:
//
// 1. forall v,l1,l2 :: count(v, l1) + count(v, l2) == count(v, append(l1, l2))
// 2. forall v,l :: ount(v,l) == count(v, reverse(l))
//
// Express the three properties as lemmas.
//////////////////////////////////////////////////////////

function count<T>(v: T, l:List<T>): nat {
    match l
        case Nil => 0
        case Cons(h, T) => if h == v then 1 + count(v, T) else count(v, T)
}

lemma count_recurse<T>(v: T, l1: List<T>, l2: List<T>)
    ensures count(v, l1) + count(v, l2) == count(v, append(l1, l2))
{}

lemma count_rev<T>(v: T, l: List<T>)
    ensures count(v, l) == count(v, reverse(l))
{
    match l
        case Nil =>
            calc == {

            }
        case Cons(h, T) =>
            calc == {
                count(v, reverse(l));
                count(v, reverse(Cons(h, T)));
                count(v, append(reverse(T), Cons (h, Nil)));
                == { count_recurse(v, reverse(T), Cons(h, Nil)); }
                count(v, reverse(T)) + count(v, Cons(h, Nil));
                count(v, T) + count(v, Cons(h, Nil));
                count(v, Cons(h, Nil)) + count(v, T);
                count(v, append(Cons(h, Nil), T));
                count(v, Cons(h, T));
            }
}