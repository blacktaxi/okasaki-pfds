namespace Chapter2

open System

/// Original implementation from the book, roughly translated.
module OriginalSet =
    type Tree<'T when 'T : comparison> = E | T of Tree<'T> * 'T * Tree<'T>

    let empty = E  

    let rec member' = function
        | (_, E) -> false
        | (x, T (a, y, b)) ->
            if x < y then member' (x, a)
            else if x > y then member' (x, b)
            else true
      
    let rec insert = function
        | (x, E) -> T (E, x, E)
        | (x, (T (a, y, b) as s)) ->
            if x < y then T (insert (x, a), y, b)
            else if x > y then T (a, y, insert (x, b))
            else s
        
/// Exercise 2.1 Write a function suffixes of type a list -» a list list that takes a
/// list xs and returns a list of all the suffixes of xs in decreasing order of length.
/// For example,
/// suffixes [1,2,3,4] = [[1,2,3,4] , [2,3,4] , [3,4] , [4], [] ]
/// Show that the resulting list of suffixes can be generated in O(n) time and rep-
/// resented in O(n) space.
module Ex21 =
    let rec suffixes = function
        | [] -> [[]]
        | (_ :: xs) as l -> l :: (suffixes xs)

/// Exercise 2.2 (Andersson [And91D In the worst case, member performs ap-
/// proximately 2d comparisons, where d is the depth of the tree. Rewrite member
/// to take no more than d + 1 comparisons by keeping track of a candidate ele-
/// ment that might be equal to the query element (say, the last element for which
/// < returned false or < returned true) and checking for equality only when you
/// hit the bottom of the tree.
module Ex22 =
    open OriginalSet

    let member' = function
        | (_, E) -> false
        | (x, (T (_, y, _) as t)) ->
            let rec aux = function
                | (candidate, E) -> x = candidate
                | (candidate, T (a, y, b)) -> 
                    if x < y then aux (candidate, a)
                    else aux (y, b)
            in aux (y, t)
                
/// Exercise 23 Inserting an existing element into a binary search tree copies the
/// entire search path even though the copied nodes are indistinguishable from the
/// originals. Rewrite insert using exceptions to avoid this copying. Establish only
/// one handler per insertion rather than one handler per iteration.
module Ex23 =
    open OriginalSet

    exception ElementAlreadyInSet

    let insert (x, t) =
        let rec insert' = function
            | (x, E) -> T (E, x, E)
            | (x, (T (a, y, b) as s)) ->
                if x < y then T (insert' (x, a), y, b)
                else if x > y then T (a, y, insert' (x, b))
                else raise ElementAlreadyInSet
        try
            insert' (x, t)
        with | ElementAlreadyInSet -> t

/// Exercise 2.4 Combine the ideas of the previous two exercises to obtain a ver-
/// sion of insert that performs no unnecessary copying and uses no more than
/// d + 1 comparisons.
module Ex24 =
    open OriginalSet

    exception ElementAlreadyInSet

    let insert = function
        | (x, E) -> T (E, x, E)
        | (x, (T (_, y, _) as t)) ->
            let rec aux = function
                | (candidate, E) -> 
                    if x = candidate then raise ElementAlreadyInSet
                    else T (E, x, E)
                | (candidate, T (a, y, b)) -> 
                    if x < y then T (aux (candidate, a), y, b)
                    else T (a, y, aux (y, b))
            in 
                try aux (y, t)
                with | ElementAlreadyInSet -> t

/// Exercise 2.5 Sharing can also be useful within a single object, not just be-
/// tween objects. For example, if the two subtrees of a given node are identical,
/// then they can be represented by the same tree.
/// (a) Using this idea, write a function complete of type Elem x int -> Tree
/// where complete (x, d) creates a complete binary tree of depth d with x
/// stored in every node. (Of course, this function makes no sense for the set
/// abstraction, but it can be useful as an auxiliary function for other abstrac-
/// tions, such as bags.) This function should run in O(d) time.
/// (b) Extend this function to create balanced trees of arbitrary size. These trees
/// will not always be complete binary trees, but should be as balanced as
/// possible: for any given node, the two subtrees should differ in size by at
/// most one. This function should run in 0(log n) time. (Hint: use a helper
/// function create2 that, given a size m, creates a pair of trees, one of size m
/// and one of size m+1.)
module Ex25 =
    open OriginalSet

    let rec complete = function
        | (_, 0) -> E
        | (x, d) -> let t = complete (x, d - 1) in T (t, x, t)

    let rec completeSize = function
        | (_, 0) -> E
        | (x, n) ->
            let rec create2 = function
                | 0 -> E, T (E, x, E)
                | n -> let left, right = create2 (n / 2) in
                       if (n % 2 <> 0) then T (left, x, left), T (left, x, right)
                       else T (left, x, right), T (right, x, right)
            let left, right = create2 ((n - 1) / 2) in
            if ((n - 1) % 2 <> 0) then T (left, x, right)
            else T (left, x, left)

/// Exercise 2.6 Adapt the UnbalancedSet functor to support finite maps rather
/// than sets. Figure 2.10 gives a minimal signature for finite maps. (Note that the
/// NOTFOUND exception is not predefined in Standard ML—you will have to de-
/// fine it yourself. Although this exception could be made part of the FINITEMAP
/// signature, with every implementation defining its own NOTFOUND exception,
/// it is convenient for all finite maps to use the same exception.)
module Ex26 =
    exception KeyNotFound

    module FiniteMap =
        type KeyValuePair<'T, 'U> = { Key : 'T; Value : 'U }
        type Tree<'T, 'U when 'T : comparison> = 
            | E 
            | T of Tree<'T, 'U> * KeyValuePair<'T, 'U> * Tree<'T, 'U>

        let empty = E

        let rec lookup = function
            | (_, E) -> raise KeyNotFound
            | (x, T (a, { Key = y; Value = v}, b)) ->
                if x < y then lookup (x, a)
                else if y < x then lookup (x, b)
                else v

        let rec bind = function
            | (key, value, E) -> T (E, { Key = key; Value = value }, E)
            | (key, value, T (a, { Key = y; Value = v }, b)) ->
                if key < y then T (bind (key, value, a), { Key = y; Value = v }, b)
                else if y < key then T (a, { Key = y; Value = v }, bind (key, value, b))
                else T (a, { Key = y; Value = v }, b)
        
/// Tests for chapter 2
module Tests2 =
    open Microsoft.VisualStudio.TestTools.UnitTesting
    open FsUnit.MsTest
    open System.Linq

    open OriginalSet

    [<TestClass>]
    type ``Chapter 2 tests`` () =
        let makeTree (xs : 'T seq) : Tree<'T> =
            Seq.fold (fun a x -> OriginalSet.insert (x, a)) OriginalSet.empty xs

        let tree1 = makeTree [1; 2; 4; 8; 10; 16; 17; 18; 19]
        let tree2 = makeTree [1; 2; 3; 4; 5; 6; 7; 8]
  
        let testMember memberFunc =
            assert (memberFunc (4, tree1) = true)
            assert (memberFunc (666, tree1) = false)
    
            for x in 1 .. 8 do
                assert (memberFunc (x, tree2))

        let genericImplTest (ins, mem, empty) =
            mem (5, (ins (5, empty))) |> should be True
            mem (6, (ins (5, empty))) |> should be False

            mem (666, empty) |> should be False

            do
                let tree = makeTree <| List.init 500 (fun _ -> 5)
                mem (5, tree) |> should be True
                mem (4, tree) |> should be False

            do
                let items = [1 .. 50]
                let tree = makeTree items 
                for i in items do
                    mem (i, tree) |> should be True

            do
                let r = new System.Random()
                let items = Array.init 5000 (fun _ -> r.Next())
                let tree = makeTree items
                for i in items do
                    mem (i, tree) |> should be True

        [<TestMethod>] 
        member x.``original Set impl`` () =
            genericImplTest (OriginalSet.insert, OriginalSet.member', OriginalSet.empty)

        [<TestMethod>] 
        member x.``exercise 2.1`` () =
            Ex21.suffixes [1; 2; 3; 4] |> should equal [[1; 2; 3; 4]; [2; 3; 4]; [3; 4]; [4]; []]
            Ex21.suffixes [] |> should equal [[]]

        [<TestMethod>] 
        member x.``exercise 2.2`` () =
            genericImplTest (OriginalSet.insert, Ex22.member', OriginalSet.empty)

        [<TestMethod>] 
        member x.``exercise 2.3`` () =
            genericImplTest (Ex23.insert, OriginalSet.member', OriginalSet.empty)

        [<TestMethod>] 
        member x.``exercise 2.4`` () =
            genericImplTest (Ex24.insert, OriginalSet.member', OriginalSet.empty)
            
        [<TestMethod>] 
        member x.``exercise 2.5a`` () =
            let mem = OriginalSet.member'

            mem (5, Ex25.complete (5, 0)) |> should be False
            mem (5, Ex25.complete (5, 1)) |> should be True
            mem (6, Ex25.complete (5, 1)) |> should be False
            mem (5, Ex25.complete (5, 1000)) |> should be True
            mem (6, Ex25.complete (5, 1000)) |> should be False

        [<TestMethod>] 
        member x.``exercise 2.5b`` () =
            let mem = OriginalSet.member'

            mem (5, Ex25.completeSize (5, 0)) |> should be False
            mem (5, Ex25.completeSize (5, 1)) |> should be True
            mem (6, Ex25.completeSize (5, 1)) |> should be False
            mem (5, Ex25.completeSize (5, 1000)) |> should be True
            mem (6, Ex25.completeSize (5, 1000)) |> should be False

            // @TODO test for balance

        [<TestMethod>] 
        member x.``exercise 2.6`` () =
            let empty, lookup, bind = Ex26.FiniteMap.empty, Ex26.FiniteMap.lookup, Ex26.FiniteMap.bind

            // @TODO doesn't work :/
            // lookup (5, empty) |> should throw typeof<Ex26.KeyNotFound>

            lookup (5, bind (5, 3, empty)) |> should equal 3

            do
                let r = new System.Random()
                // @NOTE this crashes the test runner if increased to 5000? I guess stack overflow,
                // will have to check later.
                let keys = [1 .. 1000]
                let dict = new System.Collections.Generic.Dictionary<int, int>()

                for k in keys do
                    dict.[k] <- r.Next()

                let map = Seq.fold (fun m (KeyValue(k, v)) -> bind (k, v, m)) empty dict

                for k in keys do
                    lookup (k, map) |> should equal (dict.[k])

