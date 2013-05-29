namespace Chapter3

open System

module LeftistHeap =
    exception Empty

    type Heap<'T when 'T : comparison> = E | T of int * 'T * Heap<'T> * Heap<'T>
        with override x.ToString () = sprintf "%A" x

    let rank = function
        | E -> 0
        | T (r, _, _, _) -> r

    let makeT (x, a, b) =
        if rank a >= rank b then T (rank b + 1, x, a, b)
        else T (rank a + 1, x, b, a)

    let empty = E
    let isEmpty = function
        | E -> true
        | _ -> false

    let rec merge = function
        | (h, E) -> h
        | (E, h) -> h
        | ((T (_, x, a1, b1) as h1), (T (_, y, a2, b2) as h2)) ->
            if x <= y then makeT (x, a1, merge (b1, h2))
            else makeT (y, a2, merge (h1, b2))

    let insert (x, h) = merge (T (1, x, E, E), h)

    let findMin = function
        | E -> raise Empty
        | T (_, x, a, b) -> x

    let deleteMin = function
        | E -> raise Empty
        | T (_, x, a, b) -> merge (a, b)

// Exercise 3.2 Define insert directly rather than via a call to merge.
module Ex32 =
    open LeftistHeap

    let rec insert = function
        | (x, E) -> T (1, x, E, E)
        | (x, (T (_, y, a2, b2) as h2)) ->
            if x <= y then makeT (x, E, h2)
            else makeT (y, a2, insert (x, b2))

// Exercise 3.3 Implement a function fromList of type Elem.T list ->• Heap that
// produces a leftist heap from an unordered list of elements by first converting
// each element into a singleton heap and then merging the heaps until only one
// heap remains. Instead of merging the heaps in one right-to-left or left-to-right
// pass using foldr or foldl, merge the heaps in [logn] passes, where each pass
// merges adjacent pairs of heaps. Show that fromList takes only O(n) time.
module Ex33 =
    open LeftistHeap

    let fromList xs =
        let splitAt n xs =
            Seq.take n xs, Seq.skip n xs

        let rec pairwise = function
            | [] -> []
            | [x] -> [(x, None)]
            | [x1; x2] -> [(x1, Some x2)]
            | x1 :: x2 :: rest -> (x1, Some x2) :: (pairwise rest)

        let mergePair = function
            | x1, Some x2 -> merge (x1, x2)
            | x1, None -> x1

        let rec reduce = function
            | [] -> E
            | [one] -> one
            | [x1; x2] -> mergePair (x1, (Some x2))
            | xs -> reduce <| List.map mergePair (pairwise xs)

        List.map (fun x -> T (1, x, E, E)) xs |> reduce

// Exercise 3.4 (Cho and Sahni [CS96]) Weight-biased leftist heaps are an al-
// ternative to leftist heaps that replace the leftist property with the weight-biased
// leftist property: the size of any left child is at least as large as the size of its
// right sibling.
//
// (b) Modify the implementation in Figure 3.2 to obtain weight-biased leftist
// heaps.
module Ex34b =
    open LeftistHeap

    let makeT (x, a, b) =
        if rank a >= rank b then T (rank a + rank b + 1, x, a, b)
        else T (rank a + rank b + 1, x, b, a)

    let empty = E
    let isEmpty = function
        | E -> true
        | _ -> false

    let rec merge = function
        | (h, E) -> h
        | (E, h) -> h
        | ((T (_, x, a1, b1) as h1), (T (_, y, a2, b2) as h2)) ->
            if x <= y then makeT (x, a1, merge (b1, h2))
            else makeT (y, a2, merge (h1, b2))

    let insert (x, h) = merge (T (1, x, E, E), h)

    let findMin = LeftistHeap.findMin

    let deleteMin = function
        | E -> raise Empty
        | T (_, x, a, b) -> merge (a, b)

// (c) Currently, merge operates in two passes: a top-down pass consisting of
// calls to merge, and a bottom-up pass consisting of calls to the helper
// function makeT. Modify merge for weight-biased leftist heaps to operate
// in a single, top-down pass.
module Ex34c =
    open LeftistHeap

    let empty = E
    let isEmpty = function
        | E -> true
        | _ -> false

    let merge = function
        | (h, E) -> h
        | (E, h) -> h   
        | ((T (_, x, a1, b1) as h1), (T (_, y, a2, b2) as h2)) ->
//            let x', l', r', h' =
//                if x <= y then (x, a1, b1, h2)
//                else (y, a2, b2, h1)
//            let l'', r'' =
//                if rank l' >= rank r' + rank h' then (l', merge (r', h'))
//                else (merge (r', h'), l')
//            T (rank h1 + rank h2, x', l'', r'')

            let x', a, b = 
                if x <= y then x, a1, merge (b1, h2)
                else y, a2, merge (h1, b2)
            let l, r = 
                if rank a >= rank b then a, b
                else b, a
            // @TODO is this really only top-down??
            T (rank h1 + rank h2, x', l, r)

    let insert (x, h) = merge (T (1, x, E, E), h)

    let findMin = LeftistHeap.findMin

    let deleteMin = function
        | E -> raise Empty
        | T (_, x, a, b) -> merge (a, b)

/// Tests for chapter 3
module Tests3 =
    open Microsoft.VisualStudio.TestTools.UnitTesting
    open FsUnit.MsTest
    open System.Linq

    open LeftistHeap

    [<TestClass>]
    type ``Chapter 3 tests`` () =
        let rng = new System.Random()
        let randomItem () = rng.Next()
        let randomItems n = List.init n (fun _ -> randomItem ()) |> Seq.distinct |> Seq.toList

        let rec compareHeaps = function
            | (E, E) -> true
            | (_, E) -> false
            | (E, _) -> false
            | (T (r1, x1, a1, b1), T(r2, x2, a2, b2)) ->
                (r1, x1) = (r2, x2) &&
                    (((compareHeaps (a1, a2)) && (compareHeaps (b1, b2))) || 
                     ((compareHeaps (a1, b2)) && (compareHeaps (b1, a2))))

        let (=*=) h1 h2 = compareHeaps (h1, h2)

        //    Leftist heaps [Cra72, Knu73a] are heap-ordered binary trees that satisfy the
        // leftist property: the rank of any left child is at least as large as the rank of its
        // right sibling. The rank of a node is defined to be the length of its right spine
        // (i.e., the rightmost path from the node in question to an empty node). A simple
        // consequence of the leftist property is that the right spine of any node is always
        // the shortest path to an empty node.
        let rec testLeftist = function
            | E -> true
            | T (_, x, a, b) ->
                testLeftist a && testLeftist b &&
                    (rank a >= rank b)

        let testWeightBasedSize fromList size =
            let rec actualSize = function
                | E -> 0
                | T (_, _, a, b) -> 1 + (actualSize a) + (actualSize b)
            
            for l in Seq.map (fun _ -> randomItems 500) [1..100] do
                let h = fromList l
                size h |> should equal (actualSize h)
            
        let testCompleteImpl (empty : Heap<_>, isEmpty, merge, insert, findMin, deleteMin) =
            let fromList xs = List.fold (fun h i -> insert (i, h)) empty xs

            isEmpty empty |> should be True
            isEmpty (insert (0, empty)) |> should be False

            isEmpty (deleteMin (insert (0, empty))) |> should be True

            findMin (fromList [0]) |> should equal 0
            findMin (fromList [0; 1]) |> should equal 0
            findMin (fromList [0; 1; 2; 3; 4; 5; 6; 7]) |> should equal 0
            findMin (fromList ([-1] @ (randomItems 1000))) |> should equal -1
            findMin (fromList ((randomItems 1000) @ [-1] @ (randomItems 1000))) |> should equal -1

            do
                let h = fromList ((randomItems 1000) @ [-1] @ (randomItems 1000) @ [-2] @ (randomItems 1000))
                findMin h |> should equal -2
                findMin (deleteMin h) |> should equal -1

            do
                let h1 = fromList (randomItems 1000)
                let h2 = fromList (randomItems 1000)

                findMin (merge (h1, h2)) |> should equal (min (findMin h1) (findMin h2))

            do
                let h = fromList (randomItems 1000)

                findMin (insert (-666, h)) |> should equal -666
                findMin (deleteMin (insert (-666, h))) |> should equal (findMin h)
            
        [<TestMethod>]
        member x.``original LeftistHeap impl`` () =
            testCompleteImpl (empty, isEmpty, merge, insert, findMin, deleteMin)
        
        [<TestMethod>]
        member x.``exercise 3.2`` () =
            // insert items using both original implementation and
            // impl from ex 3.2, comparing results at each step
            do
                List.fold 
                    (fun (h1, h2) x ->
                        h1 |> should equal h2
                        testLeftist h1 |> should be True
                        testLeftist h2 |> should be True
                        (insert (x, h1), Ex32.insert (x, h2)))
                    (E, E)
                    (randomItems 1000)
                |> ignore

            testCompleteImpl (empty, isEmpty, merge, Ex32.insert, findMin, deleteMin)
                    
        [<TestMethod>]
        member x.``exercise 3.3`` () =
            // compare ex 3.3 implementation with folding using original
            // insert impl
            let fromList xs = List.fold (fun h i -> insert (i, h)) E xs

            let testWithList xs =
                let h1, h2 = fromList xs, Ex33.fromList xs
                testLeftist h1 |> should be True
                testLeftist h2 |> should be True

                findMin h1 |> should equal (findMin h2)

            testWithList [1]
            testWithList [1; 2]
            testWithList [1; 2; 3]
            testWithList [1; 2; 3; 4]
            testWithList [10; 1; 9; 2; 8; 3; 7; 4; 6; 5]
            testWithList [1; 1; 1; 1; 1]

            for _ in 1 .. 100 do
                testWithList <| randomItems 1000

        [<TestMethod>]
        member x.``exercise 3.4b`` () =
            testCompleteImpl 
                (Ex34b.empty, Ex34b.isEmpty, Ex34b.merge, 
                Ex34b.insert, Ex34b.findMin, Ex34b.deleteMin)

            testWeightBasedSize
                (fun xs -> List.fold (fun h i -> Ex34b.insert (i, h)) E xs)
                (LeftistHeap.rank)

        [<TestMethod>]
        member x.``exercise 3.4c`` () =
            testCompleteImpl 
                (Ex34c.empty, Ex34c.isEmpty, Ex34c.merge, 
                Ex34c.insert, Ex34c.findMin, Ex34c.deleteMin)

            testWeightBasedSize
                (fun xs -> List.fold (fun h i -> Ex34c.insert (i, h)) E xs)
                (LeftistHeap.rank)

