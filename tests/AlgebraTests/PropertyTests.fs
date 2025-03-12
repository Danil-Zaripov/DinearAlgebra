namespace Tests

open FsCheck
open FsCheck.Xunit
open Trees
open FsCheck.FSharp


[<Properties(MaxTest = 100)>]
module PropertyTests =
    let (.=.) left right =
        left = right |> Prop.label (sprintf "%A = %A" left right)

    [<Property>]
    let matrixConversionIsCorrect (mat: int array2d) =
        let n, m = Array2D.getDims mat

        let tst () =
            let expected = mat
            let actual = mat |> QuadTree.ofMatrix |> QuadTree.toMatrix

            expected = actual

        (n <> 0 && m <> 0) ==> (lazy tst ())

    [<Property>]
    let mapIsCorrect (mat: int array2d) =
        match QuadTree.tryOfMatrix mat with
        | Some(actual) ->
            let expected = (mat |> Array2D.fold (+) 0) * 2

            let actual =
                mat
                |> QuadTree.ofMatrix
                |> QuadTree.map ((*) 2)
                |> QuadTree.toMatrix
                |> Array2D.fold (+) 0

            expected .=. actual
        | None -> true .=. true

    [<Property>]
    let getElementIsCorrect (mat: int array2d) =
        match QuadTree.tryOfMatrix mat with
        | Some(actual) ->
            let mutable isOk = true
            let n, m = Array2D.length1 mat, Array2D.length2 mat

            for i in 0 .. n - 1 do
                for j in 0 .. m - 1 do
                    if (mat[i, j] <> QuadTree.getElement (i, j) actual) then
                        isOk <- false

            isOk
        | None -> true




    [<Property>]
    let map2SumIsCorrect (mat1: int array2d) =
        let n, m = Array2D.getDims mat1

        let tst () =
            let mat2 = Utility.getRandomArray2D n m
            let tr1 = mat1 |> QuadTree.ofMatrix
            let tr2 = mat2 |> QuadTree.ofMatrix

            let actual = (QuadTree.map2 (+) tr1 tr2) |> QuadTree.toMatrix

            let expected = Array2D.copy mat1 |> Array2D.mapi (fun i j x -> x + mat2[i, j])

            expected .=. actual

        (n <> 0 && m <> 0) ==> (lazy tst ())

    [<Property>]
    let multiplyIsCorrect (mat1: int array2d) =
        let n, m = Array2D.getDims mat1

        let tst () =
            let d = (System.Random().Next(1, 200))
            let mat2 = Utility.getRandomArray2D m d
            let tr1 = mat1 |> QuadTree.ofMatrix
            let tr2 = mat2 |> QuadTree.ofMatrix

            let actual = QuadTree.multiply (*) (+) 0 tr1 tr2

            let expected = Utility.multiply (*) (+) 0 mat1 mat2

            actual |> QuadTree.toMatrix .=. expected

        (n <> 0 && m <> 0) ==> (lazy tst ())

    [<Property>]
    let multiplyBigintIsCorrect (mat1: bigint array2d) =
        let n, m = Array2D.getDims mat1

        let tst () =
            let d = (System.Random().Next(1, 200))
            let mat2 = Utility.getRandomArray2D m d |> Array2D.map bigint
            let tr1 = mat1 |> QuadTree.ofMatrix
            let tr2 = mat2 |> QuadTree.ofMatrix

            let actual = QuadTree.multiply (*) (+) (0 |> bigint) tr1 tr2

            let expected = Utility.multiply (*) (+) (0 |> bigint) mat1 mat2

            actual |> QuadTree.toMatrix .=. expected

        (n <> 0 && m <> 0) ==> (lazy tst ())

module SparseMatrixTests =

    type IntSparseMatrices =
        static member IntSparseMatrices() =
            let twoIntSparseMatricesGenerator =
                let val_min = -1000
                let val_max = 1000

                gen {
                    let! n = Gen.choose (1, 100)
                    let! k = Gen.choose (1, 100)
                    let! m = Gen.choose (1, 100)

                    let getMatrix (n, m) =
                        gen {
                            let! rand_val = Gen.choose (val_min, val_max)
                            // 33% chance for random value
                            // 66% chance for a 0 as base
                            let! base_value = Gen.frequency [ (1, gen { return rand_val }); (2, gen { return 0 }) ]

                            let mat = Array2D.create n m base_value
                            let elems = n * m
                            let! nonBaseElems = Gen.choose (0, elems / 100 + elems % 100)

                            for _ in 1..nonBaseElems do
                                let! rnd = Gen.choose (val_min, val_max)
                                let! x = Gen.choose (0, n - 1)
                                let! y = Gen.choose (0, m - 1)
                                mat[x, y] <- rnd

                            return mat
                        }

                    let! mat1 = getMatrix (n, k)
                    let! mat2 = getMatrix (k, m)
                    return (mat1, mat2)
                }

            Arb.fromGen (twoIntSparseMatricesGenerator)

    type BoolSparseMatrices =
        static member BoolSparseMatrices() =
            let twoBoolSparseMatricesGenerator =
                gen {
                    let! n = Gen.choose (1, 100)
                    let! k = Gen.choose (1, 100)
                    let! m = Gen.choose (1, 100)

                    let getMatrix (n, m) =
                        gen {
                            let mat = Array2D.create n m false
                            let elems = n * m
                            let! nonBaseElems = Gen.choose (0, elems / 100 + elems % 100)

                            for _ in 1..nonBaseElems do
                                let! x = Gen.choose (0, n - 1)
                                let! y = Gen.choose (0, m - 1)
                                mat[x, y] <- true

                            return mat
                        }

                    let! mat1 = getMatrix (n, k)
                    let! mat2 = getMatrix (k, m)
                    return (mat1, mat2)
                }

            Arb.fromGen (twoBoolSparseMatricesGenerator)

    [<Property(Arbitrary = [| typeof<IntSparseMatrices> |])>]
    let sparseMatrixIntProduct (mat1: int array2d, mat2: int array2d) =
        let tr1 = mat1 |> QuadTree.ofMatrix
        let tr2 = mat2 |> QuadTree.ofMatrix
        let actual = (QuadTree.multiply (*) (+) 0 tr1 tr2) |> QuadTree.toMatrix

        let expected = Utility.multiply (*) (+) 0 mat1 mat2

        expected = actual

    [<Property(Arbitrary = [| typeof<BoolSparseMatrices> |])>]
    let sparseMatrixBoolProduct (mat1: bool array2d, mat2: bool array2d) =
        let tr1 = mat1 |> QuadTree.ofMatrix
        let tr2 = mat2 |> QuadTree.ofMatrix
        let actual = (QuadTree.multiply (&&) (||) false tr1 tr2) |> QuadTree.toMatrix

        let expected = Utility.multiply (&&) (||) false mat1 mat2

        expected = actual


module DoubleMultiplication =

    type AdjacencyMatrix =
        static member AdjacencyMatrix() =
            let adjacencyMatrixGenerator =
                gen {
                    let! n = Gen.choose (2, 5)

                    let getMatrix n =
                        gen {
                            let mat = Array2D.init n n (fun x y -> x = y)
                            let elems = n * n
                            let! nonBaseElems = Gen.choose (0, elems / 100 + elems % 100)

                            for _ in 1..nonBaseElems do
                                let! x = Gen.choose (0, n - 1)
                                let! y = Gen.choose (0, n - 1)
                                mat[x, y] <- true

                            return mat
                        }

                    let! mat = getMatrix n
                    return mat
                }

            Arb.fromGen (adjacencyMatrixGenerator)

    [<Property(Arbitrary = [| typeof<AdjacencyMatrix> |])>]
    let doubleMultiplicationBool (mat: bool array2d) =
        let tr = QuadTree.ofMatrix mat

        let expected =
            let first = Utility.multiply (&&) (||) false mat mat
            Utility.multiply (&&) (||) false first mat

        let actual =
            let first = QuadTree.multiply (&&) (||) false tr tr
            QuadTree.multiply (&&) (||) false first tr

        let actual = QuadTree.toMatrix actual

        expected = actual


    [<Property>]
    let doubleMultiplication (n: uint) (m: uint) (k: uint) (d: uint) =
        let n, m, k, d = (int n) + 1, (int m) + 1, (int k) + 1, (int d) + 1
        let mat1 = Utility.getRandomArray2D n m
        let mat2 = Utility.getRandomArray2D m k
        let mat3 = Utility.getRandomArray2D k d

        let expected =
            let first = Utility.multiply (*) (+) 0 mat1 mat2
            Utility.multiply (*) (+) 0 first mat3

        let actual =
            let tr1 = QuadTree.ofMatrix mat1
            let tr2 = QuadTree.ofMatrix mat2
            let tr3 = QuadTree.ofMatrix mat3

            let first = QuadTree.multiply (*) (+) 0 tr1 tr2
            QuadTree.multiply (*) (+) 0 first tr3

        let actual = QuadTree.toMatrix actual

        expected = actual
