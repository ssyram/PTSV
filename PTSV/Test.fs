module PTSV.Test

open System
open FSharp.Text.Lexing
open Microsoft.FSharp.Collections
open Parser
open PTSV.Core
open PTSV.Global
open PTSV.Input
open ParserSupport
open PTSV.Translation
open NewEquationBuild
open Utils
open ShortAlgorithms

let testBSCC () = 
    let graph = {
        nodes = [0; 1; 2];
        nextNodes = HashMap.fromSeq [(0, [1; 2]); (1, [2])]; 
    } in
    printfn "BSCCs: "
    foldWith (bottomStronglyConnectedComponents graph.toGraph) () $ fun bscc () -> 
        let str = foldWith bscc "" $ fun v pre -> if isNullSeq pre then $"{v}" else $", {v}" in
        printfn $"[{str}]"

/// the example of language "a^nb^na^mc^n"
/// the result for p1 = 0.3, p2 = 0.2, p3 = 0.5 is x0 = 0.04418262...
/// the simplification alone can compute the right result
let genSampleKPTSA1 () =
    let p1 = NumericType.Parse "0.3"
    let p2 = NumericType.Parse "0.2"
    let p3 = NumericType.Parse "0.5"
    let l = [
        (0,0,0,p1,TransUp(0,0,1))
        (0,0,0,p2 + p3,TransDiv)
        (0,0,1,p1,TransUp(0,0,1))
        (0,0,1,p2,TransDown(1,2))
        (0,0,1,p3,TransDiv)
        (1,0,1,p2,TransDown(1,1))
        (1,0,1,NUMERIC_ONE - p2, TransDiv)
        (1,0,0,p3,TransUp(0,0,1))
        (1,0,0,p1,TransState 1)
        (0,1,1,p3,TransUp(0,0,1))
        (0,2,1,NUMERIC_ONE,TransTer)
    ]
    let ptsa = CodeInput.genKPTSA 2 l
    ptsa
/// the example of Stochastic CFG: S -(p)-> SS, S -(1 - p)-> \tt
/// the result should be:
/// p <= 1/2 : P = 1
/// p > 1/2 : (1 - p) / p
/// Test Passed for p = 0.8, we can compute the result by hand
/// Test Passed for p = 0.333, we can compute the result by hand
let genSampleKPTSA2 p =
    let l = [
        (0,0,0,p,TransUp (0,1,1))
        (0,0,0,NUMERIC_ONE - p,TransTer)
        (0,1,0,NUMERIC_ONE,TransUp (0,2,2))
        (0,2,0,NUMERIC_ONE,TransTer)
        (0,0,1,p,TransUp (0,1,1))
        (0,0,1,NUMERIC_ONE - p,TransDown (0,3))
        (0,1,1,NUMERIC_ONE,TransUp (0,2,2))
        (0,2,1,NUMERIC_ONE,TransDown (0,3))
        (0,0,2,p,TransUp (0,1,1))
        (0,0,2,NUMERIC_ONE - p,TransDown (0,3))
        (0,1,2,NUMERIC_ONE,TransUp (0,2,2))
        (0,2,2,NUMERIC_ONE,TransDown (0,3))
    ]
    CodeInput.genKPTSA 1 l
let sampleKPTSA = genSampleKPTSA1 ()

let testSet1 = [    // in this set, all states should have probability 1 to termination
    (0,0,0,NumericType.Parse "0.3",TransState 1)
    (0,0,0,NumericType.Parse "0.4",TransTer)
    (0,0,0,NumericType.Parse "0.3",TransState 2)
    (1,0,0,NumericType.Parse "0.1",TransState 0)
    (1,0,0,NumericType.Parse "0.5",TransTer)
    (1,0,0,NumericType.Parse "0.4",TransState 2)
    (2,0,0,NumericType.Parse "1.0",TransState 0)
]
/// hand compute result for the following:
/// Up 1: x0 = 0.84 (21/25), x1 = 0.6 (3/5), x2 = x3 = 0
/// Up 2: x0 = 0.08, x1 = 0.2, x2 = x3 = 0
/// Up 3: x0 = 0.016, x1 = 0.04, x2 = 0.2, x3 = 0
/// test passed, all the same
let testSet2 = [
    (0,0,0,NumericType.Parse "0.4",TransState 1)
    (0,0,0,NumericType.Parse "0.6",TransUp (0,0,1))
    (1,0,0,NumericType.Parse "0.5",TransState 0)
    (1,0,0,NumericType.Parse "0.3",TransState 1)
    (1,0,0,NumericType.Parse "0.1",TransUp (0,0,2))
    (1,0,0,NumericType.Parse "0.1",TransState 2)
    (2,0,0,NumericType.Parse "0.2",TransUp (0,0,3))
    (2,0,0,NumericType.Parse "0.2",TransState 3)
]// to test the validity, just compare it with the previous implementation
let variableToNewVar isExpEnv var =
    match var with
    | PVCProb (VTrips (D, g)) -> (D, g, if isExpEnv then NVTProbTrips else NVTTrips) 
    | PVCProb (VTer (D, g)) -> (D, g, NVTTer)
    | PVCExp (VTrips (D, g)) -> (D, g, NVTTrips)
    | PVCExp (VTer (D, g)) -> (D, g, NVTTer)
    | _ -> undefined ()  // no definition for other kinds
let rec mapVariableFormulaToNewVarFormula isExpEnv var =
    let recall = mapVariableFormulaToNewVarFormula isExpEnv in
    match var with
    | FAdd (f1, f2) -> FAdd (recall f1, recall f2)
    | FMul (f1, f2) -> FMul (recall f1, recall f2)
    | FConst c      -> FConst c
    | FVar v        -> FVar $ variableToNewVar isExpEnv v


// test the new implementation
let rec testNewImpl () =
    let kptsa = obtainModel () in
    let rptsa = generaliseKPTSA kptsa in
    let fSys1 = constructKPTSAEqSys kptsa in
    let fSys2 = constructRPTSAEqSys rptsa in
//    printfn $"{printNewFormulaSystem fSys1}";
//    printfn $"{printNewFormulaSystem fSys2}"
    let eq1, map = formulaSystemToExprSystemWithHint fSys1 Map.empty in
    let eq2 = fst $ formulaSystemToExprSystemWithHint fSys2 map in
    let eq1 = List.sortBy fst $ optimiseExprSystem eq1 in
    let eq2 = List.sortBy fst $ optimiseExprSystem eq2 in
    let eq2 = constSubsAndOneStepSimplForSorted eq2 in 
    printfn $"{printExprSystem eq1}"; 
    printfn $"{printExprSystem eq2}";
    printfn $"Equals = {foldWith (Seq.map (uncurry (=)) $ zip eq1 eq2) true (&&)}"
and obtainModel () =
    match TextInput.parseFile "../../../examples/PAHORS/example 12.txt" with
    | MPAHORS pahors -> (PAHORS2KPTSA.translate pahors).rptsa 
    | _              -> IMPOSSIBLE ()
and constructKPTSAEqSys kptsa = constructNewPrimitiveFormulaSystem true false kptsa
and constructRPTSAEqSys rptsa =
    let mapper (v, f) = (variableToNewVar false v, mapVariableFormulaToNewVarFormula false f) in 
    Seq.toList (Seq.map mapper $ terProbFormulaConstruct false rptsa)
and constSubsAndOneStepSimplForSorted eqs =
    let eqs = List.toArray eqs in 
    let mapper (k, e) = (k, flip substituteVar e $ fun idx ->
                            match snd eqs[idx] with EConst c -> EConst c | _ -> EVar idx) in 
    let eqs = Array.toList $ Array.map mapper eqs in
    optimiseExprSystem eqs
    

let testEpsilonElimination () =
    let targetTestSet = testSet1
    
    let kptsa = epsilonElimination false (CodeInput.genKPTSA 1 targetTestSet)
//    let kptsa = epsilonElimination (genSampleKPTSA1 ())
    printfn $"{Output.recoverStringDefinitionFromKPTSA kptsa}"

let testExpectedTerminationTime () =
    failwith "todo"

/// interact with redlog
let tryInteraction programPath =
    let p = new System.Diagnostics.Process ()
    p.StartInfo.FileName <- "/usr/bin/env"
    let commandList = [| "-S"; "bash"; "-c"; programPath |]
    for e in commandList do
        p.StartInfo.ArgumentList.Add e
    p.StartInfo.RedirectStandardInput <- true
    p.StartInfo.RedirectStandardOutput <- true
    p.StartInfo.CreateNoWindow <- true
    p.StartInfo.UseShellExecute <- false
    p.Start () |> ignore
    
    let write (s : string) = p.StandardInput.WriteLine s
    
    write "load_package redlog;"
    write "rlset reals;"
    write "rlqe ex(x, x + 1 = 0);"
    write "quit;"
    p.StandardInput.Flush ()
    p.StandardInput.Close ()
    printfn $"{p.StandardOutput.ReadToEnd ()}"
    p.WaitForExit ()

let constructExprSystemFromKPTSA kptsa =
    let es = constructPrimitiveEquationSystem_Old kptsa
    formulaSystemToExprSystem x0 es

let testApproximateByQuantitativeREDUCE () =
    let es = constructExprSystemFromKPTSA
                (genSampleKPTSA2 (NumericType.Parse "0.5"))
    let res =
        Problems.ApproximationProblem.approximateByQualitativeREDUCE
            External.REDUCE_PATH
            Flags.APPROX_ACCURACY
            es
    printfn $"Approximation Result: {res}"

let printLexbuf lexbuf =
    let mutable t = Lexer.token lexbuf
    while t <> EOF do
        let pt =
            match t with
            | ID s -> $"ID ({s})"
            | DOUBLE p -> $"Float ({p})"
            | INT p -> $"Int ({p})"
            | _ -> token_to_string t
        printfn $"Token Acquired: {pt}"
        t <- Lexer.token lexbuf
    printfn "EOF GET"

let tryRunREDUCEProgram () =
    let p = runREDUCEInteractiveProgram External.REDUCE_PATH
    let mutable input = Console.ReadLine ()
    while input <> "quit" do
        printfn $"{p (Some input)}"
        input <- Console.ReadLine ()
    printfn $"{p None}"
    ()

//let testQuantitativeByREDUCE () =
//    let kptsa = genSampleKPTSA2 0.667
//    let es = constructPrimitiveEquationSystem kptsa
//    let es = simplifyExprSystem (formulaSystemToExprSystem es)
//    let res =
//        Run.QuantitativeProblem.quantitativeByREDUCE
//            Run.QuantitativeProblem.LessThanOrEqualTo
//            0.25
//            es
//    printfn $"{res}"

/// Passed
let testIteratingApproximation () =
    let approx = Run.runFromKPTSA (genSampleKPTSA2 (NumericType.Parse "0.49"))
    printfn $"Approximation Number is {approx}"

/// Passed
let testRecoverFromKPTSADef () =
    let kptsa = genSampleKPTSA2 (NumericType.Parse "0.8")
    let s = Output.recoverStringDefinitionFromKPTSA kptsa
    printfn $"{s}"
    let ps = "%BEGINA " + $"{s}" + " %ENDA"
    printfn $"{TextInput.parseString ps}"

let tryApproximatingKPTSAExample2ExpectedTerminationTime (p : NumericType) times =
    let mutable ret = NUMERIC_ZERO
    let C2n'n n =
        if n = 0 then NUMERIC_ONE
        else
            let mutable ret = NUMERIC_ONE
            for i = 1 to n do
                ret <- ret * ((NumericType n) + i) / i
            ret
    for n = 0 to times do
        ret <- NumericType.RoundUp ret
        let n = NumericType n
        let add =
               (4 * n + 1) / (n + 1) *
                   (C2n'n (NumericType.ToInt n)) *
                   (NumericType.Pow (p, n)) * (NumericType.Pow (1 - p, n))
        Console.Write $"\rCurrent n = {n}, res = {NumericType.ToDouble ret}                               "
        ret <- ret + add
    ret

// stepCount n = ratio * n + initVal
let newTryApproximatingS2SSOrS2tt initVal ratio (p : NumericType) times =
    let mutable curRatio = 1 - p
    let accRatio = p * (1 - p)
    let mutable stepCount = initVal
    let mutable catalan = NUMERIC_ONE
    let mutable ret = curRatio * stepCount * catalan
    try
        for i in 1 .. times do
            // update paras
            curRatio <- curRatio * accRatio
            stepCount <- stepCount + ratio
            catalan <- catalan * (4 * i - 2) / (i + 1)
            // update ret
            let nRet = ret + curRatio * stepCount * catalan
            if nRet =~= ret then
                raise BreakMarkException
            ret <- nRet
        ret
    with
    | :? BreakMarkException -> ret

/// a self-contain unit to test the value of ETT of Example 2 in PAHORS
let testPAHORSExample2Value prob =
    let s = newTryApproximatingS2SSOrS2tt
                // 2n + 1
                (NumericType 1)
                (NumericType 2)
                // p
                prob
                1000
    let trueVal =
        if prob > NumericType 1/2 then
            s * prob / (1 - prob)
        else
            prob
    // + 1, because S -> F tt count as one, this is a constant cost
    printfn $"{1. + NumericType.ToDouble trueVal}"

/// computes exactly the ETT value of PAHORS Example 2
let valueOfPAHORSExample2 (p : NumericType) =
    if p > NUMERIC_ONE || p < NUMERIC_ZERO then
        failwith "Invalid probability."
    if p < NumericType 1/2 then
        (2 - 2 * p) / (1 - 2 * p)
    elif p > NumericType 1/2 then
        2 * p / (2 * p - 1)
    else
        failwith "No result with 1/2"

/// Passed
let testParseFile () =
    let s = "../../../samples/sample1.txt"
    printfn $"{TextInput.parseFile s}"

/// Passed
let testKPTSAParser () =
    let stringToTest =
        "%BEGINA
        restriction := 2
        q0 := q0
        m0 := m0
        gamma0 := g0
        (q0,m1,g1,0.5,(q0,m0,UP g1))
        (q0,m0,g0,0.3,(q0,m0,Up g1))
        (q0,m0,g0,0.7,Omega)
        (q0,m0,g1,0.3,(q0,m0, Up g1))
        (q0,m0,g1,0.2,(q1,m2, DOwn))
        (q0,m0,g1,0.5,Omega)
        (q1,m0,g1,0.2,(q1,m1, DOWn))
        (q1,m0,g1,0.8, Omega)
        (q1,m0,g0,0.5,(q0,m0,uP g1))
        (q1,m0,g0,0.3,q1)
        (q0,m2,g1,1,tt)
        %ENDA"
    let lexbuf = LexBuffer<_>.FromString stringToTest
    printLexbuf lexbuf
    match TextInput.parseString stringToTest with
    | MKPTSA kptsa -> printfn $"{kptsa}"
    | _ -> failwith "Impossible."

/// Passed
let testLexer () =
    let stringToTest = "as s b as restriction := 10 (* abc *) k := 10.5 \n dlkadg \t \r\n abcde as"
    let lexbuf = LexBuffer<_>.FromString stringToTest
    printLexbuf lexbuf

/// passed
let testExprSystem () =
    let es = constructPrimitiveEquationSystem_Old sampleKPTSA
    let es = formulaSystemToExprSystem x0 es
    printfn $"{es.Length}"
    printfn $"{Output.printExprSystem es}"
    let es = simplifyExprSystem FPTLeast es
    printfn $"{es.Length}"
    printfn $"{Output.printExprSystem es}"

/// passed
let testConstructPrimitiveEquationSystem () =
    let es = constructPrimitiveEquationSystem_Old sampleKPTSA
    let es = List.map (fun (v, f) -> (v, optimiseFormula f)) es
    printfn $"{es.Length}"
    printfn $"{Output.printFormulaSystem es None}"

/// passed
let testCodeInput () =
    printfn $"{sampleKPTSA}"

/// passed
let testPrintFormula () =
    let f = FVar x0 + FConst (NumericType.Parse "0.5")
    printfn $"{(Output.printFormula f None)}"

/// passed
let testPAHORSParserAndPrinter () =
    // as this string is not to be checked, no need to keep this valid, just test if it can produce the right thing.
    let stringToTest =
        "%BEGINT
         S : o
         F : (o & o -> o) & o -o o -> (o -> o & o)  // both '-o' and '->' are allowed, and the meaning is the same here
         
         %ENDT
         %BEGING
         S :=(0.5) F tt;
         S :=(0.5) \pi(2) <F S, F (\pi(1) <F Omega>)>;
         F x :=(0.1) x;
         F x y :=(1) F S S (\pi(10) <F tt, F (x (y tt))>);
         F :=(0.9) Omega;
         %ENDG"
    let pahors =
        match TextInput.parseString stringToTest with
        | MPAHORS pahors -> pahors
        | _ -> failwith "Impossible."
    printfn "Types are:"
    Array.iter
        (fun (ntNo, ty) -> printfn $"{printNonTerminal pahors ntNo}: {printType ty}")
        (Array.indexed pahors.nonTerminals)
    printfn ""
    printfn "Rules are:"
    Array.iter
        (fun (ntNo, l) ->
            Array.iter
                (fun (rNo, _) -> printfn $"{printRule pahors (ntNo, rNo)}")
                (Array.indexed l))
        (Array.indexed pahors.rules)
    printfn ""
    printfn "Rule para amounts are:"
    Array.iter
        (fun (ntNo, l) ->
            Array.iter
                (fun (rNo, paraAmount) -> printfn $"{printNonTerminal pahors ntNo}'s {rNo} rule: {paraAmount}")
                (Array.indexed l))
        (Array.indexed pahors.nonTerminalActualPara)
    
/// passed
let testPAHORSValidityCheck () =
    let pahors =
        match TextInput.parseFile "../../../samples/PAHORSTestSet.txt" with
        | MPAHORS pahors -> pahors
        | _ -> failwith "Impossible."
    try
        pahorsValidityChecking pahors |> ignore
    with
    | e ->
        printfn $"{e.Message}"
    printfn $"Test Passed."

/// Passed.
let testPAHORS2KPTSAConvert () =
    let pahors =
        match TextInput.parseFile "../../../samples/PAHORSTestSet.txt" with
        | MPAHORS pahors -> pahors
        | _ -> failwith "Impossible."
    try pahorsValidityChecking pahors |> ignore with
    | e -> failwith $"{e.Message}"
    printfn $"Validity Check Passed."
    let kptsa = (PAHORS2KPTSA.translate pahors).rptsa
    let kptsa = epsilonElimination_Simple kptsa
    printfn $"{Output.recoverStringDefinitionFromKPTSA kptsa}"
    printfn $"The map is:"
    
    let es = constructExprSystemFromKPTSA kptsa
//    let es = simplifyExprSystem es
    let res = Problems.ApproximationProblem.approximateByQuantitativeNLSat (NumericType.Parse "0.0001") es
    printfn $"termination probability = {res}"


let printLaTeXMatrixInfo matrix vec lineInfo columnInfo =
    let topInfo =
        Seq.map (fun _ -> " c") columnInfo
        |> Seq.reduce (+)
        |> fun x -> "c |" + x + " | c" in
    let columnInfo =
        Seq.map (fun x -> $"& {x}") columnInfo
        |> Seq.reduce (+)
        |> fun x -> x + " & " in
    Seq.zip3 lineInfo matrix vec
    |> Seq.map (fun (lineNum, line, vecNum) ->
        Seq.map (fun x -> $"& {x}") line
        |> Seq.reduce (+)
        |> fun x -> $"{lineNum} {x} & {vecNum}")
    |> Seq.map (fun x -> x + "\\\\\n")
    |> Seq.reduce (+)
    |> fun x ->
        $"\\begin{{tabular}}{{{topInfo}}} \n {columnInfo} \\\\\n \\hline\n{x}\\end{{tabular}}"

/// test passed
let testGaussianElimination () =
    // test suit 1
    let matrix =
        [|
            [| 1; 2 |];
            [| 2; 1 |];
        |]
    in
    let vec = [| 2; 1 |] in
    // test suit 2
    let matrix =
        [|
            [| 0; 2;  5; 3 |];
            [| 2; 0;  0; 5 |];
            [| 4; 8; 20; 12 |]
            [| 4; 0;  0; 10 |];
            [| 2; 4; 10; 6 |];
        |] in 
    let vec = [| 3; 6; 2; 4; 12 |] in 
    let matrix = matrix |> Array.map (Array.map NumericType) in
    let vec = vec |> Array.map NumericType in
    let matrix, vec, lineLog, columnLog =
        gaussianUpperRightTrapezium false (NumericTypeHelper ()) matrix vec in
    printfn $"{printLaTeXMatrixInfo matrix vec lineLog columnLog}"

let testGaussianPositiveLFP () =
    let matrix =
        [|
            [| 1; 2 |];
            [| 2; 1 |];
        |]
    in
    let vec = [| 2; 1 |] in
    let matrix =
        [|
            [| 0; 9; 5 |];
            [| 1; 8; 6 |];
            [| 9; 1; 7 |]
        |] in 
    let vec = [| 9; 9; 10 |] in 
    let matrix = matrix |> Array.map (Array.map NumericType) in
    let vec = vec |> Array.map NumericType in
    match Option.map printFullSeq $ gaussianPositiveLFP matrix vec with
    | Some arr -> printfn $"Solution: {arr}."
    | None     -> printfn "No Solution."

// the backup `main` function
//let main argv =
//    let settings : Dictionary<string, string> = Dictionary<_, _>()
//    settings.Add ("model", "true")
//    use ctx = new Context (settings)
//    let x = ctx.MkConst("x", ctx.RealSort) :?> ArithExpr
//    let solver = ctx.MkSolver ()
//    solver.Assert (ctx.MkBool true)
//    for expr in solver.Assertions do
//        printfn $"{expr.ToString ()}"
//    let nlsatSolver = ctx.MkSolver "QF_NRA"  // QF_NRA to enable NLSat
//    let solver = ctx.MkSolver ()
//    let e = ctx.ParseSMTLIB2String("(declare-const a Real)")
//    Global.SetParameter("z3 nlsat", "true")
//    printfn $"{1.0}"
//    let argv = [|"../../../samples/sample2.txt"|]
    
    
    
//    let TRUESTRING = "(= x0 0.2)"
//    Run.runFromFile
//        "../../../samples/sample2.txt"
//        (fun es ->
//            let be = ctx.ParseSMTLIB2String (Output.genNLSatQueryString es TRUESTRING)
//            printfn $"{nlsatSolver.Check be}"
//            ProblemResultType.PRTQuantitative true
//            )
//        |> ignore
//    Run.printRunResult (Run.runFromKPTSA
//        (Test.genSampleKPTSA2 0.3)
//        (ApproximationProblem.approximationWrapperFunc
//            (ApproximationProblem.approximateByQualitativeNLSat Flags.APPROX_ACCURACY)))
//    0

