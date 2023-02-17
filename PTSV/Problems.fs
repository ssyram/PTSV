module PTSV.Problems

open System
open PTSV
open PTSV.Core
open PTSV.Global
open PTSV.Utils

type ProblemResultType =
    | PRTQuantitative of bool
    | PRTAlmostSureTerminate
    | PRTImpossible
    | PRTPossibleButNonAST
    | PRTUnknown
    | PRTPositiveAlmostSureTermination
    | PRTApproximation of NumericType * ProblemResultType
    | PRTOmegaModelCheck of NumericType

let getResultImmediately es =
    List.fold
        (fun ns (i, e) ->
            match ns with
            | Some _ -> ns
            | None ->
                if i = 0 then
                    match e with
                    | EConst c -> Some c
                    | _ -> None
                else None)
        None
        es

module QuantitativeProblem =
    type QueryType =
        | Equal                 // =
        | LessThanOrEqualTo     // <=
        | LessThan              // <
        | NotEqual              // /=
        | GreaterThan           // >
        | GreaterThanOrEqualTo  // >=
        
        static member Parse (str : string) =
            match str with
            | "=" | "==" -> Equal
            | "<=" -> LessThanOrEqualTo
            | "<" -> LessThan
            | "/=" | "!=" | "<>" -> NotEqual
            | ">" -> GreaterThan
            | ">=" -> GreaterThanOrEqualTo
            | _ -> failwith "Invalid string format for query comparator."
        
        override qt.ToString () =
            match qt with
            | Equal -> "="
            | LessThanOrEqualTo -> "<="
            | LessThan -> "<"
            | NotEqual -> "<>"
            | GreaterThan -> "<="         // choose the false case, do not use this directly
            | GreaterThanOrEqualTo -> "<" // choose the false case, do not use this directly
        
    let queryType2String qt = $" {qt} "
        
    
    /// query type + query number + equation system + Quantitative
    type QuantitativeProblemFunc =
        QueryType -> NumericType -> (int * Expr) list -> bool
    let quantitativeByREDUCE _REDUCEProgramPath qt qNum es =
        let contentString =
            "x0" + queryType2String qt + $"{qNum}"
        let q = Output.genREDUCEQueryString es contentString
        let res = runREDUCEQuantifierElimination _REDUCEProgramPath q
        match qt with
        | GreaterThan | GreaterThanOrEqualTo -> not res
        | _ -> res
        
    let quantitativeByNLSatWithEsQuery esQuery qt qNum =
        let ctx, nlsatSolver = genNewZ3Context ()  // QF_NRA to specify using NLSat
        let query = ctx.ParseSMTLIB2String esQuery in
        nlsatSolver.Assert query
        
        match qt with
        | Equal | NotEqual ->
            let query = ctx.ParseSMTLIB2String
                            ($"(declare-const {Output.printExprVariable 0} Real)" +
                             $"(assert (<= {Output.printExprVariable 0} {Output.lispPrintProbability qNum}))")
            let res =
                // <= c
                if turnZ3SolverResultIntoBool nlsatSolver query then
                    let query2 = ctx.ParseSMTLIB2String
                                    ($"(declare-const {Output.printExprVariable 0} Real)" +
                                     $"(assert (< {Output.printExprVariable 0} {Output.lispPrintProbability qNum}))")
                    // >= c
                    turnZ3SolverResultIntoBool nlsatSolver query2 |> not
                else
                    false
            match qt with
            | Equal -> res
            | NotEqual -> not res
            | _ -> failwith "IMPOSSIBLE"
        | _ ->
            let query = ctx.ParseSMTLIB2String
                            ($"(declare-const {Output.printExprVariable 0} Real)" +
                             $"(assert ({queryType2String qt} {Output.printExprVariable 0} {Output.lispPrintProbability qNum}))")
            let res = turnZ3SolverResultIntoBool nlsatSolver query
            match qt with
            | GreaterThan | GreaterThanOrEqualTo -> not res
            | _ -> res
//        let queryString =
//            match qt with
//            | NotEqual -> $"(not (= x0 {Output.lispPrintProbability qNum}))"
//            | _ -> $"({queryType2String qt} x0 {Output.lispPrintProbability qNum})"
//        let res = turnZ3SolverResultIntoBool nlsatSolver query
//        match qt with
//        | GreaterThan | GreaterThanOrEqualTo -> not res
//        | _ -> res
        
    /// query type; query number; equation system
    let quantitativeByNLSat qt qNum es =
        quantitativeByNLSatWithEsQuery
            (Output.genNLSatQueryString es "true")
            qt
            qNum
    
    let quantitativeWrapperFunc func es =
        PRTQuantitative (func es)

module QualitativeProblem =
    let qualitativeByQuantitative
            quantitativeFunc
            es =
        match getResultImmediately es with
        | Some e ->
            if e =~= NUMERIC_ONE then PRTAlmostSureTerminate
            elif e <= NUMERIC_ZERO then PRTImpossible
            else PRTPossibleButNonAST
        | None ->
            if quantitativeFunc
                   QuantitativeProblem.GreaterThanOrEqualTo NUMERIC_ONE es then
                PRTAlmostSureTerminate
            elif quantitativeFunc
                     QuantitativeProblem.LessThanOrEqualTo NUMERIC_ZERO es then
                PRTImpossible
            else PRTPossibleButNonAST

module ApproximationProblem =
    let approximateByIteration maxIterRound minDiff es =
        if Flags.ITER_BY_PREMO then
            let res = iterByPReMo es in
            Map(res).[0], None
        else
            let res, rounds = iteratingExprSystem es maxIterRound minDiff in
            snd res[0], Some rounds
    
    let approximateByQualitativeREDUCE _REDUCEProgramPath accuracy es =
        let p = runRedlogInteractiveProgram _REDUCEProgramPath
        let mutable floor = NUMERIC_ZERO
        let mutable ceiling = NUMERIC_ONE
        while ceiling - floor > accuracy do
            let numToTest = (ceiling - floor) / (NumericType 2) + floor
            let query = Output.genREDUCEQueryString es $"x0 <= {numToTest}"
            let resString = p (Some query)
            if resString.Contains "true" then
                ceiling <- numToTest
            elif resString.Contains "false" then
                floor <- numToTest
            else failwith $"Runtime Error: REDUCE Produced Wrong Result: {resString}"
        p None |> ignore
        ceiling
    
    /// returns the larger value rather than the smaller one
    let approximateByQuantitativeNLSat accuracy es =
        let ctx, nlsatSolver = genNewZ3Context ()
        let query = Output.genNLSatQueryString es "true"
        if Flags.INNER_DEBUG then
            printfn "Acquired NLSat Query String: "
            printfn $"{query}"
        nlsatSolver.Assert (ctx.ParseSMTLIB2String query)
        if Flags.INNER_DEBUG then
            printfn "Acquired NLSat Assertions: "
            for expr in nlsatSolver.Assertions do
                printfn $"{expr}"
//        let nlsatTRUE = [||]
//        if not (turnZ3SolverResultIntoBool nlsatSolver nlsatTRUE) then
//              failwith "There is no solution to this equation system."
//        printfn "There is at least one solution to this equation system."
        let ret =
            snd $ bisectionApproximation NUMERIC_ZERO NUMERIC_ONE accuracy
                (fun numToTest ->
                    checkTimeOut $"the current approximation number: {numToTest}"
                    if Flags.DEBUG then
                        Console.Write $"\rTesting Number: {numToTest}, time elapsed: {Flags.GLOBAL_TIMING.totalTime ()}s.     "
                    let query =
                        ctx.ParseSMTLIB2String
                            ($"(declare-const {Output.printExprVariable 0} Real)" +
                             $"(assert (<= {Output.printExprVariable 0} {Output.lispPrintProbability numToTest}))")
                    turnZ3SolverResultIntoBool nlsatSolver query)
        if Flags.DEBUG then
            printfn ""
        ret
    
    let approximationWrapperFunc func es =
        match getResultImmediately es with
        | Some e ->
            if e = NUMERIC_ONE then
                PRTApproximation (e, PRTAlmostSureTerminate)
            elif e = NUMERIC_ZERO then
                PRTApproximation (e, PRTImpossible)
            else
                PRTApproximation (e, PRTPossibleButNonAST)
        | None ->
            let numRes = func es
            try
                let quaRes =
                    if not Flags.NO_QUALITATIVE_RESULT then
                        QualitativeProblem.qualitativeByQuantitative
                            QuantitativeProblem.quantitativeByNLSat
                            es
                    else PRTUnknown
                PRTApproximation (numRes, quaRes)
            with
            | _ -> PRTApproximation (numRes, PRTUnknown)
