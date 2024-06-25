/// Run format:
///
/// There are two information that is to be specified
/// One is the model description, which can be:
///     a string or a file or just internal code
///     For the code case, one must already know model type
/// The other is problem function, which accepts the generated equation system
///     and answer the three types of questions on x0
module PTSV.Run

open System
open System.Text.Json
open System.Threading
open Global

open System.IO
open Microsoft.FSharp.Collections
open Microsoft.FSharp.Core
open Microsoft.FSharp.Reflection
open PTSV
open PTSV.Core
open PTSV.Input
open PTSV.NewEquationBuild
open PTSV.Problems
open ParserSupport
open PTSV.Translation
open ExampleGenerators
open MultipleContextFreeGrammar
open Utils
open PAHORSExampleGenerator
open PTSV.ProbabilisticPushDownAutomaton

let printFormulaSystem lst =
    if Flags.NOT_PRINT_EQ_SYS then ""
    else
        flip Seq.map lst (fun (v, f) -> $"{v} = {f}\n")
        |> Seq.reduce (+)
let isFConst = function | FConst _ -> true | _ -> false
let rec substituteVarInFormula varMap f =
    match f with
    | FVar v -> varMap v
    | FConst c -> FConst c
    | FAdd (f1, f2) -> FAdd (substituteVarInFormula varMap f1,
                             substituteVarInFormula varMap f2)
    | FMul (f1, f2) -> FMul (substituteVarInFormula varMap f1,
                             substituteVarInFormula varMap f2)
let substituteConstInFormulaSystem fs =
    let replaceMap =
        flip Seq.map fs (fun (v, f) -> 
            (v, match f with
                | FConst _ -> f
                | _        -> FVar v))
        |> HashMap.fromSeq
    Seq.filter (snd >> isFConst >> not) fs
    |> Seq.map (BiMap.sndMap (substituteVarInFormula (flip HashMap.find replaceMap)))
/// a very naive simplification to formula systems
let tmpSimplifyFormulaSystem fs =
    substituteConstInFormulaSystem fs
    |> Seq.map (fun (v, f) -> (v, optimiseFormula f))
    |> substituteConstInFormulaSystem
let rec convertEquationToFormula vMap e =
    let recall = convertEquationToFormula vMap in
    match e with
    | EAdd (e1, e2) -> FAdd (recall e1, recall e2)
    | EVar vId -> vMap vId
    | EConst c -> FConst c
    | EMul (e1, e2) -> FMul (recall e1, recall e2)
    | _ -> failwith "INTERNAL: should not appear"
let backToFormulaSystem esMap es =
    let forMap =
        Map.toSeq esMap
        |> Seq.map swap
        |> HashMap.fromSeq in
    let mapV = flip HashMap.find forMap in
    Seq.map (fun (v, e) -> (mapV v, convertEquationToFormula (mapV >> FVar) e)) es
let newFormulaSystemToGeneralVariableFormulaSystem fs =
    let vMap (D, g, vType) =
        match vType with
        | NVTTrips -> PVCExp (VTrips (D, g))
        | NVTTer   -> PVCExp (VTer (D, g))
        | NVTProbTrips -> PVCProb (VTrips (D, g)) in
    Seq.map (fun (v, f) -> (vMap v, substituteVarInFormula (vMap >> FVar) f)) fs
    
let solveExpectedTerminationTimeExprSystem es =
    let es = Seq.sortBy fst es in
    let mat, arr, matMap = linearEquationSystemToMatrixVec es in
    let dimVarIndices =
        Seq.map swap matMap
        |> Array.ofSeq
        |> Array.sortBy snd
        |> Array.map fst
    in
    Option.map (Array.zip dimVarIndices >> Map.ofSeq) $ gaussianPositiveLFP mat arr
    
///// Put the raw kptsa to this place, do not conduct epsilon elimination or so
/////
///// If don't need the approximation value, return constant 1 for there is a value
//let checkPositiveAlmostSureTermination incremental needApproxValue kptsa =
//    innerDebugPrint "Original rPTSA definition."
//    innerDebugPrint $"{kptsa}"
//    let kptsa = epsilonElimination true kptsa
//    innerDebugPrint "rPTSA definition for expected time computation."
//    innerDebugPrint $"{kptsa}"
//    let rptsa = generaliseKPTSA kptsa in
//    let (probPartPes, ettPartPes), x0 =
//        let probPart, incremental = incremental in
//        ((Seq.toList probPart,
//            Seq.toList $ terExpFormulaConstruct (Some incremental) Flags.KPTSA_NORMALISED rptsa), 
//          terExpX0 rptsa)
////        (constructPrimitiveExpectedTerminationTimeFormulaSystem
////            Flags.EXPECTED_TERMINATION_TIME_ES_STANDARD_FORM
////            kptsa, x0New)
//    if Flags.INNER_DEBUG && not Flags.NOT_PRINT_EQ_SYS then begin
//        let pes = probPartPes ++ ettPartPes in
//        let pes = tmpSimplifyFormulaSystem pes in
//        let crtProbPart, crtEttPart =
//            constructPrimitiveExpectedTerminationTimeFormulaSystem
//                Flags.EXPECTED_TERMINATION_TIME_ES_STANDARD_FORM
//                kptsa in
//        let crtPes = crtProbPart ++ crtEttPart in
//        let crtPes = List.ofSeq $ tmpSimplifyFormulaSystem crtPes in
//        let crtPes = newFormulaSystemToGeneralVariableFormulaSystem crtPes in
//        printfn "----------------------------------- Obtained equation system for ETT -----------------------------------"
//        printfn $"{printFormulaSystem pes}"
//        printfn "----------------------------------- Obtained correct equation system for ETT -----------------------------------"
//        printfn $"{printFormulaSystem crtPes}";
//        
//        let es, esMap = formulaSystemToExprSystemWithHint (Seq.toList pes) (Map (seq {x0, 0})) in
//        let crtEs, crtEsMap = formulaSystemToExprSystemWithHint (Seq.toList crtPes) (Map (seq {terExpX0 rptsa, 0})) in
//        let es = simplifyExprSystem FPTLeast es in
//        let crtEs = simplifyExprSystem FPTLeast crtEs in
//        printfn "----------------------------------- Obtained equation system for ETT -----------------------------------"
//        printfn $"{printFormulaSystem $ backToFormulaSystem esMap es}"
//        printfn "----------------------------------- Obtained correct equation system for ETT -----------------------------------"
//        printfn $"{printFormulaSystem $ backToFormulaSystem crtEsMap crtEs}"
//    end
//        
//            
//    // re-map
//    let probPartEs, dic = formulaSystemToExprSystemWithHint probPartPes (Map (seq {x0, 0})) in
//    let ettPartEs, dic = formulaSystemToExprSystemWithHint ettPartPes dic in
//    
//    let probPartEs,ettPartEs =
//        let isProbMap =
//            Map.toSeq dic
//            |> Seq.map (BiMap.fstMap (function | PVCProb _ -> true | _ -> false))
//            |> Seq.map swap
//            |> HashMap.fromSeq in
//        simplifyExprSystem FPTLeast (probPartEs ++ ettPartEs)
//        |> List.partition (fst >> flip HashMap.find isProbMap)
//    in
//    eqSysPrint Flags.INNER_DEBUG $"Obtained equation system for ETT:\n{printExprSystem (probPartEs ++ ettPartEs)}";
//    // just use Z3 to know if there is any result
//    let z3Context, nlsatSolver = genNewZ3Context ()
//    let queryString =
//        genNLSatDeclarePart probPartEs true +
//        // bugfix : ett part should not have 1 bound -- it should only >= 0.
//        genNLSatDeclarePart ettPartEs false +
//        genNLSatEsDefPart probPartEs +
//        genNLSatEsDefPart ettPartEs +
//        NLSatTriggerString
//    let checkExistence () =
//        let query = z3Context.ParseSMTLIB2String queryString
//        turnZ3SolverResultIntoBool nlsatSolver query
//    let computeValue () =
//        eqSysPrint true $"{printExprSystem (List.append probPartEs ettPartEs)}"
//        let res =
//            if List.isEmpty probPartEs then
//                solveExpectedTerminationTimeExprSystem ettPartEs
//            else
//                let replaceMap =
//                    if Flags.ITER_BY_PREMO then
//                        Map(iterByPReMo probPartEs)
//                    else
//                        Map(fst $ iteratingExprSystem probPartEs Flags.MAX_ITER_ROUND Flags.APPROX_MIN_DIFF)
//                
//                // to print the final results
//                Map.toSeq replaceMap
//                |> Seq.map (fun (vId, num) -> $"""x{vId} = {num.ToString "N30"}""")
//                |> String.concat "\n"
//                |> eqSysPrint true;
//                
//                let subsFunc vId =
//                    match Map.tryFind vId replaceMap with
//                    | Some c -> EConst c
//                    | None -> EVar vId
//                // bugfix: should use `normalise` rather than `optimise` here
//                //         because the `solveExpectedTerminationTimeExprSystem` function is strict to the shape of
//                //         the input equation system
//                let es = List.map (fun (i, e) -> (i, substituteVar subsFunc e)) ettPartEs in
//                processPrint $"Final ES to solve:\n{printExprSystem es}";
//                // todo: fix this function, let it be better -- make it possible to solve the infinite case
//                solveExpectedTerminationTimeExprSystem es
//        match res with
//        | Some values -> Some values[0]
//        | None -> None
//    if Flags.EXTERNAL_ETT_QUALITATIVE_CONFIRM then
//        if needApproxValue then
//            computeValue ()
//        else Some NUMERIC_ONE
//    else
//        if checkExistence () then
//            if not needApproxValue then Some NUMERIC_ONE
//            else computeValue ()
//        else None

type RunModel =
    | RMKPTSA of KPTSA
    | RMPPDA of ProbPDAut<State, Gamma>
    
type ReuseContext =
    | RC_RPTSA of BuildContext<State,LocalMemory,Gamma,TerOp>
    | RC_PPDA of (EqVar<State,Gamma> * PpdaRHS<State,Gamma> list) list

type RunningContext =
    {
        translateFrom : string option
        translationTime : TimeSpan option
        
        model : RunModel
        reuseCtx : ReuseContext option
        
        tpPrimitiveEqSys :
            (Variable<State,Gamma> * RawFormula<Variable<State,Gamma>>) list option
        tpEqSys : (int * Expr) list option
        tpEqSysVarMap : Map<int,Variable<State,Gamma>> option
        tpResValIter : NumericType option
        tpResValBisec : NumericType option
        tpAST : bool option
        
        ettEqSys : (int * Expr) list option
        ettEqSysVarMap : Map<int,Variable<State,Gamma>> option
        cettQualRes : bool option
        cettResValIter : NumericType option
        cettResValBisec : NumericType option
        rawCettResValIter : NumericType option
        rawCettResValBisec : NumericType option
        
        // other data to collect
        tpEqSysConstructTime : TimeSpan option
        tpEqSysSimplificationTime : TimeSpan option
        tpApproximationTimeIter : TimeSpan option
        tpApproximationTimeBisec : TimeSpan option
        tpIterationRounds : uint64 option
        tpEqSysPrimitiveScale : uint option
        tpEqSysSimplifiedScale : uint option
        tpQualitativeTime : TimeSpan option
        tpQuantitativeTime : TimeSpan option
        
        ettEqSysConstructTime : TimeSpan option
        ettEqSysSimplificationTime : TimeSpan option
        ettIterationRounds : uint64 option
        ettQualitativeTime : TimeSpan option
        ettApproximationTimeIter : TimeSpan option
        ettApproximationTimeBisec : TimeSpan option
        ettEqSysPrimitiveScale : uint option
        ettEqSysSimplifiedScale : uint option
    }
    
let defaultRunningContext model =
    { model = model
      tpEqSys = None
      tpEqSysVarMap = None
      reuseCtx = None
      ettEqSys = None
      ettEqSysVarMap = None
      tpAST = None
      cettQualRes = None
      tpPrimitiveEqSys = None
      tpEqSysConstructTime = None
      tpEqSysPrimitiveScale = None
      tpEqSysSimplifiedScale = None
      tpQualitativeTime = None
      tpQuantitativeTime = None
      ettEqSysConstructTime = None
      ettQualitativeTime = None
      ettEqSysPrimitiveScale = None
      ettEqSysSimplifiedScale = None
      tpEqSysSimplificationTime = None
      ettEqSysSimplificationTime = None
      translateFrom = None
      translationTime = None
      tpIterationRounds = None
      ettIterationRounds = None
      tpResValIter = None
      tpResValBisec = None
      cettResValIter = None
      cettResValBisec = None
      rawCettResValIter = None
      rawCettResValBisec = None
      tpApproximationTimeIter = None
      tpApproximationTimeBisec = None
      ettApproximationTimeIter = None
      ettApproximationTimeBisec = None }

let getTpResVal ctx =
    match ctx.tpResValBisec with
    | Some _ as v -> v
    | None -> ctx.tpResValIter
    
let getEttResVal ctx =
    match ctx.cettResValBisec with
    | Some _ as v -> v
    | None -> ctx.cettResValIter
    
let getEttRawResVal ctx =
    match ctx.rawCettResValBisec with
    | Some _ as v -> v
    | None -> ctx.rawCettResValIter

let inline simplifyPPDA (ppda : ProbPDAut<_,_>) = ppda

let simplifyKPTSA (kptsa : KPTSA) =
    debugPrint "Start Epsilon Elimination ...";
    let simplifyTimingLog = "SimplifyTimeLog" in
    logTimingMark simplifyTimingLog;
    let kptsa = epsilonElimination (Option.isSome kptsa.stepCount) kptsa in
    debugPrint "End Epsilon Elimination";
    debugPrint "Epsilon Eliminated model: ";
    debugPrint $"{kptsa}"
    debugPrint $"Epsilon Elimination Time: {numericValuePrint $ tapTimingMark simplifyTimingLog}";
    kptsa
    
let constructTPEquationSystem model =
    innerDebugPrint "Start constructing primitive formula system..."
//    let model = generaliseKPTSA kptsa in 
    let ctx, pes, x0 =
        match model with
        | RMKPTSA kptsa ->
            let rptsa = generaliseKPTSA kptsa in
            let ctx, pes =
                terProbFormulaConstructWithCtx (isNormalisedRPTSA rptsa) rptsa
            in
            RC_RPTSA ctx, pes, terProbX0 rptsa
        | RMPPDA ppda ->
            let ctx = directBuildPrimitivePpdaEqSys ppda in
            let pes = convertToEqSys_TP ppda ctx in
            let x0 = transVar ppda PVCProb EVX0 in
            RC_PPDA ctx, pes, x0
    in
    innerDebugPrint "Primitive formula system construction finished."
    let str = numericValuePrint $ getTimingFromMark "tpEqSys" in
    innerDebugPrint $"""Primitive Formula System Construction Time: {str}s""";
    let es, transMap =
        formulaSystemToExprSystemWithHint
            (Seq.toList pes)
            (Map.add x0 0 Map.empty)
    in
    let transMap =
        Map.toSeq transMap
        |> Seq.map swap
        |> Map.ofSeq
    in
    es, transMap, ctx, pes
    

let simplifyLFPEqSys es varMap =
    if Flags.SIMPLIFY then begin
        debugPrint "Start simplification..."
        logTimingMark "simplify"
        let es = simplifyExprSystem FPTLeast es in 
        let simplificationTime = tapTimingMark "simplify" in
        debugPrint "Simplification done.";
        debugPrint $"Simplified Equation System (scale {List.length es})";
        if not Flags.NOT_PRINT_EQ_SYS then debugPrint $"{printExprSystemWithVarMap es varMap}";
        es, Some simplificationTime
    end
    else es, None

let private check_K gammaPrinter k pes =
    if Flags.CHECK_K then
        let es, revVarMap = formulaSystemToExprSystemWithHint pes Map.empty in
        let varMap = revMap revVarMap in
        let _, es = iterToFindLFPZeroVariables es in
        List.map (fst >> flip Map.find varMap) es
        |> List.map (fun v ->
            let rv = match v with | PVCProb rv | PVCExp rv -> rv in
            let D, g = match rv with | VTer (D, g) | VTrips (D, g) | VUp (D, g) -> (D, g) in
            (g, List.length D))
        // check the maximum length
        |> List.maxBy snd
        |> fun (g, maxD) ->
            let g = gammaPrinter g in
            if maxD > 2 * k then
                let word =
                    "Warning: " +
                    $"the declared {k}-PTSA has run of more than {k} visits to stack symbol \"{g}\". " +
                    "The result may hence be incorrect."
                in
                errPrint $"{word}"
            elif (maxD + 1) / 2 < k then begin
                debugPrint $"Found real k: {(maxD + 1) / 2}.";
                resultPrint $ RRealK (uint $ (maxD + 1) / 2)
            end
            else ()
//        List.map (fst >> flip Map.find varMap) es
//        |> List.iter (fun v ->
//            let rv = match v with | PVCProb rv | PVCExp rv -> rv in
//            let D, g = match rv with | VTer (D, g) | VTrips (D, g) | VUp (D, g) -> (D, g) in
//            let g = gammaPrinter g in
//            checkDGAndK D g k)
        
let runCheck_K gammaPrinter rptsa =
    if Flags.CHECK_K then begin
        let k = rptsa.k in 
        let rptsa = { rptsa with k = k + 1 } in
        let sp = TerProbCtx () in
        buildEquationSystem rptsa sp |> ignore;
        check_K gammaPrinter k $ sp.getResult ()
    end

let runTerProbEqSysConstruction ctx =
    let model = ctx.model in
    processPrint "Start constructing termination probability equation system...";
    logTimingMark "tpEqSys";
    let es, varMap, reuseCtx, pes = constructTPEquationSystem model in
    debugPrint "";
    processPrint "Equation system construction finished.";
    eqSysPrint Flags.DEBUG $"Initial Equation System:\n{printExprSystemWithVarMap es varMap}";
    let tpEqSysScale = List.length es in
    
    resultPrint $ RTpEqPrimitiveScale (uint tpEqSysScale);
    let tpEqSysConstructTime = getTimingFromMark "tpEqSys" in
    resultPrint $ RTpEqPrimitiveConsTime tpEqSysConstructTime;
    let es, time = simplifyLFPEqSys es varMap in
    resultPrint $ RTpEqSimScale (uint es.Length);
    Option.iter (resultPrint << RTpEqSimpTime) time;
    let tpEqSysConstructTime = tapTimingMark "tpEqSys" in
    resultPrint $ RTpEqTotalConsTime tpEqSysConstructTime;
    es, {
        ctx with
            tpEqSys = Some es
            tpEqSysVarMap = Some varMap
            reuseCtx = Some reuseCtx
            tpPrimitiveEqSys = Some pes
            tpEqSysConstructTime = Some tpEqSysConstructTime
            tpEqSysSimplificationTime = time
            tpEqSysPrimitiveScale = Some $ uint tpEqSysScale
            tpEqSysSimplifiedScale = Some $ uint (List.length es)
    }

let (||>) ctx (flag, func) =
    checkTimeOut (); if flag then func ctx else ctx

let rhsIsConst (_, rhs) =
    match rhs with
    | EConst _ -> true
    | _        -> false
    
let genOrGetTPEqSys ctx =
    match ctx.tpEqSys with
    | Some es -> es, ctx
    | None -> runTerProbEqSysConstruction ctx

/// THE <em> BISECTION </em> VALUE OBTAINED IS GUARANTEED TO BE GREATER THAN THE TRUE VALUE
/// HENCE AVOIDING DIVIDE BY 0 PROBLEM
let tpApproximation ctx =
    processPrint "Start computing approximation to termination probability...";
    let tpEqSys, ctx = genOrGetTPEqSys ctx in
    logTimingMark "approx";
    let mutable iterRounds = None in
    let way, approxRes =
        if tpEqSys.Length = 1 &&
           // bugfix : there may be unique equation like
           // x0 = 1/2 + 1/2 * x0 * x0
           rhsIsConst (List.exactlyOne tpEqSys) then
            let approxRes =
                List.head tpEqSys
                |> snd
                |> function EConst c -> c | _ -> IMPOSSIBLE ()
            in
            if not Flags.TP_APPROX_BY_BISECTION then iterRounds <- Some 0uL;
            "Exact Termination Probability by Simplification", approxRes
        elif Flags.TP_APPROX_BY_BISECTION then
            let approxRes =
                ApproximationProblem.approximateByQuantitativeNLSat
                    Flags.APPROX_ACCURACY
                    tpEqSys
            in
            "Approximation by Bisection Result", approxRes
        else
            let approxRes, rounds =
                ApproximationProblem.approximateByIteration
                    Flags.MAX_ITER_ROUND
                    Flags.APPROX_MIN_DIFF
                    tpEqSys
            in
            iterRounds <- rounds;
            "Approximation by Iteration Result", approxRes
    in
    processPrint $"{way}"
    let approxTime = tapTimingMark "approx" in
    if Flags.TP_APPROX_BY_BISECTION then begin
        resultPrint $ RTpApproxValBisec approxRes;
        resultPrint $ RTpApproxTimeBisec approxTime
    end
    else begin
        resultPrint $ RTpApproxValIter approxRes;
        Option.iter (resultPrint << RTpApproxIterTimes) iterRounds;
        resultPrint $ RTpApproxTimeIter approxTime
    end;
    {
        ctx with
            tpResValIter = if Flags.TP_APPROX_BY_BISECTION then None else Some approxRes
            tpResValBisec = if Flags.TP_APPROX_BY_BISECTION then Some approxRes else None
            tpApproximationTimeIter = if Flags.TP_APPROX_BY_BISECTION then None else Some approxTime
            tpApproximationTimeBisec = if Flags.TP_APPROX_BY_BISECTION then Some approxTime else None
            tpIterationRounds = iterRounds
    }
    
type TPQualitativeResult =
    | TPQAST
    | TPQImpossible
    | TPQBetween
    override x.ToString () =
        match x with
        | TPQAST -> "Almost Sure Termination (P = 1)"
        | TPQImpossible -> "Impossible (P = 0)"
        | TPQBetween -> "Neither AST Nor Impossible (0 < P < 1)"
    
let tpQualitative ctx =
    processPrint "Start computing qualitative results...";
    let tpQualitativeTimeMark = "tpQualitative" in
    logTimingMark tpQualitativeTimeMark;
    let checkQualitative () =
        let es, ctx = genOrGetTPEqSys ctx in
        let res =
            match QualitativeProblem.qualitativeByQuantitative
                QuantitativeProblem.quantitativeByNLSat
                es with
            | PRTImpossible -> TPQImpossible
            | PRTAlmostSureTerminate -> TPQAST
            | _ -> TPQBetween
        in
        res, ctx
    in
    let tpResVal = getTpResVal ctx in
    let qualRes, ctx =
        if Option.isSome tpResVal then
            let tpRes = Option.get tpResVal in
            // optimisations by the approximation value
            // by iteration and the result is 0, it means the result is 0
            if tpRes = NUMERIC_ZERO && not Flags.TP_APPROX_BY_BISECTION then
                TPQImpossible, ctx
            // by bisection and the result is not 1 or 0, it means the result is between
            elif Flags.TP_APPROX_BY_BISECTION &&
                 tpRes < NUMERIC_ONE &&
                 tpRes <> NUMERIC_ZERO then
                TPQBetween, ctx
            // otherwise, check the value directly
            else
                checkQualitative ()
        else
            checkQualitative ()
    in
    debugPrint $"Termination Qualitative Result: {qualRes}"
    resultPrint $ RTpIsAST (Ok (qualRes = TPQAST))
    let qualitativeTime = tapTimingMark tpQualitativeTimeMark in
    resultPrint $ RTpASTTime qualitativeTime;
    {
        ctx with
            tpAST = Some (qualRes = TPQAST)
            tpQualitativeTime = Some qualitativeTime
    }
    
let tpQuantitative ctx =
    // pick the inquiry out
    logTimingMark "tpQuantitative";
    let cmp, num =
        Option.get Flags.TP_QUANTITATIVE_INQUIRY
        |> BiMap.fstMap QuantitativeProblem.QueryType.Parse in
    processPrint $"Start computing quantitative inquiry for \"{cmp} {num}\"..."
    let es, ctx = genOrGetTPEqSys ctx in
    let quanRes = QuantitativeProblem.quantitativeByNLSat cmp num es in
    processPrint $"Termination Probability Quantitative Result: {quanRes}"
    let tpQuantitativeTime = tapTimingMark "tpQuantitative" in 
    processPrint $"Quantitative Time: {tpQuantitativeTime}s";
    { ctx with tpQuantitativeTime = Some tpQuantitativeTime }
    
let runConstructExpTerTimeEqSys ctx =
    processPrint "Start constructing equation system for expected termination time...";
    logTimingMark "ettEqSys"
    let getRptsa =
        lazy
        match ctx.model with
        | RMKPTSA kptsa -> generaliseKPTSA kptsa
        | _ -> IMPOSSIBLE () in
    let ettPrimitiveEqSys =
        // bugfix: for the already existed tpEqSys
        // the function only builds the pure ETT part of the equation system
        // while for when nothing is built, the equation system will explore the whole system
        if Flags.ETT_REUSE_TP_RESULT && Option.isSome ctx.reuseCtx then
            let reuseCtx = Option.get ctx.reuseCtx in
            match reuseCtx with
            | RC_RPTSA rc ->
                terExpFormulaConstruct
                    (Some rc)  // which is Some
                    (isNormalisedRPTSA getRptsa.Value)
                    getRptsa.Value
                ++
                Option.get ctx.tpPrimitiveEqSys
            | RC_PPDA pes ->
                let ppda = match ctx.model with
                           | RMPPDA ppda -> ppda
                           | _ -> IMPOSSIBLE ()
                in
                convertToEqSys_ETT ppda pes ++ ctx.tpPrimitiveEqSys.Value
        else
            match ctx.model with
            | RMKPTSA _ ->
                terExpFormulaConstruct
                    None
                    Flags.KPTSA_NORMALISED
                    getRptsa.Value
            | RMPPDA ppda ->
                directPpdaEqSys_ETT ppda
    in
    let x0 =
        match ctx.model with
        | RMKPTSA _ -> terExpX0 getRptsa.Value
        | RMPPDA ppda -> transVar ppda PVCExp EVX0
    in
    let ettEs, revMap =
        formulaSystemToExprSystemWithHint
            ettPrimitiveEqSys
            (Map.add x0 0 Map.empty)
        |> BiMap.fstMap (fun es ->
            if Flags.DEBUG then List.sortBy fst es
            else es)
    in
    let ettVarMap =
        Map.toSeq revMap
        |> Seq.map swap
        |> Map.ofSeq
    in
    eqSysPrint Flags.DEBUG $"\nConstructed Equation System: \n{printExprSystemWithVarMap ettEs ettVarMap}"
    eqSysPrint Flags.INNER_DEBUG $
        "\n------------------------------------------------------------------------\n" +
        $"Corresponding Internal Representation:\n{printExprSystem ettEs}" +
        "\n------------------------------------------------------------------------\n\n"
    let ettEqSysPrimitiveScale = List.length ettEs in
    
    resultPrint $ REttEqPrimitiveScale (uint ettEqSysPrimitiveScale);
    resultPrint $ REttEqPrimitiveConsTime (getTimingFromMark "ettEqSys");
    let ettEs, time = simplifyLFPEqSys ettEs ettVarMap in
    Option.iter (resultPrint << REttEqSimpTime) time;
    let ettEqSysSimplifiedScale = List.length ettEs in
    resultPrint $ REttEqSimScale (uint ettEqSysSimplifiedScale)
    debugPrint "Simplification Done.";
    eqSysPrint Flags.INNER_DEBUG $
        "\n------------------------------------------------------------------------\n" +
        $"Corresponding Internal Representation:\n{printExprSystem ettEs}" +
        "\n------------------------------------------------------------------------\n\n";
    processPrint "ETT Equation System Construction Done.";
    let ettEqSysConstructTime = tapTimingMark "ettEqSys" in
    resultPrint $ REttEqTotalConsTime ettEqSysConstructTime;
    ettEs, {
        ctx with
            ettEqSys = Some ettEs
            ettEqSysVarMap = Some ettVarMap
            ettEqSysConstructTime = Some ettEqSysConstructTime
            ettEqSysSimplificationTime = time
            ettEqSysPrimitiveScale = Some $ uint ettEqSysPrimitiveScale
            ettEqSysSimplifiedScale = Some $ uint ettEqSysSimplifiedScale
    }
    
let genOrGetETTEqSys ctx =
    match ctx.ettEqSys with
    | Some es -> es, ctx
    | None    -> runConstructExpTerTimeEqSys ctx
    
/// divide the ETT equation system into probability part and expectation time
let divideETTEqSys ettEqSys ettVarMap =
    flip List.partition ettEqSys $ fun (idx, _) ->
        match Map.find idx ettVarMap with
        | PVCProb _ -> true
        | PVCExp _  -> false
    
let genNLSatETTQueryString ettEqSys ettVarMap =
    let probPartEs, ettPartEs = divideETTEqSys ettEqSys ettVarMap in
    genNLSatDeclarePart probPartEs true +
    // bugfix : ett part should not have 1 bound -- it should only >= 0.
    genNLSatDeclarePart ettPartEs false +
    genNLSatEsDefPart probPartEs +
    genNLSatEsDefPart ettPartEs +
    NLSatTriggerString
    
let ettQualitativeCheck_Raw ctx =
    let ettEqSys, ctx = genOrGetETTEqSys ctx in
    logTimingMark "ettQualitative";
    let ettVarMap = Option.get ctx.ettEqSysVarMap in
    let z3Context, nlsatSolver = genNewZ3Context () in
    let queryString = genNLSatETTQueryString ettEqSys ettVarMap in
    let query = z3Context.ParseSMTLIB2String queryString in
    let ettQualitativeTime = tapTimingMark "ettQualitative" in
    let res = turnZ3SolverResultIntoBool nlsatSolver query in
    res,
    { ctx with
        cettQualRes = Some res
        ettQualitativeTime = Some ettQualitativeTime }
    
/// bisection to obtain the RAW VALUE for TP * CETT
let rawCettBisectionApproximation ctx =
    debugPrint "Computing Raw (C)ETT value by bisection...";
    let z3Ctx, nlsatSolver = genNewZ3Context () in
    let es, ctx = genOrGetETTEqSys ctx in
    let basicQuery = genNLSatETTQueryString es ctx.ettEqSysVarMap.Value in
    nlsatSolver.Assert (z3Ctx.ParseSMTLIB2String basicQuery);
    if not $ turnZ3SolverResultIntoBool nlsatSolver [||] then raise $ OverflowException ()
    else begin
        let accuracy = Flags.APPROX_ACCURACY in
        let isLe numToTest =
            checkTimeOut $"The current approximation number: {numToTest}";
            let query =
                z3Ctx.ParseSMTLIB2String $
                    $"(declare-const {Output.printExprVariable 0} Real)" +
                    $"(assert (<= {Output.printExprVariable 0} {Output.lispPrintProbability numToTest}))"
            in
            turnZ3SolverResultIntoBool nlsatSolver query
        in
        let rawCett =
            snd $ positiveOuterBisection accuracy isLe NUMERIC_ZERO NUMERIC_ONE
        in
        rawCett
    end
    
//let pastCheck ctx =
//    if not $ Option.get ctx.tpAST then begin
//        // not AST, no need to check PAST
//        resultPrint $ REttIsPAST (Ok false);
//        ctx
//    end
//    else
//        processPrint "Start checking Positive AST..."
//        let ettQualRes, ctx = ettQualitativeCheck_Raw ctx in
//        resultPrint $ REttIsPAST (Ok ettQualRes);
//        resultPrint $ REttHasVal (Ok ettQualRes);
//        resultPrint $ REttQualTime (Option.get ctx.ettQualitativeTime);
//        {
//            ctx with
//                cettQualRes = Some ettQualRes
//        }
        
let cettQualitative ctx =
    match ctx.cettQualRes with
    | Some _ -> ctx
    | None ->
        processPrint "Starting checking if there is result for conditional expected termination time..."
        let res, ctx = ettQualitativeCheck_Raw ctx in
        resultPrint $ REttHasVal (Ok res);
        // print about PAST
        if Flags.TP_QUALITATIVE && Flags.ETT_QUALITATIVE then begin
            match ctx.tpAST with
            | Some isAST -> resultPrint $ REttIsPAST (Ok (res && isAST))
            | None -> resultPrint $ REttIsPAST (Error "No result reported for AST.")
        end;
        resultPrint $ REttQualTime (Option.get ctx.ettQualitativeTime);
        { ctx with cettQualRes = Some res }
    
/// do the actual job without qualitative guard
let cettApproximation_Raw ctx =
    let ettEqSys, ctx = genOrGetETTEqSys ctx in
    logTimingMark "cettApprox";
    let ettVarMap = Option.get ctx.ettEqSysVarMap in
    eqSysPrint Flags.DEBUG $
        $"Final ES to solve:\n{printExprSystemWithVarMap (normaliseExprSystem ettEqSys) ettVarMap}";
    let run () =
        if Flags.ETT_APPROX_BY_BISECTION then
            rawCettBisectionApproximation ctx, None
        else if Flags.ITER_BY_PREMO then
            Map(iterByPReMo ettEqSys).[0], None
        else
            let res, iterRounds =
                iteratingExprSystem ettEqSys Flags.MAX_ITER_ROUND Flags.APPROX_MIN_DIFF
            in
            Map(res).[0], Some iterRounds
    in
    let rawRes, iterRounds =
        try run ()
        with | :? OverflowException -> NUMERIC_ZERO - NUMERIC_ONE, None
    in
    let cettApproxTime = tapTimingMark "cettApprox" in
    let rawRes =
        if rawRes < NUMERIC_ZERO then Error "Arithmetic Overflow Happened."
        else Ok rawRes
    in
    let ctx =
        if Flags.ETT_APPROX_BY_BISECTION then begin
            resultPrint $ REttApproxValBisec rawRes;
            resultPrint $ REttApproxTimeBisec cettApproxTime;
            { ctx with
                ettApproximationTimeBisec = Some cettApproxTime
                rawCettResValBisec = match rawRes with
                                     | Ok rr -> Some rr
                                     | _ -> None }
        end else begin
            resultPrint $ REttApproxValIter rawRes;
            Option.iter (resultPrint << REttApproxIterTimes) iterRounds;
            resultPrint $ REttApproxTimeIter cettApproxTime;
            { ctx with
                ettApproximationTimeIter = Some cettApproxTime
                rawCettResValIter = match rawRes with
                                    | Ok rr -> Some rr
                                    | _ -> None
                ettIterationRounds = iterRounds }
        end;
    in
    let printApproxVal res =
        if Flags.ETT_APPROX_BY_BISECTION
            then resultPrint $ RCondEttApproxValBisec res
            else resultPrint $ RCondEttApproxValIter res
    in
    // on the actual (C)ETT value
    if not Flags.TP_APPROXIMATION then ctx
    else begin
        let rawRes =
            match rawRes with
            | Error _ -> printApproxVal rawRes; None
            | Ok rawRes -> Some rawRes
        in
        let tpRes =
            match getTpResVal ctx with
            | None -> printApproxVal $ Error "TP approximation failed."; None
            | Some n when n = NUMERIC_ZERO ->
                printApproxVal $ Error "The TP approximation result is Zero. Hence (C)ETT is infinite.";
                None
            | Some n -> Some n
        in
        match rawRes, tpRes with
        | Some rawRes, Some tpRes ->
            let res = rawRes / tpRes in
            printApproxVal $ Ok res;
            { ctx with
                cettResValBisec = if Flags.ETT_APPROX_BY_BISECTION then Some res else None
                cettResValIter = if Flags.ETT_APPROX_BY_BISECTION then None else Some res }
        | _, _ -> ctx
    end
    
/// the entry -- with qualitative guard
let cettApproximation ctx =
    if ctx.cettQualRes = Some false then
        if Flags.ETT_APPROX_BY_BISECTION then begin
            resultPrint $ REttApproxValBisec (Error "No Finite Value");
            if Flags.TP_APPROXIMATION then
                resultPrint $ RCondEttApproxValBisec (Error "No Finite Value");
            resultPrint $ REttApproxTimeBisec TimeSpan.Zero
        end else begin
            resultPrint $ REttApproxValIter (Error "No Finite Value");
            if Flags.TP_APPROXIMATION then
                resultPrint $ RCondEttApproxValIter (Error "No Finite Value");
            resultPrint $ REttApproxTimeIter TimeSpan.Zero;
            resultPrint $ REttApproxIterTimes 0uL
        end;
        ctx
    else cettApproximation_Raw ctx
//    let ctx =
//        if not Flags.TP_APPROXIMATION then ctx
//        else begin
//            ctx
//        end
//    in
//    { ctx with
//        ettApproximationTimeBisec = if Flags.ETT_APPROX_BY_BISECTION then Some cettApproxTime else None
//        ettApproximationTimeIter = if Flags.ETT_APPROX_BY_BISECTION then None else Some cettApproxTime
//        cettResValBisec = if Flags.ETT_APPROX_BY_BISECTION then Some res else None
//        cettResValIter = if Flags.ETT_APPROX_BY_BISECTION then None else Some res
//        rawCettResValBisec = if Flags.ETT_APPROX_BY_BISECTION then Some rawRes else None
//        rawCettResValIter = if Flags.ETT_APPROX_BY_BISECTION then None else Some rawRes
//        ettIterationRounds = iterRounds }

// DISCARDED FUNCTION
///// SERIOUS PROBLEM TO THIS FUNCTIONALITY
///// we should use the LFP of the termination probability value to divide the LFP of the current value
///// which involves making use of the new functionality
///// THIS FUNCTION SHOULD NOT BE USED
//let cettQuantitative ctx =
//    if (not Flags.EXTERNAL_ETT_QUALITATIVE_CONFIRM) && ctx.cettQualRes = Some false then
//        raise $ ValueMark "No Value"
//    let cmp, num = Option.get Flags.ETT_QUANTITATIVE_INQUIRY in
//    let condStr =
//        match ctx.tpAST with
//        | Some true -> ""
//        | Some false -> "Conditional"
//        | None -> "(conditional)"
//    in
//    processPrint $"Start solving {condStr} ETT quantitative inquiry: \"{cmp} {num}\"";
//    let ettEs = Option.get ctx.ettEqSys in
//    let ettVarMap = Option.get ctx.ettEqSysVarMap in
//    let esQueryString = genNLSatETTQueryString ettEs ettVarMap in
//    let res =
//        QuantitativeProblem.quantitativeByNLSatWithEsQuery
//            esQueryString
//            (QuantitativeProblem.QueryType.Parse cmp)
//            num
//    in
//    processPrint $"Quantitative inquiry result: {res}";
//    ctx
    
// DISCARDED FUNCTION
//let newCheckPAST ctx =
//    let tpResVal = getTpResVal ctx in
//    let tpVal = Option.get tpResVal in
//    if tpVal = NUMERIC_ZERO then
//        processPrint "Termination Probability Value is 0, cannot approximate CETT."
//    else
//        let tpEqSys = Option.get ctx.tpPrimitiveEqSys in
//        let tpBuildContext = Option.get ctx.tpBuildCtx in
//        Flags.EXTERNAL_ETT_QUALITATIVE_CONFIRM <- true;
//        let res = checkPositiveAlmostSureTermination (tpEqSys, tpBuildContext) true ctx.kptsa in
//        match res with
//        | Some res ->
//            let res = res / tpVal in
//            processPrint $"""Positive Check: {res.ToString "N30"}"""
//        | None ->
//            resultPrint $ REttIsPAST (Error "")
//            processPrint "No result"

let simplifyModel model =
    match model with
    | RMKPTSA kptsa -> RMKPTSA $ simplifyKPTSA kptsa
    | RMPPDA ppda -> RMPPDA $ simplifyPPDA ppda

let runNonModelCheck kptsa : unit =
    processPrint "Start problem resolving...";
    try
        let ctx = defaultRunningContext $ simplifyModel kptsa in
        if Flags.TP_RUN_BOTH_ITER_AND_BISEC then Flags.TP_APPROX_BY_BISECTION <- true;
        let ctx =
            ctx
            // termination probability (TP): approximation
            ||> (Flags.TP_APPROXIMATION, tpApproximation)
        in
        let ctx =
            if Flags.TP_RUN_BOTH_ITER_AND_BISEC then begin
                Flags.TP_APPROX_BY_BISECTION <- false;
                ctx
                // termination probability (TP): approximation
                ||> (Flags.TP_APPROXIMATION, tpApproximation)
            end
            else ctx
        in
        let ctx =
            ctx
            // termination probability (TP): qualitative check
            // if there is value for termination probability then
            // if the value is 0, it means impossible
            // if the value is obtained by Z3 bisection and the value is 0 < p < 1,
            //      then report the result
            // otherwise, check whether it is AST and print the result directly
            ||> (Flags.TP_QUALITATIVE, tpQualitative)
            
            // termination probability (TP): quantitative check
            ||> (Flags.TP_QUANTITATIVE_INQUIRY.IsSome, tpQuantitative) 
            
            // Now, no additional PAST will be checked, will report only if TP-QUAL & ETT-QUAL both reached
//            // ETT positive AST check --
//            // if it is AST, then check it,
//            // if there is no AST information, check AST first -- this is done in the previous step
//            ||> (Flags.CHECK_PAST, pastCheck)
            
            // Now, just depends on whether to check it
//            // Conditional ETT: qualitative
//            // if there is already result for PAST, just return the value 
//            // if there is no PAST information
//            //      see if there is a solution for this value
//            // Also, it is the pre-condition of the previous two
            ||> (Flags.ETT_QUALITATIVE, cettQualitative) 
        in
        
        if Flags.ETT_RUN_BOTH_ITER_AND_BISEC then Flags.ETT_APPROX_BY_BISECTION <- true;
        let ctx =
            ctx
            // Conditional ETT: approximation
            // this must be computed when qualitative value is obtained,
            // if there is no qualitative result, compute it
            // if there is no value, say `infty`
            ||> (Flags.ETT_APPROXIMATION, cettApproximation)
        in
        let ctx =
            if Flags.ETT_RUN_BOTH_ITER_AND_BISEC then begin
                Flags.ETT_APPROX_BY_BISECTION <- false;
                ctx
                // Conditional ETT: approximation
                // this must be computed when qualitative value is obtained,
                // if there is no qualitative result, compute it
                // if there is no value, say `infty`
                ||> (Flags.ETT_APPROXIMATION, cettApproximation)
            end
            else ctx
        in
        ctx
        // end the inquiry
//        |> newCheckPAST
        |> ignore
    with
    | :? ValueMark<string> as e ->
        processPrint $"{e.getValue ()}"
    
    resultPrint $ RTotalTime (Flags.GLOBAL_TIMING.totalTime ())

//    let ret = probFunc es
//    let ret =
//        // the function to check if the kptsa is P-AST
//        let checkPAST terProbApproxVal =
//            processPrint "Checking PAST."
//            match checkPositiveAlmostSureTermination
//                      // the `option` is just for default values
//                      (Option.get probForSys, Option.get expCtx)
//                      Flags.COMPUTE_EXPECTED_TERMINATION_TIME_VALUE
//                      ori_kptsa with
//            | Some ettX0 ->
//                processPrint "PAST check passed."
//                if Flags.COMPUTE_EXPECTED_TERMINATION_TIME_VALUE then
//                    let terProb =
//                        match terProbApproxVal with
//                        | Some v ->
//                            if v <> NUMERIC_ZERO then
//                                v
//                            else failwith "The expected termination time should be infinite."
//                        | None -> NUMERIC_ONE
//                    let s =
//                        $"Approximated Expected Termination Time: {NumericType.ToDouble (ettX0 / terProb)}" +
//                        (if Flags.ELIMINATE_INSTANT_PROJECTION then
//                            " (NOTE that this may NOT be the value for the initial model.)"
//                         else "")
//                    processPrint $"{s}"
//                true
//            | None ->
//                processPrint "The equation system for expected termination time is unsolvable."
//                false
//        match ret with
//        | _ when Flags.DO_NOT_CHECK_PAST -> ret
//        | PRTAlmostSureTerminate ->
//            if checkPAST None then PRTPositiveAlmostSureTermination
//            else ret
//        | PRTApproximation (_, PRTAlmostSureTerminate) ->
//            if checkPAST None then PRTApproximation (NUMERIC_ONE, PRTPositiveAlmostSureTermination)
//            else ret
//        | PRTApproximation (approxVal, _) ->
//            if Flags.COMPUTE_NON_AST_EXPECTED_TERMINATION_TIME then
//                checkPAST (Some approxVal) |> ignore
//            ret
//        | _ -> ret
//    let problemResolvingTime = timing.tapInSecond ()
//    processPrint $"Problem Resolving Time: {problemResolvingTime}s"
    
    
// DISCARDED FUNCTION
///// THE MODEL CHECKING ALGORITHM IMPLEMENTED IS PROBLEMATIC
///// DO NOT USE THIS FUNCTION
//let runModelCheck kptsa dra : unit =
//    let rptsa = generaliseKPTSA kptsa in
//    match Flags.RPTSA_DRA_MAPPING with
//    | Some valuation ->
//        let res = ModelChecking.omegaRegularModelCheck rptsa dra valuation in
//        let print res = toString $ get res in
//        let table =
//            [|
//                ("$\\approx_\\mathit{iter}$", print res.Result)
//                ("$t_\\mathit{total}$", print res.TotalTime)
//                ("$t_=$", print res.EqBuildTime)
//                ("$t_\\mathit{trips}$", print res.TripsIterTime)
//                ("$t_\\mathit{up}$", print res.UpsIterTime)
//                ("$\\#_\\mathit{trips}$", print res.EqSysTripScale)
//                ("$\\#_\\mathit{up}$", print res.EqSysUpScale)
//            |]
//            |> Array.unzip
//            |> fun (header, content) -> [| header; content |]
//        in
//        let res = printStrTableInLaTeX table in
//        processPrint $"""Result: {res.ToString ()}"""
//    | None -> failwith "No valuation data to conduct model checking."

let runFromAutomaton ori_kptsa =
    runNonModelCheck ori_kptsa

/// if the model is a PAHORS, then translate it from this way
let runFromPAHORS pahors =
    processPrint "Start Checking PAHORS Validity...";
    pahorsValidityChecking pahors |> ignore;
    processPrint "PAHORS validity check pass.";
    processPrint "Start translating PAHORS to kPTSA ...";
    let kptsa = (PAHORS2KPTSA.translate pahors).rptsa in
    let translationTimingMark = "TranslationFromPAHORSToRPTSA" in
    logTimingMark translationTimingMark;
    processPrint "Translation done.";
    processPrint "============================= Translated rPTSA =============================";
    processPrint $"{kptsa}";
    processPrint "============================================================================";
    resultPrint $ RPahorsTranslationTime (tapTimingMark translationTimingMark);
    runFromAutomaton $ RMKPTSA kptsa
    
let genMCFGFromRules rptsa rules =
    let nts =
        Map.toSeq rules
        |> Seq.map (fun (nt, lst) ->
            List.map (fst >> List.length >> uint) lst
            |> List.distinct
            |> fun x ->
                if List.length x > 1 then
                    failwith $"Non-Terminal {nt} has different dimensions."
                else (nt, if List.isEmpty x then 0u else List.head x))
        |> Map.ofSeq in
    let terminals =
        Map.toSeq rules
        |> Seq.map snd
        |> Seq.map (List.map fst)
        |> Seq.concat
        |> Seq.concat
        |> Seq.concat
        |> Seq.map (function Terminal t -> [t] | _ -> [])
        |> Seq.concat
        |> Set.ofSeq in
    {
        nonTerminals = nts;
        terminals = terminals;
        rules = rules;
        startNonTerminal = toRawVar (absX0 rptsa) VUp;
    }
    
let runRemoveRedundantRules rules =
    let formulas =
        Map.toSeq rules
        |> Seq.map (fun (nt, lst) ->
            List.map (snd >> List.map fst) lst
            |> List.map (List.map FVar >> List.fold (*) (FConst NUMERIC_ONE))
    //               (fun x ->
    //            if List.isEmpty x then FConst NUMERIC_ONE
    //            else List.map FVar x
    //                 |> List.reduce (*))
            |> List.fold (+) (FConst NUMERIC_ZERO)
            |> fun x -> (nt, x))
    in
    let es, dic = formulaSystemToExprSystemWithHint (List.ofSeq formulas) Map.empty in
    let remap = revMap dic in
    // This will find ALL the empty variables / non-terminals
    let zeros, _ = iterToFindLFPZeroVariables es in
//    // a separate k checking procedure
//    if Flags.CHECK_K then
//        List.map (fst >> flip Map.find remap) rst
//        |> List.iter (function | VTer (D, g) | VTrips (D, g) | VUp (D, g) -> checkDGAndK D g k)
    let zeroNts = Set.ofList $ List.map (flip Map.find remap) zeros in
    if Flags.DEBUG then
        processPrint $"\nRemoved Variables:\n{printFullSeq zeroNts}";
    Map.toSeq rules
    // recover the rules
    |> Seq.map (fun (nt, lst) ->
        List.map (fun (lhs, rhs) -> (nt, lhs, rhs)) lst)
    |> Seq.concat
    |> List.ofSeq
    |> List.partition (fun (nt, _, rhs) ->
        List.map fst rhs
        |> List.map zeroNts.Contains
        |> List.fold (||) (zeroNts.Contains nt))
    |> fun (erasedRules, remainingRules) ->
        if Flags.DEBUG then begin
            processPrint "--------------------- Removed MCFG Rules ---------------------"
            List.map (fun (nt, lhs, rhs) -> printMCFGRule nt lhs rhs) erasedRules
            |> String.concat ".\n"
            |> fun x -> processPrint $"{x}."
            processPrint "--------------------------------------------------------------"
        end;
        remainingRules
    |> aggregateList (fun (nt, lhs, rhs) -> (nt, (lhs, rhs)))
    |> Map.ofSeq
    
let private configLoopDetect config rules =
    let rec detect (_, m, g as config) pathSet =
        if Set.contains config pathSet then true
        else begin
            Option.defaultValue [] (Map.tryFind config rules)
            |> flip List.fold false (fun ori (_, op) ->
                ori || match op with
                       | OpTransState q' -> detect (q', m, g) (Set.add config pathSet)
                       | _               -> false)
        end
    in
    detect config Set.empty
    
let runCheckLoop (rptsa : GeneralRPTSA<_,_,_,_>) =
    let noCharGenRules =
        Map.toSeq rptsa.delta
        |> Seq.map (BiMap.sndMap (List.map (BiMap.sndMap (function
            | OpTransSp (CharGen (_, q)) -> OpTransState q
            | x -> x))))
        |> Map.ofSeq in
    Map.toSeq noCharGenRules
    |> Seq.map fst
    |> Seq.iter (fun sts ->
        if configLoopDetect sts noCharGenRules then
            let word =
                "Conversion currently only supports rTSA with no local loop. " +
                $"Detected status containing local loop: {sts}."
            in
            failwith $"{word}")
    
let runConvertToMCFG rptsa =
    let convTimeMark = "ConvToMCFG" in
    logTimingMark convTimeMark;
    let _ = runCheckLoop rptsa in
    let sp = MCFGConvCtx () in
    buildEquationSystem rptsa sp |> ignore;
    let rules = Map.ofSeq $ sp.getGeneratedRules () in
    if Flags.DEBUG then begin
        // to add a new line
        processPrint ""
        let mcfg = genMCFGFromRules rptsa rules in
        processPrint $"Generated Primitive MCFG:\n{mcfg}"
    end
    let rules = runRemoveRedundantRules rules in
    let mcfg = genMCFGFromRules rptsa rules in
    processPrint "======================== Generated MCFG ========================"
    processPrint $"{mcfg}"
    processPrint "================================================================"
    processPrint $"Totally conversion time: {numericValuePrint $ tapTimingMark convTimeMark}s"
    match Flags.ENUM_STRING with
    | None -> ()
    | Some amount ->
        processPrint "--------------------- Generated String Examples ---------------------"
        enumerateMCFGWords mcfg
        |> seqSafeTake amount
        |> (fun seq ->
            if Seq.length seq < amount
                then processPrint "All generated strings are taken.";
            List.ofSeq seq)
        |> List.map (
            List.map (
                List.map toString
                >> String.concat " ")
            >> List.exactlyOne)
        |> List.indexed
        |> List.map (fun (idx, str) -> $"{idx}: {str}")
        |> String.concat "\n"
        |> fun x -> processPrint $"{x}"
        processPrint "---------------------------------------------------------------------"

let toTerRptsa rptsa =
    let rules =
        Map.toSeq rptsa.delta
        |> Seq.map (BiMap.sndMap (List.map (BiMap.sndMap $ function
            | OpTransState q -> OpTransState q
            | OpTransDown (q, m) -> OpTransDown (q, m)
            | OpTransUp (q, m, g) -> OpTransUp (q, m, g)
            | OpTransSp (CharGen (_, q)) -> OpTransState q
            | OpTransSp GenTer -> OpTransSp SpTer)))
        |> Map.ofSeq
    in
    { q0 = rptsa.q0
      m0 = rptsa.m0
      g0 = rptsa.g0
      k = rptsa.k
      delta = rules
      kMap = rptsa.kMap
      stateDependencies = rptsa.stateDependencies
      stepCount = None }
    
let private runInitialisation () =
    Flags.GLOBAL_TIMING.reset ();
    Flags.RESULT_ACC <- []

/// may generate its own probFunc by this string
let runFromString (s : string) =
    runInitialisation ();
    let parseTimeMark = "parseModel" in
    logTimingMark parseTimeMark;
    let model = TextInput.parseString s
    resultPrint $ RParseTime (tapTimingMark parseTimeMark)
    match model with
    | MKPTSA kptsa ->
        runCheck_K printKPTSAGamma $ generaliseKPTSA kptsa;
        // switch off the optimisations
        Flags.IS_TRANSLATED_KPTSA <- false;
        runFromAutomaton $ RMKPTSA kptsa
    | MPAHORS pahors ->
        // switch on the optimisations
        Flags.IS_TRANSLATED_KPTSA <- true;
        runFromPAHORS pahors
    | MPPDA ppda ->
        Flags.IS_TRANSLATED_KPTSA <- false;
        runFromAutomaton $ RMPPDA ppda
    | MSTRRPTSA rptsa ->
        runCheck_K toString $ toTerRptsa rptsa;
        runConvertToMCFG rptsa

let runFromFile (filePath : string) =
    let s =
        use sr = new StreamReader (filePath)
        sr.ReadToEnd ()
    runFromString s
    
let private printResults () =
    let results = List.rev Flags.RESULT_ACC in
    processPrint "-------------------------------- Results --------------------------------";
    List.map toString results
    |> String.concat "\n"
    |> println
    
let private runAndPrintResults filePath =
    runFromFile filePath;
    printResults ()
    
let private printFileTitle filePath =
    printf "================================ ";
    printf $"Running file: \"{filePath}\"";
    printfn " ================================"
    
let private printFileEnd filePath =
    printf "================================ ";
    printf $"End file: \"{filePath}\"";
    printfn " ================================\n"
    
let private runAndPrintTitle runner filePath =
    printFileTitle filePath;
    let res = runner filePath in
    printFileEnd filePath;
    res
    
let runAFile (filePath : string) =
    let run () = runAndPrintResults filePath in
    let runner _ =
        if Flags.INNER_DEBUG then run ()
        else try run ()
             with
             | :? TimeoutException -> eprintfn "Timeout."
             | e ->
                 eprintfn $"{e.Message}"
                 if Flags.INNER_DEBUG then
                     eprintfn $"{e.StackTrace}"
    in
    runAndPrintTitle runner filePath
    
let runFiles (filePaths : string list) =
    List.iter runAFile filePaths
    
// ---------------------- Non-Standard Runs to collect various special data ----------------------
    
    
//let printRunResult res =
//    match res with
//    | PRTApproximation (approxNum, state) ->
//        let followingString =
//            match state with
//            | PRTAlmostSureTerminate -> "(Almost Sure Termination)"
//            | PRTImpossible -> "(Impossible)"
//            | PRTPossibleButNonAST -> "(0 < p < 1)"
//            | PRTPositiveAlmostSureTermination -> "(Positive Almost Sure Termination)"
//            | PRTUnknown -> ""
//            | _ -> failwith "INTERNAL: Impossible Approximation State"
//        let s = "N30"
//        processPrint $"Approximation Number: {approxNum.ToString s} {followingString}"
//    | PRTImpossible ->
//        processPrint "Quality: Impossible -- p = 0"
//    | PRTAlmostSureTerminate ->
//        processPrint "Quality: Almost Sure Terminating -- p = 1"
//    | PRTPositiveAlmostSureTermination ->
//        processPrint "Positive Almost Sure Termination -- p = 1 with Finite Expected Termination Time."
//    | PRTPossibleButNonAST ->
//        processPrint
//            "Quality: Neither Impossible Nor Almost Sure Terminating -- 0 < p < 1"
//    | PRTQuantitative judgement ->
//        processPrint $"Quantitative Property Result: {judgement}"
//    | PRTOmegaModelCheck approxVal ->
//        processPrint $"""Omega model checking result: {approxVal.ToString "N30"}"""
//    | PRTUnknown -> failwith "INTERNAL: Impossible result."

type SeriesContext = {
    /// scale / indices
    series : int []
    /// produce the rPTSA by scale
    rptsaDefProd : int -> string
    /// final log directory
    logDir : string
    /// example name to work as the basis of log / graph files
    exampleName : string
}

/// cannot be private in order to call serializer of JSON
type DataToCollect = {
    tpEqSysTime : TimeSpan
    tpBisecApproxTime : TimeSpan
    tpIterApproxTime : TimeSpan
    tpASTDecideTime : TimeSpan
    tpIterVal : NumericType
    tpBisecVal : NumericType
    tpPrimitiveScale : uint
    tpSimplifiedScale : uint
    tpIsAST : bool
    ettEqSysTime : TimeSpan
    ettQualTime : TimeSpan
    ettBisecApproxTime : TimeSpan
    ettIterApproxTime : TimeSpan
    ettFinalValIter : NumericType
    ettFinalValBisec : NumericType
    ettPrimitiveScale : uint
    ettSimplifiedScale : uint
    ettHasVal : bool
}

/// run an rPTSA example to collect the information wanted
let runAnExample (example : string) =
    let kptsa = TextInput.parseString example in
    let model =
        match kptsa with
        | MKPTSA kptsa -> RMKPTSA kptsa
        | MPPDA ppda -> RMPPDA ppda
        | _ -> IMPOSSIBLE () in
    Flags.TP_APPROX_BY_BISECTION <- true;
    let runCtx =
        defaultRunningContext $ simplifyModel model
        |> tpApproximation
    in
    let bisecApproxTime =
        Option.defaultValue TimeSpan.Zero runCtx.tpApproximationTimeBisec
    in
    let bisecTpVal =
        Option.defaultValue NUMERIC_ZERO runCtx.tpResValBisec
    in
    Flags.TP_APPROX_BY_BISECTION <- false;
    let runCtx =
        tpApproximation runCtx
        |> tpQualitative
//        |> pastCheck
        |> cettQualitative
        |> fun ctx ->
            let tpResVal = getTpResVal ctx in
            if Option.get ctx.cettQualRes = true && tpResVal <> Some NUMERIC_ZERO then
                cettApproximation ctx
            else ctx
    in
    { tpEqSysTime = Option.get runCtx.tpEqSysConstructTime
      tpBisecApproxTime = bisecApproxTime
      tpIterApproxTime = Option.get runCtx.tpApproximationTimeIter
      tpASTDecideTime = Option.get runCtx.tpQualitativeTime
      tpBisecVal = bisecTpVal
      tpPrimitiveScale = Option.get runCtx.tpEqSysPrimitiveScale
      tpSimplifiedScale = Option.get runCtx.tpEqSysSimplifiedScale
      tpIsAST = Option.get runCtx.tpAST
      ettEqSysTime = Option.get runCtx.ettEqSysConstructTime
      ettQualTime = Option.get runCtx.ettQualitativeTime
      ettBisecApproxTime = Option.defaultValue TimeSpan.Zero runCtx.ettApproximationTimeBisec
      ettFinalValIter = Option.defaultValue NUMERIC_ZERO runCtx.cettResValIter
      ettFinalValBisec = Option.defaultValue NUMERIC_ZERO runCtx.cettResValBisec
      ettPrimitiveScale = Option.get runCtx.ettEqSysPrimitiveScale
      ettSimplifiedScale = Option.get runCtx.ettEqSysSimplifiedScale
      ettHasVal = Option.get runCtx.cettQualRes
      tpIterVal = Option.get runCtx.tpResValIter
      ettIterApproxTime = Option.defaultValue TimeSpan.Zero runCtx.ettApproximationTimeIter }
    
/// just for the Json files generated by the `runSeries` function
let private convertCollectedJsonToLaTeX (jsonStr : string) =
    let collection =
        JsonSerializer.Deserialize<Map<int, Map<string, Nodes.JsonValue>>> jsonStr in
        
    let exampleScaleName = "$m$" in
    let ettFinalValName = "$\\approx_\\mathit{iter}$" in
    let ettEqSysTimeName = "$t_{=}$" in
    let ettApproxTimeName = "$t_\\mathit{iter}$" in
    let ettQualTimeName = "$t_{<\\infty}$" in
    let ettPrimitiveScaleName = "$\\#=_1$" in
    let ettSimplifiedScaleName = "$\\#=_2$" in
    let tpIsASTName = "$AST?$" in
    let tpBisecValName = "$\\approx_\\mathit{bisec}$" in
    let tpIterValName = "$\\approx_\\mathit{iter}$" in
    let tpEqSysTimeName = "$t_{=}$" in
    let tpASTDecideTimeName = "$t_\\mathrm{AST}$" in
    let tpBisecApproxTimeName = "$t_\\mathit{bisec}$" in
    let tpIterApproxTimeName = "$t_\\mathit{iter}$" in
    let tpPrimitiveScaleName = "$\\#=_1$" in
    let tpSimplifiedScaleName = "$\\#=_2$" in
    
    let nameRemap name =
        match name with
        | "exampleScale" -> exampleScaleName
        | "ettFinalVal" -> ettFinalValName
        | "ettEqSysTime" -> ettEqSysTimeName
        | "ettApproxTime" -> ettApproxTimeName
        | "ettQualTime" -> ettQualTimeName
        | "ettPrimitiveScale" -> ettPrimitiveScaleName
        | "ettSimplifiedScale" -> ettSimplifiedScaleName
        | "tpIsAST" -> tpIsASTName
        | "tpBisecVal" -> tpBisecValName
        | "tpIterVal" -> tpIterValName
        | "tpEqSysTime" -> tpEqSysTimeName
        | "tpASTDecideTime" -> tpASTDecideTimeName
        | "tpBisecApproxTime" -> tpBisecApproxTimeName
        | "tpIterApproxTime" -> tpIterApproxTimeName
        | "tpPrimitiveScale" -> tpPrimitiveScaleName
        | "tpSimplifiedScale" -> tpSimplifiedScaleName
        | _ ->
            errPrint $"Warning: Unknown name \"{name}\" encountered, the same name kept.";
            name
    in
    
    let jsonTable (ty : string) =
        let jsonTable =
            collection
            |> Map.toSeq
            |> Seq.map (fun (id, map) ->
                Map.toList map
                |> List.map (BiMap.sndMap toString)
                // filter the fields
                |> List.filter (fst >> fun x ->
                    match x with
                    | "ettHasVal" -> false
                    | _           -> x.StartsWith ty)
                // add the id to the map
                |> currying List.Cons ("exampleScale", toString id)
                // modify the names and attributes
                |> List.map (fun (name, attr) ->
                    let name = nameRemap name in
                    let attr =
                        match name with
                        | "ettFinalVal" ->
                            if (Map.find "ettHasVal" map).GetValue<bool> () then
                                attr
                            else "$\\infty$"
                        | _ -> attr
                    in
                    (name, attr))
                |> Map.ofList)
            |> JsonSerializer.Serialize
        in
        let table = parseJsonTableToStringTable jsonTable in
        let rearrangeColumns table =
            let tpTable =
                [|
                    exampleScaleName
                    tpIsASTName
                    tpBisecValName
                    tpIterValName
                    tpEqSysTimeName
                    tpASTDecideTimeName
                    tpBisecApproxTimeName
                    tpIterApproxTimeName
                    tpPrimitiveScaleName
                    tpSimplifiedScaleName
                |]
            in
            let ettTable =
                [|
                    exampleScaleName
                    ettFinalValName
                    ettEqSysTimeName
                    ettApproxTimeName
                    ettQualTimeName
                    ettPrimitiveScaleName
                    ettSimplifiedScaleName
                |]
            in
            // no need to copy
            rearrangeMatrixColumns (if ty = "tp" then tpTable else ettTable) table
        in
        printStrTableInLaTeX $ rearrangeColumns table
    in
    
    (jsonTable "tp", jsonTable "ett")
    
/// convert a JSON file generated from the `runSeries` function into a LaTeX table
let private convertJsonTableFileToLaTeXTableFile filePath =
    let jsonStr = File.ReadAllText filePath in
    let tpTex, ettTex = convertCollectedJsonToLaTeX jsonStr in
    let filePathPrefix = filePath[0..filePath.Length - 6] in
    File.WriteAllText(filePathPrefix + "_tp.tex", tpTex)
    File.WriteAllText(filePathPrefix + "_ett.tex", ettTex)
    
let runConvertDirectoryJsonTableFilesToLaTeXTableFiles directoryPath =
    Directory.GetFiles directoryPath
    |> Array.filter (fun x -> x.EndsWith ".json")
    |> Array.iter (fun filePath ->
        try
            convertJsonTableFileToLaTeXTableFile filePath;
            processPrint $"Converted File: \"{filePath}\""
        with
        | e ->
            errPrint $"Error encountered during converting: \"{filePath}\".\nMessage: {e.Message}."
    )
    
let private runLogChart ctx chartName points =
    let xs, ys = Array.unzip points in
    let plt = ScottPlot.Plot 10000 in
    plt.AddScatter (xs, ys) |> ignore;
    processPrint $"""saved file: {plt.SaveFig $ ctx.logDir + "/" + ctx.exampleName + "_" + chartName + ".png"}"""

let runSeries (ctx : SeriesContext) =
    let obtainedResults =
        ctx.series
        |> Array.map (fun idx ->
            processPrint $"Testing Index: {idx}."
            (idx, runAnExample $ ctx.rptsaDefProd idx)) in
    // log the result to keep
    let logFilePath = ctx.logDir + "/" + ctx.exampleName + "_log.json" in
    let jsonFile = JsonSerializer.Serialize $ Map.ofSeq obtainedResults in 
    File.WriteAllText(logFilePath, jsonFile)
    processPrint $"JSON data:\n{jsonFile}\n\n"
    processPrint $"saved file: {logFilePath}"
    // all charts
    runLogChart ctx "tpEqSysTime" $
        Array.map (BiMap.pairMap (float, (fun x -> timeToSecond x.tpEqSysTime))) obtainedResults
    runLogChart ctx "tpPrimitiveScale" $
        Array.map (BiMap.pairMap (float, (fun x -> float x.tpPrimitiveScale))) obtainedResults
    runLogChart ctx "tpBisecTime" $
        Array.map (BiMap.pairMap (float, (fun x -> timeToSecond x.tpBisecApproxTime))) obtainedResults
    runLogChart ctx "tpSimpScale" $
        Array.map (BiMap.pairMap (float, (fun x -> float x.tpSimplifiedScale))) obtainedResults
    runLogChart ctx "tpIterTime" $
        Array.map (BiMap.pairMap (float, (fun x -> timeToSecond x.tpIterApproxTime))) obtainedResults
    runLogChart ctx "tpQualTime" $
        Array.map (BiMap.pairMap (float, (fun x -> timeToSecond x.tpASTDecideTime))) obtainedResults
    runLogChart ctx "ettApproxTime" $
        Array.map (BiMap.pairMap (float, (fun x -> timeToSecond x.ettIterApproxTime))) obtainedResults
    runLogChart ctx "ettPrimitiveScale" $
        Array.map (BiMap.pairMap (float, (fun x -> float x.ettPrimitiveScale))) obtainedResults
    runLogChart ctx "ettSimplifedScale" $
        Array.map (BiMap.pairMap (float, (fun x -> float x.ettSimplifiedScale))) obtainedResults
    runLogChart ctx "ettQualTime" $
        Array.map (BiMap.pairMap (float, (fun x -> timeToSecond x.ettQualTime))) obtainedResults
    runLogChart ctx "ettEqSysTime" $
        Array.map (BiMap.pairMap (float, (fun x -> timeToSecond x.ettEqSysTime))) obtainedResults

/// go by bisection
type OnlyTPDataToCollect = {
    tpEqSysTime : TimeSpan
    tpSimTime : TimeSpan
    tpApproxTime : TimeSpan
    tpIterVal : NumericType
    tpPrimitiveScale : uint
    tpSimplifiedScale : uint
}

/// run an rPTSA example to collect the information from Termination Probability Only
/// Go by Bisection Only
let runOnlyTerminationProbability (example : string) =
    let kptsa = TextInput.parseString example in
    let kptsa =
        match kptsa with
        | MKPTSA kptsa -> RMKPTSA kptsa
        | MPPDA ppda -> RMPPDA ppda
        | _ -> IMPOSSIBLE () in
    Flags.TP_APPROX_BY_BISECTION <- true;
    let runCtx =
        defaultRunningContext $ simplifyModel kptsa
        |> tpApproximation
    in
    {
        tpEqSysTime = Option.get runCtx.tpEqSysConstructTime
        tpApproxTime = Option.get runCtx.tpApproximationTimeBisec
        tpIterVal = Option.get runCtx.tpResValBisec
        tpPrimitiveScale = Option.get runCtx.tpEqSysPrimitiveScale
        tpSimplifiedScale = Option.get runCtx.tpEqSysSimplifiedScale
        tpSimTime = Option.get runCtx.tpEqSysSimplificationTime
    }

type CmpWithPReMoResult =
    {
        EqScale : int
        MyResult : NumericType
        PReMoResult : NumericType
        MyTime : TimeSpan
        PReMoTime : TimeSpan
    }
    override x.ToString () =
        let myResult = x.MyResult in
        let premoResult = x.PReMoResult in
        let myTime = x.MyTime in
        let premoTime = x.PReMoTime in
        let scale = x.EqScale in
        let resultDifference = (abs (myResult - premoResult)).ToString "N30" in
        let myResult = myResult.ToString "N30" in
        let premoResult = premoResult.ToString "N30" in
        let mineIsFaster = myTime < premoTime in
        let timeDifference = if mineIsFaster then premoTime - myTime else myTime - premoTime in
        let cmpWord = if mineIsFaster then "faster" else "slower" in
        [
            $"Equation System Scale: {scale}."
            $"Built-in Solution Result: {myResult}."
            $"Built-in Solution Time: {myTime}."
            $"PReMo Solution Result: {premoResult}."
            $"PReMo Solution Time: {premoTime}."
            $"The result absolute difference is: {resultDifference}."
            $"The Built-in Solution is {cmpWord} than calling PReMo by {timeDifference}."
        ]
        |> String.concat "\n\t"
        |> fun x -> $"{{\n\t{x}\n}}"
        

/// To compare the iteration method with PReMo
/// The `simplifyMySolution` means whether we should simplify in our iteration
/// The PReMo iteration will `not` work with simplification
let cmpUsualWithPReMo example simplifyInMySolution =
    Flags.TP_APPROX_BY_BISECTION <- false;
    let model = TextInput.parseString example in
    let model =
        match model with
        | MKPTSA kptsa -> RMKPTSA kptsa
        | MPPDA ppda -> RMPPDA ppda
        | _ -> IMPOSSIBLE () in
    // preserve the original equation system
    Flags.SIMPLIFY <- false;
    let runCtx = defaultRunningContext $ simplifyModel model in
    let eqSys, runCtx = genOrGetTPEqSys runCtx in
    let myTimingMark = "MySolution" in
    let premoTimingMark = "PReMoSolution" in
    
    // obtain my solution results
    logTimingMark myTimingMark;
    Flags.SIMPLIFY <- simplifyInMySolution;
    let simplifiedEqSys, _ = simplifyLFPEqSys eqSys runCtx.tpEqSysVarMap.Value in
    let runCtx =
        { runCtx with tpEqSys = Some simplifiedEqSys }
        |> tpApproximation in
    let myResult = runCtx.tpResValIter.Value in
    let myTime = tapTimingMark myTimingMark in
    
    // obtain PReMo results
    logTimingMark premoTimingMark;
    let premoResult =
        iterByPReMo eqSys
        |> Map.ofList
        |> Map.find 0
    in
    let premoTime = tapTimingMark premoTimingMark in
    
    { EqScale = eqSys.Length
      MyResult = myResult
      PReMoResult = premoResult
      MyTime = myTime
      PReMoTime = premoTime }

/// run the generated examples with the given parameters
/// then prints the concrete data to collect
let runGeneratedExamples run (exampleName : string) exampleGen paras =
    let run para =
        run (exampleGen para)
        |> fun x ->
            $"{exampleName} ({para}):\n{x}" in
    Seq.map run paras
    |> String.concat "\n\n"

let runPrecisionTestWithPReMo example precisions =
    let model = TextInput.parseString example in
    let model =
        match model with
        | MKPTSA kptsa -> RMKPTSA kptsa
        | MPPDA ppda -> RMPPDA ppda
        | _ -> IMPOSSIBLE () in
    let runCtx = defaultRunningContext $ simplifyModel model in
    let eqSys, runCtx = genOrGetTPEqSys runCtx in
    let myTimingMark = "my" in
    let premoTimingMark = "PReMo" in
    Flags.TP_APPROX_BY_BISECTION <- false;
    let testPrecision precision =
        Flags.APPROX_MIN_DIFF <- NumericType.Parse precision;
        logTimingMark myTimingMark;
        let myVal = (tpApproximation runCtx).tpResValIter.Value;
        let myTime = tapTimingMark myTimingMark in
        Flags.PREMO_ADDITIONAL_ARGUMENTS <- [ $"--eps={precision}"; "--solver=DN" ];
        logTimingMark premoTimingMark;
        let premoVal = Map(iterByPReMo eqSys).[0] in
        let premoTime = tapTimingMark premoTimingMark in
        (precision, (abs $ myVal - premoVal).ToString "Double", myTime - premoTime)
    in
    List.map testPrecision precisions
    
let private NumTwo = NumericType 2

let private tryFindPPDATime () =
    let picker = function
                 | RPpdaTranslationTime time -> Some time
                 | _ -> None in
    List.tryPick picker Flags.RESULT_ACC

let private constructCtxFromRPTSAExampleString exampleStr =
    let kptsa = TextInput.parseString exampleStr in
    let kptsa, convTime =
        match kptsa with
        | MKPTSA kptsa -> RMKPTSA kptsa, None
        | MPAHORS pahors ->
            let pahorsConvTimeMark = "PAHORS Conv" in
            logTimingMark pahorsConvTimeMark;
            RMKPTSA (PAHORS2KPTSA.translate pahors).rptsa,
                Some $ tapTimingMark pahorsConvTimeMark
        | MPPDA ppda -> RMPPDA ppda, None
        | _ -> IMPOSSIBLE () in
    let ctx = defaultRunningContext $ simplifyModel kptsa in
    match convTime with
    | Some _ ->
        { ctx with
            translateFrom = Some "PAHORS"
            translationTime = convTime }
    | None ->
        match tryFindPPDATime () with
        | Some time ->
            { ctx with
                translateFrom = Some "Automaton"
                translationTime = Some time }
        | None -> ctx

let runSequentialPrecisionTest example =
    let model = TextInput.parseString example in
    let model =
        match model with
        | MKPTSA kptsa -> RMKPTSA kptsa
        | MPPDA ppda -> RMPPDA ppda
        | _ -> IMPOSSIBLE () in
    let runCtx = defaultRunningContext $ simplifyModel model in
    let eqSys, _ = genOrGetTPEqSys runCtx in
    
    // calling PReMo
    let premoTimeMark = "PReMo" in
    logTimingMark premoTimeMark;
    let x0 = Map(iterByPReMo eqSys).[0] in
    let premoPrecision = getPrecision NumTwo 0 $ NUMERIC_ONE - x0 in
    let premoTime = tapTimingMark premoTimeMark in
    [
        "Solution with PReMo:"
        $"PReMo Result: {x0}"
        $"PReMo Precision: {premoPrecision}"
        $"PReMo Calling Time: {premoTime}"
    ]
    |> String.concat "\n\t"
    |> println;
    
    // calling ours
    let eqSys, _ = reindexedExprSystem eqSys in
    let eqSys = Array.ofList eqSys in
    let initVal = Array.map (fun _ -> NUMERIC_ZERO) eqSys in
    let timeMark = "SeqTest" in
    logTimingMark timeMark;
    let rec loop curVal (times : uint) currentPrecision =
        checkTimeOut ();
        if currentPrecision <= premoPrecision then ()
        else begin
            let newVal = NewCompute.computeExprArray eqSys curVal in
            let newX0  = Array.head newVal in
            let closeness = NUMERIC_ONE - newX0 in
            let newPrecision = getPrecision NumTwo currentPrecision closeness in
            if newPrecision <> currentPrecision then begin
                let timeSpan = getTimingFromMark timeMark in
                processPrint "";
                [
                    $"Reached Precision: {newPrecision}"
                    $"Time: {timeSpan}"
                    $"Iteration Times: {times}"
                    $"Current Value: {newX0}"
                ]
                |> String.concat "; with "
                |> println
            end else begin
                printf $"\rIteration times: {times}; Current Diff: {closeness.getDouble ()}      "
            end;
            loop newVal (times + 1u) newPrecision
        end
    in
    loop initVal 0u 0

type CollectionItem =
    | CIPAHORSConvTime
    | CIpPDAConvTime
    | CITpEqConsTime
    | CITpEqSimpTime
    | CITpEqPrimitiveScale
    | CITpEqSimpScale
    | CITpIterTime
    | CITpIterVal
    | CITpIterRoundNumber
    | CITpEqSysTotalConsTime
    | CITpTotalTime
    | CITpBisecTime
    | CITpBisecVal
    | CITpASTTime
    | CITpIsAST
    | CITpPReMoTime
    | CITpPReMoVal
    | CIEttEqConsTime
    | CIEttIterRoundNumber
    | CIEttEqSimpTime
    | CIEttEqPrimitiveScale
    | CIEttEqSimpScale
    | CIEttTotalTime
    | CIEttIterTime
    | CIEttIterVal
    | CIEttEqSysTotalConsTime
    | CIEttBisecTime
    | CIEttBisecVal
    | CIEttQualTime
    | CIEttPReMoTime
    | CIEttPReMoVal
    | CIEttHasVal
    | CIEttIsPAST
    | CIEttRawBisecVal
    | CIEttRawIterVal
    static member Cases =
        FSharpType.GetUnionCases typeof<CollectionItem>
        |> Array.map (fun x -> (x.Name.ToLower(), FSharpValue.MakeUnion (x, [||]) :?> CollectionItem))
        |> Map.ofArray
    static member Parse (str : string) =
        match str.ToLower () with
        | "pahors" -> CIPAHORSConvTime
        | "isast" -> CITpIsAST
        | "ast?" -> CITpIsAST
        | "ispast" -> CIEttIsPAST
        | "past?" -> CIEttIsPAST
        | "past" -> CIEttIsPAST
        | str ->
            match Map.tryFind str CollectionItem.Cases with
            | Some it -> it
            | None ->
                match Map.tryFind $"ci{str}" CollectionItem.Cases with
                | Some it -> it
                | _ -> failwith $"Unknown name \"{str}\" to parse for CollectionItem"
    static member ToLaTeXName (item : CollectionItem) =
        match item with
        | CIPAHORSConvTime ->        "$t_{\\mathit{conv}}$"
        | CITpIsAST ->               "$\\isast$"
        | CITpBisecVal ->            "$\\abisec$"
        | CITpIterVal ->             "$\\aiter$"
        | CITpEqSysTotalConsTime ->  "$\\teq$"
        | CITpASTTime ->             "$\\tast$"
        | CITpBisecTime ->           "$\\tbisec$"
        | CITpIterTime ->            "$\\titer$"
        | CITpEqPrimitiveScale ->    "${\\numeq}_1$"
        | CITpEqSimpScale ->         "${\\numeq}_2$"
        | CIEttHasVal ->             "$\\isfin$"
        | CIEttIsPAST ->             "$\\ispast$"
        | CIEttRawBisecVal ->        "$\\abisec$"
        | CIEttRawIterVal ->         "$\\aiter$"
        | CIEttEqSysTotalConsTime -> "$\\teq$"
        | CIEttQualTime ->           "$\\tfin$"
        | CIEttBisecTime ->          "$\\tbisec$"
        | CIEttIterTime ->           "$\\titer$"
        | CIEttEqPrimitiveScale ->   "${\\numeq}_1$"
        | CIEttEqSimpScale ->        "${\\numeq}_2$"
        | CITpIterRoundNumber ->     "$\\niter$"
        | CIEttIterRoundNumber ->    "$\\niter$"
        | CIpPDAConvTime ->          "$t_{\\mathit{conv}}$"
        | _ -> failwith $"Unknown Column Name \"{item}\" for generating the LaTeX table."

/// collect required items for the list of examples
/// returns a table generated by `tableGenerator`
/// The code generates a raw table
/// The table is generated in the same order as the given sequence
/// The left-and-uppermost item must be of name `ExampleName`
let runAutoTableCollection
    (tableGenerator : seq<seq<string>> -> 'r)
    (itemsToCollect : seq<CollectionItem>)
    (examplesWithNames : seq<string * string>)
    stopWhenFirstTimeout =
    // to just find items quickly
    let candidateItems = Set.ofSeq itemsToCollect in
    let candidateItemString = Set.map toString candidateItems |> String.concat " " |> fun x -> x.ToLower () in
    let hasItems items =
        Set.ofSeq items
        |> Set.intersect candidateItems
        |> Set.isEmpty
        |> not
    in
    let existsSubstring (toFind : string) = candidateItemString.Contains (toFind.ToLower ()) in

    // precomputed results
    let toConstructTpEqSys = existsSubstring "tp" in
    let toFindTpIterVal = existsSubstring "TpIter" in
    let toFindTpPReMoVal = hasItems [ CITpPReMoTime; CITpPReMoVal ] in
    let toFindTpBisecVal = existsSubstring "TpBisec" in
    let toFindIfAST = existsSubstring "ast" in
    let toConstructEttEqSys = existsSubstring "ett" in
    let toFindIfEttHasVal = hasItems [
        CIEttIterTime; CIEttIterVal; CIEttQualTime; CIEttHasVal
    ] in
    let toFindEttPReMoVal = hasItems [
        CIEttPReMoTime; CIEttPReMoVal
    ] in
    let toFindEttIterVal = existsSubstring "EttIter" in
    let toFindEttBisecVal = (existsSubstring "EttBisec" || existsSubstring "EttRawBisec") in
    
    let mutable stopBeforeHand = false
    
    // collect one example
    let autoCollectOneExample name example =
        if stopBeforeHand then
            flip Seq.map itemsToCollect (fun _ -> "$\\mathit{timeout}$")
            |> Seq.append [ name ]
        else
        runInitialisation ();
        let iterTpCtx = blank () in
        let tpPReMoCtx = blank () in
        let ettPReMoCtx = blank () in
        let iterEttCtx = blank () in
        // let the data collection be not bothered by the outside parameters
        Flags.ITER_BY_PREMO <- false;
        // the resulting ctx contains bisection value for TP if required
        // and the built-in iteration result for ETT if required
        let ctx =
            try
            constructCtxFromRPTSAExampleString example
            ||> (toConstructTpEqSys, snd << genOrGetTPEqSys)
            ||> (toFindTpIterVal, fun x ->
                Flags.TP_APPROX_BY_BISECTION <- false;
                Flags.ITER_BY_PREMO <- false;
                iterTpCtx.Value <- tpApproximation x;
                x)
            ||> (toFindTpPReMoVal, fun x ->
                Flags.TP_APPROX_BY_BISECTION <- false;
                Flags.ITER_BY_PREMO <- true;
                tpPReMoCtx.Value <- tpApproximation x;
                x)
            ||> (toFindTpBisecVal, fun x ->
                Flags.TP_APPROX_BY_BISECTION <- true;
                tpApproximation x)
            ||> (toFindIfAST, tpQualitative)
            ||> (toConstructEttEqSys, snd << genOrGetETTEqSys)
            ||> (toFindIfEttHasVal, cettQualitative)
            |> fun x ->
                let tpResVal = getTpResVal x in
                // there must be a value
                let hasVal = x.cettQualRes = Some true && tpResVal <> Some NUMERIC_ZERO in
//                // if externally confirmed, then, even there is no need to check, just compute
//                let hasVal = hasVal || Flags.EXTERNAL_ETT_QUALITATIVE_CONFIRM in
                if not hasVal then Some x
                else
                    x
                    ||> (toFindEttIterVal, fun x ->
                        Flags.ETT_APPROX_BY_BISECTION <- false;
                        Flags.ITER_BY_PREMO <- false;
                        iterEttCtx.Value <- cettApproximation x;
                        x)
                    ||> (toFindEttPReMoVal, fun x ->
                        Flags.ETT_APPROX_BY_BISECTION <- false;
                        Flags.ITER_BY_PREMO <- true;
                        ettPReMoCtx.Value <- cettApproximation x;
                        x)
                    ||> (toFindEttBisecVal, fun x ->
                        Flags.ETT_APPROX_BY_BISECTION <- true;
                        cettApproximation x)
                    |> Some
            with
            | :? TimeoutException ->
                errPrint $"Timeout in example \"{name}\".";
                if stopWhenFirstTimeout then stopBeforeHand <- true;
                None
        in
        processPrint $"Total Time Used for Example \"{name}\": {Flags.GLOBAL_TIMING.getTotalRawTime ()}";
        match ctx with
        | Some ctx ->
            let tpResVal = getTpResVal ctx in
            let hasEttVal = ctx.cettQualRes = Some true && tpResVal <> Some NUMERIC_ZERO in
            flip Seq.map itemsToCollect (function
                | CIpPDAConvTime ->
                    match ctx.translateFrom with
                    | Some str when Option.isSome ctx.translationTime ->
                        if str.ToLower () = "automaton" then
                            (Option.get ctx.translationTime).TotalSeconds.ToString("f4")
                        else "-"
                    | _ -> "-"
                | CIEttIterRoundNumber ->
                    if hasEttVal then
                        Option.defaultValue 0uL iterEttCtx.Value.ettIterationRounds
                        |> toString
                        |> String.filter Char.IsNumber
                    else "-"
                | CITpIterRoundNumber ->
                    Option.defaultValue 0uL iterTpCtx.Value.tpIterationRounds
                    |> toString
                    |> String.filter Char.IsNumber
                | CIPAHORSConvTime ->
                    match ctx.translationTime with
                    | None -> "-"
                    | Some v -> v.TotalSeconds.ToString("f4")
                | CITpEqConsTime -> ctx.tpEqSysConstructTime.Value.TotalSeconds.ToString("f4")
                | CITpEqSimpTime -> ctx.tpEqSysSimplificationTime.Value.TotalSeconds.ToString("f4")
                | CITpEqPrimitiveScale -> toString $ ctx.tpEqSysPrimitiveScale.Value
                | CITpEqSimpScale -> toString $ ctx.tpEqSysSimplifiedScale.Value
                | CITpIterTime -> iterTpCtx.Value.tpApproximationTimeIter.Value.TotalSeconds.ToString("f4")
                | CITpIterVal -> iterTpCtx.Value.tpResValIter.Value.ToString("f4")
                | CITpBisecTime -> ctx.tpApproximationTimeBisec.Value.TotalSeconds.ToString("f4")
                | CITpBisecVal -> ctx.tpResValBisec.Value.ToString("f4")
                | CITpASTTime -> ctx.tpQualitativeTime.Value.TotalSeconds.ToString("f4")
                | CITpIsAST -> toString $ ctx.tpAST.Value
                | CITpPReMoTime -> tpPReMoCtx.Value.tpApproximationTimeIter.Value.TotalSeconds.ToString("f4")
                | CITpPReMoVal -> tpPReMoCtx.Value.tpResValIter.Value.ToString("f4")
                | CIEttEqConsTime -> ctx.ettEqSysConstructTime.Value.TotalSeconds.ToString("f4")
                | CIEttEqSimpTime -> ctx.ettEqSysSimplificationTime.Value.TotalSeconds.ToString("f4")
                | CIEttEqPrimitiveScale -> toString $ ctx.ettEqSysPrimitiveScale.Value
                | CIEttEqSimpScale -> toString $ ctx.ettEqSysSimplifiedScale.Value
                | CIEttQualTime -> ctx.ettQualitativeTime.Value.TotalSeconds.ToString("f4")
                | CIEttHasVal -> toString $ ctx.cettQualRes.Value
                | CIEttTotalTime ->
                    [
                        ctx.ettEqSysConstructTime
                        ctx.ettEqSysSimplificationTime
                        ctx.ettQualitativeTime
                        ctx.ettApproximationTimeBisec
                        ettPReMoCtx.Value.ettApproximationTimeIter
                        iterEttCtx.Value.ettApproximationTimeIter
                    ]
                    |> List.map (Option.defaultValue TimeSpan.Zero)
                    |> List.reduce (+)
                    |> fun x -> x.TotalSeconds.ToString("f4")
                | CITpTotalTime ->
                    [
                        ctx.tpEqSysConstructTime
                        ctx.tpEqSysSimplificationTime
                        ctx.tpQualitativeTime
                        ctx.tpQuantitativeTime
                        ctx.tpApproximationTimeBisec
                        tpPReMoCtx.Value.tpApproximationTimeIter
                        iterTpCtx.Value.tpApproximationTimeIter
                    ]
                    |> List.map (Option.defaultValue TimeSpan.Zero)
                    |> List.reduce (+)
                    |> fun x -> x.TotalSeconds.ToString("f4")
                | CIEttIsPAST ->
                    let cettRes = ctx.cettQualRes.Value in
                    let astRes  = ctx.tpAST.Value in
                    toString (cettRes && astRes)
                | CITpEqSysTotalConsTime ->
                    (ctx.tpEqSysConstructTime.Value + ctx.tpEqSysSimplificationTime.Value).TotalSeconds.ToString("f4")
                | CIEttEqSysTotalConsTime ->
                    (ctx.ettEqSysConstructTime.Value + ctx.ettEqSysSimplificationTime.Value).TotalSeconds.ToString("f4")
                | CIEttIterTime -> 
                    if hasEttVal then
                        iterEttCtx.Value.ettApproximationTimeIter.Value.TotalSeconds.ToString("f4")
                    else "-"
                | CIEttIterVal -> 
                    if hasEttVal then
                        iterEttCtx.Value.cettResValIter.Value.ToString("f4")
                    else "-"
                | CIEttBisecTime ->
                    if hasEttVal then
                        ctx.ettApproximationTimeBisec.Value.TotalSeconds.ToString("f4")
                    else "-"
                | CIEttBisecVal ->
                    if hasEttVal then
                        ctx.cettResValBisec.Value.ToString("f4")
                    else "-"
                | CIEttPReMoTime -> 
                    if hasEttVal then
                        ettPReMoCtx.Value.ettApproximationTimeIter.Value.TotalSeconds.ToString("f4")
                    else "-"
                | CIEttPReMoVal -> 
                    if hasEttVal then
                        ettPReMoCtx.Value.cettResValIter.Value.ToString("f4")
                    else "-"
                | CIEttRawBisecVal -> 
                    if hasEttVal then
                        ctx.rawCettResValBisec.Value.ToString("f4")
                    else "-"
                | CIEttRawIterVal ->
                    if hasEttVal then
                        iterEttCtx.Value.rawCettResValIter.Value.ToString("f4")
                    else "-")
        | None -> flip Seq.map itemsToCollect (fun _ -> "$\\mathit{timeout}$")
        |> Seq.append [ name ]
        |> fun x ->
            processPrint $"Data for \"{name}\":"
            println $ printFullSeq x;
            x
    in
    
    // collect values
    Seq.map (uncurry autoCollectOneExample) examplesWithNames
    |> Seq.append [ Seq.append [ "ExampleName" ] $ Seq.map toString itemsToCollect ]
    |> tableGenerator

let private latexTabGen s =
    let newHeader =
        Seq.head s
        |> Array.ofSeq
        |> Array.map (fun x ->
            match x with
            | "ExampleName" -> x
            | x -> CollectionItem.Parse x |> CollectionItem.ToLaTeXName)
    in
    Seq.map Array.ofSeq s
    |> Array.ofSeq
    |> fun x ->
        x[0] <- newHeader;
        printStrTableInLaTeX x

/// input items to collect as well as the examples of form (name, exampleContent)
let runAutoLaTeXTableCollection items examples =
    runAutoTableCollection latexTabGen items examples

/// another version of collecting stuff in ONE ROUND, better control
let runAutoTpAndEttLaTeXTableCollection items examples stopWhenFirstTimeout =
    let table =
        runAutoTableCollection id items examples stopWhenFirstTimeout
        |> Seq.map Array.ofSeq
        |> Array.ofSeq
    in
    let findTableColumnNotContaining (word : string) =
        Array.transpose table
        |> Array.filter (fun x -> not $ (Array.head x).ToLower().Contains(word.ToLower()))
        |> Array.transpose
    let tpTable = findTableColumnNotContaining "CIEtt" in
    let ettTable = findTableColumnNotContaining "CITp" in
    latexTabGen tpTable, latexTabGen ettTable

/// run the examples from Wang et al. and print the latex table
let runAutoCollectWangExampleData itemsToCollect =
    let examples =
        let pProb x = $"\\prob{{{x}}}" in
        // of shape: $\text{<name>}_{<para format>}$
        let exampleNaming (exampleName : string) (paraFormat : string) =
            $"$\\text{{{exampleName}}}_{{{paraFormat}}}$" in
        let exampleList =
            [
                "Coupon" , genFullCoupon , [ 100; 300; 500 ], fun x -> pProb $"T > {x}"
                "Race"   , genFullRace   , [  40;  35;  45 ], fun x -> $"(X = {x})"
                "Prspeed", genToolPrspeed, [ 150; 200; 250 ], fun x -> pProb $"T > {x}"
                "RdAdder", genRdAdder    , [  25;  50;  75 ], fun x -> pProb $"X - E[X] >= {x}"
            ] in
        let exampleGen (name, generator, paras, naming) =
            List.map generator paras
            |> List.zip (List.map (exampleNaming name << naming) paras) in
        List.map exampleGen exampleList
        |> List.concat
    in
    runAutoLaTeXTableCollection itemsToCollect examples false
    
    
/// collect the content AT ONCE and then split them to TP and ETT table respectively
let runAutoCollectTpAndEttLaTeXTable
        genTable
        totalItemsToCollect
        exampleGen
        scales
        timeout =
    // implementation:
    // collect all data once
    // divide the TP part and the ETT part
    Flags.CORE_TIME_OUT <- timeout;
    let examples = List.map (fun scale -> ($"{scale}", exampleGen scale)) scales in
    let table =
        runAutoTableCollection id totalItemsToCollect examples true
        |> Seq.map Array.ofSeq
        |> Array.ofSeq
    in
    let findTableColumnNotContaining (word : string) =
        Array.transpose table
        |> Array.filter (fun x -> not $ (Array.head x).ToLower().Contains(word.ToLower()))
        |> Array.transpose
    let tpTable =
        genTable $ findTableColumnNotContaining "CIEtt" in
    let ettTable =
        genTable $ findTableColumnNotContaining "CITp" in
    tpTable, ettTable
    
    
let private stdTpDataToCollect =
    [
        CITpIsAST
        CITpBisecVal
        CITpIterVal
        CITpEqSysTotalConsTime
        CITpASTTime
        CITpBisecTime
        CITpIterTime
        CITpEqPrimitiveScale
        CITpEqSimpScale
        CITpIterRoundNumber
    ]
let private stdEttDataToCollect =
    [
        CIEttHasVal
        CIEttIsPAST
        CIEttRawBisecVal
        CIEttRawIterVal
        CIEttEqSysTotalConsTime
        CIEttQualTime
        CIEttBisecTime
        CIEttIterTime
        CIEttEqPrimitiveScale
        CIEttEqSimpScale
        CIEttIterRoundNumber
    ]
    
    
let convertStrTableHeaderToLaTeXHeader newNameForExampleName table =
    let tab = Seq.map Array.ofSeq table |> Array.ofSeq in
    let _ =
        tab[0] <- flip Array.map tab[0] $ fun x ->
            match x with
            | "ExampleName" -> newNameForExampleName
            | x -> CollectionItem.Parse x |> CollectionItem.ToLaTeXName
    in
    printStrTableInLaTeX tab
    
    
let runAutoCollectPAHORSLaTeXTable () =
    // configuration information
    let tpItemsToCollect =
        [
            CITpIsAST
            CITpBisecVal
            CITpIterVal
            CIPAHORSConvTime
            CITpEqSysTotalConsTime
            CITpASTTime
            CITpBisecTime
            CITpIterTime
            CITpEqPrimitiveScale
            CITpEqSimpScale
            CITpIterRoundNumber
        ]
    in
//    let examples =
//        [
//            "Ex2.3", "example phors 2.3"
//            "Listgen", "example phors listgen"
//            "Treegen", "example 5"
//            "ListEven", "example 10 (listeven)"
//            "ListEven2", "example 11"
//            "Ex5.4(0, 0)", "example 9 (0 0)"
//            "Ex5.4(0.3, 0.3)", "example 9 (3 3)"
//            "Ex5.4(0.5, 0.5)", "example 9 (5 5)"
//            "Ex5.4(0.2, 0.8)*", "example 9 (2 8)"
//            "Ex5.4(0.2, 0.8)*", "example 9 (2 8)"
//            "Ex5.4(0.2, 0.6)*", "example 9 (2 6)"
//            "TreeEven(0.5)", "example 12"
//            "TreeEven(0.49)", "example 12 (49)"
//            "TreeEven(0.51)", "example 12 (51)"
//            "Discont(0.01, 0.99)", "example 8"
//            "Discont($\\frac{1}{1024}$, $\\frac{1023}{1024}$)*", "example 8 (1024)"
//            "Example 4.9", "example 7"
//            "Printer", "example 3.1 (Heavy)"
//            "NTreegen (1)", "example ngen (1)"
//            "NTreegen (3)", "example ngen (3)"
//            "NTreegen (6)", "example ngen (6)"
//            "NTreegen (9)", "example ngen (9)"
//            "VTreegen (1)", "example vgen (1)"
//            "VTreegen (2)", "example vgen (2)"
//            "VTreegen (3)", "example vgen (3)"
//            "VTreegen (4)", "example vgen (4)"
//        ]
//    in
    
    
    // execution
//    let fetchFileContent txtName =
//        File.ReadAllText $"../../../examples/PAHORS/{txtName}.txt"
//    in
//    let nameExampleMap =
//        List.map (BiMap.sndMap fetchFileContent) examples
//        |> Map.ofSeq
//    in
//    let names = List.map fst examples in
    (Thread ((fun () -> 
        let tpTable, ettTable =
                runAutoCollectTpAndEttLaTeXTable
                    (convertStrTableHeaderToLaTeXHeader "$m$")
                    (tpItemsToCollect ++ stdEttDataToCollect)
//                    (flip Map.find nameExampleMap)
                    genPAHORSTreeGen
                    [1..9]
                    None
        in
        println $ tpTable + "\n\\bigskip\n" + ettTable),
     104857600)).Start ()
    
    
let runAutoCollectStdDataToLaTeXTable exampleGen scales timeout =
    let tpTable, ettTable =
        runAutoCollectTpAndEttLaTeXTable
            (convertStrTableHeaderToLaTeXHeader "$m$")
            (stdTpDataToCollect ++ stdEttDataToCollect)
            exampleGen
            scales
            timeout
    in
    "TP:\n" + tpTable + "ETT:\n" + ettTable
    
let runAutoCollectTreeShapeWithRandomSearchLaTeXTable () =
    (Thread ((fun () ->
        println $ runAutoCollectStdDataToLaTeXTable
            (genKDyckLanguagesWithRandomUp "1/2")
            [1..15]
            (Some $ TimeSpan.FromMilliseconds 500000)), 
     104857600)).Start ()
    
    
let runAutoCollectTreeShapeWithShortcutDivergenceLaTeXTable () =
    (Thread ((fun () ->
        println $ runAutoCollectStdDataToLaTeXTable
            (genKDyckLanguagesWithShortcut "1/2" ShortcutDivergence)
            [ 10; 20; 50; 100; 200; 500; 1000 ]
            None),
     104857600)).Start ()
    
let examplesToGenerate =
    [
//        "Tree Shape (Random Traverse)", genKDyckLanguagesWithRandomUp "1/2", [1..15]
//        "Tree Shape (Basic, 1/3-2/3)", genKDyckLanguages "1/3", [
//            10; 20; 50; 100; 200; 500; 1000
//        ]
//        "Queues (Shortcut Ter)", genQueueWithDifferentABBehavior "1/2" "1/3" "1/6" ShortcutTermination, [
//            10; 20; 50; 100; 200; 500
//        ]
//        "Queues (Shortcut Div)", genQueueWithDifferentABBehavior "1/3" "1/3" "1/3" ShortcutDivergence, [
//            10; 20; 50; 100; 200;
//        ]
//        "Lossy Numbers (Shortcut Jump)", genKCrossDependenciesWithVariantShortcut "1/2" ShortcutTermination, [
//            10; 20; 50; 100; 200; 500; 1000
//        ]
//        "Lossy Numbers (Shortcut Div)", genKCrossDependenciesWithVariantShortcut "1/2" ShortcutDivergence, [
//            10; 20; 50; 100; 200; 500; 1000
//        ]
//        "Queues (Random Serve)", genQueueGlobalRandomServe "1/3" "1/3" "1/3" "1/2" ShortcutDivergence, [1..15] 
//        "GRT (Shortcut Divergence, 1/2)", genTreeShapeGRT true "1/2", [1..20]
//        "LRT (Shortcut Divergence, 1/2)", genTreeShapeLRT true "1/2", [1..20]
//        "GRT (No Shortcut, 1/2)", genTreeShapeGRT false "1/2", [1..20]
//        "LRT (No Shortcut, 1/2)", genTreeShapeLRT false "1/2", [1..20]
//        "GRT (No Shortcut, 1/3)", genTreeShapeGRT false "1/3", [1..20]
//        "GRT (No Shortcut, 2/3)", genTreeShapeGRT false "2/3", [1..20]
//        "LRT (No Shortcut, 1/3)", genTreeShapeLRT false "1/3", [1..20]
//        "LRT (No Shortcut, 2/3)", genTreeShapeLRT false "2/3", [1..20]
//        "Queues (Random Serve, Ter)", genQueueGlobalRandomServe "1/2" "1/3" "1/6" "1/4" ShortcutTermination, [1..15]
    ]
    
/// auto run to collect the TP and ETT information in the paper
let runAutoCollectPaperExamplesLaTeXTable () =
    let timeout = Some $ TimeSpan.FromMilliseconds 500000 in
    Flags.DEBUG <- true;
//    Flags.INNER_DEBUG <- true;
    let runAnExample (name, gen, paras) =
//        try
            "---------------------------------------------------------------------------\n" +
            $"{name} Data:\n" +
            runAutoCollectStdDataToLaTeXTable gen paras timeout +
            "\n---------------------------------------------------------------------------\n\n"
//        with
//        | e ->
//            $"{name} DATA COLLECTION ERROR\n{e}\n" +
//            e.StackTrace
    in
    (Thread ((fun () ->
        List.map runAnExample examplesToGenerate
        |> String.concat "\n\n"
        |> println),
     104857600)).Start ()
    
    
/// from email by Prof. Murawski:
/// To the example ``Tree Shape'':
/// the traversal strategy determined globally is called Global Repeated Traversal (GRT)
/// while the traversal strategy determined locally is called Local Repeated Traversal (LRT)
/// This script is to run to collect only the TP value
let runAutoCollectTpOnlyLaTeXTableForGRTAndLRT () =
    Flags.DEBUG <- true;
    Flags.CORE_TIME_OUT <- Some $ TimeSpan.FromMilliseconds 500000;
    let genExamplesWithNames gen paras =
        List.map (fun idx -> (toString idx, gen idx)) paras in
    let genTable gen paras =
        runAutoTableCollection
            (convertStrTableHeaderToLaTeXHeader "$m$")
            stdTpDataToCollect
            (genExamplesWithNames gen paras)
            true
    in
    
    let examples =
        [
            "GRT (No Shortcut, 1/3)", genTreeShapeGRT false "1/3", [1..20]
            "GRT (No Shortcut, 2/3)", genTreeShapeGRT false "2/3", [1..20]
            "LRT (No Shortcut, 1/3)", genTreeShapeLRT false "1/3", [1..20]
            "LRT (No Shortcut, 2/3)", genTreeShapeLRT false "2/3", [1..20]
        ]
    let runAnExample (name, generator, paras) =
        try name + ":\n" + genTable generator paras
        with | e -> $"Error when generating \"{name}\": {e.Message}"
    in
    
    (Thread ((fun () ->
        List.map runAnExample examples
        |> String.concat "\n\n"
        |> println),
     104857600)).Start ()
    
/// extract the result item
let private extractResItem (res : FinalResult list) (item : FinalResult) =
    let getName item =
        match FSharpValue.GetUnionFields(item, item.GetType()) with
        | (info, _) -> info.Name
    in
    let itemName = getName item in
    let finder case =
        let thisName = getName case in
        thisName = itemName
    in
    List.find finder res
    
// -------------------------------- Compare Direct & Indirect pPDA Results --------------------------------
    
let private collectPpdaCmpRes example =
    // PRE-RUN to reduce system issues
    Flags.DIRECT_PPDA <- false;
    runFromString example;
    Flags.DIRECT_PPDA <- true;
    runFromString example;
    let directResult = List.rev Flags.RESULT_ACC in
    Flags.DIRECT_PPDA <- false;
    runFromString example;
    let convertResult = List.rev Flags.RESULT_ACC in
    (directResult, convertResult)
    
/// just print the two comparison results
let private printSepCmpRes dirRes convRes =
    // prepare to recover the result
    let res = Flags.RESULT_ACC in
    Flags.RESULT_ACC <- dirRes;
    printResults ();
    Flags.RESULT_ACC <- convRes;
    printResults ();
    Flags.RESULT_ACC <- res
    
let private toResMap res =
    let mapper (record : FinalResult) = record.GetAbsInfo in
    Map.ofList $ List.map mapper res
    
let percentageChange oriVal newVal =
    if oriVal = 0.0 then
        if newVal = 0.0 then 0.0
        else 100.0  // if original value is 0 and new value is non-zero, treat it as a 100% increase
    else
        ((newVal - oriVal) / oriVal) * 100.0

let resValCmp (dir : obj) (conv : obj) =
    match dir with
    | :? string as strOri -> $"{strOri} -> {conv}."
    | :? uint as uintOri -> 
        let change = percentageChange (float uintOri) (float (conv :?> uint)) in
        let direction = if change > 0.0 then "INC" elif change < 0.0 then "DEC" else "UNCHANGED" in
        $"{uintOri} -> {conv} ({direction} {Math.Abs(change)}%%)"
    | :? TimeSpan as tsOri ->
        let tsConv = conv :?> TimeSpan in
        let change = percentageChange tsOri.TotalSeconds tsConv.TotalSeconds in
        let direction = if change > 0.0 then "INC" elif change < 0.0 then "DEC" else "UNCHANGED" in
        $"{tsOri} -> {tsConv} ({direction} {Math.Abs(change)}%%)"
    | :? NumericType as numOri ->
        let numConv = conv :?> NumericType in
        let change = percentageChange (numOri.getDouble ()) (numConv.getDouble ()) in
        let direction = if change > 0.0 then "INC" elif change < 0.0 then "DEC" else "UNCHANGED" in
        $"{numericValuePrint numOri} -> {numericValuePrint numConv} ({direction} {Math.Abs change}%%)"
    | :? uint64 as uint64Ori -> 
        let change = percentageChange (float uint64Ori) (float (conv :?> uint64)) in
        let direction = if change > 0.0 then "INC" elif change < 0.0 then "DEC" else "UNCHANGED" in
        $"{uint64Ori} -> {conv} ({direction} {Math.Abs(change)}%%)"
    | :? Result<bool, string> as resOri ->
        let resConv = conv :?> Result<bool, string> in
        let resOri =
            match resOri with
            | Ok r -> toString r
            | Error e -> $"\"{e}\""
        in
        let resConv =
            match resConv with
            | Ok r -> toString r
            | Error e -> $"\"{e}\""
        in
        $"{resOri} -> {resConv}"
    | _ -> undefined ()
    
let printItemCmp dirMap convMap key =
    match (Map.tryFind key dirMap,
           Map.tryFind key convMap) with
    | (Some dirV, Some convV) ->
        println $ $"{key}: " + resValCmp dirV convV
    | (Some dirV, None) ->
        println $ $"{key}: " + FinalResult.FieldPrint dirV + " -> NONE."
    | (None, Some convV) ->
        println $ $"{key}: None -> " + FinalResult.FieldPrint convV
    | (None, None) ->
        println $ $"{key}: NO VALUE FOR BOTH."
    
let compareMaps dirMap convMap =
    let dirKeys = Set(Map.keys dirMap) in
    let convKeys = Set(Map.keys convMap) in
    let allKeys = Set.union dirKeys convKeys in
    List.iter (printItemCmp dirMap convMap) $ Set.toList allKeys
    
let private printCmpRes dirRes convRes =
    processPrint "";
    processPrint "-------------------------------- Comparison --------------------------------";
    let dirMap = toResMap dirRes in
    let convMap = toResMap convRes in
    compareMaps dirMap convMap
    
let runPpdaCmp example =
    // collect results
    let dirRes, convRes = collectPpdaCmpRes example in
    
    // print the comparisons
    printCmpRes dirRes convRes
    
let runPpdaCmpLaTeXTableGen () =
    let rec repStr n s =
        match n with
        | 0 -> ""
        | 1 -> s
        | _ -> s + repStr (n - 1) s
    in
    let sequentialN n =
        "%BEGIN pPDA config
         q0 := q
         gamma0 := S
         %END pPDA config
 
         %BEGIN pPDA rules\n" +
         $"q S -> q" + repStr n " qF" + ".
         q qF -> q F.
         t qF -> q F.
         f qF -> q F.
         q F (1 / 4)-> t .
         q F (1 / 4)-> f .
         q F (1 / 2)-> q F FI.
         t FI -> q F.
         f FI -> f .
         %END pPDA rules"
    in
    let examples =
        // mode of conducting sequential test on the `sequentialN` example series.
        let mapper idx = ($"{idx}", sequentialN idx) in
        List.map mapper [1..14] ++
        // mode of testing all `cert` examples
        getFilesWithContent "../../../../more examples/pPDA/cert/" "txt"
        // mode of the new and-or-tree example
//        [ "and-or-tree", readFileString "../../../../more examples/pPDA/new and-or-tree example.txt" ]
    in
    let tpToCollect =
        [
            CIpPDAConvTime
//            CITpIsAST
//            CITpBisecVal
//            CITpIterVal
//            CITpEqSysTotalConsTime
//            CITpASTTime
//            CITpBisecTime
//            CITpIterTime
//            CITpEqPrimitiveScale
//            CITpEqSimpScale
//            CITpIterRoundNumber
        ]
    in
    let ettToCollect =
        [
//            CIEttHasVal
//            CIEttIsPAST
//            CIEttRawBisecVal
//            CIEttRawIterVal
//            CIEttEqSysTotalConsTime
////            CIEttQualTime
////            CIEttBisecTime
//            CIEttIterTime
//            CIEttEqPrimitiveScale
//            CIEttEqSimpScale
//            CIEttIterRoundNumber
        ]
    in
    let run () =
        let run () =
            runAutoTpAndEttLaTeXTableCollection (tpToCollect ++ ettToCollect) examples false
        in
    //    Flags.INNER_DEBUG <- true;
    //    Flags.CORE_TIME_OUT <- Some $ TimeSpan.FromSeconds 30;
        // run conversion-based
        Flags.DIRECT_PPDA <- false;
        let convTables = run () in
        // run direct-way
        Flags.DIRECT_PPDA <- true;
        let directTables = run () in
        printfn "-------------------- Conversion-Based --------------------";
        printfn $"{convTables}";
        printfn "-------------------- Direct-pPDA --------------------";
        printfn $"{directTables}"
    in
    (Thread((fun () -> run ()), 104857600)).Start ()
    
let runGenATpAndEttLaTeXTable examples =
    let tpTab, ettTab =
        runAutoTpAndEttLaTeXTableCollection
            (stdTpDataToCollect ++ stdEttDataToCollect)
            examples
            false
    in
    println $ "TP:\n" + tpTab + "\nETT:\n" + ettTab
    
let runSeparateExampleLaTeXTableGen () =
    let examples =
        [
//            "example1.txt", readFileString "../../../../more examples/rPTSA/example 1.txt"
            "and-or-tree-0", readFileString "../../../../more examples/pPDA/new and-or-tree example.txt"
        ]
    in
    runGenATpAndEttLaTeXTable examples
    
let runPpdaCmpExamples examples =
    let printer (name, (dirRes, convRes)) =
        printf "====================== "
        printf $"{name}"
        printfn " ======================"
        printCmpRes dirRes convRes
        printf "====================== END "
        printf $"{name}"
        printfn " ======================"
    in
    List.map (BiMap.sndMap collectPpdaCmpRes) examples
    |> List.iter printer
    
let testRunCertExamples () =
    Flags.TP_APPROX_BY_BISECTION <- false;
    Flags.TP_QUALITATIVE <- false;
    getFilesWithContent "../../../../more examples/pPDA/cert/" "txt"
    |> runPpdaCmpExamples
    
let runGenCertExamplesTables () =
    Flags.TP_APPROX_BY_BISECTION <- false;
    Flags.TP_QUALITATIVE <- false;
    getFilesWithContent "../../../../more examples/pPDA/cert/" "txt"
    |> List.map (BiMap.sndMap collectPpdaCmpRes)
    
let testSeqSequentialN () =
    let rec repStr n s =
        match n with
        | 0 -> ""
        | 1 -> s
        | _ -> s + repStr (n - 1) s
    in
    let sequentialN n =
        "%BEGIN pPDA config
         q0 := q
         gamma0 := S
         %END pPDA config
 
         %BEGIN pPDA rules\n" +
         "q S -> q" + repStr n " qF" + ".
         q qF -> q F.
         t qF -> q F.
         f qF -> q F.
         q F (1 / 4)-> t .
         q F (1 / 4)-> f .
         q F (1 / 2)-> q F FI.
         t FI -> q F.
         f FI -> f .
         %END pPDA rules"
    in
    let run () =
        println $ runAutoCollectStdDataToLaTeXTable sequentialN [1..14] None
    in
    (Thread((fun () -> run ()), 104857600)).Start ()
    
    
let runGenAndOrTreeLaTeXTables () =
    let examples = andOrTreeExamples () in
    let ettToCollect =
        [
//            CIEttHasVal
//            CIEttIsPAST
//            CIEttRawBisecVal
            CIEttRawIterVal
            CIEttEqSysTotalConsTime
//            CIEttQualTime
//            CIEttBisecTime
            CIEttIterTime
            CIEttEqPrimitiveScale
            CIEttEqSimpScale
            CIEttIterRoundNumber
        ]
    in
    let toCollect =
        stdTpDataToCollect ++ ettToCollect
//        [ CIpPDAConvTime ]
    in
    Flags.DIRECT_PPDA <- false;
    let convTpTab, convEttTab =
        runAutoTpAndEttLaTeXTableCollection
            toCollect
            examples
            false
    in
    Flags.DIRECT_PPDA <- true;
    let dirTpTab, dirEttTab =
        runAutoTpAndEttLaTeXTableCollection
            toCollect
            examples
            false
    in
    println "-------------------- Conversion Method --------------------"
    println $ "TP:\n" + convTpTab + "\nETT:\n" + convEttTab
    println "-------------------- Direct Method --------------------"
    println $ "TP:\n" + dirTpTab + "\nETT:\n" + dirEttTab
    
let genAndOrTreeExampleFiles () =
    let dir = "../../../../more examples/pPDA/and-or-tree/" in
    let iter (name, content) =
        let path = Path.Join(dir, name + ".txt") in
        File.WriteAllText(path, content)
    in
    andOrTreeExamples ()
    |> List.iter iter
    