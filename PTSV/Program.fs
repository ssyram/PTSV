// Learn more about F# at http://docs.microsoft.com/dotnet/fsharp

module Program

open System
open System.Collections.Generic
open System.Threading
open Microsoft.FSharp.Collections
open PTSV
open PTSV.Global
open PTSV.Problems.QuantitativeProblem
open Utils

// Define a function to construct a message to print
let from whom =
    sprintf "from %s" whom

let mutable filePath = []
let mutable inTpMode = true
let mutable tpSpecified = false
let mutable ettSpecified = false

let printMenu () =
    printfn "usage: ./PTSV [-f] <file path>"
    printfn "options:"
    printfn "-d / -debug: printing various debugging information"
    printfn "-tp: to config what to analyse for termination probability"
    printfn "-ett: to config what to anlyse for expected termination time"
    printfn "-approx: to approximate the value"
    printfn "-qual: to compute qualitative results (AST / PAST)"
    printfn "-iter: to approximate the value by iteration"
    printfn "-bisec: to approximate the value by bisection (via Z3)"
    printfn "-min_diff NUMBER: specify iteration minimum difference as the iteration convergence criterion (by default 1e-6)"
    printfn "-accuracy NUMBER: specify bisection accuracy (by default 1e-6)"
    printfn "-max_iter_round NUMBER: specify maximum iteration rounds (by default infty)"
    printfn "-t <number>: setting time out, in milliseconds"
    printfn "[-D] NAME=NUMBER: to specify parse bindings (as additional `let` expressions)"
    printfn "-s: silent mode"
    printfn "-a: test all information"
    printfn "-no_expr: do not print the expressions and equation systems"
    printfn "-stack SIZE: specify the stack size to avoid the Stack Overflow problem"
    printfn "-enum_string [NUM]: to specify how many strings to enumerate when in converting to MCFG mode"
    printfn "-report_stuck: report the configurations that may involve yet will get stuck"
    printfn "-k / -check_k: check whether the declared `k` is correct (HIGH COST)"

let runAccordingToArgConfig () =
    match filePath with
    | [] -> printMenu ()
    | modelPath ->
        // re-assign the value printing stuff
        numericValuePrint <- (fun (obj : obj) ->
            match obj with
            | :? TimeSpan as time ->
                if Flags.DISPLAY_FULL_TIME then time.ToString ()
                else time.TotalSeconds.ToString $"f{Flags.DISPLAY_POSITION}" + "s"
            | :? NumericType as num ->
                if Flags.DISPLAY_RATIONAL then num.ToString ()
                else num.ToString $"f{Flags.DISPLAY_POSITION}"
            | :? Double as d -> d.ToString $"f{Flags.DISPLAY_POSITION}"
            | :? uint | :? uint64 | :? uint8 | :? uint16 as d -> String.filter Char.IsNumber (d.ToString ())
            | _ -> failwith $"Not Supported Numeric Format of Type: \"{obj.GetType().FullName}\"")
        
        let filePaths = List.rev modelPath in
        let run () =
            // do not catch the problem if it is inner debug
            if Flags.INNER_DEBUG then Run.runFiles filePaths else
            try Run.runFiles filePaths
            with
            | :? TimeoutException -> eprintfn "Timeout."
            | e ->
                eprintfn $"{e.Message}"
                if Flags.INNER_DEBUG then
                    eprintfn $"{e.StackTrace}"
        in
        match Flags.STACK_SIZE with
        | Some size -> (Thread((fun () -> run ()), size)).Start ()
        | None -> run ()
        
//        let probFunc =
//            match problemConfig with
//            | PTApproximation method ->
//                let internalFunc =
//                    match method with
//                    | PARunByNLSat ->
//                        ApproximationProblem.approximateByQuantitativeNLSat Flags.APPROX_ACCURACY
//                    | PARunByIterating ->
//                        ApproximationProblem.approximateByIteration
//                            Flags.MAX_ITER_ROUND
//                            Flags.APPROX_MIN_DIFF
//                    | PARunByREDUCE ->
//                        ApproximationProblem.approximateByQualitativeREDUCE
//                            External.REDUCE_PATH
//                            Flags.APPROX_ACCURACY
//                ApproximationProblem.approximationWrapperFunc internalFunc
//            | PTQualitative method ->
//                let internalFunc =
//                    match method with
//                    | PQlRunByNLSatQuantitative ->
//                        QualitativeProblem.qualitativeByQuantitative
//                            quantitativeByNLSat
//                    | PQlRunByDirectREDUCE ->
//                        QualitativeProblem.qualitativeByQuantitative
//                            (quantitativeByREDUCE External.REDUCE_PATH)
//                internalFunc
//            | PTQuantitative (method, op, num) ->
//                let internalFunc =
//                    match method with
//                    | PQnRunByNLSat ->
//                        quantitativeByNLSat
//                    | PQnRunByREDUCE ->
//                        quantitativeByREDUCE External.REDUCE_PATH
//                quantitativeWrapperFunc (internalFunc op num)
//        in 
//        Run.printRunResult (Run.runFromFile modelPath probFunc)

let setFilePath fp =
//    (if Option.isSome filePath then failwith "Multiple files.");
    filePath <- fp :: filePath

let rec argumentAnalysis argv =
    let isInSet (tarSet : HashSet<string>) mustWithTilde (str : string) =
        if str.Length = 0 then false
        elif mustWithTilde && str[0] <> '-' then false
        else
            let str =
                if str[0] = '-' then
                    str.Substring 1
                else str
            tarSet.Contains (str.ToLower ())
    let isApprox =
        let approxSet = HashSet ["approximation"; "approx"; "app"]
        isInSet approxSet
    let isQualitative =
        let qualSet = HashSet ["qualitative"; "qual"; "quality"]
        isInSet qualSet
    let isQuantitative =
        let quanSet = HashSet ["quantitative"; "quan"; "quantity"]
        isInSet quanSet
//    let isMethodSpecification =
//        let methodSet = HashSet ["iter"; "iteration"; "iterating"; "nlsat"; "z3"; "bisec"; "bisection"]
//        isInSet methodSet
//    if Flags.USER_SPECIFY_SIMPLIFY then Flags.SIMPLIFY <- true
//    let methodSpecification (commandStr : string) =
//        match commandStr with
//        | "iter" | "iteration" | "iterating" ->
//            problemConfig <- PTApproximation PARunByIterating
//        | "bisec" | "bisection" ->
//            problemConfig <- PTApproximation PARunByNLSat
//        | "nlsat" | "z3" ->
//            match problemConfig with
//            | PTApproximation _ ->
//                problemConfig <- PTApproximation PARunByNLSat
//            | PTQualitative _ ->
//                problemConfig <- PTQualitative PQlRunByNLSatQuantitative
//            | PTQuantitative (_, qt, num) ->
//                problemConfig <- PTQuantitative (PQnRunByNLSat, qt, num)
//        | _ -> failwith "INTERNAL: Impossible."
    match argv with
    | [] -> runAccordingToArgConfig ()
    | ("-d" | "-debug") :: l ->
        Flags.DEBUG <- true;
        argumentAnalysis l
    | "-f" :: fp :: l ->
        setFilePath fp;
        argumentAnalysis l
    | approx :: l when isApprox true approx ->
        if inTpMode then
            Flags.TP_APPROXIMATION <- true
        else
            Flags.ETT_APPROXIMATION <- true
        argumentAnalysis l
    | qual :: l when isQualitative true qual ->
        if inTpMode then
            Flags.TP_QUALITATIVE <- true
        else
            Flags.ETT_QUALITATIVE <- true
        argumentAnalysis l
    | ("-iter" | "-iteration" | "-iterating") :: l ->
        if inTpMode then
            Flags.TP_APPROX_BY_BISECTION <- false
        else
            Flags.ETT_APPROX_BY_BISECTION <- false;
        argumentAnalysis l
    | ("-bisec" | "-bisection") :: l ->
        if inTpMode then
            Flags.TP_APPROX_BY_BISECTION <- true
        else
            Flags.ETT_APPROX_BY_BISECTION <- true;
        argumentAnalysis l
    | ("-b" | "-both") :: l ->
        if inTpMode then Flags.TP_RUN_BOTH_ITER_AND_BISEC <- true
        else Flags.ETT_RUN_BOTH_ITER_AND_BISEC <- true;
        argumentAnalysis l
    | ("-a" | "-all") :: l ->
        tpSpecified <- true;
        ettSpecified <- true;
        Flags.TP_QUALITATIVE <- true;
        Flags.TP_APPROXIMATION <- true;
        Flags.ETT_QUALITATIVE <- true;
        Flags.CHECK_PAST <- true;
        Flags.ETT_APPROXIMATION <- true;
        Flags.TP_RUN_BOTH_ITER_AND_BISEC <- true;
        Flags.ETT_RUN_BOTH_ITER_AND_BISEC <- true;
        argumentAnalysis l
    | "-display" :: mode :: l ->
        match mode with
        | "rational" -> Flags.DISPLAY_RATIONAL <- true
        | "full_time" | "FullTime" | "fulltime" -> Flags.DISPLAY_FULL_TIME <- true
        | mode when mode.StartsWith "f" ->
            let toParse = ref $ UInt32 () in
            if UInt32.TryParse(mode[1..], toParse) then Flags.DISPLAY_POSITION <- int $ toParse.Value
            else errPrint $"Unknown Display Mode: \"{mode}\"."
        | _ -> errPrint $"Unknown Display Mode: \"{mode}\".";
        argumentAnalysis l
//    | "-p" :: quan :: op :: number :: l when isQuantitative false quan ->
//        try
//            problemConfig <-
//                PTQuantitative
//                    (PQnRunByNLSat,
//                     QueryType.Parse op,
//                     NumericType.Parse number)
//        with
//        | e ->
//            eprintfn
//                $"Warning: {e.Message}\nHint: for quantitative problem, comparator and number should be provided."
//        argumentAnalysis l
    | "-tp" :: l ->
        inTpMode <- true
        if not tpSpecified then
            Flags.TP_APPROXIMATION <- false
            Flags.TP_QUALITATIVE <- false
            Flags.CHECK_PAST <- false
        tpSpecified <- true
        if not ettSpecified then
            Flags.ETT_APPROXIMATION <- false
            Flags.ETT_QUALITATIVE <- false
        argumentAnalysis l
    | "-ett" :: l ->
        inTpMode <- false
        if not ettSpecified then
            Flags.ETT_APPROXIMATION <- false
            Flags.ETT_QUALITATIVE <- false
        ettSpecified <- true
        if not tpSpecified then
            Flags.TP_APPROXIMATION <- false
            Flags.TP_QUALITATIVE <- false
            Flags.CHECK_PAST <- false
        argumentAnalysis l
    | quan :: op :: number :: l when isQuantitative true quan ->
        try
            if inTpMode then
                Flags.TP_QUANTITATIVE_INQUIRY <-
                    Some ((QueryType.Parse op).ToString (), NumericType.Parse number)
            else
//                Flags.ETT_QUANTITATIVE_INQUIRY <-
//                    Some ((QueryType.Parse op).ToString (), NumericType.Parse number)
                printfn "Warning: Do no support quantitative inquiry for ETT."
        with
        | e ->
            eprintfn
                $"Warning: {e.Message}\nHint: for quantitative problem, comparator and number should be provided."
        argumentAnalysis l
//    | "-p" :: _ :: l ->
//        eprintfn "Warning: no such kind of problem."
//        argumentAnalysis l
//    | "-m" :: method :: l when isMethodSpecification false method ->
//        let method =
//            if method.[0] = '-' then
//                method.Substring 1
//            else method
//        methodSpecification (method.ToLower ())
//        argumentAnalysis l
//    | method :: l when isMethodSpecification true method ->
//        let method = method.Substring 1
//        methodSpecification (method.ToLower ())
//        argumentAnalysis l
//    | "-m" :: _ :: l ->
//        eprintfn "Warning: no such method."
//        argumentAnalysis l
    | "-min_diff" :: number :: l ->
        Flags.APPROX_MIN_DIFF <- NumericType.Parse number
        argumentAnalysis l
    | ("-max_iter_round" | "-max_iter" | "-max_round") :: number :: l ->
        Flags.MAX_ITER_ROUND <- Some (uint64 (Double.Parse number))
        argumentAnalysis l
//    | "-ns" :: l ->
//        Flags.SIMPLIFY <- false
//        argumentAnalysis l
    | "-report_stuck" :: l ->
        Flags.REPORT_STUCK <- true
        argumentAnalysis l
    | ("-accuracy" | "-acc") :: num :: l ->
        Flags.APPROX_ACCURACY <- NumericType.Parse num
        argumentAnalysis l
    | "-t" :: num :: l ->
        let rawNum = Double.Parse num
        Flags.CORE_TIME_OUT <- Some (TimeSpan.FromMilliseconds rawNum)
        argumentAnalysis l
//    | "-ld" :: ldpath :: l ->
//        External.LD_LIBRARY_PATH <- ldpath
//        argumentAnalysis l
//    | "-max_var" :: num :: l ->
//        Flags.MAXIMUM_ALLOWED_VARIABLE_AMOUNT <- UInt64.Parse num
//        argumentAnalysis l
    | "-inner_debug" :: l ->
        // a command not displayed in menu
        Flags.INNER_DEBUG <- true
        Flags.DEBUG <- true
        argumentAnalysis l
    | "-no_expr" :: l ->
        Flags.NOT_PRINT_EQ_SYS <- true;
        argumentAnalysis l
    | "-already_normalised" :: l ->
        Flags.KPTSA_NORMALISED <- true
        argumentAnalysis l
    | ("-enum_string" | "-enum_strings") :: num :: l ->
        let value, l =
            try int (UInt32.Parse num), l
            with | _ -> 10, num :: l
        in
        Flags.ENUM_STRING <- Some value 
        argumentAnalysis l
    | ["-enum_string"] | ["-enum_strings"] ->
        Flags.ENUM_STRING <- Some 10
        argumentAnalysis []
    | ("-k" | "-check_k") :: l ->
        Flags.CHECK_K <- true
        argumentAnalysis l
    | "-no_print_eq_sys" :: l ->
        Flags.NOT_PRINT_EQ_SYS <- true
        argumentAnalysis l
    | "-D" :: def :: l ->
        let ss = def.Split("=")
        if ss.Length = 2 then
            Flags.PRELOAD_BINDINGS <- Map.add ss[0] (NumericType.Parse ss[1]) Flags.PRELOAD_BINDINGS
        else printfn "Warning: not a valid variable def, nothing is added to binding."
        argumentAnalysis l
    | "-I_know_there_is_value_for_ett" :: l ->
        Flags.EXTERNAL_ETT_QUALITATIVE_CONFIRM <- true
        Flags.ETT_QUALITATIVE <- false
        argumentAnalysis l
    | "-bfs" :: l ->
        Flags.BUILD_BFS <- true
        argumentAnalysis l
    | ("-stack" | "-stack_size") :: num :: l ->
        try Flags.STACK_SIZE <- Some (int $ UInt64.Parse num)
        with | :? FormatException -> printfn $"Warning: Unrecognised stack size \"{num}\"."
        argumentAnalysis l
    | "-no_reuse" :: l ->
        Flags.ETT_REUSE_TP_RESULT <- false
        argumentAnalysis l
    | ("-premo_path"
            | "-premo_jar"
            | "-premo_jar_path") :: path :: l ->
        Flags.PREMO_JAR_PATH <- path
        argumentAnalysis l
    | ("-premo"
            | "-PReMo"
            | "-Premo"
            | "-run_by_premo"
            | "-iterate_by_premo"
            | "-iter_by_premo") :: l ->
        Flags.ITER_BY_PREMO <- true
        argumentAnalysis l
    | "-premo_arg" :: arg :: l ->
        Flags.PREMO_ADDITIONAL_ARGUMENTS <- arg :: Flags.PREMO_ADDITIONAL_ARGUMENTS
        argumentAnalysis l
    | ("-s" | "-silent" | "-silence" | "-silent_mode" | "-silence_mode") :: l ->
        Flags.SILENT_MODE <- true;
        argumentAnalysis l
    | str :: l ->
        if str.Contains("=") then
            let ss = str.Split("=")
            if ss.Length = 2 then
                Flags.PRELOAD_BINDINGS <- Map.add ss[0] (NumericType.Parse ss[1]) Flags.PRELOAD_BINDINGS
            else setFilePath str
        else
            setFilePath str
        argumentAnalysis l

[<EntryPoint>]
let main argv =
    // run some of the auto generations
//    Flags.DEBUG <- true
    
//    [
//        "0.0123"
//        "11.005"
//        "11.995"
//    ]
//    |> List.map (NumericType.Parse >> fun x -> x.ToString("f2"))
//    |> String.concat "\n"
//    |> println
    
//    
//    match argv[0] with
//    | "0" ->
//        Run.runSeries {
//            series = [| 1..200 |]
//            rptsaDefProd = (fun x -> "let p = 1/2\n" +
//                                     genKAgreementWithShortcut ShortcutTermination x)
//            logDir = "../../../test_logs"
//            exampleName = "k-agreement-shortcut-termination"
//        }
//    | "1" ->
//        Run.runSeries {
//            series = [| 1..200 |]
//            rptsaDefProd = (fun x -> "let p = 1/2\n" +
//                                     genKAgreementWithShortcut ShortcutDivergence x)
//            logDir = "../../../test_logs"
//            exampleName = "k-agreement-shortcut-divergence"
//        }
//    | "2" -> 
//        Run.runSeries {
//            series = [| 1..200 |]
//            rptsaDefProd = (fun x -> "let pA = 1/3\nlet pB = 1/3\nlet pEnd = 1/3\n" +
//                                     genNCopyWithShortcut ShortcutTermination x)
//            logDir = "../../../test_logs"
//            exampleName = "n-COPY-shortcut-termination"
//        }
//    | "3" ->
//        Run.runSeries {
//            series = [| 1..200 |]
//            rptsaDefProd = (fun x -> "let pA = 1/3\nlet pB = 1/3\nlet pEnd = 1/3\n" +
//                                     genNCopyWithShortcut ShortcutDivergence x)
//            logDir = "../../../test_logs"
//            exampleName = "n-COPY-shortcut-divergence"
//        }
//    | "4" ->
//        Run.runSeries {
//            series = [| 1..200 |]
//            rptsaDefProd = (fun x -> "let p = 1/2\n" +
//                                     genKCrossDependenciesWithShortcut ShortcutTermination x)
//            logDir = "../../../test_logs"
//            exampleName = "k-cross-dependencies-termination"
//        }
//    | "5" ->
//        Run.runSeries {
//            series = [| 1..200 |]
//            rptsaDefProd = (fun x -> "let p = 1/2\n" +
//                                     genKCrossDependenciesWithShortcut ShortcutDivergence x)
//            logDir = "../../../test_logs"
//            exampleName = "k-cross-dependencies-divergence"
//        }
//    | "6" ->
//        Run.runSeries {
//            series = [| 1..200 |]
//            rptsaDefProd = (fun x -> "let p = 1/2\n" +
//                                     genKDyckLanguagesWithRandomUp x)
//            logDir = "../../../test_logs"
//            exampleName = "k-Dyck-Language-random-ups"
//        }
//    | _ -> ()
    
//    Flags.INNER_DEBUG <- true;
//    Flags.DEBUG <- true;
    
//    match argv[0] with
//    | "0" -> Run.runSeries {
//            series = [| 2; 3; 10; |]
//            rptsaDefProd = (fun x -> "let pA = 1/3\nlet pB = 1/3\nlet pEnd = 1/3\n" +
//                                     genNCopyWithVariantShortcut ShortcutTermination x)
//            logDir = "../../../test_logs"
//            exampleName = "n-COPY-variant-termination-collect"
//        }
//    
//    | "1" -> Run.runSeries {
//            series = [| 10; 20; 50; 100; 200; 500; 1000 |]
//            rptsaDefProd = (fun x -> "let pA = 1/3\nlet pB = 1/3\nlet pEnd = 1/3\n" +
//                                     genNCopyWithVariantShortcut ShortcutDivergence x)
//            logDir = "../../../test_logs"
//            exampleName = "n-COPY-variant-divergence-collect"
//        }
//    
//    | "3" -> Run.runSeries {
//            series = [| 10; 20; 50; 100; 200; 500; 1000 |]
//            rptsaDefProd = (fun x -> "let pA = 1/3\nlet pB = 1/3\nlet pEnd = 1/3\n" +
//                                     genNCopyWithBottomVariantShortcut ShortcutDivergence x)
//            logDir = "../../../test_logs"
//            exampleName = "n-COPY-bottom-variant-divergence-collect"
//        }
//    
//    | "4" -> Run.runSeries {
//            series = [| 10; 20; 50; 100; 200; 500; 1000 |]
//            rptsaDefProd = (fun x -> "let pA = 1/3\nlet pB = 1/3\nlet pEnd = 1/3\n" +
//                                     genNCopyWithBottomVariantShortcut ShortcutTermination x)
//            logDir = "../../../test_logs"
//            exampleName = "n-COPY-bottom-variant-termination-collect"
//        }
//    
//    | "5" ->
//        Run.runConvertDirectoryJsonTableFilesToLaTeXTableFiles "../../../test_logs"
//        
//    | "6" ->
////        let thread = Thread ((fun () -> 
//        Run.runSeries {
//            series = [| 10; 20; 50; 100; 200; 500; 1000 |]
//            rptsaDefProd = (fun x -> "let p = 1/2\n" +
//                                     genKDyckLanguagesWithRandomUp x)
//            logDir = "../../../test_logs"
//            exampleName = "n-Dyck-Language-random-up-collect"
//        }
////        ), 104857600) in
////        thread.Start ()
//    
//    | "7" ->
////        let thread = Thread ((fun () ->
//            Run.runSeries {
//                series = [| 10; 20; 50; 100; 200; 500; 1000 |]
//                rptsaDefProd = (fun x -> "let p = 1/2\n" +
//                                         genKDyckLanguagesWithShortcut ShortcutTermination x)
//                logDir = "../../../test_logs"
//                exampleName = "n-Dyck-language-shortcut-termination-collect"
//            }
////        ), 104857600) in
////        thread.Start ()
//    
//    | "8" -> 
////        let thread = Thread ((fun () ->
//            Run.runSeries {
//                series = [| 2; |]
//                rptsaDefProd = (fun x -> "let p = 1/2\n" +
//                                         genKDyckLanguagesWithShortcut ShortcutDivergence x)
//                logDir = "../../../test_logs"
//                exampleName = "n-Dyck-language-shortcut-divergence-collect"
//            }
////        ), 104857600) in
////        thread.Start ()
//    
//    | _ -> ()
    
//    let query =
//        [
//            "x1 = 0.5 + 0.333333333 * x1 * x2"
//            "x2 = 0.2 + 0.1 * x1 * x2"
//        ]
//        |> String.concat "\n"
//    in
    
//    printfn $"{Run.runOnlyTerminationProbability $ genFullCoupon 500}"

//    let fullRdWalk =
//    [ 150; 200; 250 ]
//    |> List.map (genToolPrspeed >> Run.runOnlyTerminationProbability >> toString)
//    |> String.concat "\n\n"
//    |> println
//    in
    
//    let genCmpResult (name : string) generator paras =
//        Run.runGeneratedExamples
//            (flip Run.cmpUsualWithPReMo true)
//            $"{name}Cmp"
//            generator
//            paras
//    in
    
//    Flags.TP_APPROX_BY_BISECTION <- false;
//    Flags.CORE_TIME_OUT <- Some $ TimeSpan.Parse "10:0:0"
//    Flags.PREMO_ADDITIONAL_ARGUMENTS <- [
//        "--eps=1e-100"
//        "--maxSteps=0"
//        "--solver=DN"
//    ]
    
    // to reach the same precision as PReMo
//    Run.runSequentialPrecisionTest (genXEqHalfPlusHalfDouble ())
    
//    [1..20]
//    |> List.map (fun i -> $"1e-{i}")
//    |> Run.runPrecisionTestWithPReMo (genXEqHalfPlusHalfDouble 2)
//    |> List.map toString
//    |> String.concat "\n"
//    |> println
    
//    Run.runCollectWangExampleData [s

//    Run.runGeneratedExamples
//        Run.runOnlyTerminationProbability
//        "1DWalk"
//        gen1DWalk
//        [ 10; 50; 100 ]
//    |> println
    
//    Flags.PREMO_ADDITIONAL_ARGUMENTS <- [
//        "--eps=1e-100"
//        // Dense Newton's method -- the Sparse Newton's method will report error
//        "--solver=DN"
//    ]
//    genCmpResult "ComplexEqSys" genPReMoCmpHigherDimensional [3]
//    |> println
    
//    [
//        genCmpResult "FullRace"     genFullRace     [  40;  35; 45  ]
//        genCmpResult "RdWalk"       genFullRdWalk   [ 400; 500; 600 ]
//        genCmpResult "Coupon"       genFullCoupon   [ 100; 300; 500 ]
//        genCmpResult "RdAdder"      genRdAdder      [ 225; 250; 275 ]
//        genCmpResult "ToolPrspeed"  genToolPrspeed  [ 150; 200; 250 ]
//    ]
//    |> String.concat "\n--------------------------------------\n"
//    |> println
    
//    match Utils.callPremoEquationEngine Flags.PREMO_JAR_PATH query Flags.PREMO_ADDITIONAL_ARGUMENTS with 
//    | Ok result -> printfn $"{result}"
//    | Error err ->   eprintfn $"{err}"
    
//    System.IO.File.WriteAllText("../../../examples/k-PTSA/example Amber nested loops.txt",
//                                genAmber_NestedLoops ())
//    Flags.SIMPLIFY <- false
//    Flags.USER_SPECIFY_SIMPLIFY <- false
//    Flags.ITER_BY_PREMO <- true;
    
//    Run.runAutoCollectPaperExamplesLaTeXTable ()
    
//    Run.runAutoCollectPaperExamplesLaTeXTable ()
    
    // real execution of program
//    try
    argumentAnalysis (List.ofArray argv)
//    with
//    | :? TimeoutException -> eprintfn "Timeout."
//    | e ->
//        eprintfn $"{e.Message}"
//        if Flags.INNER_DEBUG then
//            eprintfn $"{e.StackTrace}"
    
    0 // return an integer exit code