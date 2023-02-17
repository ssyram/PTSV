module PTSV.Simplification

// this module is for expression simplification

open System.Collections.Generic
open Global
open System
open Core
open Utils

// there are several kinds of simplification to perform to match some specific kinds
// this file consists of several parts:
// 1. the kind judgements
// 2. the helping functions
// 3. the operation functions for LFP or GFP
// 
// there should be promises: the index of the original equation system is not changed --
// ONLY REMOVE NO REINDEXING

// ---------------------------------- Kind Judging -----------------------------------
// kind 1:
//     v = c
//     v = c * v + c' -> v = c' / (1 - c)
//     v = c * v -> v = 0
// kind 2:
//     v = c * v'
// kind 3:
//     variables that has exactly the same RHS
// kind 4:

//let private isKind1 (i, expr) =
//    match expr with
//    | EConst _ -> true
//    | EVar vi | EMul (EConst _, EVar vi) ->
//        if vi = i then
//            recordInfo i (EConst NUMERIC_ZERO)
//            false
//        else true
//    // c != 0, for it's optimised
//    // c != 1, for it violates restriction for p
//    | EAdd (EConst c', EMul (EConst c, EVar vi))
//        | EAdd (EMul (EConst c, EVar vi), EConst c') ->
//        if vi = i then
//            recordInfo i (EConst (c' / (NUMERIC_ONE - c)))
//            false
//        else true
//    | _ -> true
    


/// promise not to change the original equation system index, only removing, not changing
/// 
/// replace the variables that:
/// kind 1:
///     v = c
///     v = c * v + c' -> v = c' / (1 - c)
///     v = c * v -> v = 0
/// kind 2:
///     v = c * v'
/// kind 3:
///     variables that has exactly the same RHS
/// kind 4:
///     erase by iteration
let gfpSimplifyExprSystem lfp (es : (int * Expr) list) =
    let mutable ret = es
    let mutable changed = true
    let mutable totallyErasedVar = 0
    
    
    /// filters use "recordInfo" function to record new information
    /// v = c | v = c * v + c' | v = c * v | v = v
    let firstKindFilter recordInfo (i, e) =
        match e with
        | EConst _ ->
            recordInfo i e
            false
        | EVar vi ->
            if vi = i then
                recordInfo i (EConst $ if lfp then NUMERIC_ZERO else NUMERIC_ONE)
                false
            else true
        | EMul (EConst _, EVar vi) ->
            if vi = i then
                recordInfo i (EConst NUMERIC_ZERO)
                false
            else true
        // c != 0, for it's optimised
        // c != 1, for it violates restriction for p
        | EAdd (EConst c', EMul (EConst c, EVar vi))
            | EAdd (EMul (EConst c, EVar vi), EConst c') ->
            if vi = i then
                recordInfo i (EConst (c' / (NUMERIC_ONE - c)))
                false
            else true
        | _ -> true
    
    /// v = v'
    let secondKindFilter recordInfo (i, e) =
        match e with
        | EVar vId ->
            recordInfo i vId NUMERIC_ONE
            false
        | EMul (EConst c, EVar vId) ->
            recordInfo i vId c
            false
        | _ -> true
    
    let mutable round = 0
        
    let execute () =
        while changed do
            changed <- false
            round <- round + 1
            
            if Flags.DEBUG then
                printfn $"Conduct round {round} simplification..."
            
            /// essentially, simplification here means to exclude out trivial variables
            /// 
            /// there are four steps in each filter function
            /// 1. filter out all suitable patterns for all variables, record the target to replace, except var 0.
            /// 2. tackle var 0, not recording change
            /// 3. judge if there are changes, if yes, get to 4, otherwise, get out
            /// 4. conduct variable replacement
            ///
            /// parameters:
            ///     filterFunc should return if this variable match corresponding pattern, not including var 0.
            ///     zeroFunc : given the expression of var 0, determine its value explicitly
            ///     changedJudge should return if there are changes
            ///     subsFunc is given a variable, judge if this should be replaced
            let conductFilter filterFunc zeroFunc changedJudge subsFuc =
                let mutable zeroExpr = None
                let trueFilterFunc (i, e) =
                    if i = 0 then
                        zeroExpr <- Some e
                        false
                    else filterFunc (i, e)
                ret <- List.filter trueFilterFunc ret
                match zeroExpr with
                | None -> failwith "INTERNAL: there is no var 0."
                | Some e ->
                    ret <- (0, zeroFunc e) :: ret
                if changedJudge () then
                    changed <- true
                    ret <- List.map (fun (i, e) -> (i, substituteVar subsFuc e)) ret
            
            // filter first kind
            begin
                let mutable firstKindMap = Map.empty
                let recordInfo vId e = firstKindMap <- Map.add vId e firstKindMap
                // given the expression of var 0, determine its value
                let zeroFunc ze =
                    let mutable after = None
                    firstKindFilter (fun _ e -> after <- Some e) (0, ze) |> ignore
                    match after with
                    | None -> ze
                    | Some e -> e
                let changeJudge () = not (Map.isEmpty firstKindMap)
                let subsFunc vId =
                    match Map.tryFind vId firstKindMap with
                    | None -> EVar vId
                    | Some e -> e
                conductFilter (firstKindFilter recordInfo) zeroFunc changeJudge subsFunc
                if Flags.DEBUG then
                    printfn $"There are {firstKindMap.Count} first kind trivial variables filtered out."
                totallyErasedVar <- totallyErasedVar + firstKindMap.Count
            end
            
            // filter second kind
    // ############# Proof of Correctness Done ################
            begin
                let findSets = RatioFindSetManager ()
                // a wrong version -- only RHS substitution is not enough
    //            let recordInfo vo vn =
    //                findSets.newEqRelationDeclare vo vn
    //            let zeroFunc e =
    //                match e with
    //                | EVar vId -> findSets.newEqRelationDeclare 0 vId
    //                | _ -> ()
    //                e
    //            let changedJudge () = not (findSets.isEmpty ())
    //            // this function conduct RHS elimination
    //            conductFilter (secondKindFilter recordInfo) zeroFunc changedJudge subsFunc
                let subsFunc vId =
                    match findSets.tryFindRepresentativeAndRatio vId with
                    | None -> EVar vId
                    | Some (rId, ratio) -> EMul (EConst ratio, EVar rId)
                ret <- List.filter (secondKindFilter findSets.recordNewRatio) ret
                let rec distributeFirstMul c e =
                    let recall = distributeFirstMul c
                    match e with
                    | EAdd (e1, e2) ->
                        EAdd (recall e1, recall e2)
                    | EMinus (e1, e2) ->
                        EMinus (recall e1, recall e2)
                    | _ -> EMul (EConst c, e)
                let iterFunc (i, e) =
                    let lId, preFunc =
                        match findSets.tryFindRepresentativeAndRatio i with
                        | None -> i, id
                        | Some (rId, ratio) ->
                            rId, (distributeFirstMul (NUMERIC_ONE / ratio))
                    (lId, optimiseExpr (preFunc (substituteVar subsFunc e)))
                ret <- List.map iterFunc ret
                changed <- changed || not (findSets.isEmpty ())
                // those totally erased may be mentioned by other places, so we should replace those without head var
                // with 0
                let zeroSet =
                    let allRepresentatives = findSets.getAllRepresentatives ()
                    List.fold
                        (fun s (i, _) -> Set.remove i s)
                        allRepresentatives
                        ret
                // here, there may be no any out-way for var 0, in this case, just let ret = [(0, 0.0)] and return
                if zeroSet.Contains 0 then
                    ret <- [(0, EConst NUMERIC_ZERO)]
                    // no need to further loop, just return
                    changed <- false
                // else if there are some other erased variables, just clear them
                elif not zeroSet.IsEmpty then
                    let subsFunc vId =
                        if zeroSet.Contains vId then EConst NUMERIC_ZERO else EVar vId
                    ret <- List.map (fun (i, e) -> (i, substituteVar subsFunc e)) ret
                
                if Flags.DEBUG then
                    printfn $"There are {findSets.getSize ()} second kind trivial variables filtered out."
                totallyErasedVar <- totallyErasedVar + findSets.getSize ()
            end
            
            // filter third kind -- has exactly the same RHS
            begin
                let mutable replaceMap = Map.empty
                ret <- List.sortBy snd ret
                ret <-
                    List.fold
                        (fun lst (i, e) ->
                            match lst with
                            | [] -> [i, e]
                            | (i', e') :: _ ->
                                if e = e' then
                                    replaceMap <- Map.add i i' replaceMap
                                    changed <- true
                                    lst
                                else (i, e) :: lst)
                        []
                        ret
                // specially treat 0
                match Map.tryFind 0 replaceMap with
                | Some ti ->
                    replaceMap <-
                        Map.map
                            (fun _ rt -> if rt = ti then 0 else rt)
                            replaceMap
                    replaceMap <- Map.add ti 0 (Map.remove 0 replaceMap)
                | None -> ()
                let replaceI i =
                    match Map.tryFind i replaceMap with
                    | Some ni -> ni
                    | None -> i
                let subsFunc vId =
                    EVar (match Map.tryFind vId replaceMap with
                          | Some ti -> ti
                          | None -> vId)
                ret <- List.map (fun (i, e) -> (replaceI i, substituteVar subsFunc e)) ret
                if Flags.DEBUG then
                    printfn $"There are {replaceMap.Count} third kind trivial variables filtered out."
                totallyErasedVar <- totallyErasedVar + replaceMap.Count
            end
            
            ret <- List.map (fun (i, e) -> (i, optimiseExpr e)) ret
            
    execute ()
    
    // filter fourth kind, should only execute once
    // also modify "changed" here, as it determines whether to execute the first to third kind again
    begin
        let nes, remap = reindexedExprSystem ret
        let computeRet values = computeExprList nes values
        let values =
            let initValues =
                List.init ret.Length iterateInitValues
            computeRet initValues
        let finalValues =
            // just need n times, where n is the variable number, do not require value of ret
            fst (List.fold
                     (fun (r, count) _ ->
                        if Flags.INNER_DEBUG then
                            Console.Write $"\rFourth kind filter run for {count} times."
                        (computeRet r, count + 1)) (values, 0) ret)
        let mutable eraseMap = Map.empty
        ret <-
            let ret = List.indexed nes
            let filterFunc ((initVal, finalVal), (i, _)) =
                if finalVal = NUMERIC_ZERO then
                    eraseMap <- Map.add i NUMERIC_ZERO eraseMap
                    false
                elif initVal = finalVal then
                    eraseMap <- Map.add i finalVal eraseMap
                    false
                else true
            let remainRet =
                snd (List.unzip (List.filter filterFunc (List.zip (List.zip values finalValues) ret)))
            changed <- not (Map.isEmpty eraseMap)
            match Map.tryFind 0 eraseMap with
            | Some c ->
                changed <- false
                [0, EConst c]
            | None ->
                let subsFunc vId =
                    match Map.tryFind vId eraseMap with
                    | Some c -> EConst c
                    | None -> EVar vId
                List.map (fun (i, e) -> (i, substituteVar subsFunc e)) remainRet
        printfn ""  // to change line
        if Flags.DEBUG then
            printfn $"There are {eraseMap.Count} fourth kind trivial variables filtered out."
        totallyErasedVar <- totallyErasedVar + eraseMap.Count
        ret <- List.map (fun (i, e) -> (i, optimiseExpr e)) ret
        
        // remap ret
        ret <- List.map (fun (i, e) -> (remap[i], substituteVar (fun i -> EVar remap[i]) e)) ret 
    end
    
    execute ()
    
    // old, wrong version of 2nd kind -- var 0 is not tackled properly
//    /// do the jobs
//    while changed do
//        changed <- false
//        ret <- optimiseExprSystem ret
//        
//        let mutable info = []
//        
//        let filterReplace filter =
//            // use filter, find out info
//            ret <- List.filter
//                (filter (fun ele -> info <- ele :: info))
//                ret
//            // determine if change happen
//            if info <> [] || not (info.Length = 1 && (fst info.[0] = 0)) then changed <- true
//            let vmap = Map.ofList info
//            if Flags.INNER_DEBUG then
//                printfn $"Length of current variables : {ret.Length}"
//                printfn $"Length of variables to replace: {info.Length}"
//            let tf1 vId =
//                match Map.tryFind vId vmap with
//                | None -> EVar vId
//                | Some e -> e
//            // substitute variables
//            ret <- List.map (fun (i', e') -> (i', substituteVar tf1 e')) ret
//        
//        filterReplace firstKindFilter
//        
//        // use union-find set to tackle v = v'
//        let unionFindSet = Utils.FindSetManager []
//        
//        // 0 is not recorded
//        
//        ret <- List.filter (secondKindFilter (fun (i, vId) -> unionFindSet.newEqRelationDeclare i vId)) ret
//        
//        let tf2 vId =
//            match unionFindSet.tryFindRepresentative vId with
//            | None -> EVar vId
//            | Some nvId -> EVar nvId
//        
//        ret <- List.map (fun (i, e) -> (i, substituteVar tf2 e)) ret
//        
//        changed <- changed || (unionFindSet.isEmpty ())
        
        // this may cause problems -- some variables may just be erased
//        filterReplace secondKindFilter
    
    // finally, remove all irrelevant variables from x0
    // firstly collect all relevant variables
    begin
        let relevantVars = HashSet<int> ()
        relevantVars.Add 0 |> ignore
        let riRet, remap = reindexedExprSystem ret
        // collect relevant variable with the current variable Id
        let rec collectRelevantVars vId =
            let rec analyseTerm t =
                match t with
                | EAdd (e1, e2) ->
                    analyseTerm e1
                    analyseTerm e2
                | EMul (e1, e2) ->
                    analyseTerm e1
                    analyseTerm e2
                | EDiv (e1, e2) ->
                    analyseTerm e1
                    analyseTerm e2
                | EMinus (e1, e2) ->
                    analyseTerm e1
                    analyseTerm e2
                | EVar i ->
                    if relevantVars.Add i then collectRelevantVars i
                | EConst _ -> ()
            analyseTerm riRet.[vId]
        collectRelevantVars 0
        let erasedVariables = ret.Length - relevantVars.Count
        ret <-
            List.fold
                (fun rl (vId, rBody) ->
                    if relevantVars.Contains vId then
                        (vId, rBody) :: rl
                    else rl)
                []
                (List.indexed riRet)
        if Flags.DEBUG then
            printfn $"Erased {erasedVariables} Irrelevant Variables."
        totallyErasedVar <- totallyErasedVar + erasedVariables
        
        // remap vars
        ret <- List.map (fun (i, e) -> (remap[i], substituteVar (fun i -> EVar remap[i]) e)) ret
    end
    
    // then remove all irrelevant ones
    printfn $"Totally Erased Variables by Simplification: {totallyErasedVar}."
    
    ret
