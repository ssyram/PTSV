module PTSV.NewEquationBuild

open System.Collections.Generic
open PTSV.MultipleContextFreeGrammar
open PTSV.Utils
open PTSV.Core
open PTSV.Global

//#light "off"
    
/// a simple type alias, stands for `abstract variable`
/// the length of D is saved for shortcut use, because computing that is of linear time complexity
type AbsVar<'q, 'g> = AbsVar of D:'q list * gamma:'g * DLength:int
let private isUp (AbsVar (_, _, len)) = len % 2 = 1

/// the variable mark, throws to tell whether 
type VarMark<'q, 'g when 'q : equality and 'g : equality>(var : AbsVar<'q, 'g>) =
    class
        inherit System.Exception("Variable Mark")
        let (AbsVar (_D, g, _DLength)) = var
        let hashCode = var.GetHashCode ()
        member x.D : 'q list = _D
        member x.gamma : 'g = g
        member x.DLength = _DLength
        member x.hash = hashCode  // compute only once
    end
    
let varMarkHasVar (mark : VarMark<'q, 'g>) (AbsVar (D, g, dl), hashCode) =  // the `hashCode` is for shortcut
    mark.hash = hashCode && mark.DLength = dl && mark.gamma = g && mark.D = D

type TransOp<'q, 'm, 'g, 'sp> =
    | OpTransState of 'q
    | OpTransUp of 'q * 'm * 'g
    | OpTransDown of 'q * 'm
    | OpTransSp of 'sp
    with
    member x.toKPTSATransOp qMap mMap gMap spMap =
        match x with
        | OpTransState q -> TransState $ qMap q
        | OpTransUp (q, m, g) -> TransUp (qMap q, mMap m, gMap g)
        | OpTransDown (q, m) -> TransDown (qMap q, mMap m)
        | OpTransSp sp -> spMap sp
    end

type BuildVarResult =
    | BVRStructuralZero
    /// the variable has been shown to be non-structural-zero
    | BVRNonStructZeroDFS
    /// the variable recursively depends on another variable that depends on it,
    /// should appears in DFS case only
    | BVRRecursiveDFS
    /// the variable not-yet explored,
    /// should explored in BFS case only
    | BVRInQueueBFS
    /// for BFS, even explored cannot determine if it is structurally zero
    | BVRUnknownBFS


type BuildInfo<'q, 'm, 'g, 'acc> when 'g : comparison = 
    { curQ : 'q;
      curM : 'm;
      curGamma : 'g
      depth : uint
      curD : 'q list;
      accInfo : 'acc;
      upMap : Map<'g, 'q list * int> }
    with
        member this.getConfig() = (this.curQ, this.curM, this.curGamma)
        member this.getCurrentD() = this.curD
        member this.getUpMapStream () : seq<AbsVar<'q, 'g>> =
            Seq.map (fun (g, (D, lenD)) -> AbsVar (D, g, lenD)) $ Map.toSeq this.upMap
        member this.updateD D = { this with curD = D }
        member this.updateQ q = { this with curQ = q }
        member this.updateQ_M q m = { this with curQ = q; curM = m }
        member this.nextDepth () = { this with depth = this.depth + 1u }
        member this.updateQ_M_D q m D = { this with curQ = q; curM = m; curD = D }
        member this.getUpD gamma = Option.defaultValue ([], 0) $ Map.tryFind gamma this.upMap
        member this.remapUp g newD = { this with upMap = Map.add g newD this.upMap }
    end
let convertAccInfo info f =
    {
        curQ = info.curQ; 
        accInfo = f info.accInfo
        depth = 0u;
        curM = info.curM; 
        curGamma = info.curGamma; 
        curD = info.curD; 
        upMap = info.upMap; 
    }
    
    
type ReTravelSupportData<'q, 'g> =
    {
        /// keeps those `encountered`, which includes those in `todoList`
        alreadyEncountered : HashSet<AbsVar<'q, 'g>>;
        /// those waiting to be `explored` further
        todoQueue : Queue<AbsVar<'q, 'g>>; 
    }
type BuildVarDFSPkg<'q, 'g> =
    {
        dfsPathSet : HashSet<AbsVar<'q, 'g>>;
        dfsEnvStk : Stack<AbsVar<'q, 'g> * bool>;  // the bool keeps whether it is structurally zero
    }
type BuildVarBFSPkg<'q, 'g> =
    {
        /// the queue to conduct BFS 
        bfsQueue : Queue<AbsVar<'q, 'g>>;
//        bfsEncountered : HashSet<AbsVar<'q, 'g>>;
        mutable bfsCurrentStatus : (AbsVar<'q, 'g> * bool) option;
    }
    

// todo: fix these ugly tricks by making State, LocalMemory and Gamma real types with their own ToString
let printQ q =
    match q :> obj with
    | :? State as q -> printKPTSAState q
    | _ -> toString q
let printM m =
    match m :> obj with
    | :? LocalMemory as m -> printKPTSALocMem m
    | _ -> toString m
let printG g =
    match g :> obj with
    | :? Gamma as g -> printKPTSAGamma g
    | _ -> toString g
    
type BuildVarMode<'q, 'g> =
    | BVMDepthFirst of BuildVarDFSPkg<'q, 'g>
    | BVMBreadthFirst of BuildVarBFSPkg<'q, 'g>
    | BVMReTravel of ReTravelSupportData<'q, 'g>
/// This context is for building the information
/// the result should be stored within it
/// all main logic should be in the algorithm and context is just for operating on objects
///
/// It is the responsibility of special context to keep and compute the return result
type BuildContext<'q, 'm, 'g, 'sp> =
    {
        /// Map<'q * 'm * 'g, IEnumerable<NumericType * TransOp<'q, 'm, 'g, 'sp>>>
        rules : HashMap<'q * 'm * 'g, IEnumerable<NumericType * TransOp<'q, 'm, 'g, 'sp>>>;
        /// Map<'q * 'g, IEnumerable<'q>>
        possibleDownMap : HashMap<'q * 'g, IEnumerable<'q>>;
        k : int;
        m0 : 'm;
        /// Map<Var<'q, 'g>, BuildVarResult>
        cacheResult : HashMap<AbsVar<'q, 'g>, BuildVarResult>;
        kMap : HashMap<'g, int> option;
        /// disable up variable kinds (except for the root one)
        noUpVar : bool;
        /// this set records vacuum `prefix` 
        vacuumTrips : HashSet<AbsVar<'q, 'g>>;
        mutable exploredCounter : uint64;
        
        buildMode : BuildVarMode<'q, 'g>;
    }
    with
        member x.getRules config = flip Option.defaultValue (x.rules.tryFind config) []
        /// seems no need to record here, as it should have been computed and recorded in the usual routine
        member x.recordVacuumVar var =
            if not $ isUp var then x.vacuumTrips.Add var |> ignore
//            if isUp then x.upVacuum.Add (D, g) |> ignore
//            else x.tripsVacuum.Add (D, g) |> ignore
        member x.possibleDownQs _ (q : 'q) (g : 'g) =
            flip Option.defaultValue (x.possibleDownMap.tryFind (q, g)) []
        member x.reTravelTryAddTodo var =
            match x.buildMode with
            | BVMReTravel pkg ->
                if pkg.alreadyEncountered.Add var then
                    pkg.todoQueue.Enqueue var
            | _               -> IMPOSSIBLE ()
        member x.reTravelHasTodo () =
            match x.buildMode with
            | BVMReTravel pkg -> pkg.todoQueue.Count > 0
            | _               -> IMPOSSIBLE ()
        member x.notComputedVacuumVar var =
            match x.cacheResult.tryFind var with
            | Some BVRStructuralZero -> false
            | _                      -> isUp var || not (x.vacuumTrips.Contains var)
        member private x.extractDFSPkg () =
            match x.buildMode with
            | BVMDepthFirst pkg -> (pkg.dfsEnvStk, pkg.dfsPathSet)
            | _ -> IMPOSSIBLE "Not suitable extraction"
        member x.bfsAddTodo var =
            x.cacheResult.add var BVRInQueueBFS;
            match x.buildMode with
            | BVMBreadthFirst pkg -> pkg.bfsQueue.Enqueue var
            | _ -> IMPOSSIBLE "Mode Error: currently should be in BFS mode"
        member x.recordUpdate () =
            match x.buildMode with
            | BVMDepthFirst pkg ->
                let var, _ = pkg.dfsEnvStk.Pop () in
                pkg.dfsEnvStk.Push (var, true)
            | BVMBreadthFirst pkg ->
                // there must be a value here, otherwise, raise exception for debugging
                let var, _ = Option.get pkg.bfsCurrentStatus in
                pkg.bfsCurrentStatus <- Some (var, true)
            | BVMReTravel _ -> ()  // do nothing when re-travelling
//        member x.bfsTryAddTodo var =
//            match x.buildMode with
//            | BVMBreadthFirst pkg ->
//                pkg.bfsEncountered.Contains var
//            undefined ()
        member x.dfsInPathSet var =
            let _, dfsPathSet = x.extractDFSPkg ()
            dfsPathSet.Contains var
        member x.getK (g : 'g) =
            match x.kMap with
            | Some map -> flip Option.defaultValue (map.tryFind g) x.k
            | None     -> x.k
        member x.findCacheResult var = x.cacheResult.tryFind var
        member x.bfsGetNextTodoVar () =
            match x.buildMode with
            | BVMBreadthFirst pkg -> pkg.bfsQueue.Dequeue ()
            | _ -> IMPOSSIBLE ()
        member x.reTravelGetNextTodoVar () =
            match x.buildMode with
            | BVMReTravel pkg -> pkg.todoQueue.Dequeue ()
            | _ -> IMPOSSIBLE ()
        member x.logNewVariableConstruction var =
            checkTimeOut ()
            let (AbsVar (D, g, _len)) = var in
            let var =
                List.map printQ D
                |> String.concat ", "
                |> fun x -> $"{{{printG g}}}[{x}]"
            debugSameLinePrint $
                    $"\rExplored Variable Amount: {x.exploredCounter}, " +
                    $"Exploring Variable: {var}                                  "
            x.exploredCounter <- x.exploredCounter + 1uL;
        /// DON'T FORGET TO ADD PATH SET
        member x.dfsCreateNewVarEnvironment var =
//            match x.buildMode with
//            | BVMDepthFirst pkg -> (pkg.dfsEnvStk, pkg.dfsPathSet)
//            | _ -> IMPOSSIBLE "Not suitable extraction"
            let dfsEnvStk, dfsPathSet = x.extractDFSPkg () in
            if not $ dfsPathSet.Add var then IMPOSSIBLE ();
            dfsEnvStk.Push (var, false);
        member x.bfsHasTodo () =
            match x.buildMode with
            | BVMBreadthFirst pkg -> pkg.bfsQueue.Count > 0
            | _ -> IMPOSSIBLE ()
        member x.bfsRefreshVarEnv var =
            match x.buildMode with
            | BVMBreadthFirst pkg -> pkg.bfsCurrentStatus <- Some (var, false)
            | _ -> IMPOSSIBLE ()
        member x.bfsRecordCurrentVarInfo () =
            match x.buildMode with
            | BVMBreadthFirst pkg ->
                let var, hasUpdate = Option.get pkg.bfsCurrentStatus in
                let result =
                    if hasUpdate
                        then BVRUnknownBFS  // in BFS, it is unknown whether it is structurally zero
                        else BVRStructuralZero
                in
                x.cacheResult.add var result
            | _ -> IMPOSSIBLE ()
        member x.makeNewInfo (AbsVar (D, g, _)) initAcc = 
            match D with
            | q :: D -> 
                { curQ = q;
                  curM = x.m0;
                  curGamma = g;
                  depth = 0u;
                  curD = D;
                  accInfo = initAcc;
                  upMap = Map.empty; }
            | _       -> IMPOSSIBLE ()
        member x.dfsRecordTopVarResultAndBackToOldVar () =
            let dfsEnvStk, dfsPathSet = x.extractDFSPkg () in
            let var, hasUpdate = dfsEnvStk.Pop () in
            dfsPathSet.Remove var |> ignore;
            let topVarRes =
                if hasUpdate
                    then BVRNonStructZeroDFS  // this is definitely non-structural zero
                    else BVRStructuralZero
            in
            x.cacheResult.add var topVarRes; 
            topVarRes
        member x.notOverK lenD g =
            // this is OK for that null is translated to None for option type
            let gk = x.kMap >>= fun map -> map.tryFind g in
            // [q1] should be counted as 1 up, which means odd should be complement to be even then compute k
            (lenD + 1) / 2 <= Option.defaultValue x.k gk
        /// a special optimisation -- no up variables
        member x.okToGoUp () = not x.noUpVar
    end
    
type NotifyUpDownSp<'q, 'm, 'g, 'sp, 'acc> when 'g : comparison =
    interface
        abstract notifyUp :
            ctx:BuildContext<'q, 'm, 'g, 'sp> ->
            info:BuildInfo<'q, 'm, 'g, 'acc> ->
            'q * 'g * 'q option ->  // q X q' / q X \uparrow
            BuildInfo<'q, 'm, 'g, 'acc>
        abstract notifyDown :
            ctx:BuildContext<'q, 'm, 'g, 'sp> ->
            info:BuildInfo<'q, 'm, 'g, 'acc> ->
            BuildInfo<'q, 'm, 'g, 'acc>
    end
    
/// the context that is specially designed for different purposes
type SpecialContext<'q, 'm, 'g, 'sp, 'acc> when 'g : comparison =
    interface
        /// update the accumulated information for this step
        abstract updateStepAccInfo :
            ctx:BuildContext<'q, 'm, 'g, 'sp> -> info:BuildInfo<'q, 'm, 'g, 'acc> ->
                p:NumericType * op:TransOp<'q, 'm, 'g, 'sp> -> BuildInfo<'q, 'm, 'g, 'acc>;
        /// cope with some special operations
        abstract copeSp : ctx:BuildContext<'q, 'm, 'g, 'sp> -> info:BuildInfo<'q, 'm, 'g, 'acc> -> s_op:'sp -> unit;
        // no ned to specify at this point: as they can be done once after all upVars are found
//        /// returns a temporary object, type should then be extracted by converting
//        abstract genFoldUpInit : 
//            ctx:BuildContext<'q, 'm, 'g, 'sp> -> info:BuildInfo<'q, 'm, 'g, 'acc> ->
//                var:AbsVar<'q, 'g> option -> 'foldT;
//        /// to fold the formula results
//        abstract foldFunc : var:AbsVar<'q, 'g> -> tmp:'foldT -> 'foldT;
//        /// this function will be called everytime a new variable is to begin its construction
        abstract signalNewVarConstruction :
            ctx:BuildContext<'q, 'm, 'g, 'sp> -> info:BuildInfo<'q, 'm, 'g, 'acc> ->
                var:AbsVar<'q, 'g> -> unit;
        /// generate the initial accumulative information at the beginning
        abstract genInitAccInfo : ctx:BuildContext<'q, 'm, 'g, 'sp> -> var:AbsVar<'q, 'g> -> 'acc;
        /// notify the special context that the up-dispatch succeeded
        /// and the upVars are given to update the formula of the current variable
        /// NOTE: order information is not guaranteed in the `upVars` and it should be regarded as pure stream
        abstract notifyUpVars :
            ctx:BuildContext<'q, 'm, 'g, 'sp> ->
            info:BuildInfo<'q, 'm, 'g, 'acc> ->
            upVars:seq<AbsVar<'q, 'g>> -> unit; 
        /// build the top variable on the build-stack
        abstract buildTopVarAndBackToOldVar : 
            ctx:BuildContext<'q, 'm, 'g, 'sp> -> info:BuildInfo<'q, 'm, 'g, 'acc> -> unit;
        // the ability to fetch result should be implemented separately
        // also, this is not an essential requirement for the context itself to work
        // this functionality is shifted latter to the `IFetchVariableFormulaSystem` interface below
//        /// extract the equation system from the context
//        abstract getResult : unit -> IEnumerable<'var * RawFormula<'var>>;
    end



/// generalised variable generator, probability type 'p is 'NumericType'
/// rewrite the functions, design a special infrastructure thing, let those unchanged be kept
let rec traverseAndBuild
        (ctx : BuildContext<'q, 'm, 'g, 'sp>)
        (info : BuildInfo<'q, 'm, 'g, 'acc>)
        (sp : SpecialContext<'q, 'm, 'g, 'sp, 'acc>)
        =
    checkTimeOut ();
    let rules = ctx.getRules $ info.getConfig () in
    if Flags.REPORT_STUCK && Seq.isEmpty rules then
        let q, m, g = info.getConfig () in
        let s = (printQ q, printM m, printG g) in
        processPrint $"Found Stuck Configuration: {s}";
    for p, op in rules do
        checkTimeOut ();
        debugSameLinePrint $"\rExploring Depth: {info.depth}";
        let info = info.nextDepth () in
        let nInfo = sp.updateStepAccInfo ctx info (p, op) in
        match op with
        | OpTransState q' -> traverseAndBuild ctx (nInfo.updateQ q') sp
        | OpTransSp spOp -> sp.copeSp ctx nInfo spOp
        | OpTransUp (q, m, g) -> copeWithUp ctx nInfo sp (q, m, g)
        | OpTransDown (q, m) -> copeWithDown ctx nInfo sp (q, m)
    done
    
    
and copeWithUp ctx info sp (q', m', g') = 
    // firstly, try seeing if it can go up and never down
    let D = info.getCurrentD () in
    let g'D, g'lenD = info.getUpD g' in
    let g'var = AbsVar (g'D ++ [q'], g', g'lenD + 1) in  // just for convenience, should not shadow the logic
    if isNullSeq D &&
       ctx.okToGoUp () &&  // whether specified by the user not to compute extra up variable
       ctx.notComputedVacuumVar g'var &&
       // bugfix : here should plus 1 in order to see if the new variable deserves explore
       ctx.notOverK (g'lenD + 1) g' then begin
        let info = if sp :? NotifyUpDownSp<'q,'m,'g,'sp,'acc> then
                       (sp :?> NotifyUpDownSp<'q,'m,'g,'sp,'acc>).notifyUp ctx info (q', g', None)
                   else info in
        let varHash = g'var.GetHashCode () in
        try dispatchUpwardCompute ctx info sp (Some g'var)
        with | :? VarMark<'q, 'g> as e when varMarkHasVar e (g'var, varHash) -> 
            ctx.recordVacuumVar g'var
    end;
    // then, try going up and down again
    tryUpwardDown ctx info sp (q', m', g')
    
    
and tryUpwardDown (ctx : BuildContext<_,_,_,_>) info sp (q', m', g') = 
    for qc in ctx.possibleDownQs info q' g' do
        let g'D, g'lenD = info.getUpD g' in
        let g'newD = g'D ++ [q'; qc] in
        let g'newLenD = g'lenD + 2 in
        let g'var = AbsVar (g'newD, g', g'newLenD) in 
        if ctx.notComputedVacuumVar g'var &&
           ctx.notOverK g'newLenD g' then begin
            let info = if sp :? NotifyUpDownSp<'q,'m,'g,'sp,'acc> then
                           (sp :?> NotifyUpDownSp<'q,'m,'g,'sp,'acc>).notifyUp ctx info (q', g', Some qc)
                       else info in
            let nInfo: BuildInfo<'q,'m,'g,'acc> = info.remapUp g' (g'newD, g'newLenD) in
            let varHash = g'var.GetHashCode () in
            try traverseAndBuild ctx (nInfo.updateQ_M qc m') sp
            with | :? VarMark<'q, 'g> as e when varMarkHasVar e (g'var, varHash) ->
                ctx.recordVacuumVar g'var
        end
    done
    
    
and copeWithDown ctx info sp (q', m') =
    // this notify down may update the accumulated information
    // this is specially designed for the MCFG conversion -- because every down should incur
    // the generation of the next dimension of string
    let notifyDown () =
        if sp :? NotifyUpDownSp<'q,'m,'g,'sp,'acc>
            then (sp :?> NotifyUpDownSp<'q,'m,'g,'sp,'acc>).notifyDown ctx info
            else info in
    match info.getCurrentD () with
    | qd :: qdd :: lst when q' = qd ->  // get down and back up again
//        if isNullSeq lst then sp.signalEndOfDInUp ctx info;
        let info = notifyDown () in
        traverseAndBuild ctx (info.updateQ_M_D qdd m' lst) sp
    | [qd] when q' = qd ->  // final down and never back
        // no need to update info, as there is no further operation on info
        // bugfix : the final down should not notify
//        let info = notifyDown () in
        dispatchUpwardCompute ctx info sp None
//    | [] ->
//        // This is to perform a new down after the up variable.
//        // for DRA MC, it is important to then collect information in this way
//        // but should firstly check if this has been computed
//        sp.signalNewDownD ctx info q'
    | _ -> ()  // otherwise, do nothing
    
    
/// unleash information from the upMap and try building the formulas
and dispatchUpwardCompute ctx info sp (newUpVar : AbsVar<'q, 'g> option) = 
    let foldFunc var tmp =
        match buildVarAndDependentVars_internal ctx sp var with
        | BVRStructuralZero -> raise $ VarMark var 
        | BVRNonStructZeroDFS  // the rest three cases should be the same -- just use the variable itself
            | BVRRecursiveDFS
            | BVRInQueueBFS
            | BVRUnknownBFS -> var :: tmp
    // no need to get sp involved in this process
//                sp.foldFunc var tmp
    in
    let init = []
    // no need to get sp involved in this process
//        sp.genFoldUpInit ctx info newUpVar in
    in
    // conduct the first step computation, because 'g' in 'newUpVar' may not appear in upMap
    // this is because 'D' for this 'g' may of length 1 -- this is the first time up to 'g' and it's not registered
    let init = match newUpVar with Some var -> foldFunc var init | None -> init in
    let ignoreG = newUpVar >>= fun (AbsVar (_, g, _)) -> Some g in
    let foldRes = foldWith (info.getUpMapStream ()) init $ fun (AbsVar (_, g, lenD) as var) tmp -> 
        (if not $ ctx.notOverK lenD g then raise $ VarMark var); 
        if Some g = ignoreG then tmp else foldFunc var tmp in
    sp.notifyUpVars ctx info foldRes; 
    ctx.recordUpdate ()  // to make notify that the current var is not structurally zero
    
/// judge to build the variables in suitable mode
and buildVarAndDependentVars_internal ctx sp var : BuildVarResult =
    match ctx.buildMode with
    | BVMDepthFirst _   -> buildVarAndDependentVars_internal_dfs ctx sp var
    | BVMBreadthFirst _ -> buildVarAndDependentVars_internal_bfs ctx sp var
    | BVMReTravel _     -> buildVarAndDependentVars_internal_rt ctx sp var
    
and private buildVarAndDependentVars_internal_dfs ctx sp var : BuildVarResult =
    if ctx.dfsInPathSet var then BVRRecursiveDFS else
    match ctx.findCacheResult var with
    | Some c -> c
    | None   -> dfsBuildVar ctx sp var
    
and dfsBuildVar ctx sp var =
    ctx.dfsCreateNewVarEnvironment var;
    buildVar ctx sp var;
    ctx.dfsRecordTopVarResultAndBackToOldVar ()
    
/// build the variable, an intermediate function
/// it is the core of various buildVar related functions
and buildVar ctx sp var =
    // logging
    ctx.logNewVariableConstruction var;
    let info = ctx.makeNewInfo var $ sp.genInitAccInfo ctx var in
    sp.signalNewVarConstruction ctx info var;
    // There is no need to judge this at first, as variables with empty `D` are not recorded. 
//    let (AbsVar (D, _, _)) = var in
//    // if the D is completed at first, signal it, which will let Lambda be `1`.
//    if isUp var then match D with [_] -> sp.signalEndOfDInUp ctx info | _ -> (); 
    traverseAndBuild ctx info sp;
    sp.buildTopVarAndBackToOldVar ctx info
    
// the original multiple-functionality function, but it is better to treat them differently
//and buildVarAndDependentVars ctx sp var : BuildVarResult =
//    let buildVar () = let info = ctx.makeNewInfo var $ sp.genInitAccInfo ctx var in
//                      sp.signalNewVarConstruction ctx info var;
//                      // There is no need to judge this at first, as variables with empty `D` are not recorded. 
////                      let (AbsVar (D, _, _)) = var in
////                      // if the D is completed at first, signal it, which will let Lambda be `1`.
////                      if isUp var then match D with [_] -> sp.signalEndOfDInUp ctx info | _ -> (); 
//                      traverseAndBuild ctx info sp;
//                      sp.buildTopVarAndBackToOldVar ctx info in
//                      
//    // the first case -- it is to re-travel
//    if Option.isSome ctx.reTravelPkg then begin
//        let pkg = Option.get ctx.reTravelPkg in
//        // if ctx is at bottom, it means this variable is to be built, so no need to enqueue
//        (if pkg.alreadyEncountered.Add var && not (ctx.isAtBottom ()) then pkg.todoQueue.Enqueue var); 
//        match ctx.findCacheResult var with
//        | None -> failwith $"Encountered Uncomputed Variable of Abstract Type {var} in Re-Travel."
//        | Some c -> (if ctx.isAtBottom () then buildVar ()); c
//    end else
//        
//    // the second case, it is a new travel
//    if ctx.inPathSet var then BVRNormalVariable else
//    match ctx.findCacheResult var with
//    | Some c -> c
//    | None -> begin
//        ctx.createNewVarEnvironment var;
//        buildVar (); 
//        ctx.recordTopVarResultAndBackToOldVar ()
//    end
    
    
/// NEVER CALL THIS FUNCTION OUTSIDE,
/// the internal BFS function, see `buildVarAndDependentVarsInBFS` for the external interface
and private buildVarAndDependentVars_internal_bfs ctx _ var : BuildVarResult =
    match ctx.findCacheResult var with
    | Some c -> c
    | None   -> ctx.bfsAddTodo var; BVRInQueueBFS
    
/// NEVER CALL THIS FUNCTION OUTSIDE,
/// the internal BFS function, see `buildVarAndDependentVarsInBFS` for the external interface
and buildVarAndDependentVars_internal_rt ctx _ var : BuildVarResult =
    ctx.reTravelTryAddTodo var;
    match ctx.findCacheResult var with
    | Some c -> c
    | None   -> IMPOSSIBLE $"The abstract variable {var} should have been explored in re-travel mode."
    
    
    
    
// ---------------------------------------- build var interfaces ---------------------------------------
    
let inline bfsBuildVar 
    (ctx : BuildContext<'q, 'm, 'g, 'sp>)
    (sp : SpecialContext<'q, 'm, 'g, 'sp, 'acc>)
    (var : AbsVar<'q, 'g>) =
    ctx.bfsRefreshVarEnv var;
    buildVar ctx sp var;
    ctx.bfsRecordCurrentVarInfo ()
    
let inline buildVarAndDependentVarsInBFSStyle 
    (ctx : BuildContext<'q, 'm, 'g, 'sp>)
    (sp : SpecialContext<'q, 'm, 'g, 'sp, 'acc>)
    (var : AbsVar<'q, 'g>) : BuildVarResult =
    ctx.bfsAddTodo var;
    while ctx.bfsHasTodo () do
        let var = ctx.bfsGetNextTodoVar () in
        bfsBuildVar ctx sp var done;
    Option.get $ ctx.findCacheResult var
    
let inline reTravelBuildVar
    (ctx : BuildContext<'q, 'm, 'g, 'sp>)
    (sp : SpecialContext<'q, 'm, 'g, 'sp, 'acc>)
    (var : AbsVar<'q, 'g>) = buildVar ctx sp var
    
let inline buildVarAndDependentVarsInDFSStyle
    (ctx : BuildContext<'q, 'm, 'g, 'sp>)
    (sp : SpecialContext<'q, 'm, 'g, 'sp, 'acc>)
    (var : AbsVar<'q, 'g>) : BuildVarResult = dfsBuildVar ctx sp var
    
let inline reTravelBuildVarAndDependentVars 
    (ctx : BuildContext<'q, 'm, 'g, 'sp>)
    (sp : SpecialContext<'q, 'm, 'g, 'sp, 'acc>)
    (var : AbsVar<'q, 'g>) : BuildVarResult =
    ctx.reTravelTryAddTodo var;
    while ctx.reTravelHasTodo () do
        let var = ctx.reTravelGetNextTodoVar () in
        reTravelBuildVar ctx sp var
    done;
    Option.get $ ctx.findCacheResult var
    
/// the external interface of building the variable and its dependent variables
let buildVarAndDependentVars 
    (ctx : BuildContext<'q, 'm, 'g, 'sp>)
    (sp : SpecialContext<'q, 'm, 'g, 'sp, 'acc>)
    (var : AbsVar<'q, 'g>) : BuildVarResult =
    match ctx.buildMode with
    | BVMDepthFirst _ -> buildVarAndDependentVarsInDFSStyle ctx sp var
    | BVMBreadthFirst _ -> buildVarAndDependentVarsInBFSStyle ctx sp var
    | BVMReTravel _ -> reTravelBuildVarAndDependentVars ctx sp var
    
    
// -------------------------------------- end build var interfaces -------------------------------------
    
    
    
// ---------------------------------- Supporting Concrete Definitions ----------------------------------
    
    
type GeneralRPTSA<'q, 'm, 'g, 'sp>
    when 'q : comparison and 'm : comparison and 'g : comparison and 'sp : comparison =
    {
        q0 : 'q;
        m0 : 'm;
        g0 : 'g; 
        k : int; 
        delta : Map<'q * 'm * 'g, (NumericType * TransOp<'q, 'm, 'g, 'sp>) list>;
        kMap : Map<'g, int> option; 
        stateDependencies : Map<'q * 'g, 'q list> option;
        stepCount : Map<'q * 'm * 'g * TransOp<'q, 'm, 'g, 'sp>, NumericType> option; 
    }
    override x.ToString () =
        "{"
        + $"  q0 = {x.q0}\n"
        + $"  m0 = {x.m0}\n"
        + $"  g0 = {x.g0}\n"
        + $"  k = {x.k}\n"
        + $"""  rules = {printFullSeq_full (fun x -> $"{x}") "{" "}" "\n"  $ Map.toSeq x.delta}"""
        + "}"
let generaliseOp (op : TransOp) sp_ise =
    match op with
    | TransState s -> OpTransState s
    | TransUp(q, m, g) -> OpTransUp (q, m, g)
    | TransDown(q, m) -> OpTransDown (q, m)
    | t -> OpTransSp $ sp_ise t
let generaliseRPTSAWithSp (kptsa : KPTSA) (sp_ise : TransOp -> 'sp) =
    let func (s : Map<State * LocalMemory * Gamma * TransOp, NumericType>) =
        foldWith s Map.empty $ fun pair map -> 
            let q, m, g, op = pair.Key in
            Map.add (q, m, g, generaliseOp op sp_ise) pair.Value map in
    {
        k = kptsa.k;
        delta = Map.map (fun _ -> List.map (fun (p, e) -> (p, generaliseOp e sp_ise))) kptsa.delta;
        q0 = 0;
        m0 = 0;
        g0 = 0;  // count from 1 for non-bot gamma
        kMap = kptsa.kMap;
        stateDependencies = kptsa.stateDependencies;
        stepCount = Option.map func kptsa.stepCount; 
    }
    
/// the current implementation is just a very naive one
/// a full implementation involves a relatively complete flow analysis
let computeStateDependencies rptsa = 
    let allQs = HashSet () in
    let gDownsMap = HashMap () in
    // initialise gDownsMap
    forEach (Map.toSeq rptsa.delta) begin fun ((q, _, g), lst) -> 
        allQs.Add q |> ignore;
        forEach lst $ fun (_, op) ->
            match op with
            | OpTransDown (q, _) ->
                let mapper set = let set = match set with
                                           | None -> HashSet ()
                                           | Some set -> set in
                                 set.Add q |> ignore;
                                 Some set in
                HashMap.compute g mapper gDownsMap
            | _ -> ()
    end; 
    let sgMap = HashMap () in
    forEach gDownsMap begin fun (g, ds) -> 
        forEach allQs $ fun q -> sgMap.add (q, g) (ds :> IEnumerable<'q>) end; 
    sgMap
    
// context may be re-use, which is highly useful
let mkCtx noUpVar (rptsa : GeneralRPTSA<'q, 'm, 'g, 'sp>) : BuildContext<'q, 'm, 'g, 'sp> =
    let mapper (lst : 'a list) = lst :> IEnumerable<'a> in
    {
        rules = HashMap.map mapper $ HashMap.fromMap rptsa.delta;  
        possibleDownMap = begin match rptsa.stateDependencies with
                                | Some sd -> HashMap.map (fun (x : 'q list) -> x) $ HashMap.fromMap sd
                                | None -> computeStateDependencies rptsa
                          end;
        k = rptsa.k;
        m0 = rptsa.m0;
        cacheResult = HashMap ();
        kMap = Option.map HashMap.fromMap rptsa.kMap;
        noUpVar = noUpVar;
        vacuumTrips = HashSet ();
        // DFS is the default mode
        buildMode =
            if Flags.BUILD_BFS then BVMBreadthFirst {
                bfsQueue = Queue ();
                bfsCurrentStatus = None
            } else BVMDepthFirst {
                dfsPathSet = HashSet ();
                dfsEnvStk = Stack<AbsVar<'q, 'g> * bool> ();
            };
        exploredCounter = 0uL;
    }





// ---------------------------------- Concrete Special Contexts ----------------------------------


type TerOp = SpTer | SpDiv
/// stands for P[Var]
type RawVar<'q, 'g> =
    /// Ter_D^g
    | VTer of 'q list * 'g
    /// Trips_D^g
    | VTrips of 'q list * 'g
    /// Up_D^g
    | VUp of 'q list * 'g
    override x.ToString () =
        // todo: fix here -- wrap State and Gamma with newtype rather than do this ugly trick
        // to play an ugly trick: to see if the values are corresponding index
        let printDg D g =
            let gs = printG g in
            let ds = List.map printQ D |> String.concat ", " in 
            $"{{({gs})[{ds}]}}"
        in
        match x with
        | VTer (D, g)   -> "Ter"   + printDg D g
        | VTrips (D, g) -> "Trips" + printDg D g
        | VUp (D, g)    -> "Up"    + printDg D g
let toRawVar (AbsVar (D, g, _) as var) upCons =
    (D, g) |> if isUp var then upCons else VTrips
/// the real variable to be used in the formulas, a variable is a raw variable with a wrapper
type Variable<'q, 'g> =
    /// P[-]
    | PVCProb of RawVar<'q, 'g>
    /// E[-]
    | PVCExp of RawVar<'q, 'g>
    override x.ToString () =
        match x with
        | PVCProb var -> $"Prob[{var}]"
        | PVCExp var  -> $"Exp[{var}]"

type IFetchVariableFormulaSystem<'q, 'g> =
    interface
        abstract getResult : unit -> (Variable<'q, 'g> * RawFormula<Variable<'q, 'g>>) list
    end

let updateStkWithNewF (stk : Stack<Variable<'q, 'g> * RawFormula<Variable<'q, 'g>>>) f func =
    let var, pf = stk.Pop () in
    let pf = optimiseFormula pf in
    stk.Push (var, func pf f)
    
let terSpCope sp ctx info = function
    | SpDiv -> ()
    | SpTer -> if isNullSeq info.curD then dispatchUpwardCompute ctx info sp None

/// data of termination probability computation
type TerProbCtx<'q, 'm, 'g>
    when 'g : comparison and 'q : comparison
    () =
    class
    let formulaStk : Stack<Variable<'q, 'g> * RawFormula<Variable<'q, 'g>>> =
        Stack<Variable<'q, 'g> * RawFormula<Variable<'q, 'g>>> (); 
    let mutable eqSys : (Variable<'q, 'g> * RawFormula<Variable<'q, 'g>>) list = [];
    member this.getResult () = eqSys
    interface IFetchVariableFormulaSystem<'q, 'g> with
        member this.getResult () = eqSys
    end
    interface SpecialContext<'q, 'm, 'g, TerOp, NumericType> with
        member this.buildTopVarAndBackToOldVar _ _ = let var, pf = formulaStk.Pop () in
                                                     let pf = optimiseFormula pf in
                                                     eqSys <- (var, pf) :: eqSys
        member this.copeSp ctx info sop = terSpCope this ctx info sop
//        member this.foldFunc var f = f * (FVar $ PVCProb (toRawVar var VTer))
//        member this.genFoldUpInit _ info _ = FConst info.accInfo
        member this.genInitAccInfo _ _ = NUMERIC_ONE
//        member this.getResult () = eqSys
        member this.signalNewVarConstruction _ _ var =
            formulaStk.Push (PVCProb $ toRawVar var VTer, FConst NUMERIC_ZERO)
        member this.updateStepAccInfo _ info (p, _) = { info with accInfo = p * info.accInfo }
        member this.notifyUpVars _ info involvedVars =
            let f =
                Seq.fold
                    (fun f var -> f * (FVar $ PVCProb (toRawVar var VTer)))
                    (FConst info.accInfo)
                    involvedVars
            in
            updateStkWithNewF formulaStk f (+)
    end
    end



(* Implementation Note on Expected Termination Time Formula

There should be two kinds of accumulation: 
    one for termination probability computation
    another for expected termination time computation
The one for TerProb computation is the same as the above
The one for ETT computation is new, if the first one is computed first, we should be able to incrementally compute 
    the value without re-computing the first one.
*)
type private TerExpCtx<'q, 'm, 'g>
    when 'q : comparison and 'g : comparison and 'm : comparison 
    (rptsa) =
    class
    let stepCount : HashMap<'q * 'm * 'g * TransOp<'q, 'm, 'g, TerOp>, NumericType> option =
        Option.map HashMap.fromMap rptsa.stepCount;
    let expFormulaStk : Stack<Variable<'q, 'g> * RawFormula<Variable<'q, 'g>>> =
        Stack<Variable<'q, 'g> * RawFormula<Variable<'q, 'g>>> (); 
    let mutable expEqSys : (Variable<'q, 'g> * RawFormula<Variable<'q, 'g>>) list = []; 
    member this.getResult () = expEqSys
    interface IFetchVariableFormulaSystem<'q, 'g> with
        member this.getResult () = expEqSys
    end
    interface SpecialContext<'q, 'm, 'g, TerOp, NumericType * NumericType> with
        member this.buildTopVarAndBackToOldVar _ _ = let p = expFormulaStk.Pop () in
                                                     expEqSys <- p :: expEqSys
        member this.copeSp ctx info sop = terSpCope this ctx info sop
//        member this.foldFunc var lst = toRawVar var VTer :: lst
//        member this.genFoldUpInit _ _ _ = []
        member this.genInitAccInfo _ _ = (NUMERIC_ONE, NUMERIC_ZERO)
        member this.signalNewVarConstruction _ _ var = 
            expFormulaStk.Push (PVCExp $ toRawVar var VTer, FConst NUMERIC_ZERO)
        member this.updateStepAccInfo _ info (p, op) = 
            let pp, pStep = info.accInfo in
            let step = match stepCount with
                       | None -> NUMERIC_ONE
                       | Some tab ->
                           // if the table exists but the entry is not found, it means not to count, so 0
                           Option.defaultValue NUMERIC_ZERO $ tab.tryFind (info.curQ, info.curM, info.curGamma, op)
            { info with accInfo = (pp * p, pStep + step) }
        /// `lst` is the `vecD`
        /// mht * \prod_i P[x_i] + \sum_i hp * E[x_i] * \prod_{j /= i} P[x_j]
        member this.notifyUpVars _ info lst =
            let hp, steps = info.accInfo in
            // bugfix : mht = steps * hp -- this mht is not the full one -- but just for this route
            // real mht computation should be all route times their hp
            // but here we slightly abuse the terminology to call mht = steps * hp
            let mht = steps * hp in
            let lst = Seq.toList $ Seq.map (flip toRawVar VTer) lst in
            let mhtProd =
                List.map (PVCProb >> FVar) lst
                |> List.fold (*) (FConst mht)
            in
            let sumOfEachV =
                lstEachAndRest lst
                |> List.map (fun (v, rst) ->
                    List.map (PVCProb >> FVar) rst
                    |> List.fold (*) (FConst hp * FVar (PVCExp v)))
                // bugfix: DO NOT use `reduce` here as the lst may be empty, hence error thrown for `reduce`
                |> List.fold (+) (FConst NUMERIC_ZERO)
            // erroneous implementation
//            let synP, steps = info.accInfo in
//            let accFunc rv f = (FVar << PVCProb) rv * f in
//            let wts = foldWith lst (FConst $ synP * steps) accFunc in
//            let rec accExps rv pre post =
//                let init = FVar $ PVCExp rv in
//                let init = init * FConst synP in
//                let fst = foldWith pre (foldWith post init accFunc) accFunc in
//                fst + match post with
//                      | [] -> FConst NUMERIC_ZERO
//                      | nextRv :: post -> accExps nextRv (rv :: pre) post in
//            let exps = match lst with
//                       | rv :: post -> accExps rv [] post
//                       | []         -> FConst NUMERIC_ZERO in
//            let expFormula = wts + exps in
            updateStkWithNewF expFormulaStk (mhtProd + sumOfEachV) (+)
    end
    end

type private TerExpWithProbPartContext<'q, 'm, 'g>
    when 'q : comparison and 'g : comparison and 'm : comparison 
    (rptsa) =
    class
    let terProbCtx : SpecialContext<'q,'m,'g,_,_> = TerProbCtx ();
    let terExpCtx : SpecialContext<'q,'m,'g,_,_> = TerExpCtx rptsa;
    member x.getPairResult () = 
            (terExpCtx :?> TerExpCtx<'q,'m,'g>).getResult (),
            (terProbCtx :?> TerProbCtx<'q,'m,'g>).getResult ()
    interface IFetchVariableFormulaSystem<'q, 'g> with
        member this.getResult () =
            (terExpCtx :?> TerExpCtx<'q,'m,'g>).getResult () ++
            (terProbCtx :?> TerProbCtx<'q,'m,'g>).getResult ()
    end
    interface SpecialContext<'q, 'm, 'g, TerOp, NumericType * NumericType> with
        member this.copeSp ctx info sop = terSpCope this ctx info sop 
        member this.buildTopVarAndBackToOldVar ctx info =
            terExpCtx.buildTopVarAndBackToOldVar ctx info;
            let info = convertAccInfo info fst in 
            terProbCtx.buildTopVarAndBackToOldVar ctx info;
//        member this.foldFunc var tmp =
//            let f, lst = tmp in
//            (terProbCtx.foldFunc var f, terExpCtx.foldFunc var lst)
//        member this.genFoldUpInit ctx info var =
//            let tInfo = convertAccInfo info fst in
//            (terProbCtx.genFoldUpInit ctx tInfo var, terExpCtx.genFoldUpInit ctx info var)
        member this.genInitAccInfo ctx var = terExpCtx.genInitAccInfo ctx var
        member this.signalNewVarConstruction ctx info var =
            terExpCtx.signalNewVarConstruction ctx info var;
            let info = convertAccInfo info fst in
            terProbCtx.signalNewVarConstruction ctx info var 
        member this.updateStepAccInfo ctx info (p, op) = terExpCtx.updateStepAccInfo ctx info (p, op)
        member this.notifyUpVars ctx info upVars =
//            let f, lst = tmp in
            terExpCtx.notifyUpVars ctx info upVars;
            let info = convertAccInfo info fst;
            terProbCtx.notifyUpVars ctx info upVars
    end
    end


/// construct the special context for DRA-synchronised rPTSA construction
/// no semantic check is performed (actually almost no way to efficiently check this synchronisation)
/// the word `synchronised` is just for reminding that do not put raw rPTSA in
/// but please firstly synchronise the rPTSA with a DRA
type DRASynCtx<'q, 'm, 'g> when 'q : comparison and 'g : comparison
    (downQsMap) = 
    class
    let varStk = Stack<AbsVar<'q, 'g>> (); 
    let tripsStk = Stack<(Set<'q> * RawFormula<Variable<'q, 'g>>) list> ();
    let upsStk = Stack<HashMap<Variable<'q, 'g>, (Set<'q> * RawFormula<Variable<'q, 'g>>) list>> ();
    let mutable eqSysTrips = [];
    let mutable eqSysUps = [];
    let ofLen1 (AbsVar (_, _, lenD)) = lenD = 1
    let prevVar (AbsVar (D, g, lenD)) = AbsVar (List.take (lenD - 1) D, g, lenD - 1)
    let postVar (AbsVar (D, g, lenD)) q = AbsVar (D ++ [q], g, lenD + 1)
    /// trips: x = [(Set of Q involved, corresponding formula)]
    member x.getTrips = eqSysTrips
    member x.getUps = eqSysUps
//    member this.foldFunc var tmp = let f, maybeUp = tmp in
//                                   let rv = PVCProb $ toRawVar var VUp in
//                                   if maybeUp = Some rv then tmp  // ignore the value
//                                   else (f * FVar rv, maybeUp) 
//    member this.genFoldUpInit _ info maybeAdditionalUp = 
//        (FConst $ snd info.accInfo, Option.map (PVCProb << flip toRawVar VUp) maybeAdditionalUp)
    interface SpecialContext<'q, 'm, 'g, unit, Set<'q> * NumericType> with
        member this.buildTopVarAndBackToOldVar ctx info =
            let var = varStk.Pop () in
            if isUp var then eqSysUps   <- (PVCProb $ toRawVar var VUp, upsStk.Pop ()) :: eqSysUps;
                             // build the prevVar, note that length of `D` should be > 1 
                             if not $ ofLen1 var then buildVarAndDependentVars_internal_dfs ctx this (prevVar var) |> ignore;
                             let _, _, g = info.getConfig () in
                             // build the postVars 
                             Option.defaultValue Seq.empty (Map.tryFind g downQsMap)
                             |> Seq.iter (fun q -> buildVarAndDependentVars_internal_dfs ctx this (postVar var q) |> ignore) 
            else             eqSysTrips <- (PVCProb $ toRawVar var VUp, tripsStk.Pop ()) :: eqSysTrips
        member this.copeSp _ _ _ = ()  // do nothing 
        member this.genInitAccInfo _ _ = (Set.empty, NUMERIC_ONE)
        member this.signalNewVarConstruction _ _ var = varStk.Push var; 
                                                       if isUp var then upsStk.Push $ HashMap () 
                                                       else             tripsStk.Push [] 
        member this.updateStepAccInfo _ info (p, _) = 
            let set, pp = info.accInfo in 
            { info with accInfo = (Set.add info.curQ set, pp * p) }
        member this.notifyUpVars _ info upVars =
            failwith "Deprecated Version, use the partial version instead";
            let f, maybeRv = undefined upVars in  // originally: upVars => tmp
            let set, _ = info.accInfo in
            match maybeRv with
            | Some upVar -> let ups = upsStk.Peek () in
                            flip (HashMap.compute upVar) ups $ fun maybeLst ->
                                let lst = Option.defaultValue [] maybeLst in 
                                Some $ (set, f) :: lst 
            | None       -> let lst = tripsStk.Pop () in
                            tripsStk.Push $ (set, f) :: lst 
    end
    end


/// construct the special context for DRA-synchronised rPTSA construction
/// no semantic check is performed (actually almost no way to efficiently check this synchronisation)
/// the word `synchronised` is just for reminding that do not put raw rPTSA in
/// but please firstly synchronise the rPTSA with a DRA
///
/// Ignoring constructing the extra-Trips, compared to the above version
type DRAPartialSynCtx<'q, 'm, 'g> when 'q : comparison and 'g : comparison
    () = 
    class
    let vfStk = Stack<Variable<'q, 'g> * (NumericType * Variable<'q, 'g> list * Set<'q>) list> ();
    let mutable eqSys = [];
    /// returns: [(v, [(p, vs, synSet)])]
    /// v = \sum p * vs with synSet
    member x.getEqSys = eqSys
    interface SpecialContext<'q, 'm, 'g, unit, Set<'q> * NumericType> with
        member this.buildTopVarAndBackToOldVar _ _ = eqSys <- vfStk.Pop () :: eqSys
        member this.copeSp _ _ _ = ()  // do nothing 
        member this.genInitAccInfo _ _ = (Set.empty, NUMERIC_ONE)
        member this.signalNewVarConstruction _ _ var = vfStk.Push (PVCProb $ toRawVar var VUp, [])
        member this.updateStepAccInfo _ info (p, _) = 
            let set, pp = info.accInfo in 
            { info with accInfo = (Set.add info.curQ set, pp * p) }
        member this.notifyUpVars _ info upVars =
            let v, lst = vfStk.Pop () in
            let set, p = info.accInfo in
            vfStk.Push (v, (p, Seq.toList $ Seq.map (PVCProb << flip toRawVar VUp) upVars, set) :: lst)
    end
    end


/// the special environment for generating strings
type CharGen<'c, 'q> =
    | CharGen of char:'c * next:'q
    | GenTer

/// the non-terminal of the converted MCFG is just the variable
type ConvMCFGNonTml<'q, 'g> = RawVar<'q, 'g>

type ConvMCFGVar<'g> =
    | ConvMCFGVar of 'g * uint
    override x.ToString () =
        match x with
        | ConvMCFGVar (g, idx) -> $"{g}@{idx}"

/// convert a string-generating rPTSA to its corresponding MCFG
/// The probability will be ignored -- as the probability itself will require further computation
/// This quick context is just for showing the conversion from rTSA
/// For this reason, it is recommended that each rule of rPTSA is with low probability
/// so that the total probability of a specific status (q, m, gamma) is lower than 1 in order to pass
/// the probability check but just to use this functionality of translation
///
/// the probability value will not be checked
type MCFGConvCtx<'q, 'm, 'g, 'c>
    when 'q : comparison and 'g : comparison () =
    class
    let varStk : Stack<
        ConvMCFGNonTml<'q, 'g> *
        (LeftHandSide<'c, ConvMCFGVar<'g>> *
         RightHandSide<ConvMCFGNonTml<'q, 'g>, ConvMCFGVar<'g>>) list
        > = Stack ()
    let mutable rules : (ConvMCFGNonTml<'q, 'g> *
        (LeftHandSide<'c, ConvMCFGVar<'g>> *
         RightHandSide<ConvMCFGNonTml<'q, 'g>, ConvMCFGVar<'g>>) list) list = []
    member x.getGeneratedRules () = rules
    // the accumulated information will keep INVERSED information
    interface SpecialContext<'q, 'm, 'g, CharGen<'c, 'q>, MCFGSymbol<'c, ConvMCFGVar<'g>> list list> with
        member this.buildTopVarAndBackToOldVar _ _ = rules <- varStk.Pop () :: rules
        member this.copeSp ctx info genChar =
            match genChar with
            | CharGen (c, q) ->
                let accInfo =
                    match info.accInfo with
                    | hd :: rst -> (Terminal c :: hd) :: rst
                    | _         -> IMPOSSIBLE () in
                let info = { info with accInfo = accInfo } in
                traverseAndBuild ctx (info.updateQ q) this
            | GenTer ->
                if isNullSeq info.curD then dispatchUpwardCompute ctx info this None
        member this.genInitAccInfo _ _ = [[]]
        // save a new rule for the top non-terminal
        member this.notifyUpVars _ info upVars =
            // as the accumulation is reversed, get it in the right direction
            let lhs = List.rev $ List.map List.rev info.accInfo in
            let rhs =
                flip Seq.map upVars (fun (AbsVar (_, g, lenD) as v) ->
                    let nt = toRawVar v VUp in
                    let vars = List.map (fun dim -> ConvMCFGVar (g, uint dim)) [0..(lenD - 1) / 2] in
                    (nt, vars))  // (v, dims)
                |> Seq.toList
            in
            let v, lst = varStk.Pop () in
            varStk.Push (v, (lhs, rhs) :: lst)
        member this.signalNewVarConstruction _ _ var = varStk.Push (toRawVar var VUp, [])
        member this.updateStepAccInfo _ info (_, _) = info
    end
    interface NotifyUpDownSp<'q, 'm, 'g, CharGen<'c, 'q>, MCFGSymbol<'c, ConvMCFGVar<'g>> list list> with
        member this.notifyDown _ info = { info with accInfo = [] :: info.accInfo }
        member this.notifyUp _ info (_, g, _) =
            let _, lenD = info.getUpD g in
            let dim = lenD / 2 in
            let accInfo =
                match info.accInfo with
                | hd :: lst -> (Variable (ConvMCFGVar (g, uint dim)) :: hd) :: lst
                | _         -> IMPOSSIBLE () in
            { info with accInfo = accInfo }
    end
    end


// ------------------------------------------ Usable Interfaces ------------------------------------------

/// construct the abstract x0 variable from the given general rPTSA
let absX0 rptsa = AbsVar ([rptsa.q0], rptsa.g0, 1)

let terProbX0 rptsa = PVCProb $ toRawVar (absX0 rptsa) VTer
let terExpX0 rptsa = PVCExp $ toRawVar (absX0 rptsa) VTer

let buildEquationSystem rptsa sp =
    let ctx = mkCtx Flags.KPTSA_NORMALISED rptsa in
    let absX0 = absX0 rptsa in
    buildVarAndDependentVars ctx sp absX0

/// a supportive function to build things 
let buildResult
        ctx
        (sp : 'a when 'a :> SpecialContext<_,_,_,_,_> and 'a :> IFetchVariableFormulaSystem<_,_>)
        rptsa
        wrapX0 =
    let absX0 = absX0 rptsa in 
    match buildVarAndDependentVars ctx sp absX0 with
    | BVRNonStructZeroDFS -> sp.getResult ()
    | BVRUnknownBFS       -> sp.getResult ()
    | BVRStructuralZero   -> [(wrapX0 absX0, FConst NUMERIC_ZERO)]
    | BVRInQueueBFS       -> IMPOSSIBLE ()  // this should not be a possible result
    | BVRRecursiveDFS     -> IMPOSSIBLE ()  // this should not be a possible result

/// the (temporary) general run function for the new implementation for termination probabilistic EqSys construction
let terProbFormulaConstructWithCtx normalised rptsa =
    let ctx = mkCtx normalised rptsa in
    let sp = TerProbCtx () in
    (ctx, buildResult ctx sp rptsa $ fun x0 -> PVCProb $ toRawVar x0 VTer)  // P[x0]
let terProbFormulaConstruct normalised rptsa =
    snd $ terProbFormulaConstructWithCtx normalised rptsa
    
let generaliseKPTSA (kptsa : KPTSA) =
    generaliseRPTSAWithSp kptsa (function | TransTer -> SpTer | TransDiv -> SpDiv | _ -> IMPOSSIBLE ())

/// the (temporary) general run function for the new implementation for expected termination time EqSys construction
/// `incremental` means to only construct the expectation part
let terExpFormulaConstruct incrementalStuff normalised rptsa =
    let ctx = match incrementalStuff with
              | Some ctx -> { ctx with noUpVar = normalised;
                                       exploredCounter = 0uL;
                                       buildMode = BVMReTravel { todoQueue = Queue<_> ();
                                                                 alreadyEncountered = HashSet<_> () } }
              | None     -> mkCtx normalised rptsa in
    let wrapX0 x0 = PVCExp $ toRawVar x0 VTer  // E[x0]
    match incrementalStuff with
    | None   -> let sp = TerExpWithProbPartContext rptsa in
                buildResult ctx sp rptsa wrapX0
    | Some _ -> let sp = TerExpCtx rptsa in
                buildResult ctx sp rptsa wrapX0

let rec computeExpr expr (values : NumericType[]) : NumericType =
    let recall e = computeExpr e values in 
    match expr with
    | EAdd (e1, e2) ->
        recall e1 + recall e2
    | EMul (e1, e2) ->
        recall e1 * recall e2
    | EMinus (e1, e2) ->
        recall e1 - recall e2
    | EDiv (e1, e2) ->
        let re2 = recall e2
        if re2 = NUMERIC_ZERO then
            failwith "try dividing by 0"
        recall e1 - re2
    | EConst c -> c
    | EVar v -> values[v]

/// if the current value should be round up, it will do the job.
let computeExprArray (l : Expr []) values =
    let values =
        if Flags.ALLOW_ITER_ROUND_UP then Array.map NumericType.RoundUp values
        else values
    Array.map (flip computeExpr values) l

let isNormalisedRPTSA (rptsa : GeneralRPTSA<_,_,_,TerOp>) =
    Map.toSeq rptsa.delta
    |> Seq.forall (fun ((_, _, g), lst) ->
        List.forall (snd >> function | OpTransSp SpTer -> g = rptsa.g0 | _ -> true) lst)

/// used for normalisation
type AdditionalState<'s> =
    | ASOrigin of 's
    | ASTer
    override x.ToString () =
        match x with
        | ASOrigin st -> toString st
        | ASTer       -> "$qTer"

/// move the termination point to be happening only at root
/// NOT TESTED
let normaliseRPTSA (rptsa : GeneralRPTSA<_,_,_,TerOp>) =
    // initialise StepCount
    let sc =
        match rptsa.stepCount with
        | Some sc -> sc
        | None    ->
            // count all rules in this case
            rptsa.delta
            |> Map.toSeq
            |> Seq.map (fun ((q, m, g), lst) ->
                List.map (fun (_, op) ->
                    ((q, m, g, op), NUMERIC_ONE)) lst)
            |> Seq.concat
            |> Map.ofSeq
    in
    let mapOp m g op =
        match op with
        | OpTransSp SpTer ->
            if g = rptsa.g0 then OpTransSp SpTer
            else OpTransDown (ASTer, m)
        | OpTransState st -> OpTransState $ ASOrigin st
        | OpTransSp SpDiv -> OpTransSp SpDiv
        | OpTransUp (q', m', g') -> OpTransUp (ASOrigin q', m', g')
        | OpTransDown (q', m') -> OpTransDown (ASOrigin q', m')
    in
    // translate rules in StepCount
    let mapStepCounts ((q, m, g, op), count) =
        ((ASOrigin q, m, g, mapOp m g op), count) in
    let newStepCount =
        Map.toSeq sc
        |> Seq.map mapStepCounts
        |> Map.ofSeq
    in
    let replaceRuleInRuleList ((q, m, g), lst) =
        let lst = flip List.map lst $ fun (p, op) -> (p, mapOp m g op) in
        ((ASOrigin q, m, g), lst)
    in
    let replacedRules =
        rptsa.delta
        |> Map.toList
        // replace rule at each step
        |> List.map replaceRuleInRuleList
    in
    // relay rule for each m, g
    let relayRules =
        rptsa.delta
        |> Map.toList
        |> List.map (fun ((_, m, g), _) -> (m, g))
        |> List.distinct
        |> List.map (fun (m, g) -> ((ASTer, m, g), [
            (NUMERIC_ONE,
             if g = rptsa.g0 then OpTransSp SpTer
             else OpTransDown (ASTer, m))
        ]))
    in
    let newDelta =
        replacedRules ++ relayRules
        |> Map.ofList
    in
    let mapSd sd =
        Map.toList sd
        |> List.map (fun ((q, g), lst) ->
            ((ASOrigin q, g),
             ASTer :: List.map ASOrigin lst))
        |> Map.ofSeq
    in
    let ret =
        { q0 = ASOrigin rptsa.q0
          m0 = rptsa.m0
          g0 = rptsa.g0
          k = rptsa.k
          delta = newDelta
          kMap = rptsa.kMap
          stateDependencies = Option.map mapSd rptsa.stateDependencies
          stepCount = Some newStepCount }
    in
    innerDebugPrint $"Normalised rPTSA:\n{ret}"
    ret
